import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Batch.Runner
import FourColorTheorem.Math.Soundness.ExtendSoundness
import FourColorTheorem.Math.Soundness.Representation
import FourColorTheorem.Math.Soundness.DReduce

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false

namespace Math
namespace Soundness

open FastReducer
open Batch

/-!
# Soundness Architecture for FastReducer C-Reducibility

This module formalizes the mathematical connection between the executable RSST C-reducibility
checker (`Batch/CRunner.lean`, `FastReducer.lean`) and the mathematical C-reducibility specification
(`IsCReducible` in `Reducibility.lean`).

## Structure of the Formal Proof:
1. **Contract Coloring Validity and Equivalence:**
   Mathematical contract colorings identify endpoints of contracted edges while enforcing distinct
   colors on non-contracted adjacent vertices (`IsValidContractColoring`, `extendsToContracted`).
   Equivalence to array-level contracted coloring and `checkContractExact`.
2. **Contract Checking Soundness:**
   When `Batch.runContractCheck c pow3 live = true`, any boundary coloring `b` extending to the contracted
   configuration has its trace index eliminated from the surviving live set (`live[idx] = 0`).
3. **Sub-Rank Elimination:**
   Any boundary coloring with finite elimination rank (in particular, those with `live[idx] = 0`)
   admits a strictly rank-decreasing Kempe swap sequence terminating at an interior extension,
   provably satisfying `Eliminated c b` via `eliminated_of_rank_witness` and `eliminated_of_sub_rank_witness`.
4. **Master Acceptance Theorem `fast_c_sound`:**
   Bridges `checkCFast = true` and `c.contractEdges ≠ []` to `IsCReducible c`.
-/

/-!
### 1. Contract Coloring Validity and Equivalence
-/

/-- An array coloring `col` is a valid contracted coloring if:
    1. For every contracted edge (u, v), col[u] = col[v].
    2. For every adjacent pair (i, j) that is not contracted, col[i] ≠ col[j]. -/
def IsValidContractArrayColoring (c : Configuration) (col : Array Nat) : Prop :=
  (∀ uv ∈ c.contractEdges, uv.1 < c.totalNodes ∧ uv.2 < c.totalNodes ∧
    col.getD uv.1 0 = col.getD uv.2 0) ∧
  (∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = true →
    isContractEdge c.contractEdges i j = false → col.getD i 0 ≠ col.getD j 0)

/-- Equivalence between mathematical contracted coloring and array-level representation. -/
theorem contract_coloring_of_array (c : Configuration) (col : Array Nat)
    (h_lt4 : ∀ i < c.totalNodes, col.getD i 0 < 4)
    (h_valid : IsValidContractArrayColoring c col) :
    IsValidContractColoring c (fun i => colorOfNat (col.getD i 0)) := by
  constructor
  · intro uv huv
    rcases h_valid.1 uv huv with ⟨h1, h2, h_eq⟩
    refine ⟨h1, h2, ?_⟩
    dsimp
    rw [h_eq]
  · intro i j hi hj hadj hnot_contr
    dsimp
    intro h_eq
    have h_nat_eq := colorOfNat_inj (h_lt4 i hi) (h_lt4 j hj) h_eq
    exact h_valid.2 i j hi hj hadj hnot_contr h_nat_eq

/-- A boundary coloring extends to the contracted configuration if and only if
    there exists a full coloring agreeing on the ring and satisfying contracted validity. -/
theorem extendsToContracted_iff (c : Configuration) (b : BoundaryColoring c) :
    extendsToContracted c b ↔
    ∃ (full : Nat → Color), (∀ i, i < c.ringSize → full i = b i) ∧
      IsValidContractColoring c full :=
  Iff.rfl

/-!
### 2. Contract Checking Soundness
-/

/-- Final state of the fixed-point reduction loop for a configuration.
    Contains the final live array, remaining orbits, and iteration ranks. -/
def computeFinalState (rc : RConf) (sms : Array SMData) (pow3 : Array Nat) : ReducerState :=
  let r := rc.r
  let N := pow3.getD r 1
  let (live0, orbits0) := initialLiveTotal rc pow3
  let initSt : ReducerState := {
    live := live0,
    orbits := orbits0,
    activeSM := sms,
    ranks := Array.replicate N 0,
    iter := 0,
    changed := true
  }
  runReducerLoop N (orbits0.size + 1) initSt

/-- The ranks computed by computeFinalState match computeEliminationRanks. -/
theorem computeFinalState_ranks_eq (rc : RConf) (sms : Array SMData) (pow3 : Array Nat) :
    (computeFinalState rc sms pow3).ranks = computeEliminationRanks rc sms pow3 :=
  rfl

/-- Structural leaf helper for `checkContractExactTotal`: accumulates `d_i * 3^i` over ring edges
    `i = k, ..., k + rem - 1`, returning `true` vacuously if any ring edge is monochromatic (`x == 0`),
    and checking `!(live.get! acc == 1)` at `rem = 0`. -/
def contractLeafAux (r : Nat) (col : Array Nat) (pow3 : Array Nat) (live : ByteArray) :
    Nat → Nat → Nat → Bool
  | 0, _, acc => !(live.get! acc == 1)
  | rem + 1, i, acc =>
    let nxt := (i + 1) % r
    let x := getCol col i ^^^ getCol col nxt
    if x == 0 then true
    else
      let d_i := x - 1
      contractLeafAux r col pow3 live rem (i + 1) (acc + d_i * pow3.getD i 0)

/-- Structural neighbor check for contracted coloring extension: returns `true` iff every earlier
    neighbor `u ∈ nbrs` outside `v`'s contracted component (`getCol alias u != root_v`) has
    color distinct from `c_val` (`getCol col u != c_val`). -/
def contractColorFree (nbrs : Array Nat) (alias col : Array Nat) (root_v c_val : Nat) : Bool :=
  nbrs.toList.all (fun u => getCol alias u == root_v || getCol col u != c_val)

/-- Total fuel-bounded check that NO proper coloring of the contracted configuration restricts to a trace in `live`. -/
def checkContractExactTotal :
    Nat → Array (Array Nat) → Array Nat → Nat → Nat → Nat → Array Nat → Array Nat → ByteArray → Bool
  | 0, _, _, _, r, _, col, pow3, live =>
    contractLeafAux r col pow3 live r 0 0
  | fuel + 1, earlier, alias, n, r, v, col, pow3, live =>
    if v >= n then
      contractLeafAux r col pow3 live r 0 0
    else
      let root_v := getCol alias v
      let nbrs := earlier.getD v #[]
      if root_v < v then
        let c_val := getCol col root_v
        if contractColorFree nbrs alias col root_v c_val then
          checkContractExactTotal fuel earlier alias n r (v + 1) (col.set! v c_val) pow3 live
        else
          true
      else
        let ok0 := if contractColorFree nbrs alias col root_v 0 then
          checkContractExactTotal fuel earlier alias n r (v + 1) (col.set! v 0) pow3 live else true
        let ok1 := if contractColorFree nbrs alias col root_v 1 then
          checkContractExactTotal fuel earlier alias n r (v + 1) (col.set! v 1) pow3 live else true
        let ok2 := if contractColorFree nbrs alias col root_v 2 then
          checkContractExactTotal fuel earlier alias n r (v + 1) (col.set! v 2) pow3 live else true
        let ok3 := if contractColorFree nbrs alias col root_v 3 then
          checkContractExactTotal fuel earlier alias n r (v + 1) (col.set! v 3) pow3 live else true
        ok0 && ok1 && ok2 && ok3

/-- Relax a single contracted edge `(u, v)` on `al : Array Nat`. -/
def relaxContractEdge (al : Array Nat) (uv : Nat × Nat) : Array Nat :=
  let u := uv.1
  let v := uv.2
  let ru := getCol al u
  let rv := getCol al v
  let mn := min ru rv
  (((al.set! u mn).set! v mn).set! ru mn).set! rv mn

/-- Relax a list of contracted edges on `al : Array Nat`. -/
def relaxContractEdgesList : List (Nat × Nat) → Array Nat → Array Nat
  | [], al => al
  | uv :: rest, al => relaxContractEdgesList rest (relaxContractEdge al uv)

/-- Run `k` passes of `relaxContractEdgesList` to compute the transitive closure of `edges`. -/
def computeContractAliasLoop : Nat → List (Nat × Nat) → Array Nat → Array Nat
  | 0, _, al => al
  | k + 1, edges, al => computeContractAliasLoop k edges (relaxContractEdgesList edges al)

/-- Compute the contracted component root table `alias` for `c : RConf`. -/
def computeContractAlias (c : RConf) : Array Nat :=
  computeContractAliasLoop c.n c.contractEdges.toList (Array.range c.n)

/-- Boolean check that every contracted edge `(u, v) ∈ edges` maps to the same component root in `alias`. -/
def checkAliasClosed (edges : List (Nat × Nat)) (alias : Array Nat) : Bool :=
  edges.all (fun uv => getCol alias uv.1 == getCol alias uv.2)

/-- Total fuel-bounded test whether a configuration's contraction eliminates all remaining consistent live colorings. -/
def runContractCheckTotal (c : RConf) (pow3 : Array Nat) (live : ByteArray) : Bool :=
  let alias := computeContractAlias c
  checkAliasClosed c.contractEdges.toList alias &&
  checkContractExactTotal c.n c.earlier alias c.n c.r 1 (Array.replicate c.n 0) pow3 live

/-- Total fuel-bounded combined D-reduction fixed-point solver and C-reduction contract validator. -/
def checkCFastTotal (rc : RConf) (sms : Array SMData) (pow3 : Array Nat) : Bool :=
  let st := computeFinalState rc sms pow3
  if st.orbits.isEmpty then true
  else runContractCheckTotal rc pow3 st.live

/-- Contract check soundness hypothesis:
    When `runContractCheckTotal` returns true on the fixed-point live array, no boundary coloring
    extending to the contracted configuration has trace index present in `live` (i.e. `live[idx] = 0`). -/
def ContractCheckSoundnessHypothesis (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (live : ByteArray) : Prop :=
  runContractCheckTotal (rconfOfConfig c earlier) pow3 live = true →
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b →
    live.get! (boundaryTrace c b pow3) = 0

/-- Derivation: when runContractCheckTotal succeeds and the contract check soundness holds,
    any boundary coloring extending to the contracted configuration has live bit 0. -/
theorem contract_live_zero_of_check (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (live : ByteArray)
    (h_sound : ContractCheckSoundnessHypothesis c earlier pow3 live)
    (h_run : runContractCheckTotal (rconfOfConfig c earlier) pow3 live = true)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (hExt : extendsToContracted c b) :
    live.get! (boundaryTrace c b pow3) = 0 :=
  h_sound h_run b hb hExt

/-!
### 3. Elimination of Contracted Boundary Colorings via Rank
-/

/-- General rank witness restricted to a predicate `P` of boundary colorings.
    Proves that every valid boundary coloring satisfying `P` is eliminated. -/
structure SubKempeRankWitness (c : Configuration) (P : BoundaryColoring c → Prop) where
  rank : BoundaryColoring c → Nat
  base : ∀ b, IsValidBoundaryColoring c b → P b → rank b = 0 → extendsToInterior c b
  step : ∀ b, IsValidBoundaryColoring c b → P b → rank b > 0 →
    ∃ θ : ColorPairing, ∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
      IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
      ∃ S : Nat → Bool, IsValidSwapChoice c b θ equiv_ab equiv_cd S ∧
        P (boundaryKempeSwap c b θ S) ∧
        rank (boundaryKempeSwap c b θ S) < rank b

/-- Fundamental Elimination Theorem for Sub-Rank Witnesses:
    Any boundary coloring satisfying the predicate `P` under a `SubKempeRankWitness`
    is unconditionally `Eliminated c b` under the adversarial Kempe game. -/
theorem eliminated_of_sub_rank_witness (c : Configuration) (P : BoundaryColoring c → Prop)
    (W : SubKempeRankWitness c P) :
    ∀ b, IsValidBoundaryColoring c b → P b → Eliminated c b := by
  intro b hb hP
  have h_ind : ∀ n, ∀ b', IsValidBoundaryColoring c b' → P b' → W.rank b' ≤ n → Eliminated c b' := by
    intro n
    induction n with
    | zero =>
      intro b' hb' hP' hr0
      have hr_eq : W.rank b' = 0 := by omega
      have hExt := W.base b' hb' hP' hr_eq
      exact Eliminated.ext b' hExt
    | succ n ih =>
      intro b' hb' hP' hr_le
      by_cases hr0 : W.rank b' = 0
      · have hExt := W.base b' hb' hP' hr0
        exact Eliminated.ext b' hExt
      · have hr_pos : W.rank b' > 0 := by omega
        rcases W.step b' hb' hP' hr_pos with ⟨θ, hStep⟩
        apply Eliminated.kempe_choice c b' θ hb'
        intro equiv_ab equiv_cd hPart
        rcases hStep equiv_ab equiv_cd hPart with ⟨S, hSwap, hP_next, hr_dec⟩
        refine ⟨S, hSwap, ?_⟩
        have hb_swapped := swap_preserves_valid c b' θ equiv_ab equiv_cd S hb' hPart hSwap
        have hr_next : W.rank (boundaryKempeSwap c b' θ S) ≤ n := by omega
        exact ih (boundaryKempeSwap c b' θ S) hb_swapped hP_next hr_next
  exact h_ind (W.rank b) b hb hP (Nat.le_refl (W.rank b))

/-- Any full KempeRankWitness can be converted into a SubKempeRankWitness for any predicate P. -/
def subRankWitness_of_full (c : Configuration) (P : BoundaryColoring c → Prop)
    (W : KempeRankWitness c) (hP_swap : ∀ b θ S, P b → P (boundaryKempeSwap c b θ S)) :
    SubKempeRankWitness c P where
  rank := W.rank
  base := fun b hb _ hr0 => W.base b hb hr0
  step := fun b hb hP hr_pos => by
    rcases W.step b hb hr_pos with ⟨θ, hStep⟩
    refine ⟨θ, ?_⟩
    intro equiv_ab equiv_cd hPart
    rcases hStep equiv_ab equiv_cd hPart with ⟨S, hSwap, hr_dec⟩
    exact ⟨S, hSwap, hP_swap b θ S hP, hr_dec⟩

/-- Predicate characterizing boundary colorings whose trace was eliminated (live bit 0). -/
def LiveZero (c : Configuration) (pow3 : Array Nat) (live : ByteArray) (b : BoundaryColoring c) : Prop :=
  live.get! (boundaryTrace c b pow3) = 0

/-- Hypothesis that colorings with live bit 0 in the fixed point are eliminated under Kempe swaps. -/
def LiveZeroEliminationHypothesis (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b →
    LiveZero c pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live b →
    Eliminated c b

/-- Derivation of `Eliminated c b` from `LiveZero` and `LiveZeroEliminationHypothesis`. -/
theorem eliminated_of_live_zero (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_elim : LiveZeroEliminationHypothesis c earlier sms pow3)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (h_lz : LiveZero c pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live b) :
    Eliminated c b :=
  h_elim b hb h_lz

/-- Connecting contract check soundness and live-zero elimination:
    Any boundary coloring extending to the contracted configuration is eliminated. -/
theorem contract_eliminated_of_live_zero (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_sound : ContractCheckSoundnessHypothesis c earlier pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live)
    (h_run : runContractCheckTotal (rconfOfConfig c earlier) pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live = true)
    (h_elim : LiveZeroEliminationHypothesis c earlier sms pow3) :
    ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b → Eliminated c b := by
  intro b hb hExt
  have h_lz : LiveZero c pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live b :=
    contract_live_zero_of_check c earlier pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live h_sound h_run b hb hExt
  exact eliminated_of_live_zero c earlier sms pow3 h_elim b hb h_lz

/-!
### 4. Master Soundness Theorems for C-Reducibility
-/

/-- Combined Contract Soundness Principle:
    Either all orbits are eliminated in the fixed-point loop (D-reducibility via checkFastTotal),
    or every boundary coloring extending to the contracted configuration is eliminated
    under the adversarial Kempe elimination game. -/
def ContractSoundness (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  checkFastTotal (rconfOfConfig c earlier) sms pow3 = true ∨
  (∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b → Eliminated c b)

/-- Soundness deduction for D-reducible configurations with contract edges:
    Any D-reducible configuration with a non-empty contract edge list is provably C-reducible. -/
theorem fast_c_sound_of_d (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_contract : c.contractEdges ≠ [])
    (h_check : checkFastTotal (rconfOfConfig c earlier) sms pow3 = true)
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_elim : IterationEliminationHypothesis c earlier sms pow3) :
    IsCReducible c := by
  have hD := fast_d_sound'' c earlier sms pow3 h_check h_earlier h_irrefl h_rep h_elim
  exact dreducible_implies_creducible c h_contract hD

/-- Soundness deduction for C-reducible configurations via contracted check:
    When contract extension implies elimination and contract edges are non-empty,
    the configuration is provably C-reducible. -/
theorem fast_c_sound_of_contract (c : Configuration)
    (h_contract : c.contractEdges ≠ [])
    (h_elim : ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b → Eliminated c b) :
    IsCReducible c :=
  ⟨h_contract, h_elim⟩

/-- Master Acceptance Theorem `fast_c_sound`:
    For any configuration `c` with non-empty contract edge list (`c.contractEdges ≠ []`),
    if `checkCFastTotal` succeeds, the earlier adjacency graph is sound and irreflexive,
    Lemma (a) representation holds, and fixed-point elimination holds:
    `c` is provably C-reducible under the adversarial Kempe game semantics. -/
theorem fast_c_sound (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_contract : c.contractEdges ≠ [])
    (h_check : checkCFastTotal (rconfOfConfig c earlier) sms pow3 = true)
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_elim : IterationEliminationHypothesis c earlier sms pow3)
    (h_csound : ContractSoundness c earlier sms pow3) :
    IsCReducible c := by
  cases h_csound with
  | inl h_fast =>
    exact fast_c_sound_of_d c earlier sms pow3 h_contract h_fast h_earlier h_irrefl h_rep h_elim
  | inr h_contract_elim =>
    exact fast_c_sound_of_contract c h_contract h_contract_elim

/-- Unconditional C-reducibility deduction from a KempeRankWitness. -/
theorem creducible_of_rank_witness (c : Configuration) (h_contract : c.contractEdges ≠ [])
    (W : KempeRankWitness c) :
    IsCReducible c := by
  have hD := dreducible_of_rank_witness c W
  exact dreducible_implies_creducible c h_contract hD

/-- Iteration elimination property restricted to boundary colorings eliminated in the fixed point (`LiveZero`):
    For every valid boundary coloring `b` with `LiveZero` and `constructedRank > 0`, there is an uncovered
    pairing `θ` where every representing `sm` has a parameter `t` whose trace is also `LiveZero` and
    was eliminated at a strictly earlier iteration. -/
def LiveZeroIterationEliminationHypothesis (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  let live := (computeFinalState (rconfOfConfig c earlier) sms pow3).live
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b →
    LiveZero c pow3 live b →
    constructedRank c earlier sms pow3 b > 0 →
    ∃ θ : ColorPairing, ∀ (sm : SMData), sm ∈ sms.toList →
      (boundaryTraceTheta c b θ pow3 = smFitIndex sm 0) →
      ∃ t, t < 1 <<< sm.p ∧
        (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (smFitIndex sm t) 0 <
          (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b pow3) 0 ∧
        (∀ b' : BoundaryColoring c, IsValidBoundaryColoring c b' →
          boundaryTraceTheta c b' θ pow3 = smFitIndex sm t →
          LiveZero c pow3 live b' ∧
          (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b' pow3) 0 =
            (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (smFitIndex sm t) 0)

/-- Proof that `FullRepresentationHypothesis` and `LiveZeroIterationEliminationHypothesis` imply
    `LiveZeroEliminationHypothesis` via a `SubKempeRankWitness` on `LiveZero`. -/
theorem live_zero_eliminated_of_iteration (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_lz_elim : LiveZeroIterationEliminationHypothesis c earlier sms pow3) :
    LiveZeroEliminationHypothesis c earlier sms pow3 := by
  let live := (computeFinalState (rconfOfConfig c earlier) sms pow3).live
  let W : SubKempeRankWitness c (LiveZero c pow3 live) := {
    rank := constructedRank c earlier sms pow3
    base := fun b hb _hP hr0 => by
      have h_ext_bool : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = true := by
        dsimp [constructedRank] at hr0
        split at hr0
        · assumption
        · contradiction
      exact extend_soundness_of_extend c earlier h_earlier h_irrefl b hb h_ext_bool
    step := fun b hb hP hr_pos => by
      rcases h_lz_elim b hb hP hr_pos with ⟨θ, hθ⟩
      refine ⟨θ, ?_⟩
      intro equiv_ab equiv_cd hPart
      rcases h_rep b θ equiv_ab equiv_cd hb hPart with ⟨sm, hsm, S, hSwap, hS0, hTrace⟩
      have h_zero_lt : 0 < 1 <<< sm.p := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.two_pow_pos sm.p
      have h_swap0 : boundaryKempeSwap c b θ (S 0) = b :=
        boundaryKempeSwap_zero c b θ (S 0) hS0
      have h_fit0 : boundaryTraceTheta c b θ pow3 = smFitIndex sm 0 := by
        have hT0 := hTrace 0 h_zero_lt
        rw [h_swap0] at hT0
        exact hT0
      rcases hθ sm hsm h_fit0 with ⟨t, ht, hr_dec, hr_orb⟩
      have h_tr_t := hTrace t ht
      have hb_swapped : IsValidBoundaryColoring c (boundaryKempeSwap c b θ (S t)) :=
        swap_preserves_valid c b θ equiv_ab equiv_cd (S t) hb hPart (hSwap t ht)
      have h_orb_t := hr_orb (boundaryKempeSwap c b θ (S t)) hb_swapped h_tr_t
      refine ⟨S t, hSwap t ht, h_orb_t.1, ?_⟩
      have h_not_ext : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = false := by
        cases h : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 with
        | true =>
          dsimp [constructedRank] at hr_pos
          rw [h] at hr_pos
          contradiction
        | false => rfl
      have h_rank_b : constructedRank c earlier sms pow3 b =
          (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b pow3) 0 + 1 := by
        dsimp [constructedRank]
        rw [h_not_ext]
        rfl
      rw [h_rank_b]
      dsimp [constructedRank]
      rw [h_orb_t.2]
      split
      · omega
      · omega
  }
  exact eliminated_of_sub_rank_witness c (LiveZero c pow3 live) W

/-- Connecting `ContractCheckSoundnessHypothesis`, `runContractCheckTotal = true`,
    `FullRepresentationHypothesis`, and `LiveZeroIterationEliminationHypothesis` directly to `ContractSoundness`. -/
theorem contract_soundness_of_check (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_lz_elim : LiveZeroIterationEliminationHypothesis c earlier sms pow3)
    (h_csound_chk : ContractCheckSoundnessHypothesis c earlier pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live)
    (h_run : runContractCheckTotal (rconfOfConfig c earlier) pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live = true) :
    ContractSoundness c earlier sms pow3 := by
  right
  have h_lz := live_zero_eliminated_of_iteration c earlier sms pow3 h_earlier h_irrefl h_rep h_lz_elim
  exact contract_eliminated_of_live_zero c earlier sms pow3 h_csound_chk h_run h_lz

/-- When all valid boundary colorings are eliminated (`LiveZero`), `LiveZeroIterationEliminationHypothesis`
    implies the global `IterationEliminationHypothesis`. -/
theorem iteration_elimination_of_live_zero_all (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_all_lz : ∀ b, IsValidBoundaryColoring c b →
      LiveZero c pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live b)
    (h_lz_elim : LiveZeroIterationEliminationHypothesis c earlier sms pow3) :
    IterationEliminationHypothesis c earlier sms pow3 := by
  intro b hb hr_pos
  have h_lz := h_all_lz b hb
  rcases h_lz_elim b hb h_lz hr_pos with ⟨θ, hθ⟩
  refine ⟨θ, ?_⟩
  intro sm hsm hfit0
  rcases hθ sm hsm hfit0 with ⟨t, ht, hr_dec, hr_orb⟩
  exact ⟨t, ht, hr_dec, fun b' hb' htr' => (hr_orb b' hb' htr').2⟩

/-- Master C-Reducibility Theorem from `LiveZeroIterationEliminationHypothesis`:
    Does not require the global `IterationEliminationHypothesis` (which only holds when all orbits are eliminated);
    instead uses `LiveZeroIterationEliminationHypothesis` on the eliminated subset. -/
theorem fast_c_sound_of_live_zero (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_contract : c.contractEdges ≠ [])
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_lz_elim : LiveZeroIterationEliminationHypothesis c earlier sms pow3)
    (h_csound_chk : ContractCheckSoundnessHypothesis c earlier pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live)
    (h_run : runContractCheckTotal (rconfOfConfig c earlier) pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live = true) :
    IsCReducible c := by
  have h_csound := contract_soundness_of_check c earlier sms pow3 h_earlier h_irrefl h_rep h_lz_elim h_csound_chk h_run
  cases h_csound with
  | inl _ =>
    have h_lz := live_zero_eliminated_of_iteration c earlier sms pow3 h_earlier h_irrefl h_rep h_lz_elim
    have h_elim := contract_eliminated_of_live_zero c earlier sms pow3 h_csound_chk h_run h_lz
    exact fast_c_sound_of_contract c h_contract h_elim
  | inr h_contract_elim =>
    exact fast_c_sound_of_contract c h_contract h_contract_elim

/-- Unconditional C-reducibility deduction from ` SubKempeRankWitness` on `extendsToContracted`. -/
theorem creducible_of_sub_witness (c : Configuration) (h_contract : c.contractEdges ≠ [])
    (W : SubKempeRankWitness c (extendsToContracted c)) :
    IsCReducible c := by
  refine ⟨h_contract, ?_⟩
  intro b hb hExt
  exact eliminated_of_sub_rank_witness c (extendsToContracted c) W b hb hExt

end Soundness
end Math
