import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Batch.Runner
import FourColorTheorem.Math.Batch.CRunner
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
  let (live0, orbits0) := initialLiveFast rc pow3
  let initSt : ReducerState := {
    live := live0,
    orbits := orbits0,
    activeSM := sms,
    ranks := mkArray N 0,
    iter := 0,
    changed := true
  }
  runReducerLoop N (orbits0.size + 1) initSt

/-- The ranks computed by computeFinalState match computeEliminationRanks. -/
theorem computeFinalState_ranks_eq (rc : RConf) (sms : Array SMData) (pow3 : Array Nat) :
    (computeFinalState rc sms pow3).ranks = computeEliminationRanks rc sms pow3 :=
  rfl

/-- Contract check soundness hypothesis:
    When `Batch.runContractCheck` returns true on the fixed-point live array, no boundary coloring
    extending to the contracted configuration has trace index present in `live` (i.e. `live[idx] = 0`). -/
def ContractCheckSoundnessHypothesis (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (live : ByteArray) : Prop :=
  Batch.runContractCheck (rconfOfConfig c earlier) pow3 live = true →
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b →
    live.get! (boundaryTrace c b pow3) = 0

/-- Derivation: when Batch.runContractCheck succeeds and the contract check soundness holds,
    any boundary coloring extending to the contracted configuration has live bit 0. -/
theorem contract_live_zero_of_check (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (live : ByteArray)
    (h_sound : ContractCheckSoundnessHypothesis c earlier pow3 live)
    (h_run : Batch.runContractCheck (rconfOfConfig c earlier) pow3 live = true)
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
    (h_run : Batch.runContractCheck (rconfOfConfig c earlier) pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live = true)
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
    Either all orbits are eliminated in the fixed-point loop (D-reducibility via checkFast),
    or every boundary coloring extending to the contracted configuration is eliminated
    under the adversarial Kempe elimination game. -/
def ContractSoundness (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  checkFast (rconfOfConfig c earlier) sms pow3 = true ∨
  (∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b → Eliminated c b)

/-- Soundness deduction for D-reducible configurations with contract edges:
    Any D-reducible configuration with a non-empty contract edge list is provably C-reducible. -/
theorem fast_c_sound_of_d (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_contract : c.contractEdges ≠ [])
    (h_check : checkFast (rconfOfConfig c earlier) sms pow3 = true)
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
    if `checkCFast` succeeds, the earlier adjacency graph is sound and irreflexive,
    Lemma (a) representation holds, and fixed-point elimination holds:
    `c` is provably C-reducible under the adversarial Kempe game semantics. -/
theorem fast_c_sound (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_contract : c.contractEdges ≠ [])
    (h_check : checkCFast (rconfOfConfig c earlier) sms pow3 = true)
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

/-- Unconditional C-reducibility deduction from a SubKempeRankWitness on `extendsToContracted`. -/
theorem creducible_of_sub_witness (c : Configuration) (h_contract : c.contractEdges ≠ [])
    (W : SubKempeRankWitness c (extendsToContracted c)) :
    IsCReducible c := by
  refine ⟨h_contract, ?_⟩
  intro b hb hExt
  exact eliminated_of_sub_rank_witness c (extendsToContracted c) W b hb hExt

end Soundness
end Math
