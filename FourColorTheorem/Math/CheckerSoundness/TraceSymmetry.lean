import FourColorTheorem.Math.CheckerSoundness.StructuralChecks
import FourColorTheorem.Math.CheckerSoundness.IterationProof

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-!
# Trace Symmetry and `S₃` / Bit-Complement Invariance (Stage B1 & B2)

This module proves the two key algebraic symmetry theorems connecting `boundaryTraceTheta`,
`relabelBoundary`, and `smFitIndex` to the `S₃` digit permutations and `(12)` bit-complement symmetry:

1. **Step B1 (`boundaryTrace_relabel`):** On any configuration with a ring cycle (`IsRingCycle c`),
   relabelling a valid boundary coloring `b` by `relabelBoundary θ` acts on each base-3 edge digit
   `d_i ∈ {0, 1, 2}` by the corresponding `S₃` digit permutation `relabelDigit θ`:
   - `theta1` (`δ = 1`): identity `[0, 1, 2]` (`orb.j0`)
   - `theta2` (`δ = 2`): swap `0 ↔ 1` `[1, 0, 2]` (`orb.j2`)
   - `theta3` (`δ = 3`): swap `0 ↔ 2` `[2, 1, 0]` (`orb.j5`)

2. **Step B2 (`smFitTree_flipBits`, `smFitIndex_flipBits`, `allFitLiveTotal_swapSM`):**
   Flipping all `p` bits of parameter `t` via `flipBits sm.p t` transforms `smFitIndex sm` into
   `smFitIndex (swapSM sm)` (swapping the `a` and `b` delta tables, i.e., swapping digits `1 ↔ 2`),
   and leaves `allFitLiveTotal` invariant.
-/

/-- `relabelColor θ` is an `𝔽₂`-linear automorphism of the Klein four-group `(V₄, ^^^)`:
    for every `θ : ColorPairing` and all `col1, col2 : Color`,
    `(relabelColor θ col1).toNat ^^^ (relabelColor θ col2).toNat` depends only on `col1.toNat ^^^ col2.toNat`. -/
theorem relabelColor_xor (θ : ColorPairing) (col1 col2 : Color) :
    (relabelColor θ col1).toNat ^^^ (relabelColor θ col2).toNat =
      (relabelColor θ (colorOfNat (col1.toNat ^^^ col2.toNat))).toNat := by
  dsimp [relabelColor]
  cases θ.a <;> cases θ.b <;> cases col1 <;> cases col2 <;> rfl

/-- The induced `S₃` permutation on base-3 edge digits `d ∈ {0, 1, 2}` for color pairing `θ`. -/
def relabelDigit (θ : ColorPairing) (d : Nat) : Nat :=
  let diff := (relabelColor θ (colorOfNat (d + 1))).toNat
  if diff > 0 then diff - 1 else 0

/-- For any two distinct colors `col1 ≠ col2`, the edge digit of `(relabelColor θ col1, relabelColor θ col2)`
    equals `relabelDigit θ` applied to the edge digit of `(col1, col2)`. -/
theorem edge_digit_relabel (θ : ColorPairing) (col1 col2 : Color) (h_ne : col1 ≠ col2) :
    (let diff' := (relabelColor θ col1).toNat ^^^ (relabelColor θ col2).toNat
     if diff' > 0 then diff' - 1 else 0) =
    relabelDigit θ (let diff := col1.toNat ^^^ col2.toNat; if diff > 0 then diff - 1 else 0) := by
  dsimp [relabelColor, relabelDigit]
  cases θ.a <;> cases θ.b <;> cases col1 <;> cases col2 <;> revert h_ne <;> decide

/-- Structural trace accumulation with a digit permutation `p : Nat → Nat` applied to each edge digit `d_i`. -/
def permTraceAux (p : Nat → Nat) (r : Nat) (b : Nat → Color) (pow3 : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | rem + 1, i, acc =>
    let nxt := (i + 1) % r
    let diff := (b i).toNat ^^^ (b nxt).toNat
    let d_i := if diff > 0 then diff - 1 else 0
    permTraceAux p r b pow3 rem (i + 1) (acc + p d_i * pow3.getD i 0)

/-- At `p = id`, `permTraceAux` coincides with `boundaryTraceAux`. -/
theorem permTraceAux_id (r : Nat) (b : Nat → Color) (pow3 : Array Nat) (rem i acc : Nat) :
    permTraceAux (fun d => d) r b pow3 rem i acc = boundaryTraceAux r b pow3 rem i acc := by
  induction rem generalizing i acc with
  | zero => rfl
  | succ rem ih =>
    dsimp [permTraceAux, boundaryTraceAux]
    exact ih (i + 1) _

/-- Step B1 helper: On a ring cycle `IsRingCycle c`, relabelling a valid boundary coloring `b` by `θ`
    transforms `boundaryTraceAux` into `permTraceAux (relabelDigit θ)`. -/
theorem boundaryTraceAux_relabel (c : Configuration) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (θ : ColorPairing) (pow3 : Array Nat) (rem i acc : Nat)
    (h_le : i + rem ≤ c.ringSize) :
    boundaryTraceAux c.ringSize (relabelBoundary θ b) pow3 rem i acc =
      permTraceAux (relabelDigit θ) c.ringSize b pow3 rem i acc := by
  induction rem generalizing i acc with
  | zero => rfl
  | succ rem ih =>
    have hi : i < c.ringSize := by omega
    have h_nxt : (i + 1) % c.ringSize < c.ringSize :=
      Nat.mod_lt (i + 1) (by have := h_ring.1; omega)
    have h_adj : c.adj i ((i + 1) % c.ringSize) = true := h_ring.2 i hi
    have h_ne : b i ≠ b ((i + 1) % c.ringSize) := hb i ((i + 1) % c.ringSize) hi h_nxt h_adj
    dsimp [boundaryTraceAux, permTraceAux, relabelBoundary]
    rw [edge_digit_relabel θ (b i) (b ((i + 1) % c.ringSize)) h_ne]
    exact ih (i + 1) _ (by omega)

/-- **Theorem B1 (`boundaryTrace_relabel`):**
    On any configuration with a ring cycle (`IsRingCycle c`), `boundaryTraceTheta c b θ pow3`
    equals the digit-permuted trace `permTraceAux (relabelDigit θ) c.ringSize b pow3 c.ringSize 0 0`. -/
theorem boundaryTrace_relabel (c : Configuration) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (θ : ColorPairing) (pow3 : Array Nat) :
    boundaryTraceTheta c b θ pow3 =
      permTraceAux (relabelDigit θ) c.ringSize b pow3 c.ringSize 0 0 :=
  boundaryTraceAux_relabel c h_ring b hb θ pow3 c.ringSize 0 0 (by omega)

/-- Correspondence between `relabelDigit` for the three canonical pairings `theta1, theta2, theta3`
    and the three orbit permutations `perms[0]!` (`j0`), `perms[2]!` (`j2`), `perms[5]!` (`j5`). -/
theorem relabelDigit_theta1_eq (d : Nat) (hd : d < 3) :
    relabelDigit theta1 d = (perms[0]!)[d]! := by
  revert hd; cases d with
  | zero => decide
  | succ d1 => cases d1 with
    | zero => decide
    | succ d2 => cases d2 with
      | zero => decide
      | succ _ => omega

theorem relabelDigit_theta2_eq (d : Nat) (hd : d < 3) :
    relabelDigit theta2 d = (perms[2]!)[d]! := by
  revert hd; cases d with
  | zero => decide
  | succ d1 => cases d1 with
    | zero => decide
    | succ d2 => cases d2 with
      | zero => decide
      | succ _ => omega

theorem relabelDigit_theta3_eq (d : Nat) (hd : d < 3) :
    relabelDigit theta3 d = (perms[5]!)[d]! := by
  revert hd; cases d with
  | zero => decide
  | succ d1 => cases d1 with
    | zero => decide
    | succ d2 => cases d2 with
      | zero => decide
      | succ _ => omega

/-!
### Part 2: Bit-Complement (`swap₁₂`) Symmetry of `smFitTree`, `smFitIndex`, and `allFitLiveTotal` (Step B2)
-/

/-- Dual signed matching obtained by swapping the `a` (bit = 0) and `b` (bit = 1) delta tables.
    Under `buildSMData`, swapping `a` and `b` corresponds to swapping base-3 digits `1 ↔ 2` (`swap₁₂`). -/
def swapSM (sm : SMData) : SMData where
  p := sm.p
  a := sm.b
  b := sm.a

@[simp] theorem swapSM_swapSM (sm : SMData) : swapSM (swapSM sm) = sm := by
  cases sm; rfl

/-- Structurally flip the lowest `fuel` bits of parameter `t`. -/
def flipBits : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, t =>
    if (t &&& 1) == 0 then 2 * flipBits fuel (t >>> 1) + 1
    else 2 * flipBits fuel (t >>> 1)

/-- `flipBits fuel t` always lies in `[0, 2^fuel)`. -/
theorem flipBits_lt (fuel t : Nat) : flipBits fuel t < 1 <<< fuel := by
  induction fuel generalizing t with
  | zero => dsimp [flipBits]; decide
  | succ fuel ih =>
    have h_sub := ih (t >>> 1)
    rw [Nat.shiftLeft_eq, Nat.one_mul] at h_sub ⊢
    rw [Nat.pow_succ]
    dsimp [flipBits]
    split <;> omega

/-- **Theorem B2a (`smFitTree_flipBits`):**
    Evaluating `smFitTree sm` at the bit-complement `flipBits fuel t` is identical to
    evaluating `smFitTree (swapSM sm)` at `t`. -/
theorem smFitTree_flipBits (sm : SMData) (fuel k t acc : Nat) :
    smFitTree sm fuel k (flipBits fuel t) acc =
      smFitTree (swapSM sm) fuel k t acc := by
  induction fuel generalizing k t acc with
  | zero => rfl
  | succ fuel ih =>
    dsimp [smFitTree]
    have hp : (swapSM sm).p = sm.p := rfl
    have ha : (swapSM sm).a = sm.b := rfl
    have hb : (swapSM sm).b = sm.a := rfl
    rw [hp, ha, hb]
    by_cases hk : k ≥ sm.p
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk]
      dsimp [flipBits]
      cases hbit : ((t &&& 1) == 0) with
      | true =>
        rw [if_pos rfl]
        have h_and : ((2 * flipBits fuel (t >>> 1) + 1) &&& 1 == 0) = false := by
          rw [Nat.and_one_is_mod]
          simp
        have h_shr : (2 * flipBits fuel (t >>> 1) + 1) >>> 1 = flipBits fuel (t >>> 1) := by
          rw [Nat.shiftRight_eq_div_pow]
          change (2 * flipBits fuel (t >>> 1) + 1) / 2 = flipBits fuel (t >>> 1)
          omega
        rw [h_and]
        dsimp
        rw [h_shr]
        exact ih (k + 1) (t >>> 1) (acc + sm.b[k]!)
      | false =>
        rw [if_neg Bool.noConfusion]
        have h_and : ((2 * flipBits fuel (t >>> 1)) &&& 1 == 0) = true := by
          rw [Nat.and_one_is_mod]
          simp
        have h_shr : (2 * flipBits fuel (t >>> 1)) >>> 1 = flipBits fuel (t >>> 1) := by
          rw [Nat.shiftRight_eq_div_pow]
          simp
        rw [h_and, if_pos rfl, h_shr]
        exact ih (k + 1) (t >>> 1) (acc + sm.a[k]!)

/-- **Theorem B2b (`smFitIndex_flipBits`):**
    Flipping all `sm.p` bits of `t` in `smFitIndex sm` swaps the `a` and `b` delta tables (`swapSM sm`). -/
theorem smFitIndex_flipBits (sm : SMData) (t : Nat) :
    smFitIndex sm (flipBits sm.p t) = smFitIndex (swapSM sm) t := by
  rw [← smFitTree_eq_smFitIndex sm (flipBits sm.p t)]
  rw [smFitTree_flipBits sm sm.p 0 t 0]
  exact smFitTree_eq_smFitIndex (swapSM sm) t

/-- **Theorem B2c (`allFitLiveTotal_swapSM`):**
    `allFitLiveTotal` is invariant under `swapSM` (since conjunction `&&` is commutative). -/
theorem allFitLiveTotal_swapSM (fuel : Nat) (sm : SMData) (live : ByteArray) (k acc : Nat) :
    allFitLiveTotal fuel (swapSM sm) live k acc = allFitLiveTotal fuel sm live k acc := by
  induction fuel generalizing k acc with
  | zero => rfl
  | succ fuel ih =>
    dsimp [allFitLiveTotal]
    have hp : (swapSM sm).p = sm.p := rfl
    have ha : (swapSM sm).a = sm.b := rfl
    have hb : (swapSM sm).b = sm.a := rfl
    rw [hp, ha, hb]
    by_cases hk : k ≥ sm.p
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk]
      rw [ih (k + 1) (acc + sm.b[k]!), ih (k + 1) (acc + sm.a[k]!), Bool.and_comm]

/-- **Theorem B2d (`markFitCoverTotal_sets_flipBits`):**
    `markFitCoverTotal` on `sm` also marks every leaf of the dual matching `swapSM sm`. -/
theorem markFitCoverTotal_sets_flipBits (fuel : Nat) (sm : SMData) (k acc : Nat) (cov : ByteArray)
    (t : Nat) (ht : t < 1 <<< fuel) (h_bound : smFitTree (swapSM sm) fuel k t acc < cov.size) :
    ((markFitCoverTotal fuel sm k acc cov).get! (smFitTree (swapSM sm) fuel k t acc) == 1) = true := by
  rw [← smFitTree_flipBits sm fuel k t acc]
  exact markFitCoverTotal_sets_leaf fuel sm k acc cov (flipBits fuel t) (flipBits_lt fuel t)
    (by rwa [smFitTree_flipBits sm fuel k t acc])

/-- **Theorem B2e (`uncovered_of_stepSMList_swapSM`):**
    If trace `j < cov.size` is uncovered after `stepSMList`, then any `sm ∈ sms` whose `(12)`-dual
    `swapSM sm` fits `j` at `t = 0` (`smFitTree (swapSM sm) sm.p 0 0 0 = j`) ALSO has a parameter
    `t < 1 <<< sm.p` whose leaf trace index `smFitTree sm sm.p 0 t 0` is not live. -/
theorem uncovered_of_stepSMList_swapSM (live : ByteArray) (sms : List SMData)
    (cov : ByteArray) (nextSM : Array SMData) (j : Nat) (hj_bound : j < cov.size)
    (h_uncov : ((stepSMList live sms cov nextSM).1.get! j == 1) = false)
    (sm : SMData) (hsm : sm ∈ sms) (h_fit_dual : smFitTree (swapSM sm) sm.p 0 0 0 = j) :
    ∃ t < 1 <<< sm.p, (live.get! (smFitTree sm sm.p 0 t 0) == 1) = false := by
  have h_flip : smFitTree sm sm.p 0 (flipBits sm.p 0) 0 = j := by
    rw [smFitTree_flipBits sm sm.p 0 0 0]
    exact h_fit_dual
  induction sms generalizing cov nextSM with
  | nil => contradiction
  | cons sm0 rest ih =>
    rcases List.mem_cons.mp hsm with rfl | h_mem_rest
    · dsimp [stepSMList] at h_uncov
      cases h_all : allFitLiveTotal sm.p sm live 0 0 with
      | false =>
        exact exists_not_live_of_allFitLiveTotal_false sm.p sm live 0 0 h_all
      | true =>
        exfalso
        rw [h_all, if_pos rfl] at h_uncov
        have h_flip_lt : flipBits sm.p 0 < 1 <<< sm.p := flipBits_lt sm.p 0
        have h_leaf_bound : smFitTree sm sm.p 0 (flipBits sm.p 0) 0 < cov.size := by
          rw [h_flip]; exact hj_bound
        have h_cov1 : ((markFitCoverTotal sm.p sm 0 0 cov).get! j == 1) = true := by
          rw [← h_flip]
          exact markFitCoverTotal_sets_leaf sm.p sm 0 0 cov (flipBits sm.p 0) h_flip_lt h_leaf_bound
        have h_cov_end := stepSMList_preserves_one live rest
          (markFitCoverTotal sm.p sm 0 0 cov) (nextSM.push sm) j h_cov1
        rw [h_cov_end] at h_uncov
        contradiction
    · dsimp [stepSMList] at h_uncov
      split at h_uncov
      · have hj_bound' : j < (markFitCoverTotal sm0.p sm0 0 0 cov).size := by
          rw [markFitCoverTotal_size]; exact hj_bound
        exact ih (markFitCoverTotal sm0.p sm0 0 0 cov) (nextSM.push sm0) hj_bound' h_uncov h_mem_rest
      · exact ih cov nextSM hj_bound h_uncov h_mem_rest

/-!
### Part 3: Orbit Elimination Round Theorem for `stepOrbitsList` and `runReducerLoop` (Steps B3–B5)
-/

theorem mem_stepOrbitsList_of_mem_acc (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (orb : Orbit6) (h_acc : orb ∈ nextOrbits.toList) :
    orb ∈ (stepOrbitsList cover iter orbs nextOrbits live ranks).1.toList := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => exact h_acc
  | cons orb0 rest ih =>
    dsimp [stepOrbitsList]
    split
    · apply ih
      exact mem_push_data nextOrbits orb0 orb h_acc
    · exact ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter) h_acc

/-- Every `orb ∈ orbs` is either retained in `(stepOrbitsList ...).1` or has at least one uncovered
    canonical pairing (`j0`, `j2`, or `j5`) in `cover`. -/
theorem stepOrbitsList_retained_or_uncovered (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (orb : Orbit6) (horb : orb ∈ orbs) :
    orb ∈ (stepOrbitsList cover iter orbs nextOrbits live ranks).1.toList ∨
      (cover.get! orb.j0 == 1 && cover.get! orb.j2 == 1 && cover.get! orb.j5 == 1) = false := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => contradiction
  | cons orb0 rest ih =>
    rcases List.mem_cons.mp horb with rfl | h_rest
    · dsimp [stepOrbitsList]
      cases h_cov : (cover.get! orb.j0 == 1 && cover.get! orb.j2 == 1 && cover.get! orb.j5 == 1) with
      | true =>
        rw [if_pos rfl]
        left
        apply mem_stepOrbitsList_of_mem_acc
        exact mem_push_self nextOrbits orb
      | false =>
        exact Or.inr rfl
    · dsimp [stepOrbitsList]
      split
      · exact ih (nextOrbits.push orb0) live ranks h_rest
      · exact ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter) h_rest

theorem not_isEmpty_of_mem_toList {α : Type} (a : Array α) (x : α) (hx : x ∈ a.toList) :
    a.isEmpty = false := by
  cases a with
  | mk l =>
    cases l with
    | nil => contradiction
    | cons _ _ => rfl

/-- **General Orbit Elimination Round Theorem (for both D- and C-reducibility, Steps B3–B5):**
    If `orb ∈ st.orbits.toList` and `orb ∉ (runReducerLoop N fuel st).orbits.toList`,
    then there exists a round state `st_k` reached during `runReducerLoop` such that:
    1. `orb ∈ st_k.orbits.toList`,
    2. `(cov_k.get! orb.j0 == 1 && cov_k.get! orb.j2 == 1 && cov_k.get! orb.j5 == 1) = false`,
    3. Every `sm ∈ st.activeSM.toList` satisfies the active-SM invariant at `st_k`,
    4. Liveness is monotone from `st` to `st_k`, and
    5. Liveness is monotone from `st_k` to `runReducerLoop N fuel st`. -/
theorem exists_eliminating_round_of_not_mem_orbits (N fuel : Nat) (st : ReducerState)
    (orb : Orbit6) (horb : orb ∈ st.orbits.toList)
    (h_not_mem : orb ∉ (runReducerLoop N fuel st).orbits.toList) :
    ∃ st_k : ReducerState,
      orb ∈ st_k.orbits.toList ∧
      (let cov := (stepSMList st_k.live st_k.activeSM.toList (zeros N) (Array.mkEmpty st_k.activeSM.size)).1
       (cov.get! orb.j0 == 1 && cov.get! orb.j2 == 1 && cov.get! orb.j5 == 1) = false) ∧
      (∀ sm ∈ st.activeSM.toList,
        sm ∈ st_k.activeSM.toList ∨ ∃ t < 1 <<< sm.p, (st_k.live.get! (smFitIndex sm t) == 1) = false) ∧
      (∀ j, (st.live.get! j == 1) = false → (st_k.live.get! j == 1) = false) ∧
      (∀ j, (st_k.live.get! j == 1) = false → ((runReducerLoop N fuel st).live.get! j == 1) = false) := by
  induction fuel generalizing st with
  | zero =>
    dsimp [runReducerLoop] at h_not_mem
    exact False.elim (h_not_mem horb)
  | succ fuel ih =>
    dsimp [runReducerLoop] at h_not_mem
    by_cases h_cond : (st.changed && !st.orbits.isEmpty) = true
    · rw [if_pos h_cond] at h_not_mem
      rcases stepOrbitsList_retained_or_uncovered
          (stepSMList st.live st.activeSM.toList (zeros N) (Array.mkEmpty st.activeSM.size)).1
          (st.iter + 1) st.orbits.toList (Array.mkEmpty st.orbits.size) st.live st.ranks
          orb horb with h_ret | h_uncov
      · rcases ih (reducerStep N st) h_ret h_not_mem with
          ⟨st_k, horb_k, h_uncov_k, h_sm_k, h_from_step, h_to_end⟩
        refine ⟨st_k, horb_k, h_uncov_k, ?_, ?_, ?_⟩
        · intro sm hsm
          rcases retained_or_not_live_of_reducerStep N st sm hsm with h_sm_ret | ⟨t, ht, h_dead⟩
          · exact h_sm_k sm h_sm_ret
          · right
            exact ⟨t, ht, h_from_step (smFitIndex sm t) h_dead⟩
        · intro j hj
          exact h_from_step j (reducerStep_not_live_mono N st j hj)
        · intro j hj
          dsimp [runReducerLoop]
          rw [if_pos h_cond]
          exact h_to_end j hj
      · refine ⟨st, horb, h_uncov, fun sm hsm => Or.inl hsm, fun _ hj => hj, ?_⟩
        intro j hj
        dsimp [runReducerLoop]
        rw [if_pos h_cond]
        exact runReducerLoop_not_live_mono N fuel (reducerStep N st) j
          (reducerStep_not_live_mono N st j hj)
    · rw [if_neg h_cond] at h_not_mem
      exact False.elim (h_not_mem horb)

/-- **Combined Eliminating Round + Signed-Matching Elimination Theorem:**
    At any eliminating round `st_k` of an orbit `orb` during `runReducerLoop N fuel st`,
    there exists an uncovered canonical pairing trace `j_θ ∈ {orb.j0, orb.j2, orb.j5}` such that
    if `j_θ < N`, then for EVERY `sm ∈ st.activeSM.toList` fitting `j_θ` at `t = 0`
    (or via its `(12)`-dual `swapSM sm`), there exists a parameter `t < 1 <<< sm.p` such that
    `smFitIndex sm t` is already non-live at the start of round `st_k` (`(st_k.live.get! (smFitIndex sm t) == 1) = false`)
    and remains non-live at the end of `runReducerLoop N fuel st`. -/
theorem round_uncovered_sm_elimination (N fuel : Nat) (st : ReducerState)
    (orb : Orbit6) (horb : orb ∈ st.orbits.toList)
    (h_not_mem : orb ∉ (runReducerLoop N fuel st).orbits.toList)
    (h0_lt : orb.j0 < N) (h2_lt : orb.j2 < N) (h5_lt : orb.j5 < N) :
    ∃ st_k : ReducerState,
      orb ∈ st_k.orbits.toList ∧
      ∃ j_θ : Nat, (j_θ = orb.j0 ∨ j_θ = orb.j2 ∨ j_θ = orb.j5) ∧
        ∀ sm ∈ st.activeSM.toList,
          (smFitIndex sm 0 = j_θ ∨ smFitIndex (swapSM sm) 0 = j_θ) →
          ∃ t < 1 <<< sm.p,
            (st_k.live.get! (smFitIndex sm t) == 1) = false ∧
            ((runReducerLoop N fuel st).live.get! (smFitIndex sm t) == 1) = false := by
  rcases exists_eliminating_round_of_not_mem_orbits N fuel st orb horb h_not_mem with
    ⟨st_k, horb_k, h_uncov_k, h_sm_k, _, h_to_end⟩
  let cov := (stepSMList st_k.live st_k.activeSM.toList (zeros N) (Array.mkEmpty st_k.activeSM.size)).1
  have h_pair := uncovered_pairing_of_not_covered cov orb h_uncov_k
  have h_helper : ∀ j_θ : Nat, j_θ < N → (cov.get! j_θ == 1) = false →
      ∀ sm ∈ st.activeSM.toList, (smFitIndex sm 0 = j_θ ∨ smFitIndex (swapSM sm) 0 = j_θ) →
      ∃ t < 1 <<< sm.p,
        (st_k.live.get! (smFitIndex sm t) == 1) = false ∧
        ((runReducerLoop N fuel st).live.get! (smFitIndex sm t) == 1) = false := by
    intro j_θ hj_lt hj_uncov sm hsm h_fit
    rcases h_sm_k sm hsm with h_active | ⟨t, ht, h_dead⟩
    · rcases h_fit with h_fit0 | h_fit_dual
      · rcases exists_not_live_of_uncovered_in_round N st_k j_θ hj_lt hj_uncov sm (Or.inl h_active) h_fit0 with
          ⟨t, ht, h_dead⟩
        exact ⟨t, ht, h_dead, h_to_end (smFitIndex sm t) h_dead⟩
      · have h_tree_dual : smFitTree (swapSM sm) sm.p 0 0 0 = j_θ := by
          have := smFitTree_eq_smFitIndex (swapSM sm) 0
          dsimp [swapSM] at this ⊢
          rw [this]
          exact h_fit_dual
        have hj_zeros : j_θ < (zeros N).size := by
          rw [zeros_size]
          exact hj_lt
        rcases uncovered_of_stepSMList_swapSM st_k.live st_k.activeSM.toList (zeros N)
            (Array.mkEmpty st_k.activeSM.size) j_θ hj_zeros hj_uncov sm h_active h_tree_dual with
          ⟨t, ht, h_dead⟩
        rw [smFitTree_eq_smFitIndex] at h_dead
        exact ⟨t, ht, h_dead, h_to_end (smFitIndex sm t) h_dead⟩
    · exact ⟨t, ht, h_dead, h_to_end (smFitIndex sm t) h_dead⟩
  refine ⟨st_k, horb_k, ?_⟩
  rcases h_pair with h0 | h2 | h5
  · exact ⟨orb.j0, Or.inl rfl, h_helper orb.j0 h0_lt h0⟩
  · exact ⟨orb.j2, Or.inr (Or.inl rfl), h_helper orb.j2 h2_lt h2⟩
  · exact ⟨orb.j5, Or.inr (Or.inr rfl), h_helper orb.j5 h5_lt h5⟩

/-!
### Part 4: Rank Bound and Rank Preservation Invariants Across `stepOrbitsList` and `runReducerLoop`
-/

/-- Membership of a trace index `j` in the 6 indices of `orb`. -/
def inOrbit6 (orb : Orbit6) (j : Nat) : Prop :=
  j = orb.j0 ∨ j = orb.j1 ∨ j = orb.j2 ∨ j = orb.j3 ∨ j = orb.j4 ∨ j = orb.j5

/-- All 6 trace indices of `orb` are currently live in `live`. -/
def orbitAllLive (live : ByteArray) (orb : Orbit6) : Prop :=
  (live.get! orb.j0 == 1) = true ∧
  (live.get! orb.j1 == 1) = true ∧
  (live.get! orb.j2 == 1) = true ∧
  (live.get! orb.j3 == 1) = true ∧
  (live.get! orb.j4 == 1) = true ∧
  (live.get! orb.j5 == 1) = true

/-- If `orbitAllLive live orb` holds and `(live.get! j == 1) = false`, then `j` cannot belong to `orb`. -/
theorem not_inOrbit6_of_not_live (live : ByteArray) (orb : Orbit6) (j : Nat)
    (h_live : orbitAllLive live orb) (hj : (live.get! j == 1) = false) :
    ¬ inOrbit6 orb j := by
  rintro (rfl | rfl | rfl | rfl | rfl | rfl)
  · rw [h_live.1] at hj; contradiction
  · rw [h_live.2.1] at hj; contradiction
  · rw [h_live.2.2.1] at hj; contradiction
  · rw [h_live.2.2.2.1] at hj; contradiction
  · rw [h_live.2.2.2.2.1] at hj; contradiction
  · rw [h_live.2.2.2.2.2] at hj; contradiction

/-- If `j` does not belong to `orb`, `setOrbitRanks` leaves `ranks.getD j 0` unchanged. -/
theorem setOrbitRanks_getD_of_not_inOrbit6 (ranks : Array Nat) (orb : Orbit6) (iter j : Nat)
    (h_not : ¬ inOrbit6 orb j) :
    (setOrbitRanks ranks orb iter).getD j 0 = ranks.getD j 0 := by
  have h0 : orb.j0 ≠ j := fun h => h_not (Or.inl h.symm)
  have h1 : orb.j1 ≠ j := fun h => h_not (Or.inr (Or.inl h.symm))
  have h2 : orb.j2 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inl h.symm)))
  have h3 : orb.j3 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inl h.symm))))
  have h4 : orb.j4 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm)))))
  have h5 : orb.j5 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.symm)))))
  unfold setOrbitRanks
  rw [array_getD_set!_ne _ orb.j5 j iter h5,
      array_getD_set!_ne _ orb.j4 j iter h4,
      array_getD_set!_ne _ orb.j3 j iter h3,
      array_getD_set!_ne _ orb.j2 j iter h2,
      array_getD_set!_ne _ orb.j1 j iter h1,
      array_getD_set!_ne _ orb.j0 j iter h0]

/-- Setting an entry of `a : Array Nat` to `v ≤ bound` preserves `∀ j, a.getD j 0 ≤ bound`. -/
theorem array_getD_set!_le (a : Array Nat) (i v j bound : Nat)
    (hj : a.getD j 0 ≤ bound) (hv : v ≤ bound) :
    (a.set! i v).getD j 0 ≤ bound := by
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · rw [array_getD_set!_self a i v hi]
      exact hv
    · simp [Array.getD, hi] at hj ⊢
  · rw [array_getD_set!_ne a i j v hij]
    exact hj

/-- `setOrbitRanks` preserves upper bounds `≤ bound` whenever `iter ≤ bound`. -/
theorem setOrbitRanks_getD_le (ranks : Array Nat) (orb : Orbit6) (iter j bound : Nat)
    (hj : ranks.getD j 0 ≤ bound) (h_iter : iter ≤ bound) :
    (setOrbitRanks ranks orb iter).getD j 0 ≤ bound := by
  unfold setOrbitRanks
  exact array_getD_set!_le _ orb.j5 iter j bound
    (array_getD_set!_le _ orb.j4 iter j bound
      (array_getD_set!_le _ orb.j3 iter j bound
        (array_getD_set!_le _ orb.j2 iter j bound
          (array_getD_set!_le _ orb.j1 iter j bound
            (array_getD_set!_le _ orb.j0 iter j bound hj h_iter)
            h_iter)
          h_iter)
        h_iter)
      h_iter)
    h_iter

/-- `stepOrbitsList` preserves upper bounds `≤ bound` whenever `iter ≤ bound`. -/
theorem stepOrbitsList_ranks_getD_le (cover : ByteArray) (iter : Nat) (orbs : List Orbit6)
    (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat) (j bound : Nat)
    (hj : ranks.getD j 0 ≤ bound) (h_iter : iter ≤ bound) :
    (stepOrbitsList cover iter orbs nextOrbits live ranks).2.2.getD j 0 ≤ bound := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => exact hj
  | cons orb rest ih =>
    dsimp [stepOrbitsList]
    split
    · exact ih (nextOrbits.push orb) live ranks hj
    · exact ih nextOrbits (clearOrbitLive live orb) (setOrbitRanks ranks orb iter)
        (setOrbitRanks_getD_le ranks orb iter j bound hj h_iter)

/-- **Rank Upper Bound Invariant across `reducerStep`:**
    If every entry of `st.ranks` is `≤ st.iter`, then after `reducerStep N st`,
    every entry of `(reducerStep N st).ranks` is `≤ (reducerStep N st).iter`. -/
theorem reducerStep_ranks_le_iter (N : Nat) (st : ReducerState)
    (h_le : ∀ j, st.ranks.getD j 0 ≤ st.iter) (j : Nat) :
    (reducerStep N st).ranks.getD j 0 ≤ (reducerStep N st).iter := by
  dsimp [reducerStep]
  exact stepOrbitsList_ranks_getD_le _ (st.iter + 1) st.orbits.toList
    (Array.mkEmpty st.orbits.size) st.live st.ranks j (st.iter + 1)
    (Nat.le_succ_of_le (h_le j)) (Nat.le_refl (st.iter + 1))

/-- If `j` does not belong to any orbit in `orbs`, `stepOrbitsList` preserves `ranks.getD j 0`. -/
theorem stepOrbitsList_ranks_preserves_of_not_in_orbs (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (j : Nat) (h_not : ∀ orb ∈ orbs, ¬ inOrbit6 orb j) :
    (stepOrbitsList cover iter orbs nextOrbits live ranks).2.2.getD j 0 = ranks.getD j 0 := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => rfl
  | cons orb rest ih =>
    have h_not_head : ¬ inOrbit6 orb j := h_not orb (List.mem_cons_self ..)
    have h_not_rest : ∀ orb' ∈ rest, ¬ inOrbit6 orb' j :=
      fun orb' h_mem => h_not orb' (List.mem_cons_of_mem orb h_mem)
    dsimp [stepOrbitsList]
    split
    · exact ih (nextOrbits.push orb) live ranks h_not_rest
    · rw [ih nextOrbits (clearOrbitLive live orb) (setOrbitRanks ranks orb iter) h_not_rest]
      exact setOrbitRanks_getD_of_not_inOrbit6 ranks orb iter j h_not_head

/-- Every orbit in `(stepOrbitsList cover iter orbs nextOrbits live ranks).1.toList`
    was either in `nextOrbits.toList` or in `orbs`. -/
theorem mem_of_mem_stepOrbitsList (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (orb : Orbit6)
    (h_mem : orb ∈ (stepOrbitsList cover iter orbs nextOrbits live ranks).1.toList) :
    orb ∈ nextOrbits.toList ∨ orb ∈ orbs := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => exact Or.inl h_mem
  | cons orb0 rest ih =>
    dsimp [stepOrbitsList] at h_mem
    split at h_mem
    · rcases ih (nextOrbits.push orb0) live ranks h_mem with h_push | h_rest
      · rw [Array.toList_push, List.mem_append] at h_push
        rcases h_push with h_acc | h_single
        · exact Or.inl h_acc
        · rw [List.mem_singleton] at h_single
          subst h_single
          exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem orb0 h_rest)
    · rcases ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter) h_mem with h_acc | h_rest
      · exact Or.inl h_acc
      · exact Or.inr (List.mem_cons_of_mem orb0 h_rest)

/-- Active orbits are a subset of the previous round's orbits across `reducerStep`. -/
theorem reducerStep_orbits_sub (N : Nat) (st : ReducerState) (orb : Orbit6)
    (h_mem : orb ∈ (reducerStep N st).orbits.toList) :
    orb ∈ st.orbits.toList := by
  dsimp [reducerStep] at h_mem
  rcases mem_of_mem_stepOrbitsList _ _ _ _ _ _ orb h_mem with h_empty | h_in
  · contradiction
  · exact h_in

/-- If `j` does not belong to any orbit in `st.orbits.toList`, then `reducerStep` preserves `ranks.getD j 0`. -/
theorem reducerStep_ranks_preserves_of_not_in_orbits (N : Nat) (st : ReducerState) (j : Nat)
    (h_not : ∀ orb ∈ st.orbits.toList, ¬ inOrbit6 orb j) :
    (reducerStep N st).ranks.getD j 0 = st.ranks.getD j 0 := by
  dsimp [reducerStep]
  exact stepOrbitsList_ranks_preserves_of_not_in_orbs _ _ _ _ _ _ j h_not

/-- If `j` does not belong to any orbit in `st.orbits.toList`, then `runReducerLoop` preserves `ranks.getD j 0`
    across any number of remaining rounds `fuel`. -/
theorem runReducerLoop_ranks_preserves_of_not_in_orbits (N fuel : Nat) (st : ReducerState) (j : Nat)
    (h_not : ∀ orb ∈ st.orbits.toList, ¬ inOrbit6 orb j) :
    (runReducerLoop N fuel st).ranks.getD j 0 = st.ranks.getD j 0 := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
    dsimp [runReducerLoop]
    split
    · have h_sub : ∀ orb ∈ (reducerStep N st).orbits.toList, ¬ inOrbit6 orb j :=
        fun orb h_mem => h_not orb (reducerStep_orbits_sub N st orb h_mem)
      rw [ih (reducerStep N st) h_sub]
      exact reducerStep_ranks_preserves_of_not_in_orbits N st j h_not
    · rfl

/-- **Master Strict Rank Decrease Theorem at an Eliminating Round (Steps B3–B5):**
    Suppose at round `st_k` during `runReducerLoop`:
    - Every entry of `st_k.ranks` is bounded by `st_k.iter` (`∀ j, st_k.ranks.getD j 0 ≤ st_k.iter`),
    - Every active orbit in `st_k.orbits.toList` has all 6 of its traces live in `st_k.live`
      (`∀ orb' ∈ st_k.orbits.toList, orbitAllLive st_k.live orb'`),
    - Trace `j_dead` is already non-live at the start of round `st_k` (`(st_k.live.get! j_dead == 1) = false`), and
    - Trace `j_orb` is assigned rank `st_k.iter + 1` in `(runReducerLoop N rem st_k).ranks`.
    Then `(runReducerLoop N rem st_k).ranks.getD j_dead 0 < (runReducerLoop N rem st_k).ranks.getD j_orb 0`. -/
theorem strict_rank_decrease_of_not_live_at_round (N rem : Nat) (st_k : ReducerState)
    (h_ranks_le : ∀ j, st_k.ranks.getD j 0 ≤ st_k.iter)
    (h_orbs_live : ∀ orb' ∈ st_k.orbits.toList, orbitAllLive st_k.live orb')
    (j_dead j_orb : Nat)
    (h_dead : (st_k.live.get! j_dead == 1) = false)
    (h_orb_rank : (runReducerLoop N rem st_k).ranks.getD j_orb 0 = st_k.iter + 1) :
    (runReducerLoop N rem st_k).ranks.getD j_dead 0 <
      (runReducerLoop N rem st_k).ranks.getD j_orb 0 := by
  have h_not_in : ∀ orb' ∈ st_k.orbits.toList, ¬ inOrbit6 orb' j_dead :=
    fun orb' h_mem => not_inOrbit6_of_not_live st_k.live orb' j_dead (h_orbs_live orb' h_mem) h_dead
  have h_pres := runReducerLoop_ranks_preserves_of_not_in_orbits N rem st_k j_dead h_not_in
  have h_le := h_ranks_le j_dead
  rw [h_pres, h_orb_rank]
  omega

/-- If `j` does not belong to `orb`, `clearOrbitLive` leaves `live.get! j` unchanged. -/
theorem clearOrbitLive_get!_of_not_inOrbit6 (live : ByteArray) (orb : Orbit6) (j : Nat)
    (h_not : ¬ inOrbit6 orb j) :
    (clearOrbitLive live orb).get! j = live.get! j := by
  have h0 : orb.j0 ≠ j := fun h => h_not (Or.inl h.symm)
  have h1 : orb.j1 ≠ j := fun h => h_not (Or.inr (Or.inl h.symm))
  have h2 : orb.j2 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inl h.symm)))
  have h3 : orb.j3 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inl h.symm))))
  have h4 : orb.j4 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm)))))
  have h5 : orb.j5 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.symm)))))
  unfold clearOrbitLive
  rw [byteArray_get!_set!_ne _ orb.j5 j 0 h5,
      byteArray_get!_set!_ne _ orb.j4 j 0 h4,
      byteArray_get!_set!_ne _ orb.j3 j 0 h3,
      byteArray_get!_set!_ne _ orb.j2 j 0 h2,
      byteArray_get!_set!_ne _ orb.j1 j 0 h1,
      byteArray_get!_set!_ne _ orb.j0 j 0 h0]

/-- All 6 indices of `orb` are bounded by `N`. -/
def orbitBounded (N : Nat) (orb : Orbit6) : Prop :=
  orb.j0 < N ∧ orb.j1 < N ∧ orb.j2 < N ∧ orb.j3 < N ∧ orb.j4 < N ∧ orb.j5 < N

/-- For any `j` belonging to `orb`, `setOrbitRanks ranks orb iter` assigns `iter` to `j`. -/
theorem setOrbitRanks_getD_of_inOrbit6 (ranks : Array Nat) (orb : Orbit6) (iter j : Nat)
    (h_bnd : orbitBounded ranks.size orb) (hj : inOrbit6 orb j) :
    (setOrbitRanks ranks orb iter).getD j 0 = iter := by
  have h_all := setOrbitRanks_all_eq ranks orb iter
    h_bnd.1 h_bnd.2.1 h_bnd.2.2.1 h_bnd.2.2.2.1 h_bnd.2.2.2.2.1 h_bnd.2.2.2.2.2
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h_all.1
  · exact h_all.2.1
  · exact h_all.2.2.1
  · exact h_all.2.2.2.1
  · exact h_all.2.2.2.2.1
  · exact h_all.2.2.2.2.2

/-- For any `j` belonging to `orb`, `clearOrbitLive live orb` sets `live.get! j` to `0`. -/
theorem clearOrbitLive_get!_of_inOrbit6 (live : ByteArray) (orb : Orbit6) (j : Nat)
    (h_bnd : orbitBounded live.size orb) (hj : inOrbit6 orb j) :
    (clearOrbitLive live orb).get! j = 0 := by
  have h_all := clearOrbitLive_all_zero live orb
    h_bnd.1 h_bnd.2.1 h_bnd.2.2.1 h_bnd.2.2.2.1 h_bnd.2.2.2.2.1 h_bnd.2.2.2.2.2
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h_all.1
  · exact h_all.2.1
  · exact h_all.2.2.1
  · exact h_all.2.2.2.1
  · exact h_all.2.2.2.2.1
  · exact h_all.2.2.2.2.2

theorem clearOrbitLive_preserves_zero (live : ByteArray) (orb : Orbit6) (j : Nat)
    (hj : live.get! j = 0) :
    (clearOrbitLive live orb).get! j = 0 := by
  unfold clearOrbitLive
  exact byteArray_get!_set!_preserves_zero _ orb.j5 j
    (byteArray_get!_set!_preserves_zero _ orb.j4 j
      (byteArray_get!_set!_preserves_zero _ orb.j3 j
        (byteArray_get!_set!_preserves_zero _ orb.j2 j
          (byteArray_get!_set!_preserves_zero _ orb.j1 j
            (byteArray_get!_set!_preserves_zero _ orb.j0 j hj)))))

theorem stepOrbitsList_preserves_zero (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (j : Nat) (hj : live.get! j = 0) :
    (stepOrbitsList cover iter orbs nextOrbits live ranks).2.1.get! j = 0 := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => exact hj
  | cons orb0 rest ih =>
    dsimp [stepOrbitsList]
    split
    · exact ih (nextOrbits.push orb0) live ranks hj
    · exact ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter)
        (clearOrbitLive_preserves_zero live orb0 j hj)

/-- When `orb ∈ orbs` is uncovered in `cover` and disjoint from all other orbits in `orbs`,
    `stepOrbitsList` assigns rank `iter` to every index `j` of `orb` and clears `live.get! j` to `0`. -/
theorem stepOrbitsList_eliminated_orb_ranks_and_live (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (orb : Orbit6) (horb : orb ∈ orbs) (h_nodup : orbs.Nodup)
    (h_disj : ∀ orb1 ∈ orbs, ∀ orb2 ∈ orbs, orb1 ≠ orb2 → ∀ j, inOrbit6 orb1 j → ¬ inOrbit6 orb2 j)
    (h_bnd_r : orbitBounded ranks.size orb)
    (h_bnd_l : orbitBounded live.size orb)
    (h_uncov : (cover.get! orb.j0 == 1 && cover.get! orb.j2 == 1 && cover.get! orb.j5 == 1) = false)
    (j : Nat) (hj : inOrbit6 orb j) :
    (stepOrbitsList cover iter orbs nextOrbits live ranks).2.2.getD j 0 = iter ∧
    (stepOrbitsList cover iter orbs nextOrbits live ranks).2.1.get! j = 0 := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => contradiction
  | cons orb0 rest ih =>
    rcases List.nodup_cons.mp h_nodup with ⟨h_not_mem_rest, h_nodup_rest⟩
    rcases List.mem_cons.mp horb with rfl | h_in_rest
    · dsimp [stepOrbitsList]
      rw [h_uncov]
      dsimp
      have h_not_in_rest : ∀ orb' ∈ rest, ¬ inOrbit6 orb' j := by
        intro orb' h_mem'
        have h_ne : orb ≠ orb' := fun h_eq => h_not_mem_rest (h_eq ▸ h_mem')
        exact h_disj orb (List.mem_cons_self ..) orb' (List.mem_cons_of_mem orb h_mem') h_ne j hj
      rw [stepOrbitsList_ranks_preserves_of_not_in_orbs _ _ _ _ _ _ j h_not_in_rest]
      refine ⟨setOrbitRanks_getD_of_inOrbit6 ranks orb iter j h_bnd_r hj, ?_⟩
      exact stepOrbitsList_preserves_zero _ _ _ _ _ _ j
        (clearOrbitLive_get!_of_inOrbit6 live orb j h_bnd_l hj)
    · have h_disj_rest : ∀ orb1 ∈ rest, ∀ orb2 ∈ rest, orb1 ≠ orb2 → ∀ j, inOrbit6 orb1 j → ¬ inOrbit6 orb2 j :=
        fun o1 h1 o2 h2 hne => h_disj o1 (List.mem_cons_of_mem orb0 h1) o2 (List.mem_cons_of_mem orb0 h2) hne
      dsimp [stepOrbitsList]
      split
      · exact ih (nextOrbits.push orb0) live ranks h_in_rest h_nodup_rest h_disj_rest h_bnd_r h_bnd_l
      · have h_bnd_r' : orbitBounded (setOrbitRanks ranks orb0 iter).size orb := by
          rw [setOrbitRanks_size]; exact h_bnd_r
        have h_bnd_l' : orbitBounded (clearOrbitLive live orb0).size orb := by
          rw [clearOrbitLive_size]; exact h_bnd_l
        exact ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter)
          h_in_rest h_nodup_rest h_disj_rest h_bnd_r' h_bnd_l'

/-- If `orb ∉ nextOrbits.toList`, `orbs.Nodup`, and `orb` is uncovered in `cover`,
    then `orb ∉ (stepOrbitsList cover iter orbs nextOrbits live ranks).1.toList`. -/
theorem stepOrbitsList_not_mem_of_uncovered (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (orb : Orbit6) (h_not_acc : orb ∉ nextOrbits.toList) (h_nodup : orbs.Nodup)
    (h_uncov : (cover.get! orb.j0 == 1 && cover.get! orb.j2 == 1 && cover.get! orb.j5 == 1) = false) :
    orb ∉ (stepOrbitsList cover iter orbs nextOrbits live ranks).1.toList := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => exact h_not_acc
  | cons orb0 rest ih =>
    rcases List.nodup_cons.mp h_nodup with ⟨h_not_in_rest, h_nodup_rest⟩
    dsimp [stepOrbitsList]
    by_cases h_eq : orb = orb0
    · subst h_eq
      rw [h_uncov]
      dsimp
      intro h_mem
      rcases mem_of_mem_stepOrbitsList _ _ _ _ _ _ orb h_mem with h_acc | h_rest
      · exact h_not_acc h_acc
      · exact h_not_in_rest h_rest
    · split
      · have h_not_acc' : orb ∉ (nextOrbits.push orb0).toList := by
          rw [Array.toList_push, List.mem_append, List.mem_singleton]
          rintro (h_acc | rfl)
          · exact h_not_acc h_acc
          · exact h_eq rfl
        exact ih (nextOrbits.push orb0) live ranks h_not_acc' h_nodup_rest
      · exact ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter) h_not_acc h_nodup_rest

theorem reducerStep_preserves_zero (N : Nat) (st : ReducerState) (j : Nat)
    (hj : st.live.get! j = 0) :
    (reducerStep N st).live.get! j = 0 := by
  dsimp [reducerStep]
  exact stepOrbitsList_preserves_zero _ _ _ _ _ _ j hj

theorem runReducerLoop_preserves_zero (N fuel : Nat) (st : ReducerState) (j : Nat)
    (hj : st.live.get! j = 0) :
    (runReducerLoop N fuel st).live.get! j = 0 := by
  induction fuel generalizing st with
  | zero => exact hj
  | succ fuel ih =>
    dsimp [runReducerLoop]
    split
    · exact ih (reducerStep N st) (reducerStep_preserves_zero N st j hj)
    · exact hj

/-- **Master Eliminated-Orbit Final Rank and Liveness Theorem (Steps B3–B5):**
    When `orb ∈ st_k.orbits.toList` is uncovered at round `st_k` (with `st_k.orbits.toList.Nodup`
    and pairwise disjoint orbits):
    1. Every index `j` of `orb` (`inOrbit6 orb j`) has final rank `st_k.iter + 1` and final `live.get! j = 0`
       after `runReducerLoop N rem (reducerStep N st_k)`.
    2. Any two indices `j1, j2` of `orb` have equal final rank (`S₃`-invariance of `ranks` on `orb`).
    3. Any index `j_dead` that is already non-live at the start of round `st_k` (`(st_k.live.get! j_dead == 1) = false`,
       where all orbits in `st_k.orbits.toList` have `orbitAllLive` and `∀ j', st_k.ranks.getD j' 0 ≤ st_k.iter`)
       has strictly smaller final rank than `j`. -/
theorem eliminated_orb_final_rank_and_live (N rem : Nat) (st_k : ReducerState)
    (orb : Orbit6) (horb : orb ∈ st_k.orbits.toList)
    (h_nodup : st_k.orbits.toList.Nodup)
    (h_disj : ∀ orb1 ∈ st_k.orbits.toList, ∀ orb2 ∈ st_k.orbits.toList,
      orb1 ≠ orb2 → ∀ j, inOrbit6 orb1 j → ¬ inOrbit6 orb2 j)
    (h_bnd_r : orbitBounded st_k.ranks.size orb)
    (h_bnd_l : orbitBounded st_k.live.size orb)
    (h_uncov :
      (let cov := (stepSMList st_k.live st_k.activeSM.toList (zeros N) (Array.mkEmpty st_k.activeSM.size)).1
       (cov.get! orb.j0 == 1 && cov.get! orb.j2 == 1 && cov.get! orb.j5 == 1) = false))
    (j : Nat) (hj : inOrbit6 orb j) :
    (runReducerLoop N rem (reducerStep N st_k)).ranks.getD j 0 = st_k.iter + 1 ∧
    (runReducerLoop N rem (reducerStep N st_k)).live.get! j = 0 := by
  have h_step := stepOrbitsList_eliminated_orb_ranks_and_live
    (stepSMList st_k.live st_k.activeSM.toList (zeros N) (Array.mkEmpty st_k.activeSM.size)).1
    (st_k.iter + 1) st_k.orbits.toList (Array.mkEmpty st_k.orbits.size) st_k.live st_k.ranks
    orb horb h_nodup h_disj h_bnd_r h_bnd_l h_uncov j hj
  have h_not_mem_step : orb ∉ (reducerStep N st_k).orbits.toList := by
    dsimp [reducerStep]
    exact stepOrbitsList_not_mem_of_uncovered _ _ _ _ _ _ orb (by simp) h_nodup h_uncov
  have h_not_in_step_orbs : ∀ orb' ∈ (reducerStep N st_k).orbits.toList, ¬ inOrbit6 orb' j := by
    intro orb' h_mem'
    have h_in_st : orb' ∈ st_k.orbits.toList := reducerStep_orbits_sub N st_k orb' h_mem'
    have h_ne : orb ≠ orb' := fun h_eq => h_not_mem_step (h_eq ▸ h_mem')
    exact h_disj orb horb orb' h_in_st h_ne j hj
  refine ⟨?_, ?_⟩
  · rw [runReducerLoop_ranks_preserves_of_not_in_orbits N rem (reducerStep N st_k) j h_not_in_step_orbs]
    exact h_step.1
  · exact runReducerLoop_preserves_zero N rem (reducerStep N st_k) j h_step.2

end CheckerSoundness
end Math
