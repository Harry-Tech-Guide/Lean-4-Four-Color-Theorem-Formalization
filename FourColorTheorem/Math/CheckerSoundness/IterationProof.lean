import FourColorTheorem.Math.Soundness.DReduce
import FourColorTheorem.Math.Soundness.CReduce

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false

/-!
# Checker Soundness: Tree Traversal and Fixed-Point Iteration Invariants

This module proves the soundness of the recursive binary-tree operations
`allFitLiveTotal` and `markFitCoverTotal` with respect to `smFitIndex`,
as well as the state invariants of `reducerStep` and `runReducerLoop`.
-/

/-- Structural tree indexing matching the recursion of `allFitLiveTotal` and `markFitCoverTotal`. -/
def smFitTree (sm : SMData) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, k, t, acc =>
    if k >= sm.p then acc
    else
      let delta := if (t &&& 1) == 0 then sm.a[k]! else sm.b[k]!
      smFitTree sm fuel (k + 1) (t >>> 1) (acc + delta)

/-- When `t = 0`, `smFitTree` always selects the `a[k]!` branch at every level. -/
theorem smFitTree_zero_step (sm : SMData) (fuel k acc : Nat) (hk : ¬ (k ≥ sm.p)) :
    smFitTree sm (fuel + 1) k 0 acc = smFitTree sm fuel (k + 1) 0 (acc + sm.a[k]!) := by
  dsimp [smFitTree]
  rw [if_neg hk]

/-- If `allFitLiveTotal fuel sm live k acc = false`, then there exists a parameter `t < 1 <<< fuel`
    whose leaf index `smFitTree sm fuel k t acc` is not live (`live.get! idx != 1`). -/
theorem exists_not_live_of_allFitLiveTotal_false (fuel : Nat) (sm : SMData) (live : ByteArray)
    (k acc : Nat) (h_false : allFitLiveTotal fuel sm live k acc = false) :
    ∃ t < 1 <<< fuel, (live.get! (smFitTree sm fuel k t acc) == 1) = false := by
  induction fuel generalizing k acc with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · decide
    · dsimp [allFitLiveTotal, smFitTree] at h_false ⊢
      exact h_false
  | succ fuel ih =>
    dsimp [allFitLiveTotal] at h_false
    by_cases hk : k ≥ sm.p
    · rw [if_pos hk] at h_false
      refine ⟨0, ?_, ?_⟩
      · rw [Nat.shiftLeft_eq, Nat.one_mul]
        exact Nat.two_pow_pos (fuel + 1)
      · dsimp [smFitTree]
        rw [if_pos hk]
        exact h_false
    · rw [if_neg hk] at h_false
      cases h_left : allFitLiveTotal fuel sm live (k + 1) (acc + sm.a[k]!) with
      | false =>
        rcases ih (k + 1) (acc + sm.a[k]!) h_left with ⟨t', ht', h_not_live⟩
        refine ⟨2 * t', ?_, ?_⟩
        · rw [Nat.shiftLeft_eq, Nat.one_mul] at ht' ⊢
          rw [Nat.pow_succ]
          omega
        · dsimp [smFitTree]
          rw [if_neg hk]
          have h_bit : ((2 * t') &&& 1 == 0) = true := by
            rw [Nat.and_one_is_mod]
            simp
          have h_shift : (2 * t') >>> 1 = t' := by
            rw [Nat.shiftRight_eq_div_pow]
            simp
          rw [h_bit, if_pos rfl, h_shift]
          exact h_not_live
      | true =>
        rw [h_left, Bool.true_and] at h_false
        rcases ih (k + 1) (acc + sm.b[k]!) h_false with ⟨t', ht', h_not_live⟩
        refine ⟨2 * t' + 1, ?_, ?_⟩
        · rw [Nat.shiftLeft_eq, Nat.one_mul] at ht' ⊢
          rw [Nat.pow_succ]
          omega
        · dsimp [smFitTree]
          rw [if_neg hk]
          have h_bit : ((2 * t' + 1) &&& 1 == 0) = false := by
            rw [Nat.and_one_is_mod]
            simp
          have h_shift : (2 * t' + 1) >>> 1 = t' := by
            rw [Nat.shiftRight_eq_div_pow]
            change (2 * t' + 1) / 2 = t'
            omega
          rw [h_bit]
          dsimp
          rw [h_shift]
          exact h_not_live

/-- If `allFitLiveTotal fuel sm live k acc = true`, then for every parameter `t < 1 <<< fuel`,
    the leaf index `smFitTree sm fuel k t acc` is live (`live.get! idx == 1`). -/
theorem all_live_of_allFitLiveTotal_true (fuel : Nat) (sm : SMData) (live : ByteArray)
    (k acc : Nat) (h_true : allFitLiveTotal fuel sm live k acc = true) :
    ∀ t < 1 <<< fuel, (live.get! (smFitTree sm fuel k t acc) == 1) = true := by
  induction fuel generalizing k acc with
  | zero =>
    intro t _
    dsimp [allFitLiveTotal, smFitTree] at h_true ⊢
    exact h_true
  | succ fuel ih =>
    intro t ht
    dsimp [allFitLiveTotal] at h_true
    by_cases hk : k ≥ sm.p
    · rw [if_pos hk] at h_true
      dsimp [smFitTree]
      rw [if_pos hk]
      exact h_true
    · rw [if_neg hk] at h_true
      have h_and := Bool.and_eq_true_iff.mp h_true
      have ht' : t >>> 1 < 1 <<< fuel := shift_right_lt_pow fuel t ht
      dsimp [smFitTree]
      rw [if_neg hk]
      by_cases hbit : (t &&& 1 == 0) = true
      · rw [if_pos hbit]
        exact ih (k + 1) (acc + sm.a[k]!) h_and.1 (t >>> 1) ht'
      · rw [if_neg hbit]
        exact ih (k + 1) (acc + sm.b[k]!) h_and.2 (t >>> 1) ht'

theorem byteArray_get!_eq_data (a : ByteArray) (i : Nat) :
    a.get! i = a.data[i]! := rfl

theorem byteArray_set!_data (a : ByteArray) (i : Nat) (v : UInt8) :
    (a.set! i v).data = a.data.set! i v := rfl

theorem byteArray_size_set! (a : ByteArray) (i : Nat) (v : UInt8) :
    (a.set! i v).size = a.size := by
  change (a.data.set! i v).size = a.data.size
  simp

theorem byteArray_get!_set!_self (a : ByteArray) (i : Nat) (v : UInt8) (hi : i < a.size) :
    (a.set! i v).get! i = v := by
  change (a.data.set! i v)[i]! = v
  simp [Array.getElem!_eq_getD, Array.getD]
  omega

theorem byteArray_get!_set!_ne (a : ByteArray) (i j : Nat) (v : UInt8) (hij : i ≠ j) :
    (a.set! i v).get! j = a.get! j := by
  change (a.data.set! i v)[j]! = a.data[j]!
  simp [Array.getElem!_eq_getD, Array.getD]
  split
  · next hj =>
    exact Array.getElem_setIfInBounds_ne hj hij
  · rfl

theorem byteArray_get!_set!_one_mono (a : ByteArray) (i j : Nat)
    (hj : (a.get! j == 1) = true) :
    ((a.set! i 1).get! j == 1) = true := by
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · rw [byteArray_get!_set!_self a i 1 hi]
      rfl
    · exfalso
      have h_oob : a.get! i = 0 := by
        change a.data[i]! = 0
        simp [Array.getElem!_eq_getD, Array.getD]
        rw [dif_neg hi]
        rfl
      rw [h_oob] at hj
      contradiction
  · rw [byteArray_get!_set!_ne a i j 1 hij]
    exact hj

theorem markFitCoverTotal_size (fuel : Nat) (sm : SMData) (k acc : Nat) (cov : ByteArray) :
    (markFitCoverTotal fuel sm k acc cov).size = cov.size := by
  induction fuel generalizing k acc cov with
  | zero =>
    dsimp [markFitCoverTotal]
    exact byteArray_size_set! cov acc 1
  | succ fuel ih =>
    dsimp [markFitCoverTotal]
    split
    · exact byteArray_size_set! cov acc 1
    · rw [ih, ih]

theorem markFitCoverTotal_preserves_one (fuel : Nat) (sm : SMData) (k acc : Nat)
    (cov : ByteArray) (j : Nat) (hj : (cov.get! j == 1) = true) :
    ((markFitCoverTotal fuel sm k acc cov).get! j == 1) = true := by
  induction fuel generalizing k acc cov with
  | zero =>
    dsimp [markFitCoverTotal]
    exact byteArray_get!_set!_one_mono cov acc j hj
  | succ fuel ih =>
    dsimp [markFitCoverTotal]
    split
    · exact byteArray_get!_set!_one_mono cov acc j hj
    · apply ih
      exact ih (k + 1) (acc + sm.a[k]!) cov hj

theorem markFitCoverTotal_sets_leaf (fuel : Nat) (sm : SMData) (k acc : Nat) (cov : ByteArray)
    (t : Nat) (ht : t < 1 <<< fuel)
    (h_bound : smFitTree sm fuel k t acc < cov.size) :
    ((markFitCoverTotal fuel sm k acc cov).get! (smFitTree sm fuel k t acc) == 1) = true := by
  induction fuel generalizing k acc cov t with
  | zero =>
    dsimp [markFitCoverTotal, smFitTree] at h_bound ⊢
    rw [byteArray_get!_set!_self cov acc 1 h_bound]
    rfl
  | succ fuel ih =>
    dsimp [markFitCoverTotal]
    by_cases hk : k ≥ sm.p
    · rw [if_pos hk]
      dsimp [smFitTree] at h_bound ⊢
      rw [if_pos hk] at h_bound ⊢
      rw [byteArray_get!_set!_self cov acc 1 h_bound]
      rfl
    · rw [if_neg hk]
      have ht' : t >>> 1 < 1 <<< fuel := shift_right_lt_pow fuel t ht
      dsimp [smFitTree] at h_bound ⊢
      rw [if_neg hk] at h_bound ⊢
      by_cases hbit : (t &&& 1 == 0) = true
      · rw [if_pos hbit] at h_bound ⊢
        apply markFitCoverTotal_preserves_one
        exact ih (k + 1) (acc + sm.a[k]!) cov (t >>> 1) ht' h_bound
      · rw [if_neg hbit] at h_bound ⊢
        have h_bound' : smFitTree sm fuel (k + 1) (t >>> 1) (acc + sm.b[k]!) <
            (markFitCoverTotal fuel sm (k + 1) (acc + sm.a[k]!) cov).size := by
          rw [markFitCoverTotal_size]
          exact h_bound
        exact ih (k + 1) (acc + sm.b[k]!)
          (markFitCoverTotal fuel sm (k + 1) (acc + sm.a[k]!) cov) (t >>> 1) ht' h_bound'

/-- Monotonicity of `allFitLiveTotal` under shrinking `live` sets:
    if every live entry of `live2` was already live in `live1`, then `allFitLiveTotal` on `live2`
    implies `allFitLiveTotal` on `live1`. -/
theorem allFitLiveTotal_mono (fuel : Nat) (sm : SMData) (live1 live2 : ByteArray)
    (h_sub : ∀ idx, (live2.get! idx == 1) = true → (live1.get! idx == 1) = true)
    (k acc : Nat) (h2 : allFitLiveTotal fuel sm live2 k acc = true) :
    allFitLiveTotal fuel sm live1 k acc = true := by
  induction fuel generalizing k acc with
  | zero =>
    dsimp [allFitLiveTotal] at h2 ⊢
    exact h_sub acc h2
  | succ fuel ih =>
    dsimp [allFitLiveTotal] at h2 ⊢
    split
    · next hk =>
      rw [if_pos hk] at h2
      exact h_sub acc h2
    · next hk =>
      rw [if_neg hk] at h2
      have h_and := Bool.and_eq_true_iff.mp h2
      exact Bool.and_eq_true_iff.mpr
        ⟨ih (k + 1) (acc + sm.a[k]!) h_and.1, ih (k + 1) (acc + sm.b[k]!) h_and.2⟩

/-- Structural fold over a list of signed matchings computing `(cover, nextSM)` in one iteration. -/
def stepSMList (live : ByteArray) : List SMData → ByteArray → Array SMData → ByteArray × Array SMData
  | [], cov, nextSM => (cov, nextSM)
  | sm :: rest, cov, nextSM =>
    if allFitLiveTotal sm.p sm live 0 0 then
      stepSMList live rest (markFitCoverTotal sm.p sm 0 0 cov) (nextSM.push sm)
    else
      stepSMList live rest cov nextSM

theorem stepSMList_size (live : ByteArray) (sms : List SMData) (cov : ByteArray) (nextSM : Array SMData) :
    (stepSMList live sms cov nextSM).1.size = cov.size := by
  induction sms generalizing cov nextSM with
  | nil => rfl
  | cons sm rest ih =>
    dsimp [stepSMList]
    split
    · rw [ih, markFitCoverTotal_size]
    · exact ih cov nextSM

theorem stepSMList_preserves_one (live : ByteArray) (sms : List SMData)
    (cov : ByteArray) (nextSM : Array SMData) (j : Nat)
    (hj : (cov.get! j == 1) = true) :
    ((stepSMList live sms cov nextSM).1.get! j == 1) = true := by
  induction sms generalizing cov nextSM with
  | nil => exact hj
  | cons sm rest ih =>
    dsimp [stepSMList]
    split
    · apply ih
      exact markFitCoverTotal_preserves_one sm.p sm 0 0 cov j hj
    · exact ih cov nextSM hj

/-- Fundamental Uncovered Matching Theorem:
    If trace index `j < cov.size` remains uncovered (`get! j != 1`) after `stepSMList`,
    then every signed matching `sm ∈ sms` fitting `j` at `t = 0` (`smFitTree sm sm.p 0 0 0 = j`)
    has `allFitLiveTotal sm.p sm live 0 0 = false`, and therefore possesses a parameter
    `t < 1 <<< sm.p` whose leaf trace index `smFitTree sm sm.p 0 t 0` is not live (`live.get! idx != 1`). -/
theorem uncovered_of_stepSMList (live : ByteArray) (sms : List SMData)
    (cov : ByteArray) (nextSM : Array SMData) (j : Nat) (hj_bound : j < cov.size)
    (h_uncov : ((stepSMList live sms cov nextSM).1.get! j == 1) = false)
    (sm : SMData) (hsm : sm ∈ sms) (h_fit0 : smFitTree sm sm.p 0 0 0 = j) :
    ∃ t < 1 <<< sm.p, (live.get! (smFitTree sm sm.p 0 t 0) == 1) = false := by
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
        have h_zero_lt : 0 < 1 <<< sm.p := by
          rw [Nat.shiftLeft_eq, Nat.one_mul]
          exact Nat.two_pow_pos sm.p
        have h_leaf_bound : smFitTree sm sm.p 0 0 0 < cov.size := by
          rw [h_fit0]; exact hj_bound
        have h_cov1 : ((markFitCoverTotal sm.p sm 0 0 cov).get! j == 1) = true := by
          rw [← h_fit0]
          exact markFitCoverTotal_sets_leaf sm.p sm 0 0 cov 0 h_zero_lt h_leaf_bound
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

theorem mem_stepSMList_of_mem_acc (live : ByteArray) (sms : List SMData)
    (cov : ByteArray) (nextSM : Array SMData) (sm : SMData)
    (h_acc : sm ∈ nextSM.toList) :
    sm ∈ (stepSMList live sms cov nextSM).2.toList := by
  induction sms generalizing cov nextSM with
  | nil => exact h_acc
  | cons sm0 rest ih =>
    dsimp [stepSMList]
    split
    · apply ih
      exact mem_push_data nextSM sm0 sm h_acc
    · exact ih cov nextSM h_acc

/-- Active-set compaction invariant for `stepSMList`:
    For every `sm ∈ sms`, either `sm` is retained in `(stepSMList live sms cov nextSM).2`,
    or `sm` already has a non-live leaf trace index in `live`. -/
theorem retained_or_not_live_of_stepSMList (live : ByteArray) (sms : List SMData)
    (cov : ByteArray) (nextSM : Array SMData) (sm : SMData) (hsm : sm ∈ sms) :
    sm ∈ (stepSMList live sms cov nextSM).2.toList ∨
      ∃ t < 1 <<< sm.p, (live.get! (smFitTree sm sm.p 0 t 0) == 1) = false := by
  induction sms generalizing cov nextSM with
  | nil => contradiction
  | cons sm0 rest ih =>
    rcases List.mem_cons.mp hsm with rfl | h_mem_rest
    · dsimp [stepSMList]
      cases h_all : allFitLiveTotal sm.p sm live 0 0 with
      | true =>
        rw [if_pos rfl]
        left
        apply mem_stepSMList_of_mem_acc
        exact mem_push_self nextSM sm
      | false =>
        rw [if_neg Bool.noConfusion]
        right
        exact exists_not_live_of_allFitLiveTotal_false sm.p sm live 0 0 h_all
    · dsimp [stepSMList]
      split
      · exact ih (markFitCoverTotal sm0.p sm0 0 0 cov) (nextSM.push sm0) h_mem_rest
      · exact ih cov nextSM h_mem_rest

/-- Setting an entry of a `ByteArray` to `0` never creates a `1`:
    if `(a.set! i 0).get! j == 1`, then `a.get! j == 1`. -/
theorem byteArray_get!_set!_zero_mono (a : ByteArray) (i j : Nat)
    (hj : ((a.set! i 0).get! j == 1) = true) :
    (a.get! j == 1) = true := by
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · rw [byteArray_get!_set!_self a i 0 hi] at hj
      contradiction
    · exfalso
      have h_oob : (a.set! i 0).get! i = 0 := by
        change (a.data.set! i 0)[i]! = 0
        simp [Array.getElem!_eq_getD, Array.getD]
        intro _
        rfl
      rw [h_oob] at hj
      contradiction
  · rw [byteArray_get!_set!_ne a i j 0 hij] at hj
    exact hj

/-- Clear all 6 trace indices of an `S₃`-orbit in `live`. -/
def clearOrbitLive (live : ByteArray) (orb : Orbit6) : ByteArray :=
  let l0 := live.set! orb.j0 0
  let l1 := l0.set! orb.j1 0
  let l2 := l1.set! orb.j2 0
  let l3 := l2.set! orb.j3 0
  let l4 := l3.set! orb.j4 0
  l4.set! orb.j5 0

/-- Record elimination iteration `iter` on all 6 trace indices of an `S₃`-orbit in `ranks`. -/
def setOrbitRanks (ranks : Array Nat) (orb : Orbit6) (iter : Nat) : Array Nat :=
  let r0 := ranks.set! orb.j0 iter
  let r1 := r0.set! orb.j1 iter
  let r2 := r1.set! orb.j2 iter
  let r3 := r2.set! orb.j3 iter
  let r4 := r3.set! orb.j4 iter
  r4.set! orb.j5 iter

theorem clearOrbitLive_mono (live : ByteArray) (orb : Orbit6) (j : Nat)
    (hj : ((clearOrbitLive live orb).get! j == 1) = true) :
    (live.get! j == 1) = true := by
  dsimp [clearOrbitLive] at hj
  have h4 := byteArray_get!_set!_zero_mono _ orb.j5 j hj
  have h3 := byteArray_get!_set!_zero_mono _ orb.j4 j h4
  have h2 := byteArray_get!_set!_zero_mono _ orb.j3 j h3
  have h1 := byteArray_get!_set!_zero_mono _ orb.j2 j h2
  have h0 := byteArray_get!_set!_zero_mono _ orb.j1 j h1
  exact byteArray_get!_set!_zero_mono _ orb.j0 j h0

/-- Structural fold over the orbit list in one elimination round. -/
def stepOrbitsList (cover : ByteArray) (iter : Nat) :
    List Orbit6 → Array Orbit6 → ByteArray → Array Nat → Array Orbit6 × ByteArray × Array Nat
  | [], nextOrbits, live, ranks => (nextOrbits, live, ranks)
  | orb :: rest, nextOrbits, live, ranks =>
    if cover.get! orb.j0 == 1 && cover.get! orb.j2 == 1 && cover.get! orb.j5 == 1 then
      stepOrbitsList cover iter rest (nextOrbits.push orb) live ranks
    else
      stepOrbitsList cover iter rest nextOrbits (clearOrbitLive live orb) (setOrbitRanks ranks orb iter)

theorem stepOrbitsList_live_mono (cover : ByteArray) (iter : Nat) (orbs : List Orbit6)
    (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat) (j : Nat)
    (hj : ((stepOrbitsList cover iter orbs nextOrbits live ranks).2.1.get! j == 1) = true) :
    (live.get! j == 1) = true := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => exact hj
  | cons orb rest ih =>
    dsimp [stepOrbitsList] at hj
    split at hj
    · exact ih (nextOrbits.push orb) live ranks hj
    · exact clearOrbitLive_mono live orb j (ih nextOrbits (clearOrbitLive live orb) (setOrbitRanks ranks orb iter) hj)

/-- If an orbit `orb` is not covered across all three pairings (`j0`, `j2`, `j5`),
    then at least one of its three canonical pairing traces is uncovered (`get! j != 1`). -/
theorem uncovered_pairing_of_not_covered (cover : ByteArray) (orb : Orbit6)
    (h_not_cov : (cover.get! orb.j0 == 1 && cover.get! orb.j2 == 1 && cover.get! orb.j5 == 1) = false) :
    (cover.get! orb.j0 == 1) = false ∨
    (cover.get! orb.j2 == 1) = false ∨
    (cover.get! orb.j5 == 1) = false := by
  cases h0 : (cover.get! orb.j0 == 1) with
  | false => exact Or.inl rfl
  | true =>
    cases h2 : (cover.get! orb.j2 == 1) with
    | false => exact Or.inr (Or.inl rfl)
    | true =>
      cases h5 : (cover.get! orb.j5 == 1) with
      | false => exact Or.inr (Or.inr rfl)
      | true =>
        rw [h0, h2, h5] at h_not_cov
        contradiction

theorem byteArray_get!_set!_preserves_zero (a : ByteArray) (i j : Nat)
    (hj : a.get! j = 0) :
    (a.set! i 0).get! j = 0 := by
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · exact byteArray_get!_set!_self a i 0 hi
    · change (a.data.set! i 0)[i]! = 0
      simp [Array.getElem!_eq_getD, Array.getD]
      intro _
      rfl
  · rw [byteArray_get!_set!_ne a i j 0 hij]
    exact hj

/-- `clearOrbitLive` sets all 6 trace indices `orb.j0 .. orb.j5` in `live` to `0`. -/
theorem clearOrbitLive_all_zero (live : ByteArray) (orb : Orbit6)
    (h0 : orb.j0 < live.size) (h1 : orb.j1 < live.size) (h2 : orb.j2 < live.size)
    (h3 : orb.j3 < live.size) (h4 : orb.j4 < live.size) (h5 : orb.j5 < live.size) :
    (clearOrbitLive live orb).get! orb.j0 = 0 ∧
    (clearOrbitLive live orb).get! orb.j1 = 0 ∧
    (clearOrbitLive live orb).get! orb.j2 = 0 ∧
    (clearOrbitLive live orb).get! orb.j3 = 0 ∧
    (clearOrbitLive live orb).get! orb.j4 = 0 ∧
    (clearOrbitLive live orb).get! orb.j5 = 0 := by
  unfold clearOrbitLive
  let l0 := live.set! orb.j0 0
  let l1 := l0.set! orb.j1 0
  let l2 := l1.set! orb.j2 0
  let l3 := l2.set! orb.j3 0
  let l4 := l3.set! orb.j4 0
  let l5 := l4.set! orb.j5 0
  have hs0 : l0.size = live.size := byteArray_size_set! live orb.j0 0
  have hs1 : l1.size = live.size := (byteArray_size_set! l0 orb.j1 0).trans hs0
  have hs2 : l2.size = live.size := (byteArray_size_set! l1 orb.j2 0).trans hs1
  have hs3 : l3.size = live.size := (byteArray_size_set! l2 orb.j3 0).trans hs2
  have hs4 : l4.size = live.size := (byteArray_size_set! l3 orb.j4 0).trans hs3
  have hz0 : l0.get! orb.j0 = 0 := byteArray_get!_set!_self live orb.j0 0 h0
  have hz1 : l1.get! orb.j1 = 0 := byteArray_get!_set!_self l0 orb.j1 0 (hs0.symm ▸ h1)
  have hz2 : l2.get! orb.j2 = 0 := byteArray_get!_set!_self l1 orb.j2 0 (hs1.symm ▸ h2)
  have hz3 : l3.get! orb.j3 = 0 := byteArray_get!_set!_self l2 orb.j3 0 (hs2.symm ▸ h3)
  have hz4 : l4.get! orb.j4 = 0 := byteArray_get!_set!_self l3 orb.j4 0 (hs3.symm ▸ h4)
  have hz5 : l5.get! orb.j5 = 0 := byteArray_get!_set!_self l4 orb.j5 0 (hs4.symm ▸ h5)
  refine ⟨?_, ?_, ?_, ?_, ?_, hz5⟩
  · exact byteArray_get!_set!_preserves_zero l4 orb.j5 orb.j0
      (byteArray_get!_set!_preserves_zero l3 orb.j4 orb.j0
        (byteArray_get!_set!_preserves_zero l2 orb.j3 orb.j0
          (byteArray_get!_set!_preserves_zero l1 orb.j2 orb.j0
            (byteArray_get!_set!_preserves_zero l0 orb.j1 orb.j0 hz0))))
  · exact byteArray_get!_set!_preserves_zero l4 orb.j5 orb.j1
      (byteArray_get!_set!_preserves_zero l3 orb.j4 orb.j1
        (byteArray_get!_set!_preserves_zero l2 orb.j3 orb.j1
          (byteArray_get!_set!_preserves_zero l1 orb.j2 orb.j1 hz1)))
  · exact byteArray_get!_set!_preserves_zero l4 orb.j5 orb.j2
      (byteArray_get!_set!_preserves_zero l3 orb.j4 orb.j2
        (byteArray_get!_set!_preserves_zero l2 orb.j3 orb.j2 hz2))
  · exact byteArray_get!_set!_preserves_zero l4 orb.j5 orb.j3
      (byteArray_get!_set!_preserves_zero l3 orb.j4 orb.j3 hz3)
  · exact byteArray_get!_set!_preserves_zero l4 orb.j5 orb.j4 hz4

theorem array_size_set! (a : Array Nat) (i v : Nat) :
    (a.set! i v).size = a.size := by
  simp

theorem array_getD_set!_self (a : Array Nat) (i v : Nat) (hi : i < a.size) :
    (a.set! i v).getD i 0 = v := by
  simp [Array.getD, hi]

theorem array_getD_set!_ne (a : Array Nat) (i j v : Nat) (hij : i ≠ j) :
    (a.set! i v).getD j 0 = a.getD j 0 := by
  simp [Array.getD]
  split
  · next hj => exact Array.getElem_setIfInBounds_ne hj hij
  · rfl

theorem array_getD_set!_preserves_val (a : Array Nat) (i j v : Nat)
    (hj : a.getD j 0 = v) :
    (a.set! i v).getD j 0 = v := by
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · exact array_getD_set!_self a i v hi
    · simp [Array.getD, hi] at hj ⊢
      exact hj
  · rw [array_getD_set!_ne a i j v hij]
    exact hj

/-- `setOrbitRanks` assigns the exact same rank `iter` to all 6 trace indices `orb.j0 .. orb.j5`,
    establishing `S₃`-invariance of `computeEliminationRanks` across every orbit. -/
theorem setOrbitRanks_all_eq (ranks : Array Nat) (orb : Orbit6) (iter : Nat)
    (h0 : orb.j0 < ranks.size) (h1 : orb.j1 < ranks.size) (h2 : orb.j2 < ranks.size)
    (h3 : orb.j3 < ranks.size) (h4 : orb.j4 < ranks.size) (h5 : orb.j5 < ranks.size) :
    (setOrbitRanks ranks orb iter).getD orb.j0 0 = iter ∧
    (setOrbitRanks ranks orb iter).getD orb.j1 0 = iter ∧
    (setOrbitRanks ranks orb iter).getD orb.j2 0 = iter ∧
    (setOrbitRanks ranks orb iter).getD orb.j3 0 = iter ∧
    (setOrbitRanks ranks orb iter).getD orb.j4 0 = iter ∧
    (setOrbitRanks ranks orb iter).getD orb.j5 0 = iter := by
  unfold setOrbitRanks
  let r0 := ranks.set! orb.j0 iter
  let r1 := r0.set! orb.j1 iter
  let r2 := r1.set! orb.j2 iter
  let r3 := r2.set! orb.j3 iter
  let r4 := r3.set! orb.j4 iter
  let r5 := r4.set! orb.j5 iter
  have hs0 : r0.size = ranks.size := array_size_set! ranks orb.j0 iter
  have hs1 : r1.size = ranks.size := (array_size_set! r0 orb.j1 iter).trans hs0
  have hs2 : r2.size = ranks.size := (array_size_set! r1 orb.j2 iter).trans hs1
  have hs3 : r3.size = ranks.size := (array_size_set! r2 orb.j3 iter).trans hs2
  have hs4 : r4.size = ranks.size := (array_size_set! r3 orb.j4 iter).trans hs3
  have hr0 : r0.getD orb.j0 0 = iter := array_getD_set!_self ranks orb.j0 iter h0
  have hr1 : r1.getD orb.j1 0 = iter := array_getD_set!_self r0 orb.j1 iter (hs0.symm ▸ h1)
  have hr2 : r2.getD orb.j2 0 = iter := array_getD_set!_self r1 orb.j2 iter (hs1.symm ▸ h2)
  have hr3 : r3.getD orb.j3 0 = iter := array_getD_set!_self r2 orb.j3 iter (hs2.symm ▸ h3)
  have hr4 : r4.getD orb.j4 0 = iter := array_getD_set!_self r3 orb.j4 iter (hs3.symm ▸ h4)
  have hr5 : r5.getD orb.j5 0 = iter := array_getD_set!_self r4 orb.j5 iter (hs4.symm ▸ h5)
  refine ⟨?_, ?_, ?_, ?_, ?_, hr5⟩
  · exact array_getD_set!_preserves_val r4 orb.j5 orb.j0 iter
      (array_getD_set!_preserves_val r3 orb.j4 orb.j0 iter
        (array_getD_set!_preserves_val r2 orb.j3 orb.j0 iter
          (array_getD_set!_preserves_val r1 orb.j2 orb.j0 iter
            (array_getD_set!_preserves_val r0 orb.j1 orb.j0 iter hr0))))
  · exact array_getD_set!_preserves_val r4 orb.j5 orb.j1 iter
      (array_getD_set!_preserves_val r3 orb.j4 orb.j1 iter
        (array_getD_set!_preserves_val r2 orb.j3 orb.j1 iter
          (array_getD_set!_preserves_val r1 orb.j2 orb.j1 iter hr1)))
  · exact array_getD_set!_preserves_val r4 orb.j5 orb.j2 iter
      (array_getD_set!_preserves_val r3 orb.j4 orb.j2 iter
        (array_getD_set!_preserves_val r2 orb.j3 orb.j2 iter hr2))
  · exact array_getD_set!_preserves_val r4 orb.j5 orb.j3 iter
      (array_getD_set!_preserves_val r3 orb.j4 orb.j3 iter hr3)
  · exact array_getD_set!_preserves_val r4 orb.j5 orb.j4 iter hr4

end CheckerSoundness
end Math
