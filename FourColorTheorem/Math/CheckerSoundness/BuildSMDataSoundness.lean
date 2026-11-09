import FourColorTheorem.Math.CheckerSoundness.MatchingExtraction

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-!
# Stage A (Checkpoint A2): `buildSMDataTotal` Completeness & Unconditional `FullRepresentationHypothesis`

This module completes the proof of RSST Lemma (a) (`FullRepresentationHypothesis`) by structural
induction on `IsExtractedMatching`:
1. Constructs the sign bitmask `signMaskOfChords`, baseline parameter `baseParamOfChords`,
   and valid Kempe swap choice family `swapOfChords` for any extracted non-crossing matching `m`.
2. Proves the cyclic sign-parity condition `(negSignCount s m.length % 2 == r % 2) = true`
   and membership `mkSMData pow3 m s ∈ (buildSMDataTotal r pow3).toList`.
3. Proves that `boundaryTrace c (boundaryKempeSwap c b theta1 (swapOfChords r b m t)) pow3`
   equals `smFitIndex (mkSMData pow3 m s) t` for every `t < 1 <<< m.length`.
4. Proves `fullRepresentation_of_ringCycle` and `fullRepresentation_sharedPow3_of_ringCycle`
   unconditionally.
-/

/-!
### Part 1: Sign Bitmask, Baseline Parameter, and Swap-Choice Construction
-/

/-- Sign bitmask `s < 2^m.length` of a chord list `m` for coloring `b`:
    bit `0` of `(x, y) :: rest` is `1` (`+`) iff `edgeDigitAt r b x == edgeDigitAt r b y`. -/
def signMaskOfChords (r : Nat) (b : Nat → Color) : List (Nat × Nat) → Nat
  | [] => 0
  | (x, y) :: rest =>
    (if edgeDigitAt r b x == edgeDigitAt r b y then 1 else 0) + 2 * signMaskOfChords r b rest

/-- Baseline fitting parameter `t₀ < 2^m.length` of a chord list `m` for coloring `b`:
    bit `0` of `(x, y) :: rest` is `1` iff `edgeDigitAt r b x == 2`. -/
def baseParamOfChords (r : Nat) (b : Nat → Color) : List (Nat × Nat) → Nat
  | [] => 0
  | (x, _) :: rest =>
    (if edgeDigitAt r b x == 2 then 1 else 0) + 2 * baseParamOfChords r b rest

/-- Kempe swap choice on chord list `m` for parameter `t`:
    toggles vertex `i` on `(x, y)` iff `(t &&& 1 == 1)` differs from `(edgeDigitAt r b x == 2)`
    and `x < i ∧ i ≤ y`, then recurses on `rest` with `t >>> 1`. -/
def swapOfChords (r : Nat) (b : Nat → Color) : List (Nat × Nat) → Nat → Nat → Bool
  | [], _, _ => false
  | (x, y) :: rest, t, i =>
    let prev := swapOfChords r b rest (t >>> 1) i
    let flip := ((t &&& 1 == 1) != (edgeDigitAt r b x == 2))
    if flip && decide (x < i ∧ i ≤ y) then !prev else prev

theorem bit0_add_two_mul (b₀ s' : Nat) (hb : b₀ = 0 ∨ b₀ = 1) :
    (b₀ + 2 * s') &&& 1 = b₀ ∧ (b₀ + 2 * s') >>> 1 = s' := by
  rcases hb with rfl | rfl
  · simp [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  · simp [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    omega

theorem ite_zero_one_cases (cond : Bool) :
    (if cond then 1 else 0) = 0 ∨ (if cond then 1 else 0) = 1 := by
  cases cond <;> simp

theorem signMaskOfChords_lt (r : Nat) (b : Nat → Color) (m : List (Nat × Nat)) :
    signMaskOfChords r b m < 1 <<< m.length := by
  induction m with
  | nil => simp [signMaskOfChords]
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    dsimp [signMaskOfChords]
    rw [Nat.shiftLeft_eq, Nat.one_mul] at ih ⊢
    rw [Nat.pow_succ]
    have h01 := ite_zero_one_cases (edgeDigitAt r b x == edgeDigitAt r b y)
    rcases h01 with h0 | h1 <;> omega

theorem baseParamOfChords_lt (r : Nat) (b : Nat → Color) (m : List (Nat × Nat)) :
    baseParamOfChords r b m < 1 <<< m.length := by
  induction m with
  | nil => simp [baseParamOfChords]
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    dsimp [baseParamOfChords]
    rw [Nat.shiftLeft_eq, Nat.one_mul] at ih ⊢
    rw [Nat.pow_succ]
    have h01 := ite_zero_one_cases (edgeDigitAt r b x == 2)
    rcases h01 with h0 | h1 <;> omega

/-- At the baseline parameter `t₀ = baseParamOfChords r b m`, `swapOfChords r b m t₀ i = false` for all `i`. -/
theorem swapOfChords_baseParam (r : Nat) (b : Nat → Color) (m : List (Nat × Nat)) (i : Nat) :
    swapOfChords r b m (baseParamOfChords r b m) i = false := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    dsimp [swapOfChords, baseParamOfChords]
    have h_bits := bit0_add_two_mul (if edgeDigitAt r b x == 2 then 1 else 0)
      (baseParamOfChords r b rest) (ite_zero_one_cases (edgeDigitAt r b x == 2))
    rw [h_bits.1, h_bits.2, ih]
    cases edgeDigitAt r b x == 2 <;> rfl

/-- If every chord `(x, y) ∈ m` has `0 ≤ x < y < c.ringSize` and an `E`-closed interval `(x, y]`,
    then `swapOfChords c.ringSize b m t` is a valid swap choice for every `t`. -/
theorem swapOfChords_valid (c : Configuration) (b : BoundaryColoring c)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (m : List (Nat × Nat))
    (h_rng : ∀ p ∈ m, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < c.ringSize)
    (h_closed : ∀ p ∈ m, ∀ u < c.ringSize, ∀ w < c.ringSize,
      partEquiv equiv_ab equiv_cd u w → ((p.1 < u ∧ u ≤ p.2) ↔ (p.1 < w ∧ w ≤ p.2)))
    (t : Nat) :
    IsValidSwapChoice c b theta1 equiv_ab equiv_cd (swapOfChords c.ringSize b m t) := by
  induction m generalizing t with
  | nil => exact empty_swap_is_valid c b theta1 equiv_ab equiv_cd
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    have hp_rng := h_rng (x, y) List.mem_cons_self
    have hp_closed := h_closed (x, y) List.mem_cons_self
    have h_prev := ih
      (fun q hq => h_rng q (List.mem_cons_of_mem (x, y) hq))
      (fun q hq => h_closed q (List.mem_cons_of_mem (x, y) hq))
      (t >>> 1)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      dsimp [swapOfChords] at hi
      cases h_cond : (((t &&& 1 == 1) != (edgeDigitAt c.ringSize b x == 2)) && decide (x < i ∧ i ≤ y))
      · rw [h_cond, if_neg Bool.noConfusion] at hi
        exact h_prev.ring_only i hi
      · rw [Bool.and_eq_true, decide_eq_true_eq] at h_cond
        have := h_cond.2
        omega
    · intro i hi j hj hab
      dsimp [swapOfChords]
      have h_prev_eq := h_prev.respects_ab i hi j hj hab
      have h_iff := hp_closed i hi j hj (Or.inl hab)
      have h_dec : decide (x < i ∧ i ≤ y) = decide (x < j ∧ j ≤ y) := by
        cases h1 : decide (x < i ∧ i ≤ y) <;> cases h2 : decide (x < j ∧ j ≤ y)
        · rfl
        · exfalso
          exact of_decide_eq_false h1 (h_iff.mpr (of_decide_eq_true h2))
        · exfalso
          exact of_decide_eq_false h2 (h_iff.mp (of_decide_eq_true h1))
        · rfl
      rw [h_prev_eq, h_dec]
    · intro i hi j hj hcd
      dsimp [swapOfChords]
      have h_prev_eq := h_prev.respects_cd i hi j hj hcd
      have h_iff := hp_closed i hi j hj (Or.inr hcd)
      have h_dec : decide (x < i ∧ i ≤ y) = decide (x < j ∧ j ≤ y) := by
        cases h1 : decide (x < i ∧ i ≤ y) <;> cases h2 : decide (x < j ∧ j ≤ y)
        · rfl
        · exfalso
          exact of_decide_eq_false h1 (h_iff.mpr (of_decide_eq_true h2))
        · exfalso
          exact of_decide_eq_false h2 (h_iff.mp (of_decide_eq_true h1))
        · rfl
      rw [h_prev_eq, h_dec]

/-!
### Part 2: Cyclic Sign-Parity Theorem (`negSignCount % 2 == r % 2`)
-/

theorem negSignCount_signMask_cons (r : Nat) (b : Nat → Color)
    (x y : Nat) (rest : List (Nat × Nat)) :
    negSignCount (signMaskOfChords r b ((x, y) :: rest)) (((x, y) :: rest).length) =
      (if edgeDigitAt r b x == edgeDigitAt r b y then 0 else 1) +
        negSignCount (signMaskOfChords r b rest) rest.length := by
  dsimp [signMaskOfChords, negSignCount]
  have h_bits := bit0_add_two_mul (if edgeDigitAt r b x == edgeDigitAt r b y then 1 else 0)
    (signMaskOfChords r b rest) (ite_zero_one_cases (edgeDigitAt r b x == edgeDigitAt r b y))
  rw [h_bits.1, h_bits.2]
  cases edgeDigitAt r b x == edgeDigitAt r b y <;> rfl

theorem negSignCount_signMask_append (r : Nat) (b : Nat → Color)
    (m1 m2 : List (Nat × Nat)) :
    negSignCount (signMaskOfChords r b (m1 ++ m2)) (m1 ++ m2).length =
      negSignCount (signMaskOfChords r b m1) m1.length +
        negSignCount (signMaskOfChords r b m2) m2.length := by
  induction m1 with
  | nil => simp [signMaskOfChords, negSignCount]
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    rw [List.cons_append, negSignCount_signMask_cons, negSignCount_signMask_cons, ih, Nat.add_assoc]

/-- Count of edges `i ∈ [lo, hi)` with `edgeDigitAt r b i == 1`. -/
def rangeDigitOneCount (r : Nat) (b : Nat → Color) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    (if edgeDigitAt r b lo == 1 then 1 else 0) + rangeDigitOneCount r b (lo + 1) hi
  else 0
termination_by hi - lo

theorem rangeDigitOneCount_eq_zero (r : Nat) (b : Nat → Color) (lo hi : Nat) (h : ¬ (lo < hi)) :
    rangeDigitOneCount r b lo hi = 0 := by
  rw [rangeDigitOneCount, dif_neg h]

theorem rangeDigitOneCount_step (r : Nat) (b : Nat → Color) (lo hi : Nat) (h : lo < hi) :
    rangeDigitOneCount r b lo hi =
      (if edgeDigitAt r b lo == 1 then 1 else 0) + rangeDigitOneCount r b (lo + 1) hi := by
  rw [rangeDigitOneCount, dif_pos h]

theorem rangeDigitOneCount_split (r : Nat) (b : Nat → Color) (lo mid hi : Nat)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    rangeDigitOneCount r b lo hi =
      rangeDigitOneCount r b lo mid + rangeDigitOneCount r b mid hi := by
  have h_aux : ∀ d, mid - lo = d →
      rangeDigitOneCount r b lo hi =
        rangeDigitOneCount r b lo mid + rangeDigitOneCount r b mid hi := by
    intro d
    induction d generalizing lo with
    | zero =>
      intro h_diff
      have h_eq : lo = mid := by omega
      subst h_eq
      rw [rangeDigitOneCount_eq_zero r b lo lo (by omega), Nat.zero_add]
    | succ d ih =>
      intro h_diff
      have h_lt_mid : lo < mid := by omega
      have h_lt_hi : lo < hi := Nat.lt_of_lt_of_le h_lt_mid h2
      rw [rangeDigitOneCount_step r b lo hi h_lt_hi,
          rangeDigitOneCount_step r b lo mid h_lt_mid,
          ih (lo + 1) (by omega) (by omega), Nat.add_assoc]
  exact h_aux (mid - lo) rfl

theorem transition_edgeDigit_one_or_two (c : Configuration) (b : BoundaryColoring c)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (i : Nat) (hi : i < c.ringSize)
    (h_diff : theta1Pair b (i % c.ringSize) ≠ theta1Pair b ((i + 1) % c.ringSize)) :
    edgeDigitAt c.ringSize b i = 1 ∨ edgeDigitAt c.ringSize b i = 2 := by
  rw [Nat.mod_eq_of_lt hi] at h_diff
  have h_ne0 : edgeDigitAt c.ringSize b i ≠ 0 := by
    intro h0
    exact h_diff ((edgeDigitAt_eq_zero_iff_same_pair c b h_ring hb i hi).mp h0)
  have h_lt3 := edgeDigitAt_lt_three c.ringSize b i
  omega

private theorem pair_digit_one_parity (d1 d2 : Nat)
    (h1 : d1 = 1 ∨ d1 = 2) (h2 : d2 = 1 ∨ d2 = 2) :
    ((if d1 == 1 then 1 else 0) + (if d2 == 1 then 1 else 0)) % 2 =
      (if d1 == d2 then 0 else 1) % 2 := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> decide

/-- For any extracted matching `m` on `[lo, hi)`, `negSignCount` has the exact same parity
    as `rangeDigitOneCount c.ringSize b lo hi`. -/
theorem negSignCount_mod_two_eq_rangeDigitOneCount (c : Configuration) (b : BoundaryColoring c)
    (E : Nat → Nat → Prop) (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    {lo hi : Nat} {m : List (Nat × Nat)}
    (h_ext : IsExtractedMatching c.ringSize (theta1Pair b) E lo hi m) :
    negSignCount (signMaskOfChords c.ringSize b m) m.length % 2 =
      rangeDigitOneCount c.ringSize b lo hi % 2 := by
  induction h_ext with
  | nil lo _ =>
    rw [rangeDigitOneCount_eq_zero c.ringSize b lo lo (by omega)]
    rfl
  | skip lo hi m h_lt h_hi h_same _ ih =>
    have hlo_r : lo < c.ringSize := Nat.lt_of_lt_of_le h_lt h_hi
    rw [Nat.mod_eq_of_lt hlo_r] at h_same
    have hd0 : edgeDigitAt c.ringSize b lo = 0 :=
      (edgeDigitAt_eq_zero_iff_same_pair c b h_ring hb lo hlo_r).mpr h_same
    rw [rangeDigitOneCount_step c.ringSize b lo hi h_lt, hd0]
    simpa using ih
  | pair lo k₀ hi m1 m2 hk_ge hk_lt h_hi h_diff_lo h_diff_k0 _ _ _ ih1 ih2 =>
    have hk0_r : k₀ < c.ringSize := Nat.lt_of_lt_of_le hk_lt h_hi
    have hlo_r : lo < c.ringSize := by omega
    have hd_lo := transition_edgeDigit_one_or_two c b h_ring hb lo hlo_r h_diff_lo
    have hd_k0 := transition_edgeDigit_one_or_two c b h_ring hb k₀ hk0_r h_diff_k0
    have h_par := pair_digit_one_parity (edgeDigitAt c.ringSize b lo) (edgeDigitAt c.ringSize b k₀) hd_lo hd_k0
    rw [negSignCount_signMask_cons, negSignCount_signMask_append]
    rw [rangeDigitOneCount_step c.ringSize b lo hi (by omega),
        rangeDigitOneCount_split c.ringSize b (lo + 1) k₀ hi hk_ge (Nat.le_of_lt hk_lt),
        rangeDigitOneCount_step c.ringSize b k₀ hi hk_lt]
    omega

private theorem edgeDigitAt_one_bit0_rel (c1 c2 : Color) (hne : c1 ≠ c2) :
    ((if (let diff := c1.toNat ^^^ c2.toNat; if diff > 0 then diff - 1 else 0) == 1 then 1 else 0) +
      1 + c1.toNat % 2 + c2.toNat % 2) % 2 = 0 := by
  cases c1 <;> cases c2 <;> revert hne <;> decide

/-- Telescoping parity formula for `rangeDigitOneCount c.ringSize b 0 k` (`k ≤ c.ringSize`). -/
theorem rangeDigitOneCount_prefix_mod_two (c : Configuration) (b : BoundaryColoring c)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (k : Nat) (hk : k ≤ c.ringSize) :
    rangeDigitOneCount c.ringSize b 0 k % 2 =
      (k + (b 0).toNat % 2 + (b (k % c.ringSize)).toNat % 2) % 2 := by
  induction k with
  | zero =>
    rw [rangeDigitOneCount_eq_zero c.ringSize b 0 0 (by omega), Nat.zero_mod, Nat.zero_mod]
    omega
  | succ k ih =>
    have hk_lt : k < c.ringSize := Nat.lt_of_succ_le hk
    have hr_pos : c.ringSize > 0 := by have := h_ring.1; omega
    have h_nxt_lt : (k + 1) % c.ringSize < c.ringSize := Nat.mod_lt _ hr_pos
    have hadj : c.adj k ((k + 1) % c.ringSize) = true := h_ring.2 k hk_lt
    have hne : b k ≠ b ((k + 1) % c.ringSize) := hb k ((k + 1) % c.ringSize) hk_lt h_nxt_lt hadj
    have h_bit := edgeDigitAt_one_bit0_rel (b k) (b ((k + 1) % c.ringSize)) hne
    change ((if edgeDigitAt c.ringSize b k == 1 then 1 else 0) +
      1 + (b k).toNat % 2 + (b ((k + 1) % c.ringSize)).toNat % 2) % 2 = 0 at h_bit
    rw [rangeDigitOneCount_split c.ringSize b 0 k (k + 1) (Nat.zero_le k) (Nat.le_succ k),
        rangeDigitOneCount_step c.ringSize b k (k + 1) (Nat.lt_succ_self k),
        rangeDigitOneCount_eq_zero c.ringSize b (k + 1) (k + 1) (by omega),
        Nat.add_zero]
    have h_ih := ih (Nat.le_of_lt hk_lt)
    rw [Nat.mod_eq_of_lt hk_lt] at h_ih
    omega

/-- Full ring parity theorem: for any extracted matching `m` on `[0, c.ringSize)`,
    `(negSignCount (signMaskOfChords c.ringSize b m) m.length % 2 == c.ringSize % 2) = true`. -/
theorem negSignCount_signMask_ring_parity (c : Configuration) (b : BoundaryColoring c)
    (E : Nat → Nat → Prop) (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (m : List (Nat × Nat))
    (h_ext : IsExtractedMatching c.ringSize (theta1Pair b) E 0 c.ringSize m) :
    (negSignCount (signMaskOfChords c.ringSize b m) m.length % 2 == c.ringSize % 2) = true := by
  rw [beq_iff_eq]
  rw [negSignCount_mod_two_eq_rangeDigitOneCount c b E h_ring hb h_ext]
  rw [rangeDigitOneCount_prefix_mod_two c b h_ring hb c.ringSize (Nat.le_refl c.ringSize)]
  rw [Nat.mod_self]
  omega

/-!
### Part 3: Structural `chordFitSum`, `smFitIndex` Equivalence, and `rangeTraceSum`
-/

/-- Structural sum of selected chord deltas over a chord list `m`, sign bitmask `s`, and parameter `t`. -/
def chordFitSum (pow3 : Array Nat) : List (Nat × Nat) → Nat → Nat → Nat
  | [], _, _ => 0
  | (x, y) :: rest, s, t =>
    let px := pow3.getD x 0
    let py := pow3.getD y 0
    let d :=
      if s &&& 1 == 1 then
        if t &&& 1 == 0 then px + py else 2 * px + 2 * py
      else
        if t &&& 1 == 0 then px + 2 * py else 2 * px + py
    d + chordFitSum pow3 rest (s >>> 1) (t >>> 1)

theorem shiftRight_succ_eq (t k : Nat) :
    t >>> (k + 1) = (t >>> k) >>> 1 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem shiftRight_add_eq (t a b : Nat) :
    t >>> (a + b) = (t >>> a) >>> b := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
      Nat.pow_add, Nat.div_div_eq_div_mul]

theorem list_getD_append_mid {α : Type} (pre suff : List α) (d x : α)
    (k : Nat) (hk : pre.length = k) :
    (pre ++ d :: suff).toArray.getD k x = d := by
  subst hk
  have h_lt : pre.length < (pre ++ d :: suff).toArray.size := by
    simp
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h_lt]
  change (pre ++ d :: suff)[pre.length] = d
  simp

theorem buildSMDeltas_length (pow3 : Array Nat) (s : Nat) (m : List (Nat × Nat)) :
    (buildSMDeltas pow3 s m).1.length = m.length ∧
    (buildSMDeltas pow3 s m).2.length = m.length := by
  induction m generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    dsimp [buildSMDeltas]
    have h_ih := ih (s >>> 1)
    split
    · exact ⟨congrArg Nat.succ h_ih.1, congrArg Nat.succ h_ih.2⟩
    · exact ⟨congrArg Nat.succ h_ih.1, congrArg Nat.succ h_ih.2⟩

theorem smFitIndexAux_eq_chordFitSum (pow3 : Array Nat) (sm : SMData)
    (m : List (Nat × Nat)) (pre_a pre_b : List Nat) (s t k acc : Nat)
    (ha : sm.a = (pre_a ++ (buildSMDeltas pow3 s m).1).toArray)
    (hb : sm.b = (pre_b ++ (buildSMDeltas pow3 s m).2).toArray)
    (hk_a : pre_a.length = k) (hk_b : pre_b.length = k) :
    smFitIndexAux sm t m.length k acc = acc + chordFitSum pow3 m s (t >>> k) := by
  induction m generalizing pre_a pre_b s k acc with
  | nil =>
    dsimp [smFitIndexAux, chordFitSum]
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    dsimp [smFitIndexAux, chordFitSum, buildSMDeltas] at ha hb ⊢
    cases hs : (s &&& 1 == 1)
    · rw [hs] at ha hb
      dsimp at ha hb ⊢
      have h_da : sm.a.getD k 0 = pow3.getD x 0 + 2 * pow3.getD y 0 := by
        rw [ha]; exact list_getD_append_mid pre_a _ _ 0 k hk_a
      have h_db : sm.b.getD k 0 = 2 * pow3.getD x 0 + pow3.getD y 0 := by
        rw [hb]; exact list_getD_append_mid pre_b _ _ 0 k hk_b
      have ha' : sm.a = ((pre_a ++ [pow3.getD x 0 + 2 * pow3.getD y 0]) ++ (buildSMDeltas pow3 (s >>> 1) rest).1).toArray := by
        simp [ha, List.append_assoc]
      have hb' : sm.b = ((pre_b ++ [2 * pow3.getD x 0 + pow3.getD y 0]) ++ (buildSMDeltas pow3 (s >>> 1) rest).2).toArray := by
        simp [hb, List.append_assoc]
      have hk_a' : (pre_a ++ [pow3.getD x 0 + 2 * pow3.getD y 0]).length = k + 1 := by simp [hk_a]
      have hk_b' : (pre_b ++ [2 * pow3.getD x 0 + pow3.getD y 0]).length = k + 1 := by simp [hk_b]
      rw [h_da, h_db, ih (pre_a ++ [pow3.getD x 0 + 2 * pow3.getD y 0])
          (pre_b ++ [2 * pow3.getD x 0 + pow3.getD y 0]) (s >>> 1) (k + 1) _ ha' hb' hk_a' hk_b',
          shiftRight_succ_eq t k, Nat.add_assoc]
    · rw [hs] at ha hb
      dsimp at ha hb ⊢
      have h_da : sm.a.getD k 0 = pow3.getD x 0 + pow3.getD y 0 := by
        rw [ha]; exact list_getD_append_mid pre_a _ _ 0 k hk_a
      have h_db : sm.b.getD k 0 = 2 * pow3.getD x 0 + 2 * pow3.getD y 0 := by
        rw [hb]; exact list_getD_append_mid pre_b _ _ 0 k hk_b
      have ha' : sm.a = ((pre_a ++ [pow3.getD x 0 + pow3.getD y 0]) ++ (buildSMDeltas pow3 (s >>> 1) rest).1).toArray := by
        simp [ha, List.append_assoc]
      have hb' : sm.b = ((pre_b ++ [2 * pow3.getD x 0 + 2 * pow3.getD y 0]) ++ (buildSMDeltas pow3 (s >>> 1) rest).2).toArray := by
        simp [hb, List.append_assoc]
      have hk_a' : (pre_a ++ [pow3.getD x 0 + pow3.getD y 0]).length = k + 1 := by simp [hk_a]
      have hk_b' : (pre_b ++ [2 * pow3.getD x 0 + 2 * pow3.getD y 0]).length = k + 1 := by simp [hk_b]
      rw [h_da, h_db, ih (pre_a ++ [pow3.getD x 0 + pow3.getD y 0])
          (pre_b ++ [2 * pow3.getD x 0 + 2 * pow3.getD y 0]) (s >>> 1) (k + 1) _ ha' hb' hk_a' hk_b',
          shiftRight_succ_eq t k, Nat.add_assoc]

/-- `smFitIndex (mkSMData pow3 m s) t` equals `chordFitSum pow3 m s t`. -/
theorem smFitIndex_mkSMData_eq (pow3 : Array Nat) (m : List (Nat × Nat)) (s t : Nat) :
    smFitIndex (mkSMData pow3 m s) t = chordFitSum pow3 m s t := by
  unfold smFitIndex mkSMData
  have h := smFitIndexAux_eq_chordFitSum pow3 (mkSMData pow3 m s) m [] [] s t 0 0 rfl rfl rfl rfl
  dsimp [mkSMData] at h
  rw [h, Nat.zero_add]

theorem chordFitSum_signMask_cons (r : Nat) (b : Nat → Color) (pow3 : Array Nat)
    (x y : Nat) (rest : List (Nat × Nat)) (t : Nat) :
    chordFitSum pow3 ((x, y) :: rest) (signMaskOfChords r b ((x, y) :: rest)) t =
      (let px := pow3.getD x 0
       let py := pow3.getD y 0
       if edgeDigitAt r b x == edgeDigitAt r b y then
         if t &&& 1 == 0 then px + py else 2 * px + 2 * py
       else
         if t &&& 1 == 0 then px + 2 * py else 2 * px + py) +
      chordFitSum pow3 rest (signMaskOfChords r b rest) (t >>> 1) := by
  dsimp [chordFitSum, signMaskOfChords]
  have h_bits := bit0_add_two_mul (if edgeDigitAt r b x == edgeDigitAt r b y then 1 else 0)
    (signMaskOfChords r b rest) (ite_zero_one_cases (edgeDigitAt r b x == edgeDigitAt r b y))
  rw [h_bits.1, h_bits.2]
  cases edgeDigitAt r b x == edgeDigitAt r b y <;> rfl

theorem chordFitSum_signMask_append (r : Nat) (b : Nat → Color) (pow3 : Array Nat)
    (m1 m2 : List (Nat × Nat)) (t : Nat) :
    chordFitSum pow3 (m1 ++ m2) (signMaskOfChords r b (m1 ++ m2)) t =
      chordFitSum pow3 m1 (signMaskOfChords r b m1) t +
        chordFitSum pow3 m2 (signMaskOfChords r b m2) (t >>> m1.length) := by
  induction m1 generalizing t with
  | nil => simp [chordFitSum]
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    rw [List.cons_append, chordFitSum_signMask_cons, chordFitSum_signMask_cons, ih (t >>> 1)]
    have h_sh : (t >>> 1) >>> rest.length = t >>> ((x, y) :: rest).length := by
      dsimp [List.length]
      rw [← shiftRight_add_eq, Nat.add_comm]
    rw [h_sh, Nat.add_assoc]

/-!
## Part 4: Coboundary (`edgeXor`) of `swapOfChords` and `rangeTraceSum = chordFitSum`
-/

/-- 1-coboundary of a vertex swap choice `S` at ring edge `i`:
    `true` iff exactly one endpoint of `(i, (i + 1) % r)` is in `S`. -/
def edgeXor (r : Nat) (S : Nat → Bool) (i : Nat) : Bool :=
  Bool.xor (S i) (S ((i + 1) % r))

theorem ite_not_eq_xor (c prev : Bool) : (if c then !prev else prev) = Bool.xor c prev := by
  cases c <;> cases prev <;> rfl

theorem bool_xor_four (a1 b1 a2 b2 : Bool) :
    Bool.xor (Bool.xor a1 b1) (Bool.xor a2 b2) =
      Bool.xor (Bool.xor a1 a2) (Bool.xor b1 b2) := by
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> rfl

theorem bool_and_xor_distrib (f a b : Bool) :
    Bool.xor (f && a) (f && b) = (f && Bool.xor a b) := by
  cases f <;> cases a <;> cases b <;> rfl

/-- On the cycle `ℤ / rℤ`, the 1-coboundary of the chord interval `(x, y]` (`0 ≤ x < y < r`)
    is supported on the two endpoints `{x, y}`. -/
theorem inArc_edgeXor (r x y i : Nat) (hxy : x < y) (hy : y < r) (hi : i < r) :
    Bool.xor (decide (x < i ∧ i ≤ y)) (decide (x < (i + 1) % r ∧ (i + 1) % r ≤ y)) =
      decide (i = x ∨ i = y) := by
  by_cases h_lt : i + 1 < r
  · rw [Nat.mod_eq_of_lt h_lt]
    by_cases h1 : (x < i ∧ i ≤ y) <;>
    by_cases h2 : (x < i + 1 ∧ i + 1 ≤ y) <;>
    by_cases h3 : (i = x ∨ i = y) <;>
    simp [h1, h2, h3] <;> omega
  · have h_eq : i + 1 = r := by omega
    rw [h_eq, Nat.mod_self]
    by_cases h1 : (x < i ∧ i ≤ y) <;>
    by_cases h2 : (x < 0 ∧ 0 ≤ y) <;>
    by_cases h3 : (i = x ∨ i = y) <;>
    simp [h1, h2, h3] <;> omega

theorem edgeXor_swapOfChords_cons (r : Nat) (b : Nat → Color)
    (x y : Nat) (rest : List (Nat × Nat)) (t i : Nat)
    (hxy : x < y) (hy : y < r) (hi : i < r) :
    edgeXor r (swapOfChords r b ((x, y) :: rest) t) i =
      Bool.xor
        (((t &&& 1 == 1) != (edgeDigitAt r b x == 2)) && decide (i = x ∨ i = y))
        (edgeXor r (swapOfChords r b rest (t >>> 1)) i) := by
  dsimp [edgeXor, swapOfChords]
  rw [ite_not_eq_xor, ite_not_eq_xor, bool_xor_four, bool_and_xor_distrib,
      inArc_edgeXor r x y i hxy hy hi]

theorem swapOfChords_append (r : Nat) (b : Nat → Color)
    (m1 m2 : List (Nat × Nat)) (t v : Nat) :
    swapOfChords r b (m1 ++ m2) t v =
      Bool.xor (swapOfChords r b m1 t v) (swapOfChords r b m2 (t >>> m1.length) v) := by
  induction m1 generalizing t with
  | nil => simp [swapOfChords]
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    dsimp [swapOfChords]
    rw [ite_not_eq_xor, ite_not_eq_xor, ih (t >>> 1)]
    have h_sh : (t >>> 1) >>> rest.length = t >>> (rest.length + 1) := by
      rw [← shiftRight_add_eq, Nat.add_comm]
    rw [h_sh]
    cases (((t &&& 1 == 1) != (edgeDigitAt r b x == 2)) && decide (x < v ∧ v ≤ y)) <;>
    cases swapOfChords r b rest (t >>> 1) v <;>
    cases swapOfChords r b m2 (t >>> (rest.length + 1)) v <;> rfl

theorem edgeXor_swapOfChords_append (r : Nat) (b : Nat → Color)
    (m1 m2 : List (Nat × Nat)) (t i : Nat) :
    edgeXor r (swapOfChords r b (m1 ++ m2) t) i =
      Bool.xor (edgeXor r (swapOfChords r b m1 t) i)
        (edgeXor r (swapOfChords r b m2 (t >>> m1.length)) i) := by
  dsimp [edgeXor]
  rw [swapOfChords_append, swapOfChords_append, bool_xor_four]

theorem edgeXor_swapOfChords_eq_false_of_not_endpoint (r : Nat) (b : Nat → Color)
    (m : List (Nat × Nat)) (t i : Nat) (hi : i < r)
    (h_bounds : ∀ p ∈ m, p.1 < p.2 ∧ p.2 < r)
    (h_not_ep : ∀ p ∈ m, i ≠ p.1 ∧ i ≠ p.2) :
    edgeXor r (swapOfChords r b m t) i = false := by
  induction m generalizing t with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨x, y⟩
    have h_xy := h_bounds (x, y) List.mem_cons_self
    have h_ne := h_not_ep (x, y) List.mem_cons_self
    rw [edgeXor_swapOfChords_cons r b x y rest t i h_xy.1 h_xy.2 hi]
    have h_dec : decide (i = x ∨ i = y) = false :=
      decide_eq_false (by rintro (rfl | rfl); exact h_ne.1 rfl; exact h_ne.2 rfl)
    have h_ih := ih (t >>> 1)
      (fun p hp => h_bounds p (List.mem_cons_of_mem _ hp))
      (fun p hp => h_not_ep p (List.mem_cons_of_mem _ hp))
    rw [h_dec, Bool.and_false, h_ih]
    rfl

/-!
### Edge Digit Identities under `boundaryKempeSwap`
-/

theorem edgeDigitAt_boundaryKempeSwap_of_edgeXor_false
    (c : Configuration) (r : Nat) (b : Nat → Color) (S : Nat → Bool) (i : Nat)
    (h_xor : edgeXor r S i = false) :
    edgeDigitAt r (boundaryKempeSwap c b theta1 S) i = edgeDigitAt r b i := by
  dsimp [edgeDigitAt, boundaryKempeSwap, edgeXor] at h_xor ⊢
  cases h1 : S i <;> cases h2 : S ((i + 1) % r)
  · rfl
  · rw [h1, h2] at h_xor; contradiction
  · rw [h1, h2] at h_xor; contradiction
  · cases b i <;> cases b ((i + 1) % r) <;> rfl

private theorem color_swap_digit_left (cx1 cx2 : Color) (sx1 sx2 bt : Bool)
    (h_pair_x : Nat.ble 2 cx1.toNat ≠ Nat.ble 2 cx2.toNat)
    (h_xor_x : Bool.xor sx1 sx2 =
      (bt != ((let diff := cx1.toNat ^^^ cx2.toNat; if diff > 0 then diff - 1 else 0) == 2))) :
    (let c1 := if sx1 then theta1.swap cx1 else cx1
     let c2 := if sx2 then theta1.swap cx2 else cx2
     let diff := c1.toNat ^^^ c2.toNat
     if diff > 0 then diff - 1 else 0) = (if bt then 2 else 1) := by
  revert h_pair_x h_xor_x
  cases cx1 <;> cases cx2 <;> cases sx1 <;> cases sx2 <;> cases bt <;> decide

private theorem color_swap_digit_right (cx1 cx2 cy1 cy2 : Color) (sy1 sy2 bt : Bool)
    (h_pair_x : Nat.ble 2 cx1.toNat ≠ Nat.ble 2 cx2.toNat)
    (h_pair_y : Nat.ble 2 cy1.toNat ≠ Nat.ble 2 cy2.toNat)
    (h_xor_y : Bool.xor sy1 sy2 =
      (bt != ((let diff := cx1.toNat ^^^ cx2.toNat; if diff > 0 then diff - 1 else 0) == 2))) :
    (let c1 := if sy1 then theta1.swap cy1 else cy1
     let c2 := if sy2 then theta1.swap cy2 else cy2
     let diff := c1.toNat ^^^ c2.toNat
     if diff > 0 then diff - 1 else 0) =
    (let dx := let diff := cx1.toNat ^^^ cx2.toNat; if diff > 0 then diff - 1 else 0
     let dy := let diff := cy1.toNat ^^^ cy2.toNat; if diff > 0 then diff - 1 else 0
     if dx == dy then (if bt then 2 else 1) else (if bt then 1 else 2)) := by
  revert h_pair_x h_pair_y h_xor_y
  cases cx1 <;> cases cx2 <;> cases cy1 <;> cases cy2 <;> cases sy1 <;> cases sy2 <;> cases bt <;> decide

theorem and_one_zero_or_one (t : Nat) : t &&& 1 = 0 ∨ t &&& 1 = 1 := by
  rw [Nat.and_one_is_mod]
  omega

theorem chord_endpoints_trace_eq (c : Configuration) (r : Nat) (b : Nat → Color)
    (pow3 : Array Nat) (S : Nat → Bool) (x y t : Nat)
    (h_pair_x : theta1Pair b x ≠ theta1Pair b ((x + 1) % r))
    (h_pair_y : theta1Pair b y ≠ theta1Pair b ((y + 1) % r))
    (h_xor_x : edgeXor r S x = ((t &&& 1 == 1) != (edgeDigitAt r b x == 2)))
    (h_xor_y : edgeXor r S y = ((t &&& 1 == 1) != (edgeDigitAt r b x == 2))) :
    edgeDigitAt r (boundaryKempeSwap c b theta1 S) x * pow3.getD x 0 +
      edgeDigitAt r (boundaryKempeSwap c b theta1 S) y * pow3.getD y 0 =
    (let px := pow3.getD x 0
     let py := pow3.getD y 0
     if edgeDigitAt r b x == edgeDigitAt r b y then
       if t &&& 1 == 0 then px + py else 2 * px + 2 * py
     else
       if t &&& 1 == 0 then px + 2 * py else 2 * px + py) := by
  have hx := color_swap_digit_left (b x) (b ((x + 1) % r)) (S x) (S ((x + 1) % r)) (t &&& 1 == 1)
    h_pair_x h_xor_x
  have hy := color_swap_digit_right (b x) (b ((x + 1) % r)) (b y) (b ((y + 1) % r))
    (S y) (S ((y + 1) % r)) (t &&& 1 == 1) h_pair_x h_pair_y h_xor_y
  change (let c1 := if S x then theta1.swap (b x) else b x
          let c2 := if S ((x + 1) % r) then theta1.swap (b ((x + 1) % r)) else b ((x + 1) % r)
          let diff := c1.toNat ^^^ c2.toNat
          if diff > 0 then diff - 1 else 0) * pow3.getD x 0 +
         (let c1 := if S y then theta1.swap (b y) else b y
          let c2 := if S ((y + 1) % r) then theta1.swap (b ((y + 1) % r)) else b ((y + 1) % r)
          let diff := c1.toNat ^^^ c2.toNat
          if diff > 0 then diff - 1 else 0) * pow3.getD y 0 = _
  rw [hx, hy]
  change (if (t &&& 1 == 1) = true then 2 else 1) * pow3.getD x 0 +
    (if (edgeDigitAt r b x == edgeDigitAt r b y) = true then
      if (t &&& 1 == 1) = true then 2 else 1
     else
      if (t &&& 1 == 1) = true then 1 else 2) * pow3.getD y 0 = _
  rcases and_one_zero_or_one t with ht | ht <;>
  cases h_eq : (edgeDigitAt r b x == edgeDigitAt r b y) <;>
  simp [ht] <;> omega

/-!
### `rangeTraceSum` and the Inductive Trace Equality Theorem
-/

/-- Sum of `edgeDigitAt r b i * pow3.getD i 0` over `i ∈ [lo, hi)`. -/
def rangeTraceSum (r : Nat) (b : Nat → Color) (pow3 : Array Nat) (lo hi : Nat) : Nat :=
  if h : lo < hi then
    edgeDigitAt r b lo * pow3.getD lo 0 + rangeTraceSum r b pow3 (lo + 1) hi
  else
    0
termination_by hi - lo

theorem rangeTraceSum_eq_zero_of_ge (r : Nat) (b : Nat → Color) (pow3 : Array Nat)
    (lo hi : Nat) (h : hi ≤ lo) :
    rangeTraceSum r b pow3 lo hi = 0 := by
  rw [rangeTraceSum, dif_neg (by omega)]

theorem rangeTraceSum_step (r : Nat) (b : Nat → Color) (pow3 : Array Nat)
    (lo hi : Nat) (h : lo < hi) :
    rangeTraceSum r b pow3 lo hi =
      edgeDigitAt r b lo * pow3.getD lo 0 + rangeTraceSum r b pow3 (lo + 1) hi := by
  rw [rangeTraceSum, dif_pos h]

theorem rangeTraceSum_split (r : Nat) (b : Nat → Color) (pow3 : Array Nat)
    (lo mid hi : Nat) (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    rangeTraceSum r b pow3 lo hi =
      rangeTraceSum r b pow3 lo mid + rangeTraceSum r b pow3 mid hi := by
  have h_gen : ∀ len lo, mid - lo ≤ len → lo ≤ mid → mid ≤ hi →
      rangeTraceSum r b pow3 lo hi =
        rangeTraceSum r b pow3 lo mid + rangeTraceSum r b pow3 mid hi := by
    intro len
    induction len with
    | zero =>
      intro lo h_len h_lo _
      have h_eq : lo = mid := by omega
      subst h_eq
      rw [rangeTraceSum_eq_zero_of_ge r b pow3 lo lo (by omega), Nat.zero_add]
    | succ len ih =>
      intro lo h_len h_lo h_mid
      by_cases h_lt : lo < mid
      · rw [rangeTraceSum_step r b pow3 lo hi (by omega),
            rangeTraceSum_step r b pow3 lo mid h_lt,
            ih (lo + 1) (by omega) (by omega) h_mid, Nat.add_assoc]
      · have h_eq : lo = mid := by omega
        subst h_eq
        rw [rangeTraceSum_eq_zero_of_ge r b pow3 lo lo (by omega), Nat.zero_add]
  exact h_gen (mid - lo) lo (Nat.le_refl _) h1 h2

theorem boundaryTraceAux_eq_rangeTraceSum (r : Nat) (b : Nat → Color) (pow3 : Array Nat)
    (rem i acc : Nat) :
    boundaryTraceAux r b pow3 rem i acc = acc + rangeTraceSum r b pow3 i (i + rem) := by
  induction rem generalizing i acc with
  | zero =>
    dsimp [boundaryTraceAux]
    rw [rangeTraceSum_eq_zero_of_ge r b pow3 i i (by omega), Nat.add_zero]
  | succ rem ih =>
    dsimp [boundaryTraceAux]
    change boundaryTraceAux r b pow3 rem (i + 1) (acc + edgeDigitAt r b i * pow3.getD i 0) =
      acc + rangeTraceSum r b pow3 i (i + (rem + 1))
    rw [ih (i + 1) _, rangeTraceSum_step r b pow3 i (i + (rem + 1)) (by omega)]
    have h_add : i + 1 + rem = i + (rem + 1) := by omega
    rw [h_add, Nat.add_assoc]

theorem boundaryTrace_eq_rangeTraceSum (c : Configuration) (b : BoundaryColoring c) (pow3 : Array Nat) :
    boundaryTrace c b pow3 = rangeTraceSum c.ringSize b pow3 0 c.ringSize := by
  unfold boundaryTrace
  rw [boundaryTraceAux_eq_rangeTraceSum c.ringSize b pow3 c.ringSize 0 0, Nat.zero_add, Nat.zero_add]

/-- Main inductive trace theorem: on any sub-interval `[lo, hi)` (`hi ≤ c.ringSize`),
    if `m` is an extracted matching on `[lo, hi)` and `edgeXor c.ringSize S` agrees with
    `edgeXor c.ringSize (swapOfChords c.ringSize b m t)` on `[lo, hi)`, then
    `rangeTraceSum` of `boundaryKempeSwap c b theta1 S` over `[lo, hi)` equals `chordFitSum`. -/
theorem rangeTraceSum_eq_chordFitSum_of_edgeXor
    (c : Configuration) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (E : Nat → Nat → Prop) (pow3 : Array Nat)
    (lo hi : Nat) (m : List (Nat × Nat))
    (h_ext : IsExtractedMatching c.ringSize (theta1Pair b) E lo hi m)
    (S : Nat → Bool) (t : Nat)
    (hS : ∀ i, lo ≤ i → i < hi →
      edgeXor c.ringSize S i = edgeXor c.ringSize (swapOfChords c.ringSize b m t) i) :
    rangeTraceSum c.ringSize (boundaryKempeSwap c b theta1 S) pow3 lo hi =
      chordFitSum pow3 m (signMaskOfChords c.ringSize b m) t := by
  induction h_ext generalizing t with
  | nil lo _ =>
    rw [rangeTraceSum_eq_zero_of_ge _ _ _ lo lo (by omega)]
    rfl
  | skip lo hi m' h_lt h_hi h_same h_rest ih =>
    have h_lo_r : lo < c.ringSize := Nat.lt_of_lt_of_le h_lt h_hi
    rw [Nat.mod_eq_of_lt h_lo_r] at h_same
    have h_d0 : edgeDigitAt c.ringSize b lo = 0 :=
      (edgeDigitAt_eq_zero_iff_same_pair c b h_ring hb lo h_lo_r).mpr h_same
    have h_xor_lo : edgeXor c.ringSize S lo = false := by
      rw [hS lo (Nat.le_refl _) h_lt]
      refine edgeXor_swapOfChords_eq_false_of_not_endpoint c.ringSize b m' t lo h_lo_r ?_ ?_
      · intro p hp
        have h_in := isExtractedMatching_chords_in_range h_rest p hp
        omega
      · intro p hp
        have h_in := isExtractedMatching_chords_in_range h_rest p hp
        omega
    have h_d0' : edgeDigitAt c.ringSize (boundaryKempeSwap c b theta1 S) lo = 0 := by
      rw [edgeDigitAt_boundaryKempeSwap_of_edgeXor_false c c.ringSize b S lo h_xor_lo, h_d0]
    rw [rangeTraceSum_step _ _ _ lo hi h_lt, h_d0', Nat.zero_mul, Nat.zero_add]
    exact ih t (fun i h1 h2 => hS i (by omega) h2)
  | pair lo k₀ hi m1 m2 hk_ge hk_lt h_hi h_diff_lo h_diff_k0 h_closed h_ext1 h_ext2 ih1 ih2 =>
    have h_k_r : k₀ < c.ringSize := Nat.lt_of_lt_of_le hk_lt h_hi
    have h_lo_r : lo < c.ringSize := by omega
    have h_lt1 : lo < k₀ := by omega
    rw [Nat.mod_eq_of_lt h_lo_r] at h_diff_lo
    rw [Nat.mod_eq_of_lt h_k_r] at h_diff_k0
    have h_bounds_m12 : ∀ p ∈ m1 ++ m2, p.1 < p.2 ∧ p.2 < c.ringSize := by
      intro p hp
      rcases List.mem_append.mp hp with hp1 | hp2
      · have h_in := isExtractedMatching_chords_in_range h_ext1 p hp1; omega
      · have h_in := isExtractedMatching_chords_in_range h_ext2 p hp2; omega
    -- 1. Evaluate edgeXor at lo and k₀
    have h_xor_lo : edgeXor c.ringSize S lo =
        ((t &&& 1 == 1) != (edgeDigitAt c.ringSize b lo == 2)) := by
      rw [hS lo (Nat.le_refl _) (by omega),
          edgeXor_swapOfChords_cons c.ringSize b lo k₀ (m1 ++ m2) t lo h_lt1 h_k_r h_lo_r]
      have h_rest_lo : edgeXor c.ringSize (swapOfChords c.ringSize b (m1 ++ m2) (t >>> 1)) lo = false := by
        refine edgeXor_swapOfChords_eq_false_of_not_endpoint c.ringSize b (m1 ++ m2) (t >>> 1) lo h_lo_r h_bounds_m12 ?_
        intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · have h_in := isExtractedMatching_chords_in_range h_ext1 p hp1; omega
        · have h_in := isExtractedMatching_chords_in_range h_ext2 p hp2; omega
      rw [decide_eq_true (Or.inl rfl), Bool.and_true, h_rest_lo, Bool.xor_false]
    have h_xor_k : edgeXor c.ringSize S k₀ =
        ((t &&& 1 == 1) != (edgeDigitAt c.ringSize b lo == 2)) := by
      rw [hS k₀ (by omega) hk_lt,
          edgeXor_swapOfChords_cons c.ringSize b lo k₀ (m1 ++ m2) t k₀ h_lt1 h_k_r h_k_r]
      have h_rest_k : edgeXor c.ringSize (swapOfChords c.ringSize b (m1 ++ m2) (t >>> 1)) k₀ = false := by
        refine edgeXor_swapOfChords_eq_false_of_not_endpoint c.ringSize b (m1 ++ m2) (t >>> 1) k₀ h_k_r h_bounds_m12 ?_
        intro p hp
        rcases List.mem_append.mp hp with hp1 | hp2
        · have h_in := isExtractedMatching_chords_in_range h_ext1 p hp1; omega
        · have h_in := isExtractedMatching_chords_in_range h_ext2 p hp2; omega
      rw [decide_eq_true (Or.inr rfl), Bool.and_true, h_rest_k, Bool.xor_false]
    -- 2. Evaluate sub-interval [lo + 1, k₀) via ih1
    have h_sub1 : rangeTraceSum c.ringSize (boundaryKempeSwap c b theta1 S) pow3 (lo + 1) k₀ =
        chordFitSum pow3 m1 (signMaskOfChords c.ringSize b m1) (t >>> 1) := by
      refine ih1 (t >>> 1) (fun i h1 h2 => ?_)
      have hi_r : i < c.ringSize := by omega
      rw [hS i (by omega) (by omega),
          edgeXor_swapOfChords_cons c.ringSize b lo k₀ (m1 ++ m2) t i h_lt1 h_k_r hi_r,
          edgeXor_swapOfChords_append]
      have h_dec : decide (i = lo ∨ i = k₀) = false := decide_eq_false (by omega)
      have h_m2_i : edgeXor c.ringSize (swapOfChords c.ringSize b m2 ((t >>> 1) >>> m1.length)) i = false := by
        refine edgeXor_swapOfChords_eq_false_of_not_endpoint c.ringSize b m2 _ i hi_r ?_ ?_
        · intro p hp; have h_in := isExtractedMatching_chords_in_range h_ext2 p hp; omega
        · intro p hp; have h_in := isExtractedMatching_chords_in_range h_ext2 p hp; omega
      rw [h_dec, Bool.and_false, h_m2_i, Bool.xor_false, Bool.false_xor]
    -- 3. Evaluate sub-interval [k₀ + 1, hi) via ih2
    have h_sub2 : rangeTraceSum c.ringSize (boundaryKempeSwap c b theta1 S) pow3 (k₀ + 1) hi =
        chordFitSum pow3 m2 (signMaskOfChords c.ringSize b m2) ((t >>> 1) >>> m1.length) := by
      refine ih2 ((t >>> 1) >>> m1.length) (fun i h1 h2 => ?_)
      have hi_r : i < c.ringSize := by omega
      rw [hS i (by omega) h2,
          edgeXor_swapOfChords_cons c.ringSize b lo k₀ (m1 ++ m2) t i h_lt1 h_k_r hi_r,
          edgeXor_swapOfChords_append]
      have h_dec : decide (i = lo ∨ i = k₀) = false := decide_eq_false (by omega)
      have h_m1_i : edgeXor c.ringSize (swapOfChords c.ringSize b m1 (t >>> 1)) i = false := by
        refine edgeXor_swapOfChords_eq_false_of_not_endpoint c.ringSize b m1 _ i hi_r ?_ ?_
        · intro p hp; have h_in := isExtractedMatching_chords_in_range h_ext1 p hp; omega
        · intro p hp; have h_in := isExtractedMatching_chords_in_range h_ext1 p hp; omega
      rw [h_dec, Bool.and_false, h_m1_i, Bool.false_xor, Bool.false_xor]
    -- 4. Combine the 4 pieces of [lo, hi)
    rw [rangeTraceSum_step _ _ _ lo hi (by omega),
        rangeTraceSum_split _ _ _ (lo + 1) k₀ hi hk_ge (Nat.le_of_lt hk_lt),
        rangeTraceSum_step _ _ _ k₀ hi hk_lt,
        h_sub1, h_sub2,
        chordFitSum_signMask_cons, chordFitSum_signMask_append]
    have h_ep := chord_endpoints_trace_eq c c.ringSize b pow3 S lo k₀ t
      h_diff_lo h_diff_k0 h_xor_lo h_xor_k
    omega

/-- Top-level assembly for `theta1`: for any valid boundary coloring `b` and joint planar
    partition `(equiv_ab, equiv_cd)` on a ring cycle `IsRingCycle c`, there exists
    `sm ∈ (buildSMDataTotal c.ringSize pow3).toList` that faithfully represents the partition. -/
theorem representsPartition_theta1_of_ringCycle
    (c : Configuration) (pow3 : Array Nat) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (equiv_ab equiv_cd : Nat → Nat → Prop)
    (hb : IsValidBoundaryColoring c b)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd) :
    ∃ sm ∈ (buildSMDataTotal c.ringSize pow3).toList,
      RepresentsPartition c b theta1 equiv_ab equiv_cd sm pow3 := by
  rcases exists_ncMatching_of_partition c b equiv_ab equiv_cd h_ring hPart with ⟨m, h_mem_m, h_ext⟩
  let s := signMaskOfChords c.ringSize b m
  let sm := mkSMData pow3 m s
  have h_s_lt : s < 1 <<< m.length := signMaskOfChords_lt c.ringSize b m
  have h_parity : (negSignCount s m.length % 2 == c.ringSize % 2) = true :=
    negSignCount_signMask_ring_parity c b (partEquiv equiv_ab equiv_cd) h_ring hb m h_ext
  have h_sm_mem : sm ∈ (buildSMDataTotal c.ringSize pow3).toList :=
    mem_buildSMDataTotal c.ringSize pow3 m h_mem_m s h_s_lt h_parity
  refine ⟨sm, h_sm_mem, swapOfChords c.ringSize b m, ?_, ?_, ?_⟩
  · intro t _
    exact swapOfChords_valid c b equiv_ab equiv_cd m
      (isExtractedMatching_chords_in_range h_ext)
      (isExtractedMatching_intervals_closed h_ext) t
  · refine ⟨baseParamOfChords c.ringSize b m, ?_, swapOfChords_baseParam c.ringSize b m⟩
    dsimp [sm, mkSMData]
    exact baseParamOfChords_lt c.ringSize b m
  · intro t _
    rw [boundaryTraceTheta_theta1, boundaryTrace_eq_rangeTraceSum,
        rangeTraceSum_eq_chordFitSum_of_edgeXor c h_ring b hb
          (partEquiv equiv_ab equiv_cd) pow3 0 c.ringSize m h_ext
          (swapOfChords c.ringSize b m t) t (fun _ _ _ => rfl),
        ← smFitIndex_mkSMData_eq]

/-- **Main Theorem (Stage A / RSST Lemma (a)):**
    For every configuration `c` with a ring cycle (`IsRingCycle c`) and every `pow3` table,
    `buildSMDataTotal c.ringSize pow3` satisfies `FullRepresentationHypothesis c (buildSMDataTotal c.ringSize pow3) pow3`. -/
theorem fullRepresentation_of_ringCycle
    (c : Configuration) (pow3 : Array Nat) (h_ring : IsRingCycle c) :
    FullRepresentationHypothesis c (buildSMDataTotal c.ringSize pow3) pow3 :=
  full_representation_of_theta1 c (buildSMDataTotal c.ringSize pow3) pow3
    (representsPartition_theta1_of_ringCycle c pow3 h_ring)

/-- Specialization of `fullRepresentation_of_ringCycle` to `sharedPow3`. -/
theorem fullRepresentation_sharedPow3_of_ringCycle
    (c : Configuration) (h_ring : IsRingCycle c) :
    FullRepresentationHypothesis c (buildSMDataTotal c.ringSize sharedPow3) sharedPow3 :=
  fullRepresentation_of_ringCycle c sharedPow3 h_ring

end CheckerSoundness
end Math
