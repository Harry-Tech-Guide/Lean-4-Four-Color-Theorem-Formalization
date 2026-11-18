module

public import FourColorTheorem.Math.Soundness.Representation
public import FourColorTheorem.Math.CheckerSoundness.InitialLive

@[expose] public section

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-!
# Stage A (Checkpoint A1): Non-Crossing Matching Extraction from Joint Planar Ring Partitions

This module proves the first half of RSST Lemma (a) (`FullRepresentationHypothesis`):
For any configuration `c` with `IsRingCycle c`, any valid boundary coloring `b`, and any
joint planar ring partition `(equiv_ab, equiv_cd)` under `theta1`, there exists an enumerated
non-crossing matching `m ∈ (ncMatchings 0 c.ringSize).toList` such that:
1. All chords `(x, y)` of `m` satisfy `0 ≤ x < y < c.ringSize` and are pairwise disjoint.
2. The endpoints of `m` are **exactly** the transition edges
   `{i < c.ringSize | edgeDigit c b i ≠ 0}` (`theta1Pair b i ≠ theta1Pair b ((i + 1) % c.ringSize)`).
3. For every chord `(x, y) ∈ m.toList`, the half-open vertex interval
   `I(x, y) = {i < c.ringSize | x < i ∧ i ≤ y}` is closed under both `equiv_ab` and `equiv_cd`.
-/

/-!
### Part 1: `theta1Pair` and Unified Planar Equivalence Relation `partEquiv`
-/

/-- Color-pair indicator for `theta1`: `false` on `{c0, c1}`, `true` on `{c2, c3}`. -/
def theta1Pair (b : Nat → Color) (i : Nat) : Bool :=
  Nat.ble 2 (b i).toNat

theorem theta1Pair_false_iff (col : Color) :
    Nat.ble 2 col.toNat = false ↔ (col = theta1.a ∨ col = theta1.b) := by
  cases col <;> decide

theorem theta1Pair_true_iff (col : Color) :
    Nat.ble 2 col.toNat = true ↔ (col = theta1.c ∨ col = theta1.d) := by
  cases col <;> decide

theorem color_diff_one_iff_same_pair (c1 c2 : Color) (hne : c1 ≠ c2) :
    (c1.toNat ^^^ c2.toNat) = 1 ↔ Nat.ble 2 c1.toNat = Nat.ble 2 c2.toNat := by
  cases c1 <;> cases c2 <;> revert hne <;> decide

theorem color_diff_gt_one_iff_diff_pair (c1 c2 : Color) (hne : c1 ≠ c2) :
    ((c1.toNat ^^^ c2.toNat) = 2 ∨ (c1.toNat ^^^ c2.toNat) = 3) ↔
      Nat.ble 2 c1.toNat ≠ Nat.ble 2 c2.toNat := by
  cases c1 <;> cases c2 <;> revert hne <;> decide

/-- On a valid boundary coloring of a ring cycle, `edgeDigitAt c.ringSize b i = 0` iff edge `i` connects
    two vertices in the same `theta1` color pair. -/
theorem edgeDigitAt_eq_zero_iff_same_pair (c : Configuration) (b : BoundaryColoring c)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (i : Nat) (hi : i < c.ringSize) :
    edgeDigitAt c.ringSize b i = 0 ↔ theta1Pair b i = theta1Pair b ((i + 1) % c.ringSize) := by
  have hr_pos : c.ringSize > 0 := by have := h_ring.1; omega
  have h_nxt_lt : (i + 1) % c.ringSize < c.ringSize := Nat.mod_lt _ hr_pos
  have hadj : c.adj i ((i + 1) % c.ringSize) = true := h_ring.2 i hi
  have hne : b i ≠ b ((i + 1) % c.ringSize) := hb i ((i + 1) % c.ringSize) hi h_nxt_lt hadj
  dsimp [edgeDigitAt, theta1Pair]
  generalize b i = c1, b ((i + 1) % c.ringSize) = c2 at hne ⊢
  cases c1 <;> cases c2 <;> revert hne <;> decide

/-- Unified equivalence relation of a joint planar ring partition. -/
def partEquiv (equiv_ab equiv_cd : Nat → Nat → Prop) (i j : Nat) : Prop :=
  equiv_ab i j ∨ equiv_cd i j

/-- Abstract axiomatization of a planar ring equivalence relation on `{0, ..., r - 1}`
    compatible with a binary color-pair indicator `pair : Nat → Bool`. -/
structure PlanarRingEquiv (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop) : Prop where
  r_pos : 0 < r
  refl : ∀ i < r, E i i
  symm : ∀ i < r, ∀ j < r, E i j → E j i
  trans : ∀ i < r, ∀ j < r, ∀ l < r, E i j → E j l → E i l
  same_pair : ∀ i < r, ∀ j < r, E i j → pair i = pair j
  step_same : ∀ i < r, pair i = pair ((i + 1) % r) → E i ((i + 1) % r)
  noncross : ∀ i j l m, i < j → j < l → l < m → m < r → E i l → E j m → E i j

/-- Every `IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd` on a ring cycle `c`
    induces a `PlanarRingEquiv c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd)`. -/
theorem planarRingEquiv_of_partition (c : Configuration) (b : BoundaryColoring c)
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (h_ring : IsRingCycle c)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd) :
    PlanarRingEquiv c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd) where
  r_pos := by have := h_ring.1; omega
  refl := fun i hi => by
    cases h_pair : theta1Pair b i
    · left
      exact hPart.ab_refl i hi ((theta1Pair_false_iff (b i)).mp h_pair)
    · right
      exact hPart.cd_refl i hi ((theta1Pair_true_iff (b i)).mp h_pair)
  symm := fun i hi j hj h => by
    rcases h with hab | hcd
    · exact Or.inl (hPart.ab_symm i hi j hj hab)
    · exact Or.inr (hPart.cd_symm i hi j hj hcd)
  trans := fun i hi j hj l hl hij hjl => by
    rcases hij with hab1 | hcd1 <;> rcases hjl with hab2 | hcd2
    · exact Or.inl (hPart.ab_trans i hi j hj l hl hab1 hab2)
    · have h1 : theta1Pair b j = false :=
        (theta1Pair_false_iff (b j)).mpr (hPart.ab_color j hj i hi (hPart.ab_symm i hi j hj hab1))
      have h2 : theta1Pair b j = true :=
        (theta1Pair_true_iff (b j)).mpr (hPart.cd_color j hj l hl hcd2)
      rw [h1] at h2; contradiction
    · have h1 : theta1Pair b j = true :=
        (theta1Pair_true_iff (b j)).mpr (hPart.cd_color j hj i hi (hPart.cd_symm i hi j hj hcd1))
      have h2 : theta1Pair b j = false :=
        (theta1Pair_false_iff (b j)).mpr (hPart.ab_color j hj l hl hab2)
      rw [h1] at h2; contradiction
    · exact Or.inr (hPart.cd_trans i hi j hj l hl hcd1 hcd2)
  same_pair := fun i hi j hj h => by
    rcases h with hab | hcd
    · have hi_p : theta1Pair b i = false :=
        (theta1Pair_false_iff (b i)).mpr (hPart.ab_color i hi j hj hab)
      have hj_p : theta1Pair b j = false :=
        (theta1Pair_false_iff (b j)).mpr (hPart.ab_color j hj i hi (hPart.ab_symm i hi j hj hab))
      rw [hi_p, hj_p]
    · have hi_p : theta1Pair b i = true :=
        (theta1Pair_true_iff (b i)).mpr (hPart.cd_color i hi j hj hcd)
      have hj_p : theta1Pair b j = true :=
        (theta1Pair_true_iff (b j)).mpr (hPart.cd_color j hj i hi (hPart.cd_symm i hi j hj hcd))
      rw [hi_p, hj_p]
  step_same := fun i hi h_eq => by
    have hr_pos : c.ringSize > 0 := by have := h_ring.1; omega
    have h_nxt : (i + 1) % c.ringSize < c.ringSize := Nat.mod_lt _ hr_pos
    have hadj : c.adj i ((i + 1) % c.ringSize) = true := h_ring.2 i hi
    cases hp : theta1Pair b i
    · have hp_nxt : theta1Pair b ((i + 1) % c.ringSize) = false := h_eq.symm.trans hp
      left
      exact hPart.ab_adj i hi ((i + 1) % c.ringSize) h_nxt hadj
        ((theta1Pair_false_iff (b i)).mp hp)
        ((theta1Pair_false_iff (b ((i + 1) % c.ringSize))).mp hp_nxt)
    · have hp_nxt : theta1Pair b ((i + 1) % c.ringSize) = true := h_eq.symm.trans hp
      right
      exact hPart.cd_adj i hi ((i + 1) % c.ringSize) h_nxt hadj
        ((theta1Pair_true_iff (b i)).mp hp)
        ((theta1Pair_true_iff (b ((i + 1) % c.ringSize))).mp hp_nxt)
  noncross := fun i j l m hij hjl hlm hmr h1 h2 => by
    rcases h1 with hab1 | hcd1 <;> rcases h2 with hab2 | hcd2
    · exact Or.inl (hPart.ab_noncross i j l m hij hjl hlm hmr hab1 hab2)
    · exact False.elim (hPart.cross_ab_cd i j l m hij hjl hlm hmr hab1 hcd2)
    · exact False.elim (hPart.cross_cd_ab i j l m hij hjl hlm hmr hcd1 hab2)
    · exact Or.inr (hPart.cd_noncross i j l m hij hjl hlm hmr hcd1 hcd2)

/-!
### Part 2: Sub-Interval Invariant & $E$-Closed Partner Interval $I(lo, k_0)$
-/

/-- Invariant on a sub-interval `[lo, hi) ⊆ [0, r)` during non-crossing matching extraction. -/
structure SubIntervalInv (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop) (lo hi : Nat) : Prop where
  le_hi : lo ≤ hi
  hi_le_r : hi ≤ r
  pair_eq : pair (lo % r) = pair (hi % r)
  closed_other_pair : ∀ u, lo < u → u < hi → ∀ w < r,
    E u w → ¬ (lo < w ∧ w < hi) → pair u = pair (lo % r)

/-- Root invariant on `[0, r)`. -/
theorem subIntervalInv_root (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) :
    SubIntervalInv r pair E 0 r where
  le_hi := Nat.zero_le r
  hi_le_r := Nat.le_refl r
  pair_eq := by rw [Nat.zero_mod, Nat.mod_self]
  closed_other_pair := by
    intro u hu_gt hu_lt w hw_lt h_eu h_out
    have hw0 : w = 0 := by omega
    subst hw0
    rw [Nat.zero_mod]
    exact hE.same_pair u hu_lt 0 hE.r_pos h_eu

/-- Step invariant when `pair (lo % r) = pair ((lo + 1) % r)` (edge `lo` is not a transition edge). -/
theorem subIntervalInv_skip (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) (lo hi : Nat) (h_lt : lo < hi)
    (h_inv : SubIntervalInv r pair E lo hi)
    (h_same : pair (lo % r) = pair ((lo + 1) % r)) :
    SubIntervalInv r pair E (lo + 1) hi where
  le_hi := h_lt
  hi_le_r := h_inv.hi_le_r
  pair_eq := h_same.symm.trans h_inv.pair_eq
  closed_other_pair := by
    intro u hu_gt hu_lt w hw_lt h_eu h_out
    have hu_r : u < r := Nat.lt_of_lt_of_le hu_lt h_inv.hi_le_r
    by_cases hw_lo1 : w = lo + 1
    · subst hw_lo1
      have hlo1_r : lo + 1 < r := Nat.lt_trans hu_gt hu_r
      rw [Nat.mod_eq_of_lt hlo1_r]
      exact hE.same_pair u hu_r (lo + 1) hlo1_r h_eu
    · have h_out_lo : ¬ (lo < w ∧ w < hi) := by
        intro h_in
        exact h_out ⟨ by omega, h_in.2 ⟩
      rw [← h_same]
      exact h_inv.closed_other_pair u (by omega) hu_lt w hw_lt h_eu h_out_lo

/-- Finite maximum existence in `[lo1, hi)` for any predicate `P` holding at `lo1`. -/
theorem exists_max_in_range (P : Nat → Prop) (lo1 hi : Nat)
    (h_lt : lo1 < hi) (h_lo1 : P lo1) :
    ∃ k₀, lo1 ≤ k₀ ∧ k₀ < hi ∧ P k₀ ∧ ∀ v, k₀ < v → v < hi → ¬ P v := by
  open Classical in
  induction hi with
  | zero => omega
  | succ hi ih =>
    by_cases h_hi : P hi ∧ lo1 ≤ hi
    · refine ⟨hi, h_hi.2, Nat.lt_succ_self hi, h_hi.1, ?_⟩
      intro v hv_gt hv_lt
      omega
    · have h_lt' : lo1 < hi := by
        by_cases h_eq : lo1 = hi
        · subst h_eq
          exact False.elim (h_hi ⟨h_lo1, Nat.le_refl lo1⟩)
        · omega
      have h_not_hi : ¬ P hi := fun hp => h_hi ⟨hp, Nat.le_of_lt h_lt'⟩
      rcases ih h_lt' with ⟨k₀, hk_ge, hk_lt, hPk, hk_max⟩
      refine ⟨k₀, hk_ge, Nat.lt_succ_of_lt hk_lt, hPk, ?_⟩
      intro v hv_gt hv_lt
      by_cases hv_eq : v = hi
      · subst hv_eq; exact h_not_hi
      · exact hk_max v hv_gt (by omega)

/-- Under `SubIntervalInv r pair E lo hi`, if `lo < hi` and `pair (lo % r) ≠ pair ((lo + 1) % r)`,
    then `lo + 1 < hi`. -/
theorem lo_add_one_lt_hi_of_diff_pair (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (lo hi : Nat) (h_lt : lo < hi) (h_inv : SubIntervalInv r pair E lo hi)
    (h_diff : pair (lo % r) ≠ pair ((lo + 1) % r)) :
    lo + 1 < hi := by
  by_cases h_eq : lo + 1 = hi
  · exfalso
    rw [h_eq] at h_diff
    exact h_diff h_inv.pair_eq
  · omega

/-- If `k₀` is the maximum element in `[lo + 1, hi)` with `E (lo + 1) k₀` under `SubIntervalInv`,
    then no `w < r` outside `[lo + 1, k₀]` satisfies `E (lo + 1) w`. -/
theorem not_equiv_lo1_outside_interval (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) (lo hi k₀ : Nat)
    (h_inv : SubIntervalInv r pair E lo hi)
    (h_diff : pair (lo % r) ≠ pair ((lo + 1) % r))
    (hk_ge : lo + 1 ≤ k₀) (hk_lt : k₀ < hi)
    (hk_max : ∀ v, k₀ < v → v < hi → ¬ E (lo + 1) v)
    (w : Nat) (hw_lt : w < r) (h_out : ¬ (lo < w ∧ w ≤ k₀)) :
    ¬ E (lo + 1) w := by
  intro h_ew
  have hlo1_lt_hi : lo + 1 < hi := Nat.lt_of_le_of_lt hk_ge hk_lt
  have hlo1_lt_r : lo + 1 < r := Nat.lt_of_lt_of_le hlo1_lt_hi h_inv.hi_le_r
  by_cases h_in_hi : lo < w ∧ w < hi
  · have hk_lt_w : k₀ < w := by omega
    exact hk_max w hk_lt_w h_in_hi.2 h_ew
  · have h_pair_eq := h_inv.closed_other_pair (lo + 1) (Nat.lt_succ_self lo) hlo1_lt_hi w hw_lt h_ew h_in_hi
    rw [← Nat.mod_eq_of_lt hlo1_lt_r] at h_pair_eq
    exact h_diff h_pair_eq.symm

/-- **Fundamental Interval Closure Lemma:**
    If `k₀` is the maximum element in `[lo + 1, hi)` with `E (lo + 1) k₀` under `SubIntervalInv`,
    then the half-open interval `I(lo, k₀) = {u < r | lo < u ∧ u ≤ k₀}` is closed under `E`. -/
theorem partner_interval_closed (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) (lo hi k₀ : Nat)
    (h_inv : SubIntervalInv r pair E lo hi)
    (h_diff : pair (lo % r) ≠ pair ((lo + 1) % r))
    (hk_ge : lo + 1 ≤ k₀) (hk_lt : k₀ < hi)
    (h_ek0 : E (lo + 1) k₀)
    (hk_max : ∀ v, k₀ < v → v < hi → ¬ E (lo + 1) v)
    (u w : Nat) (hu_lt : u < r) (hw_lt : w < r)
    (hu_in : lo < u ∧ u ≤ k₀) (h_euw : E u w) :
    lo < w ∧ w ≤ k₀ := by
  apply Classical.byContradiction
  intro h_out
  have h_not_lo1_w : ¬ E (lo + 1) w :=
    not_equiv_lo1_outside_interval r pair E hE lo hi k₀ h_inv h_diff hk_ge hk_lt hk_max w hw_lt h_out
  have hlo1_lt_r : lo + 1 < r := Nat.lt_of_le_of_lt hk_ge (Nat.lt_of_lt_of_le hk_lt h_inv.hi_le_r)
  have hk0_lt_r : k₀ < r := Nat.lt_of_lt_of_le hk_lt h_inv.hi_le_r
  by_cases hu_lo1 : u = lo + 1
  · subst hu_lo1
    exact h_not_lo1_w h_euw
  · by_cases hu_k0 : u = k₀
    · rw [hu_k0] at h_euw
      exact h_not_lo1_w (hE.trans (lo + 1) hlo1_lt_r k₀ hk0_lt_r w hw_lt h_ek0 h_euw)
    · have hu_gt : lo + 1 < u := by omega
      have hu_lt_k0 : u < k₀ := by omega
      by_cases hw_le_lo : w ≤ lo
      · have hw_lt_lo1 : w < lo + 1 := by omega
        have h_ewu : E w u := hE.symm u hu_lt w hw_lt h_euw
        have h_ew_lo1 : E w (lo + 1) :=
          hE.noncross w (lo + 1) u k₀ hw_lt_lo1 hu_gt hu_lt_k0 hk0_lt_r h_ewu h_ek0
        exact h_not_lo1_w (hE.symm w hw_lt (lo + 1) hlo1_lt_r h_ew_lo1)
      · have hk0_lt_w : k₀ < w := by omega
        have h_elo1_u : E (lo + 1) u :=
          hE.noncross (lo + 1) u k₀ w hu_gt hu_lt_k0 hk0_lt_w hw_lt h_ek0 h_euw
        exact h_not_lo1_w (hE.trans (lo + 1) hlo1_lt_r u hu_lt w hw_lt h_elo1_u h_euw)

/-- Bidirectional $E$-closure of `I(lo, k₀)`: for all `u, w < r`, `E u w → (lo < u ∧ u ≤ k₀ ↔ lo < w ∧ w ≤ k₀)`. -/
theorem partner_interval_closed_iff (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) (lo hi k₀ : Nat)
    (h_inv : SubIntervalInv r pair E lo hi)
    (h_diff : pair (lo % r) ≠ pair ((lo + 1) % r))
    (hk_ge : lo + 1 ≤ k₀) (hk_lt : k₀ < hi)
    (h_ek0 : E (lo + 1) k₀)
    (hk_max : ∀ v, k₀ < v → v < hi → ¬ E (lo + 1) v)
    (u w : Nat) (hu_lt : u < r) (hw_lt : w < r) (h_euw : E u w) :
    (lo < u ∧ u ≤ k₀) ↔ (lo < w ∧ w ≤ k₀) := by
  constructor
  · intro hu_in
    exact partner_interval_closed r pair E hE lo hi k₀ h_inv h_diff hk_ge hk_lt h_ek0 hk_max u w hu_lt hw_lt hu_in h_euw
  · intro hw_in
    exact partner_interval_closed r pair E hE lo hi k₀ h_inv h_diff hk_ge hk_lt h_ek0 hk_max w u hw_lt hu_lt hw_in
      (hE.symm u hu_lt w hw_lt h_euw)

/-- Two unequal `Bool` values have opposite values; if `b1 ≠ b2` and `b2 ≠ b3`, then `b1 = b3`. -/
private theorem bool_eq_of_ne_of_ne {b1 b2 b3 : Bool} (h12 : b1 ≠ b2) (h23 : b2 ≠ b3) : b1 = b3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> revert h12 h23 <;> decide

/-- Partner edge `k₀` is a transition edge (`pair (k₀ % r) ≠ pair ((k₀ + 1) % r)`) and
    restores the outer color pair (`pair ((k₀ + 1) % r) = pair (lo % r)`). -/
theorem partner_edge_diff_pair (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) (lo hi k₀ : Nat)
    (h_inv : SubIntervalInv r pair E lo hi)
    (h_diff : pair (lo % r) ≠ pair ((lo + 1) % r))
    (hk_ge : lo + 1 ≤ k₀) (hk_lt : k₀ < hi)
    (h_ek0 : E (lo + 1) k₀)
    (hk_max : ∀ v, k₀ < v → v < hi → ¬ E (lo + 1) v) :
    pair (k₀ % r) ≠ pair ((k₀ + 1) % r) ∧ pair ((k₀ + 1) % r) = pair (lo % r) := by
  have hk0_lt_r : k₀ < r := Nat.lt_of_lt_of_le hk_lt h_inv.hi_le_r
  have hlo1_lt_r : lo + 1 < r := Nat.lt_of_le_of_lt hk_ge hk0_lt_r
  have h_nxt_lt_r : (k₀ + 1) % r < r := Nat.mod_lt _ hE.r_pos
  have h_not_e_nxt : ¬ E k₀ ((k₀ + 1) % r) := by
    intro h_e_nxt
    have h_in := partner_interval_closed r pair E hE lo hi k₀ h_inv h_diff hk_ge hk_lt h_ek0 hk_max
      k₀ ((k₀ + 1) % r) hk0_lt_r h_nxt_lt_r ⟨by omega, Nat.le_refl k₀⟩ h_e_nxt
    by_cases hk1_lt : k₀ + 1 < r
    · rw [Nat.mod_eq_of_lt hk1_lt] at h_in
      omega
    · have hk1_eq : k₀ + 1 = r := by omega
      rw [hk1_eq, Nat.mod_self] at h_in
      omega
  have h_k0_diff : pair (k₀ % r) ≠ pair ((k₀ + 1) % r) := by
    rw [Nat.mod_eq_of_lt hk0_lt_r]
    intro h_same
    exact h_not_e_nxt (hE.step_same k₀ hk0_lt_r h_same)
  have h_pair_lo1_k0 : pair ((lo + 1) % r) = pair (k₀ % r) := by
    rw [Nat.mod_eq_of_lt hlo1_lt_r, Nat.mod_eq_of_lt hk0_lt_r]
    exact hE.same_pair (lo + 1) hlo1_lt_r k₀ hk0_lt_r h_ek0
  have h_diff_k0 : pair (lo % r) ≠ pair (k₀ % r) := by
    rw [← h_pair_lo1_k0]
    exact h_diff
  exact ⟨h_k0_diff, (bool_eq_of_ne_of_ne h_diff_k0 h_k0_diff).symm⟩

/-- Left recursive subproblem `[lo + 1, k₀)` satisfies `SubIntervalInv`. -/
theorem subIntervalInv_left (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) (lo hi k₀ : Nat)
    (h_inv : SubIntervalInv r pair E lo hi)
    (h_diff : pair (lo % r) ≠ pair ((lo + 1) % r))
    (hk_ge : lo + 1 ≤ k₀) (hk_lt : k₀ < hi)
    (h_ek0 : E (lo + 1) k₀)
    (hk_max : ∀ v, k₀ < v → v < hi → ¬ E (lo + 1) v) :
    SubIntervalInv r pair E (lo + 1) k₀ where
  le_hi := hk_ge
  hi_le_r := Nat.le_of_lt (Nat.lt_of_lt_of_le hk_lt h_inv.hi_le_r)
  pair_eq := by
    have hk0_lt_r : k₀ < r := Nat.lt_of_lt_of_le hk_lt h_inv.hi_le_r
    have hlo1_lt_r : lo + 1 < r := Nat.lt_of_le_of_lt hk_ge hk0_lt_r
    rw [Nat.mod_eq_of_lt hlo1_lt_r, Nat.mod_eq_of_lt hk0_lt_r]
    exact hE.same_pair (lo + 1) hlo1_lt_r k₀ hk0_lt_r h_ek0
  closed_other_pair := by
    intro u hu_gt hu_lt w hw_lt h_euw h_out
    have hk0_lt_r : k₀ < r := Nat.lt_of_lt_of_le hk_lt h_inv.hi_le_r
    have hlo1_lt_r : lo + 1 < r := Nat.lt_of_le_of_lt hk_ge hk0_lt_r
    have hu_lt_r : u < r := Nat.lt_trans hu_lt hk0_lt_r
    have hw_in : lo < w ∧ w ≤ k₀ :=
      partner_interval_closed r pair E hE lo hi k₀ h_inv h_diff hk_ge hk_lt h_ek0 hk_max
        u w hu_lt_r hw_lt ⟨by omega, Nat.le_of_lt hu_lt⟩ h_euw
    rw [Nat.mod_eq_of_lt hlo1_lt_r]
    by_cases hw_lo1 : w = lo + 1
    · subst hw_lo1
      exact hE.same_pair u hu_lt_r (lo + 1) hlo1_lt_r h_euw
    · have hw_k0 : w = k₀ := by omega
      rw [hw_k0] at h_euw
      have h_u_k0 := hE.same_pair u hu_lt_r k₀ hk0_lt_r h_euw
      have h_lo1_k0 := hE.same_pair (lo + 1) hlo1_lt_r k₀ hk0_lt_r h_ek0
      exact h_u_k0.trans h_lo1_k0.symm

/-- Right recursive subproblem `[k₀ + 1, hi)` satisfies `SubIntervalInv`. -/
theorem subIntervalInv_right (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) (lo hi k₀ : Nat)
    (h_inv : SubIntervalInv r pair E lo hi)
    (h_diff : pair (lo % r) ≠ pair ((lo + 1) % r))
    (hk_ge : lo + 1 ≤ k₀) (hk_lt : k₀ < hi)
    (h_ek0 : E (lo + 1) k₀)
    (hk_max : ∀ v, k₀ < v → v < hi → ¬ E (lo + 1) v) :
    SubIntervalInv r pair E (k₀ + 1) hi where
  le_hi := hk_lt
  hi_le_r := h_inv.hi_le_r
  pair_eq := by
    have h_k0 := partner_edge_diff_pair r pair E hE lo hi k₀ h_inv h_diff hk_ge hk_lt h_ek0 hk_max
    exact h_k0.2.trans h_inv.pair_eq
  closed_other_pair := by
    intro u hu_gt hu_lt w hw_lt h_euw h_out
    have hu_lt_r : u < r := Nat.lt_of_lt_of_le hu_lt h_inv.hi_le_r
    have h_k0 := partner_edge_diff_pair r pair E hE lo hi k₀ h_inv h_diff hk_ge hk_lt h_ek0 hk_max
    have h_w_not_in_left : ¬ (lo < w ∧ w ≤ k₀) := by
      intro hw_in
      have hu_in := (partner_interval_closed_iff r pair E hE lo hi k₀ h_inv h_diff hk_ge hk_lt h_ek0 hk_max
        u w hu_lt_r hw_lt h_euw).mpr hw_in
      omega
    by_cases hw_k1 : w = k₀ + 1
    · subst hw_k1
      have hk1_lt_r : k₀ + 1 < r := Nat.lt_trans hu_gt hu_lt_r
      rw [Nat.mod_eq_of_lt hk1_lt_r]
      exact hE.same_pair u hu_lt_r (k₀ + 1) hk1_lt_r h_euw
    · have h_w_out_hi : ¬ (lo < w ∧ w < hi) := by
        intro hw_hi
        exact h_out ⟨by omega, hw_hi.2⟩
      rw [h_k0.2]
      exact h_inv.closed_other_pair u (by omega) hu_lt w hw_lt h_euw h_w_out_hi

/-!
### Part 3: Structural Non-Crossing Matching Enumeration & Completeness
-/

/-- Total structural enumeration of non-crossing partial matchings on `[lo, hi)`. -/
def ncMatchingsList : Nat → Nat → Nat → List (List (Nat × Nat))
  | 0, _, _ => [[]]
  | fuel + 1, lo, hi =>
    if lo ≥ hi then [[]]
    else
      ncMatchingsList fuel (lo + 1) hi ++
        ((List.range (hi - (lo + 1))).flatMap fun d =>
          let k := lo + 1 + d
          let left := ncMatchingsList fuel (lo + 1) k
          let right := ncMatchingsList fuel (k + 1) hi
          left.flatMap fun m1 =>
            right.map fun m2 => ((lo, k) :: m1) ++ m2)

theorem mem_ncMatchingsList_skip (fuel lo hi : Nat) (h_lt : lo < hi)
    (m : List (Nat × Nat)) (hm : m ∈ ncMatchingsList fuel (lo + 1) hi) :
    m ∈ ncMatchingsList (fuel + 1) lo hi := by
  dsimp [ncMatchingsList]
  rw [if_neg (by omega)]
  exact List.mem_append_left _ hm

theorem mem_ncMatchingsList_pair (fuel lo k hi : Nat)
    (hk_ge : lo + 1 ≤ k) (hk_lt : k < hi)
    (m1 m2 : List (Nat × Nat))
    (hm1 : m1 ∈ ncMatchingsList fuel (lo + 1) k)
    (hm2 : m2 ∈ ncMatchingsList fuel (k + 1) hi) :
    ((lo, k) :: (m1 ++ m2)) ∈ ncMatchingsList (fuel + 1) lo hi := by
  dsimp [ncMatchingsList]
  rw [if_neg (by omega)]
  apply List.mem_append_right
  rw [List.mem_flatMap]
  refine ⟨k - (lo + 1), List.mem_range.mpr (by omega), ?_⟩
  have hk_eq : lo + 1 + (k - (lo + 1)) = k := by omega
  rw [hk_eq, List.mem_flatMap]
  refine ⟨m1, hm1, ?_⟩
  rw [List.mem_map]
  exact ⟨m2, hm2, rfl⟩

/-- Flat list of all endpoints `[x₀, y₀, x₁, y₁, ...]` of a chord list `m`. -/
def chordEndpoints (m : List (Nat × Nat)) : List Nat :=
  m.flatMap fun p => [p.1, p.2]

@[simp] theorem chordEndpoints_nil : chordEndpoints [] = [] := rfl

@[simp] theorem chordEndpoints_cons (p : Nat × Nat) (m : List (Nat × Nat)) :
    chordEndpoints (p :: m) = p.1 :: p.2 :: chordEndpoints m := rfl

theorem chordEndpoints_append (m1 m2 : List (Nat × Nat)) :
    chordEndpoints (m1 ++ m2) = chordEndpoints m1 ++ chordEndpoints m2 := by
  unfold chordEndpoints
  exact List.flatMap_append

theorem chordEndpoints_bounds (lo hi : Nat) (m : List (Nat × Nat))
    (h_rng : ∀ p ∈ m, lo ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < hi)
    (i : Nat) (hi_mem : i ∈ chordEndpoints m) :
    lo ≤ i ∧ i < hi := by
  unfold chordEndpoints at hi_mem
  rw [List.mem_flatMap] at hi_mem
  rcases hi_mem with ⟨p, hp_mem, hi_p⟩
  have hp := h_rng p hp_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi_p
  rcases hi_p with rfl | rfl <;> omega

theorem nodup_append_of_disjoint {α : Type} (L1 L2 : List α)
    (h1 : L1.Nodup) (h2 : L2.Nodup) (hdj : ∀ x ∈ L1, x ∉ L2) :
    (L1 ++ L2).Nodup := by
  induction L1 with
  | nil => exact h2
  | cons a tl ih =>
    rcases List.nodup_cons.mp h1 with ⟨ha_tl, htl⟩
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, ih htl (fun x hx => hdj x (List.mem_cons_of_mem a hx))⟩
    intro ha_app
    rcases List.mem_append.mp ha_app with ha1 | ha2
    · exact ha_tl ha1
    · exact hdj a List.mem_cons_self ha2

/-- Inductive characterization of a non-crossing matching `m` extracted from `[lo, hi)`:
    Directly mirrors the three cases (`nil`, `skip`, `pair`) of the sub-interval recursion,
    enabling 1-step structural induction on `[lo, hi)` for both parity and trace-sum proofs! -/
inductive IsExtractedMatching (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop) :
    Nat → Nat → List (Nat × Nat) → Prop where
  | nil (lo : Nat) (h_le : lo ≤ r) :
      IsExtractedMatching r pair E lo lo []
  | skip (lo hi : Nat) (m : List (Nat × Nat))
      (h_lt : lo < hi) (h_hi : hi ≤ r)
      (h_same : pair (lo % r) = pair ((lo + 1) % r))
      (h_rest : IsExtractedMatching r pair E (lo + 1) hi m) :
      IsExtractedMatching r pair E lo hi m
  | pair (lo k₀ hi : Nat) (m1 m2 : List (Nat × Nat))
      (hk_ge : lo + 1 ≤ k₀) (hk_lt : k₀ < hi) (h_hi : hi ≤ r)
      (h_diff_lo : pair (lo % r) ≠ pair ((lo + 1) % r))
      (h_diff_k0 : pair (k₀ % r) ≠ pair ((k₀ + 1) % r))
      (h_closed : ∀ u < r, ∀ w < r, E u w → ((lo < u ∧ u ≤ k₀) ↔ (lo < w ∧ w ≤ k₀)))
      (h_left : IsExtractedMatching r pair E (lo + 1) k₀ m1)
      (h_right : IsExtractedMatching r pair E (k₀ + 1) hi m2) :
      IsExtractedMatching r pair E lo hi ((lo, k₀) :: (m1 ++ m2))

theorem isExtractedMatching_chords_in_range {r : Nat} {pair : Nat → Bool} {E : Nat → Nat → Prop}
    {lo hi : Nat} {m : List (Nat × Nat)}
    (h : IsExtractedMatching r pair E lo hi m) :
    ∀ p ∈ m, lo ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < hi := by
  induction h with
  | nil lo _ => intro _ hp; exact False.elim (List.not_mem_nil hp)
  | skip lo hi m h_lt _ _ _ ih =>
    intro p hp
    have h1 := ih p hp
    omega
  | pair lo k₀ hi m1 m2 hk_ge hk_lt _ _ _ _ _ _ ih1 ih2 =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp_rest
    · exact ⟨Nat.le_refl lo, by omega, hk_lt⟩
    · rcases List.mem_append.mp hp_rest with hp1 | hp2
      · have h1 := ih1 p hp1; omega
      · have h2 := ih2 p hp2; omega

theorem isExtractedMatching_intervals_closed {r : Nat} {pair : Nat → Bool} {E : Nat → Nat → Prop}
    {lo hi : Nat} {m : List (Nat × Nat)}
    (h : IsExtractedMatching r pair E lo hi m) :
    ∀ p ∈ m, ∀ u < r, ∀ w < r, E u w → ((p.1 < u ∧ u ≤ p.2) ↔ (p.1 < w ∧ w ≤ p.2)) := by
  induction h with
  | nil lo _ => intro _ hp; exact False.elim (List.not_mem_nil hp)
  | skip _ _ _ _ _ _ _ ih => exact ih
  | pair lo k₀ hi m1 m2 _ _ _ _ _ h_closed _ _ ih1 ih2 =>
    intro p hp u hu w hw he
    rcases List.mem_cons.mp hp with rfl | hp_rest
    · exact h_closed u hu w hw he
    · rcases List.mem_append.mp hp_rest with hp1 | hp2
      · exact ih1 p hp1 u hu w hw he
      · exact ih2 p hp2 u hu w hw he

/-- **Main Theorem A1.1 (`exists_ncMatching_of_subIntervalInv`):**
    Under `PlanarRingEquiv r pair E` and `SubIntervalInv r pair E lo hi` with `hi - lo ≤ fuel`,
    there exists a non-crossing matching `m ∈ ncMatchingsList fuel lo hi` satisfying
    `IsExtractedMatching r pair E lo hi m`. -/
theorem exists_ncMatching_of_subIntervalInv (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop)
    (hE : PlanarRingEquiv r pair E) (fuel lo hi : Nat)
    (h_fuel : hi - lo ≤ fuel)
    (h_inv : SubIntervalInv r pair E lo hi) :
    ∃ m ∈ ncMatchingsList fuel lo hi, IsExtractedMatching r pair E lo hi m := by
  open Classical in
  induction fuel generalizing lo hi with
  | zero =>
    have h_eq : lo = hi := by have := h_inv.le_hi; omega
    subst h_eq
    exact ⟨[], List.mem_singleton_self [], IsExtractedMatching.nil lo h_inv.hi_le_r⟩
  | succ fuel ih =>
    by_cases h_lt : lo < hi
    · by_cases h_same : pair (lo % r) = pair ((lo + 1) % r)
      · have h_inv_skip := subIntervalInv_skip r pair E hE lo hi h_lt h_inv h_same
        rcases ih (lo + 1) hi (by omega) h_inv_skip with ⟨m, hm_mem, hm_ext⟩
        exact ⟨m, mem_ncMatchingsList_skip fuel lo hi h_lt m hm_mem,
          IsExtractedMatching.skip lo hi m h_lt h_inv.hi_le_r h_same hm_ext⟩
      · have h_lo1_lt_hi : lo + 1 < hi :=
          lo_add_one_lt_hi_of_diff_pair r pair E lo hi h_lt h_inv h_same
        have h_lo1_lt_r : lo + 1 < r := Nat.lt_of_lt_of_le h_lo1_lt_hi h_inv.hi_le_r
        rcases exists_max_in_range (fun v => E (lo + 1) v) (lo + 1) hi h_lo1_lt_hi
            (hE.refl (lo + 1) h_lo1_lt_r) with ⟨k₀, hk_ge, hk_lt, h_ek0, hk_max⟩
        have h_inv_l := subIntervalInv_left r pair E hE lo hi k₀ h_inv h_same hk_ge hk_lt h_ek0 hk_max
        have h_inv_r := subIntervalInv_right r pair E hE lo hi k₀ h_inv h_same hk_ge hk_lt h_ek0 hk_max
        rcases ih (lo + 1) k₀ (by omega) h_inv_l with ⟨m1, hm1_mem, hm1_ext⟩
        rcases ih (k₀ + 1) hi (by omega) h_inv_r with ⟨m2, hm2_mem, hm2_ext⟩
        have h_k0_edge := partner_edge_diff_pair r pair E hE lo hi k₀ h_inv h_same hk_ge hk_lt h_ek0 hk_max
        have h_closed := partner_interval_closed_iff r pair E hE lo hi k₀ h_inv h_same hk_ge hk_lt h_ek0 hk_max
        exact ⟨(lo, k₀) :: (m1 ++ m2),
          mem_ncMatchingsList_pair fuel lo k₀ hi hk_ge hk_lt m1 m2 hm1_mem hm2_mem,
          IsExtractedMatching.pair lo k₀ hi m1 m2 hk_ge hk_lt h_inv.hi_le_r
            h_same h_k0_edge.1 (fun u hu w hw he => h_closed u w hu hw he) hm1_ext hm2_ext⟩
    · have h_eq : lo = hi := by have := h_inv.le_hi; omega
      subst h_eq
      have h_mem_nil : [] ∈ ncMatchingsList (fuel + 1) lo lo := by
        dsimp [ncMatchingsList]
        rw [if_pos (Nat.le_refl lo)]
        exact List.mem_singleton_self []
      exact ⟨[], h_mem_nil, IsExtractedMatching.nil lo h_inv.hi_le_r⟩

/-- **Main Theorem A1.2 (`exists_ncMatching_of_partition`):**
    For any configuration `c` with `IsRingCycle c`, valid boundary coloring `b`, and
    joint planar ring partition `(equiv_ab, equiv_cd)` under `theta1`, there exists
    `m ∈ ncMatchingsList c.ringSize 0 c.ringSize` satisfying
    `IsExtractedMatching c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd) 0 c.ringSize m`. -/
theorem exists_ncMatching_of_partition (c : Configuration) (b : BoundaryColoring c)
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (h_ring : IsRingCycle c)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd) :
    ∃ m ∈ ncMatchingsList c.ringSize 0 c.ringSize,
      IsExtractedMatching c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd) 0 c.ringSize m := by
  have hE := planarRingEquiv_of_partition c b equiv_ab equiv_cd h_ring hPart
  exact exists_ncMatching_of_subIntervalInv c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd)
    hE c.ringSize 0 c.ringSize (by omega)
    (subIntervalInv_root c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd) hE)

/-!
### Part 4: Structural `buildSMDataTotal` Definition
-/

/-- Structural count of negative signs (`bit k of s == 0`) among `p` chords. -/
def negSignCount : Nat → Nat → Nat
  | _, 0 => 0
  | s, rem + 1 =>
    (if s &&& 1 == 1 then 0 else 1) + negSignCount (s >>> 1) rem

/-- Structural construction of `(a, b)` delta lists for a chord list `m` and sign bitmask `s`. -/
def buildSMDeltas (pow3 : Array Nat) : Nat → List (Nat × Nat) → List Nat × List Nat
  | _, [] => ([], [])
  | s, (x, y) :: rest =>
    let px := pow3.getD x 0
    let py := pow3.getD y 0
    let (a_rest, b_rest) := buildSMDeltas pow3 (s >>> 1) rest
    if s &&& 1 == 1 then
      ((px + py) :: a_rest, (2 * px + 2 * py) :: b_rest)
    else
      ((px + 2 * py) :: a_rest, (2 * px + py) :: b_rest)

/-- Construct an `SMData` from chord list `m` and sign bitmask `s`. -/
def mkSMData (pow3 : Array Nat) (m : List (Nat × Nat)) (s : Nat) : SMData :=
  let (a, b) := buildSMDeltas pow3 s m
  { p := m.length, a := a.toArray, b := b.toArray }

/-- Total structural version of `buildSMData r pow3`. -/
def buildSMDataTotal (r : Nat) (pow3 : Array Nat) : Array SMData :=
  ((ncMatchingsList r 0 r).flatMap fun m =>
    let p := m.length
    ((List.range (1 <<< p)).filter fun s =>
      negSignCount s p % 2 == r % 2).map fun s =>
      mkSMData pow3 m s).toArray

theorem mem_buildSMDataTotal (r : Nat) (pow3 : Array Nat)
    (m : List (Nat × Nat)) (hm : m ∈ ncMatchingsList r 0 r)
    (s : Nat) (hs_lt : s < 1 <<< m.length)
    (hs_par : (negSignCount s m.length % 2 == r % 2) = true) :
    mkSMData pow3 m s ∈ (buildSMDataTotal r pow3).toList := by
  unfold buildSMDataTotal
  rw [List.toList_toArray, List.mem_flatMap]
  refine ⟨m, hm, ?_⟩
  rw [List.mem_map]
  refine ⟨s, ?_, rfl⟩
  rw [List.mem_filter]
  exact ⟨List.mem_range.mpr hs_lt, hs_par⟩



end CheckerSoundness
end Math
