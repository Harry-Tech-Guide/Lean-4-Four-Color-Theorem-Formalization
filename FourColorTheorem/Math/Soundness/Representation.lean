import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.FastReducer
import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Soundness

open FastReducer
open Batch

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-!
# Combinatorial Representation of Joint Planar Partitions (Lemma (a))

In the RSST D-reducibility theory, Lemma (a) establishes that:
For every valid boundary coloring `b` of configuration `c`, every color pairing `θ`,
and every joint planar ring partition `(equiv_ab, equiv_cd)` presented by the exterior
Kempe graph, there exists an enumerated balanced signed non-crossing matching `(M, s)`
such that:
1. `b` fits `(M, s)` under `θ`.
2. Every swap choice parameter `t ∈ [0, 2^p)` associated with `(M, s)` corresponds to
   an admissible boundary Kempe swap choice `S : Nat → Bool` respecting the equivalence
   classes of both `equiv_ab` and `equiv_cd`.
3. The boundary Kempe swap under `S` produces a coloring whose edge trace matches
   the checker's `t`-th fitting trace `smFitIndex sm t`.
-/

/-- Base-3 trace index of boundary coloring b on ring vertices of configuration c.
    Edge difference x_i = b(i) ^^^ b((i+1)%r) ∈ {1, 2, 3}.
    Base-3 digit d_i = x_i - 1 ∈ {0, 1, 2}.
    Returns ∑ d_i * 3^i. -/
-- Structural helper for `boundaryTrace`: accumulates `d_i * 3^i` for `i = k, ..., k + rem - 1`.
def boundaryTraceAux (r : Nat) (b : Nat → Color) (pow3 : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | rem + 1, i, acc =>
    let nxt := (i + 1) % r
    let diff := (b i).toNat ^^^ (b nxt).toNat
    let d_i := if diff > 0 then diff - 1 else 0
    boundaryTraceAux r b pow3 rem (i + 1) (acc + d_i * pow3.getD i 0)

/-- Base-3 trace index of boundary coloring b on ring vertices of configuration c. -/
def boundaryTrace (c : Configuration) (b : BoundaryColoring c) (pow3 : Array Nat) : Nat :=
  boundaryTraceAux c.ringSize b pow3 c.ringSize 0 0

def boundaryTraceLoopUnused (c : Configuration) (b : BoundaryColoring c) (pow3 : Array Nat) : Nat := Id.run do
  let r := c.ringSize
  let mut idx := 0
  for i in [0:r] do
    let nxt := (i + 1) % r
    let diff := (b i).toNat ^^^ (b nxt).toNat
    let d_i := if diff > 0 then diff - 1 else 0
    idx := idx + d_i * pow3.getD i 0
  return idx

/-- Canonical ColorPairing for theta = 1:
    pairs {c0, c1} and {c2, c3}, corresponding to difference 1 in V₄. -/
def theta1 : ColorPairing where
  a := Color.c0
  b := Color.c1
  c := Color.c2
  d := Color.c3
  distinct := by decide

/-- Canonical ColorPairing for theta = 2:
    pairs {c0, c2} and {c1, c3}, corresponding to difference 2 in V₄. -/
def theta2 : ColorPairing where
  a := Color.c0
  b := Color.c2
  c := Color.c1
  d := Color.c3
  distinct := by decide

/-- Canonical ColorPairing for theta = 3:
    pairs {c0, c3} and {c1, c2}, corresponding to difference 3 in V₄. -/
def theta3 : ColorPairing where
  a := Color.c0
  b := Color.c3
  c := Color.c1
  d := Color.c2
  distinct := by decide

/-- Helper: relabel `col` by an S₃ involution fixing `c0` based on the XOR difference of `a` and `b`. -/
def relabelColorAux (a b col : Color) : Color :=
  let δ := a.toNat ^^^ b.toNat
  if δ == 2 then
    match col with
    | Color.c0 => Color.c0
    | Color.c1 => Color.c2
    | Color.c2 => Color.c1
    | Color.c3 => Color.c3
  else if δ == 3 then
    match col with
    | Color.c0 => Color.c0
    | Color.c1 => Color.c3
    | Color.c2 => Color.c2
    | Color.c3 => Color.c1
  else col

/-- Relabel colors by an S₃ involution fixing `c0` so that the within-pair XOR difference
    `δ = θ.a.toNat ^^^ θ.b.toNat` of `θ` maps to `1` (the difference of `theta1`):
    - if `δ = 1` (`theta1`), identity on colors;
    - if `δ = 2` (`theta2`), swap `c1 ↔ c2`;
    - if `δ = 3` (`theta3`), swap `c1 ↔ c3`. -/
def relabelColor (θ : ColorPairing) (col : Color) : Color :=
  relabelColorAux θ.a θ.b col

/-- Relabel a boundary coloring so that pairing `θ` is normalized to `theta1`. -/
def relabelBoundary (θ : ColorPairing) (b : Nat → Color) : Nat → Color :=
  fun i => relabelColor θ (b i)

/-- Base-3 trace index of boundary coloring `b` normalized with respect to color pairing `θ`.
    For `θ = theta1`, this is definitionally `boundaryTrace c b pow3` (`orb.j0`).
    For `θ = theta2`, this applies the `c1 ↔ c2` color permutation (`orb.j2`).
    For `θ = theta3`, this applies the `c1 ↔ c3` color permutation (`orb.j5`). -/
def boundaryTraceTheta (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing) (pow3 : Array Nat) : Nat :=
  boundaryTrace c (relabelBoundary θ b) pow3

@[simp] theorem relabelColor_theta1 (col : Color) : relabelColor theta1 col = col := rfl

@[simp] theorem relabelBoundary_theta1 (b : Nat → Color) : relabelBoundary theta1 b = b := rfl

@[simp] theorem boundaryTraceTheta_theta1 (c : Configuration) (b : BoundaryColoring c) (pow3 : Array Nat) :
    boundaryTraceTheta c b theta1 pow3 = boundaryTrace c b pow3 := rfl

/-- The trace index of the t-th fitting coloring of a signed matching `sm`.
    Bit k of parameter t selects delta `a[k]` (bit = 0) or delta `b[k]` (bit = 1). -/
-- Structural helper for `smFitIndex`: accumulates selected delta `a[k]` or `b[k]` for `k = i, ..., i + rem - 1`.
def smFitIndexAux (sm : SMData) (t : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | rem + 1, k, acc =>
    let first := (t >>> k) &&& 1 == 0
    let delta := if first then sm.a.getD k 0 else sm.b.getD k 0
    smFitIndexAux sm t rem (k + 1) (acc + delta)

def smFitIndex (sm : SMData) (t : Nat) : Nat :=
  smFitIndexAux sm t sm.p 0 0

def smFitIndexLoopUnused (sm : SMData) (t : Nat) : Nat := Id.run do
  let mut j := 0
  for k in [0:sm.p] do
    let first := (t >>> k) &&& 1 == 0
    j := j + (if first then sm.a.getD k 0 else sm.b.getD k 0)
  return j

/-- A signed matching `sm` faithfully represents a joint planar partition `(equiv_ab, equiv_cd)`
    for boundary coloring `b` under color pairing `θ`. -/
def RepresentsPartition (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (sm : SMData) (pow3 : Array Nat) : Prop :=
  ∃ (S : Nat → (Nat → Bool)),
    (∀ t, t < 1 <<< sm.p → IsValidSwapChoice c b θ equiv_ab equiv_cd (S t)) ∧
    (∀ i, S 0 i = false) ∧
    (∀ t, t < 1 <<< sm.p →
      boundaryTraceTheta c (boundaryKempeSwap c b θ (S t)) θ pow3 = smFitIndex sm t)

/-- Full Lemma (a) Representation Property (RSST / Gonthier):
    For every configuration `c`, valid boundary coloring `b`, color pairing `θ`, and
    joint planar ring partition `(equiv_ab, equiv_cd)`, there exists an enumerated
    balanced signed matching `sm ∈ sms` that faithfully represents the partition. -/
def FullRepresentationHypothesis (c : Configuration) (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  ∀ (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop),
    IsValidBoundaryColoring c b →
    IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
    ∃ (sm : SMData), sm ∈ sms.toList ∧
      RepresentsPartition c b θ equiv_ab equiv_cd sm pow3

/-!
### Part (iii): The Parity and Sign Condition
-/

/-- In V₄, the cyclic XOR sum of `(r - 2p)` unmatched edges (each contributing 1)
    and `p_neg` negative pairs (each contributing 1) vanishes if and only if
    `(r - 2p + p_neg)` is even, which is equivalent to `p_neg % 2 = r % 2`. -/
theorem balance_parity_iff (r p p_neg : Nat) (hp : 2 * p ≤ r) (hp_neg : p_neg ≤ p) :
    (r - 2 * p + p_neg) % 2 = 0 ↔ p_neg % 2 = r % 2 := by
  omega

/-- XOR difference in V₄ of equal colors is 0: (2 ⊕ 2 = 0 and 3 ⊕ 3 = 0). -/
theorem v4_xor_equal (c : Nat) (h : c < 4) : c ^^^ c = 0 := by
  cases c with
  | zero => rfl
  | succ c =>
    cases c with
    | zero => rfl
    | succ c =>
      cases c with
      | zero => rfl
      | succ c =>
        cases c with
        | zero => rfl
        | succ c => omega

/-- XOR difference in V₄ of opposite transition colors is 1: (2 ⊕ 3 = 1 and 3 ⊕ 2 = 1). -/
theorem v4_xor_opposite_23 : 2 ^^^ 3 = 1 := rfl
theorem v4_xor_opposite_32 : 3 ^^^ 2 = 1 := rfl

/-!
### Part (ii): Non-Crossing Matchings & Enumeration Structure
-/

/-- A chord `(a, b)` on `{0, ..., n-1}` with `a < b`. -/
structure Chord where
  x : Nat
  y : Nat
  lt : x < y
  deriving DecidableEq

/-- Two chords `(a, b)` and `(c, d)` with `a < b` and `c < d` cross if
    their endpoints strictly interleave: `a < c < b < d` or `c < a < d < b`. -/
def ChordsCross (c1 c2 : Chord) : Prop :=
  (c1.x < c2.x ∧ c2.x < c1.y ∧ c1.y < c2.y) ∨
  (c2.x < c1.x ∧ c1.x < c2.y ∧ c2.y < c1.y)

/-- A set of chords is non-crossing if no two chords cross each other. -/
def ChordsNonCrossing (chords : List Chord) : Prop :=
  ∀ c1 ∈ chords, ∀ c2 ∈ chords, ¬ ChordsCross c1 c2

/-- The empty matching is trivially non-crossing. -/
theorem empty_chords_noncrossing : ChordsNonCrossing [] := by
  intro c1 h1
  contradiction

/-- A chord is disjoint from another chord if they share no endpoints. -/
def ChordDisjoint (c1 c2 : Chord) : Prop :=
  c1.x ≠ c2.x ∧ c1.x ≠ c2.y ∧ c1.y ≠ c2.x ∧ c1.y ≠ c2.y

/-- A list of chords is pairwise disjoint. -/
def ChordsDisjoint (chords : List Chord) : Prop :=
  ∀ c1 ∈ chords, ∀ c2 ∈ chords, c1 ≠ c2 → ChordDisjoint c1 c2

/-- The length or span of a chord. -/
def chordSpan (c : Chord) : Nat := c.y - c.x

/-- If two non-crossing disjoint chords satisfy c1.x < c2.x < c1.y, then c2 is strictly nested inside c1. -/
theorem nested_of_x_between (c1 c2 : Chord)
    (h_nc : ¬ ChordsCross c1 c2)
    (h_dj : ChordDisjoint c1 c2)
    (hx : c1.x < c2.x ∧ c2.x < c1.y) :
    c1.x < c2.x ∧ c2.y < c1.y := by
  have h_not_cross1 : ¬ (c1.x < c2.x ∧ c2.x < c1.y ∧ c1.y < c2.y) := by
    intro h; exact h_nc (Or.inl h)
  by_cases hy : c1.y < c2.y
  · exact False.elim (h_not_cross1 ⟨hx.1, hx.2, hy⟩)
  · have h_y_ne : c2.y ≠ c1.y := Ne.symm h_dj.2.2.2
    have : c2.y < c1.y := by omega
    exact ⟨hx.1, this⟩

/-- If two non-crossing disjoint chords satisfy c1.x < c2.y < c1.y, then c2 is strictly nested inside c1. -/
theorem nested_of_y_between (c1 c2 : Chord)
    (h_nc : ¬ ChordsCross c1 c2)
    (h_dj : ChordDisjoint c1 c2)
    (hy : c1.x < c2.y ∧ c2.y < c1.y) :
    c1.x < c2.x ∧ c2.y < c1.y := by
  have h_not_cross2 : ¬ (c2.x < c1.x ∧ c1.x < c2.y ∧ c2.y < c1.y) := by
    intro h; exact h_nc (Or.inr h)
  by_cases hx : c2.x < c1.x
  · exact False.elim (h_not_cross2 ⟨hx, hy.1, hy.2⟩)
  · have h_x_ne : c1.x ≠ c2.x := h_dj.1
    have : c1.x < c2.x := by omega
    exact ⟨this, hy.2⟩

/-- If c2 is strictly nested inside c1, the span of c2 is strictly smaller than the span of c1. -/
theorem span_strictly_smaller (c1 c2 : Chord)
    (h_nest : c1.x < c2.x ∧ c2.y < c1.y) :
    chordSpan c2 < chordSpan c1 := by
  dsimp [chordSpan]
  have h1 := c1.lt
  have h2 := c2.lt
  omega

/-- A chord is innermost in a list of chords if no other chord has endpoints strictly between its endpoints. -/
def IsInnermostChord (c : Chord) (chords : List Chord) : Prop :=
  c ∈ chords ∧ ∀ c' ∈ chords, c' ≠ c →
    (c'.x < c.x ∨ c'.x > c.y) ∧ (c'.y < c.x ∨ c'.y > c.y)

/-- Any chord with minimal span in a non-crossing disjoint matching is innermost. -/
theorem minimal_span_is_innermost (chords : List Chord) (c1 : Chord)
    (h_mem : c1 ∈ chords)
    (h_nc : ChordsNonCrossing chords)
    (h_dj : ChordsDisjoint chords)
    (h_min : ∀ c2 ∈ chords, chordSpan c1 ≤ chordSpan c2) :
    IsInnermostChord c1 chords := by
  refine ⟨h_mem, ?_⟩
  intro c2 hc2 h_ne
  have h_nc12 := h_nc c1 h_mem c2 hc2
  have h_dj12 := h_dj c1 h_mem c2 hc2 h_ne.symm
  have h_span_le := h_min c2 hc2
  have hx_not_between : ¬ (c1.x < c2.x ∧ c2.x < c1.y) := by
    intro hx
    have h_nest := nested_of_x_between c1 c2 h_nc12 h_dj12 hx
    have h_smaller := span_strictly_smaller c1 c2 h_nest
    omega
  have hy_not_between : ¬ (c1.x < c2.y ∧ c2.y < c1.y) := by
    intro hy
    have h_nest := nested_of_y_between c1 c2 h_nc12 h_dj12 hy
    have h_smaller := span_strictly_smaller c1 c2 h_nest
    omega
  have h_x_ne1 : c2.x ≠ c1.x := Ne.symm h_dj12.1
  have h_x_ne2 : c2.x ≠ c1.y := Ne.symm h_dj12.2.2.1
  have h_y_ne1 : c2.y ≠ c1.x := Ne.symm h_dj12.2.1
  have h_y_ne2 : c2.y ≠ c1.y := Ne.symm h_dj12.2.2.2
  have hx_out : c2.x < c1.x ∨ c2.x > c1.y := by omega
  have hy_out : c2.y < c1.x ∨ c2.y > c1.y := by omega
  exact ⟨hx_out, hy_out⟩

/-- A non-empty list of chords contains a chord of minimal span. -/
theorem exists_minimal_span (chords : List Chord) (h_ne : chords ≠ []) :
    ∃ c ∈ chords, ∀ c' ∈ chords, chordSpan c ≤ chordSpan c' := by
  induction chords with
  | nil => contradiction
  | cons c cs ih =>
    by_cases hcs : cs = []
    · subst hcs
      refine ⟨c, List.mem_singleton_self c, ?_⟩
      intro c' hc'
      have : c' = c := List.mem_singleton.mp hc'
      subst this; exact Nat.le_refl _
    · rcases ih hcs with ⟨m, hm, hmin⟩
      by_cases h_le : chordSpan c ≤ chordSpan m
      · refine ⟨c, List.mem_cons_self, ?_⟩
        intro c' hc'
        cases hc' with
        | head => exact Nat.le_refl _
        | tail _ hc' =>
          have := hmin c' hc'
          omega
      · refine ⟨m, List.mem_cons_of_mem c hm, ?_⟩
        intro c' hc'
        cases hc' with
        | head => omega
        | tail _ hc' => exact hmin c' hc'

/-- Existence of an innermost chord in any non-empty non-crossing disjoint matching. -/
theorem exists_innermost_chord (chords : List Chord) (h_ne : chords ≠ [])
    (h_nc : ChordsNonCrossing chords)
    (h_dj : ChordsDisjoint chords) :
    ∃ c, IsInnermostChord c chords := by
  rcases exists_minimal_span chords h_ne with ⟨c, hc, hmin⟩
  exact ⟨c, minimal_span_is_innermost chords c hc h_nc h_dj hmin⟩

/-- Removing a chord preserves the non-crossing property. -/
theorem erase_noncrossing (c : Chord) (chords : List Chord)
    (h_nc : ChordsNonCrossing chords) :
    ChordsNonCrossing (chords.erase c) := by
  intro c1 hc1 c2 hc2
  have h1 : c1 ∈ chords := List.mem_of_mem_erase hc1
  have h2 : c2 ∈ chords := List.mem_of_mem_erase hc2
  exact h_nc c1 h1 c2 h2

/-- Removing a chord preserves pairwise disjointness. -/
theorem erase_disjoint (c : Chord) (chords : List Chord)
    (h_dj : ChordsDisjoint chords) :
    ChordsDisjoint (chords.erase c) := by
  intro c1 hc1 c2 hc2 h_ne
  have h1 : c1 ∈ chords := List.mem_of_mem_erase hc1
  have h2 : c2 ∈ chords := List.mem_of_mem_erase hc2
  exact h_dj c1 h1 c2 h2 h_ne

/-- Removing a member chord decreases the length of the list by 1. -/
theorem erase_length (c : Chord) (chords : List Chord)
    (h_mem : c ∈ chords) :
    (chords.erase c).length = chords.length - 1 := by
  exact List.length_erase_of_mem h_mem

/-- Strong induction on chord list length for non-crossing disjoint matchings. -/
theorem noncrossing_chord_induction
    (P : List Chord → Prop)
    (h_empty : P [])
    (h_step : ∀ (chords : List Chord) (c : Chord),
      ChordsNonCrossing chords → ChordsDisjoint chords →
      IsInnermostChord c chords →
      P (chords.erase c) → P chords) :
    ∀ (n : Nat) (chords : List Chord),
      chords.length = n →
      ChordsNonCrossing chords →
      ChordsDisjoint chords →
      P chords := by
  intro n
  induction n with
  | zero =>
    intro chords h_len _ _
    cases chords with
    | nil => exact h_empty
    | cons _ _ => contradiction
  | succ k ih =>
    intro chords h_len h_nc h_dj
    have h_ne : chords ≠ [] := by
      rintro rfl
      contradiction
    rcases exists_innermost_chord chords h_ne h_nc h_dj with ⟨c, hc_inner⟩
    have hc_mem := hc_inner.1
    have h_erase_len : (chords.erase c).length = k := by
      have h1 := erase_length c chords hc_mem
      rw [h_len] at h1
      omega
    have h_erase_nc := erase_noncrossing c chords h_nc
    have h_erase_dj := erase_disjoint c chords h_dj
    have h_rec := ih (chords.erase c) h_erase_len h_erase_nc h_erase_dj
    exact h_step chords c h_nc h_dj hc_inner h_rec

/-- Chord recombination induction principle for non-crossing disjoint matchings:
    Any property holding for the empty matching and preserved by innermost chord recombination
    holds for all non-crossing disjoint matchings. -/
theorem noncrossing_matching_induction
    (P : List Chord → Prop)
    (h_empty : P [])
    (h_step : ∀ (chords : List Chord) (c : Chord),
      ChordsNonCrossing chords → ChordsDisjoint chords →
      IsInnermostChord c chords →
      P (chords.erase c) → P chords)
    (chords : List Chord)
    (h_nc : ChordsNonCrossing chords)
    (h_dj : ChordsDisjoint chords) :
    P chords :=
  noncrossing_chord_induction P h_empty h_step chords.length chords rfl h_nc h_dj

/-- Every pushed element is in the resulting array. -/
theorem mem_push_self {α : Type} (a : Array α) (x : α) :
    x ∈ (a.push x).toList := by
  simp

/-- Pushing to an array preserves membership of existing elements. -/
theorem mem_push_data {α : Type} (a : Array α) (y : α) (x : α) (hx : x ∈ a.toList) :
    x ∈ (a.push y).toList := by
  simp [hx]




/-!
### Part (i): Valid Swap Choices from Partitions
-/

/-- The trivial empty swap choice `fun _ => false` is always an admissible `IsValidSwapChoice`
    over ANY joint planar partition. -/
theorem empty_swap_is_valid (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) :
    IsValidSwapChoice c b θ equiv_ab equiv_cd (fun _ => false) where
  ring_only := fun _ h => False.elim (Bool.noConfusion h)
  respects_ab := fun _ _ _ _ _ => rfl
  respects_cd := fun _ _ _ _ _ => rfl

/-- The full ring swap choice `fun i => i < c.ringSize` is always an admissible `IsValidSwapChoice`
    over ANY joint planar partition. -/
theorem full_swap_is_valid (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) :
    IsValidSwapChoice c b θ equiv_ab equiv_cd (fun i => if i < c.ringSize then true else false) where
  ring_only := fun i h => by
    split at h
    · assumption
    · contradiction
  respects_ab := fun i hi j hj _ => by
    rw [if_pos hi, if_pos hj]
  respects_cd := fun i hi j hj _ => by
    rw [if_pos hi, if_pos hj]

/-!
### Representation Base Case: Zero-Pair Matchings
-/

/-- A 0-pair signed matching faithfully represents a partition with no transition edges,
    using the identity swap `fun _ => false`. -/
theorem zero_pair_represents (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (pow3 : Array Nat)
    (sm : SMData) (h_p0 : sm.p = 0)
    (h_trace : boundaryTraceTheta c b θ pow3 = smFitIndex sm 0) :
    RepresentsPartition c b θ equiv_ab equiv_cd sm pow3 := by
  refine ⟨fun _ => fun _ => false, ?_, ?_, ?_⟩
  · intro t ht
    exact empty_swap_is_valid c b θ equiv_ab equiv_cd
  · intro i; rfl
  · intro t ht
    have h_pow : 1 <<< sm.p = 1 := by rw [h_p0]; rfl
    have ht0 : t = 0 := by omega
    subst ht0
    have h_swap_id : boundaryKempeSwap c b θ (fun _ => false) = b := by
      funext i; rfl
    rw [h_swap_id]
    exact h_trace

/-- Base condition: combining swap choices preserves the identity swap at t = 0. -/
theorem combine_swap_zero (S_rest : Nat → (Nat → Bool)) (K : Nat → Prop) [DecidablePred K]
    (hS0 : ∀ i, S_rest 0 i = false) (i : Nat) :
    (if (0 &&& 1 == 1) ∧ K i then !(S_rest (0 >>> 1) i) else S_rest (0 >>> 1) i) = false := by
  dsimp
  exact hS0 i

/-- Combined swap choice parameterization for chord recombination:
    Bit 0 of parameter t selects whether the innermost chord's region K is swapped,
    while higher bits `t >>> 1` select swap choices on the remaining chords. -/
def combineSwapChoice (S_rest : Nat → (Nat → Bool)) (K : Nat → Prop) [DecidablePred K]
    (t : Nat) (i : Nat) : Bool :=
  if (t &&& 1 == 1) ∧ K i then !(S_rest (t >>> 1) i) else S_rest (t >>> 1) i

/-- At parameter t = 0, the combined swap choice is identity everywhere if S_rest is. -/
theorem combineSwapChoice_zero (S_rest : Nat → (Nat → Bool)) (K : Nat → Prop) [DecidablePred K]
    (hS0 : ∀ i, S_rest 0 i = false) (i : Nat) :
    combineSwapChoice S_rest K 0 i = false :=
  combine_swap_zero S_rest K hS0 i

/-- Shifting parameter t right by 1 preserves bounds under bit-doubling:
    if `t < 1 <<< (p + 1)`, then `t >>> 1 < 1 <<< p`. -/
theorem shift_right_lt_pow (p t : Nat) (ht : t < 1 <<< (p + 1)) :
    t >>> 1 < 1 <<< p := by
  rw [Nat.shiftLeft_eq] at ht
  rw [Nat.shiftLeft_eq]
  rw [Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ (p + 1) = 2 ^ p * 2 := Nat.pow_succ 2 p
  rw [hpow] at ht
  omega

/-- Admissibility preservation under chord recombination:
    If K is a ring component respecting equivalence relations equiv_ab and equiv_cd,
    and S_rest produces admissible swap choices for remaining chords,
    then combineSwapChoice produces admissible swap choices for the combined matching. -/
theorem combineSwapChoice_valid (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (S_rest : Nat → (Nat → Bool)) (K : Nat → Prop) [DecidablePred K]
    (hK_ring : ∀ i, K i → i < c.ringSize)
    (hK_ab : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_ab i j → (K i ↔ K j))
    (hK_cd : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_cd i j → (K i ↔ K j))
    (p : Nat) (hS_valid : ∀ t', t' < 1 <<< p → IsValidSwapChoice c b θ equiv_ab equiv_cd (S_rest t')) :
    ∀ t, t < 1 <<< (p + 1) →
      IsValidSwapChoice c b θ equiv_ab equiv_cd (combineSwapChoice S_rest K t) := by
  intro t ht
  have ht' := shift_right_lt_pow p t ht
  have h_val := hS_valid (t >>> 1) ht'
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    dsimp [combineSwapChoice] at hi
    split at hi
    · rename_i h_cond
      exact hK_ring i h_cond.2
    · exact h_val.ring_only i hi
  · intro i hi j hj hab
    dsimp [combineSwapChoice]
    have hK_iff := hK_ab i hi j hj hab
    have hS_eq := h_val.respects_ab i hi j hj hab
    by_cases hKi : K i
    · have hKj : K j := hK_iff.mp hKi
      by_cases h_bit : t &&& 1 == 1
      · rw [if_pos ⟨h_bit, hKi⟩, if_pos ⟨h_bit, hKj⟩, hS_eq]
      · rw [if_neg (fun h => h_bit h.1), if_neg (fun h => h_bit h.1)]
        exact hS_eq
    · have hKj : ¬ K j := fun hj => hKi (hK_iff.mpr hj)
      rw [if_neg (fun h => hKi h.2), if_neg (fun h => hKj h.2)]
      exact hS_eq
  · intro i hi j hj hcd
    dsimp [combineSwapChoice]
    have hK_iff := hK_cd i hi j hj hcd
    have hS_eq := h_val.respects_cd i hi j hj hcd
    by_cases hKi : K i
    · have hKj : K j := hK_iff.mp hKi
      by_cases h_bit : t &&& 1 == 1
      · rw [if_pos ⟨h_bit, hKi⟩, if_pos ⟨h_bit, hKj⟩, hS_eq]
      · rw [if_neg (fun h => h_bit h.1), if_neg (fun h => h_bit h.1)]
        exact hS_eq
    · have hKj : ¬ K j := fun hj => hKi (hK_iff.mpr hj)
      rw [if_neg (fun h => hKi h.2), if_neg (fun h => hKj h.2)]
      exact hS_eq



/-- Inductive extension lemma for Lemma (a) swap choices:
    Given an innermost chord c0 and its associated ring region K (satisfying hK_ring, hK_ab, hK_cd),
    and an inductive hypothesis providing RepresentsPartition for sm_rest on the erased chords,
    combineSwapChoice provides valid swap choices for the combined matching sm_ext (with sm_ext.p = sm_rest.p + 1). -/
theorem combineSwapChoice_extension_valid
    (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (pow3 : Array Nat)
    (sm_rest sm_ext : SMData) (c0 : Chord)
    (K : Nat → Prop) [DecidablePred K]
    (hK_ring : ∀ i, K i → i < c.ringSize)
    (hK_ab : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_ab i j → (K i ↔ K j))
    (hK_cd : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_cd i j → (K i ↔ K j))
    (hp : sm_ext.p = sm_rest.p + 1)
    (h_rep : RepresentsPartition c b θ equiv_ab equiv_cd sm_rest pow3) :
    ∃ S_ext : Nat → (Nat → Bool),
      (∀ t, t < 1 <<< sm_ext.p → IsValidSwapChoice c b θ equiv_ab equiv_cd (S_ext t)) ∧
      (∀ i, S_ext 0 i = false) := by
  rcases h_rep with ⟨S_rest, hS_valid, hS0, _⟩
  refine ⟨combineSwapChoice S_rest K, ?_, ?_⟩
  · intro t ht
    rw [hp] at ht
    exact combineSwapChoice_valid c b θ equiv_ab equiv_cd S_rest K hK_ring hK_ab hK_cd sm_rest.p hS_valid t ht
  · intro i
    exact combineSwapChoice_zero S_rest K hS0 i

/-- Direct inductive swap validity for combineSwapChoice on sm_ext:
    For any valid swap choices S_rest on sm_rest, combineSwapChoice S_rest K
    yields valid swap choices on sm_ext. -/
theorem combineSwapChoice_inductive_valid
    (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (sm_rest sm_ext : SMData) (c0 : Chord)
    (K : Nat → Prop) [DecidablePred K]
    (hK_ring : ∀ i, K i → i < c.ringSize)
    (hK_ab : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_ab i j → (K i ↔ K j))
    (hK_cd : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_cd i j → (K i ↔ K j))
    (hp : sm_ext.p = sm_rest.p + 1)
    (S_rest : Nat → (Nat → Bool))
    (hS_valid : ∀ t, t < 1 <<< sm_rest.p → IsValidSwapChoice c b θ equiv_ab equiv_cd (S_rest t)) :
    ∀ t, t < 1 <<< sm_ext.p →
      IsValidSwapChoice c b θ equiv_ab equiv_cd (combineSwapChoice S_rest K t) := by
  intro t ht
  rw [hp] at ht
  exact combineSwapChoice_valid c b θ equiv_ab equiv_cd S_rest K hK_ring hK_ab hK_cd sm_rest.p hS_valid t ht

/-- Inductive step for Lemma (a) representation:
    Extends zero_pair_represents to arbitrary non-crossing matchings by chord recombination.
    Given an innermost chord c0, its associated ring region K, and a representation
    of the reduced matching sm_rest, the combined swap choices faithfully represent sm_ext. -/
theorem represents_partition_step
    (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (pow3 : Array Nat)
    (sm_rest sm_ext : SMData) (c0 : Chord)
    (K : Nat → Prop) [DecidablePred K]
    (hK_ring : ∀ i, K i → i < c.ringSize)
    (hK_ab : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_ab i j → (K i ↔ K j))
    (hK_cd : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_cd i j → (K i ↔ K j))
    (hp : sm_ext.p = sm_rest.p + 1)
    (h_trace : ∀ S_rest,
      (∀ t, t < 1 <<< sm_rest.p → IsValidSwapChoice c b θ equiv_ab equiv_cd (S_rest t)) →
      (∀ i, S_rest 0 i = false) →
      (∀ t, t < 1 <<< sm_rest.p → boundaryTraceTheta c (boundaryKempeSwap c b θ (S_rest t)) θ pow3 = smFitIndex sm_rest t) →
      ∀ t, t < 1 <<< sm_ext.p →
        boundaryTraceTheta c (boundaryKempeSwap c b θ (combineSwapChoice S_rest K t)) θ pow3 = smFitIndex sm_ext t)
    (h_rep : RepresentsPartition c b θ equiv_ab equiv_cd sm_rest pow3) :
    RepresentsPartition c b θ equiv_ab equiv_cd sm_ext pow3 := by
  rcases h_rep with ⟨S_rest, hS_valid, hS0, hT_rest⟩
  refine ⟨combineSwapChoice S_rest K, ?_, ?_, ?_⟩
  · intro t ht
    rw [hp] at ht
    exact combineSwapChoice_valid c b θ equiv_ab equiv_cd S_rest K hK_ring hK_ab hK_cd sm_rest.p hS_valid t ht
  · intro i
    exact combineSwapChoice_zero S_rest K hS0 i
  · exact h_trace S_rest hS_valid hS0 hT_rest

/-!
### Part (iv): S₃ Color Symmetry & Reduction of Arbitrary `θ` to `theta1`
-/

/-- `relabelColor θ` is an involution on `Color`. -/
theorem relabelColor_inv (θ : ColorPairing) (col : Color) :
    relabelColor θ (relabelColor θ col) = col := by
  dsimp [relabelColor]
  cases θ.a <;> cases θ.b <;> cases col <;> rfl

/-- `relabelColor θ` is injective on `Color`. -/
theorem relabelColor_inj (θ : ColorPairing) (c1 c2 : Color) :
    relabelColor θ c1 = relabelColor θ c2 ↔ c1 = c2 := by
  constructor
  · intro h
    have h' := congrArg (relabelColor θ) h
    rwa [relabelColor_inv, relabelColor_inv] at h'
  · intro h; rw [h]

/-- For every valid 4-color pairing `θ`, conjugating `θ.swap` by `relabelColor θ` yields `theta1.swap`. -/
theorem relabelColor_swap (θ : ColorPairing) (col : Color) :
    relabelColor θ (θ.swap col) = theta1.swap (relabelColor θ col) := by
  rcases θ with ⟨x1, x2, x3, x4, h⟩
  cases col <;> cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> revert h <;> decide

/-- Relabelling a valid boundary coloring preserves `IsValidBoundaryColoring`. -/
theorem relabelBoundary_valid (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (hb : IsValidBoundaryColoring c b) :
    IsValidBoundaryColoring c (relabelBoundary θ b) := by
  intro i j hi hj hadj h_eq
  have h_col : b i = b j := (relabelColor_inj θ (b i) (b j)).mp h_eq
  exact hb i j hi hj hadj h_col

/-- Relabelling commutes with `boundaryKempeSwap`, converting `θ` into `theta1`. -/
theorem relabelBoundary_swap (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (S : Nat → Bool) :
    relabelBoundary θ (boundaryKempeSwap c b θ S) =
      boundaryKempeSwap c (relabelBoundary θ b) theta1 S := by
  funext i
  dsimp [relabelBoundary, boundaryKempeSwap]
  split
  · exact relabelColor_swap θ (b i)
  · rfl

theorem relabelColor_ab_of_pos (θ : ColorPairing) (col : Color)
    (ha : relabelColor θ θ.a = Color.c0 ∨ relabelColor θ θ.a = Color.c1) :
    (col = θ.a ∨ col = θ.b) ↔ (relabelColor θ col = theta1.a ∨ relabelColor θ col = theta1.b) := by
  rcases θ with ⟨x1, x2, x3, x4, h⟩
  cases col <;> cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> revert h ha <;> decide

theorem relabelColor_cd_of_pos (θ : ColorPairing) (col : Color)
    (ha : relabelColor θ θ.a = Color.c0 ∨ relabelColor θ θ.a = Color.c1) :
    (col = θ.c ∨ col = θ.d) ↔ (relabelColor θ col = theta1.c ∨ relabelColor θ col = theta1.d) := by
  rcases θ with ⟨x1, x2, x3, x4, h⟩
  cases col <;> cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> revert h ha <;> decide

theorem relabelColor_ab_of_neg (θ : ColorPairing) (col : Color)
    (ha : ¬ (relabelColor θ θ.a = Color.c0 ∨ relabelColor θ θ.a = Color.c1)) :
    (col = θ.a ∨ col = θ.b) ↔ (relabelColor θ col = theta1.c ∨ relabelColor θ col = theta1.d) := by
  rcases θ with ⟨x1, x2, x3, x4, h⟩
  cases col <;> cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> revert h ha <;> decide

theorem relabelColor_cd_of_neg (θ : ColorPairing) (col : Color)
    (ha : ¬ (relabelColor θ θ.a = Color.c0 ∨ relabelColor θ θ.a = Color.c1)) :
    (col = θ.c ∨ col = θ.d) ↔ (relabelColor θ col = theta1.a ∨ relabelColor θ col = theta1.b) := by
  rcases θ with ⟨x1, x2, x3, x4, h⟩
  cases col <;> cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> revert h ha <;> decide

/-- Under `relabelColor θ`, the pairs `{θ.a, θ.b}` and `{θ.c, θ.d}` map either to
    `({theta1.a, theta1.b}, {theta1.c, theta1.d})` or to `({theta1.c, theta1.d}, {theta1.a, theta1.b})`. -/
theorem relabelColor_pair_cases (θ : ColorPairing) :
    ((∀ col, (col = θ.a ∨ col = θ.b) ↔ (relabelColor θ col = theta1.a ∨ relabelColor θ col = theta1.b)) ∧
     (∀ col, (col = θ.c ∨ col = θ.d) ↔ (relabelColor θ col = theta1.c ∨ relabelColor θ col = theta1.d))) ∨
    ((∀ col, (col = θ.a ∨ col = θ.b) ↔ (relabelColor θ col = theta1.c ∨ relabelColor θ col = theta1.d)) ∧
     (∀ col, (col = θ.c ∨ col = θ.d) ↔ (relabelColor θ col = theta1.a ∨ relabelColor θ col = theta1.b))) := by
  by_cases ha : relabelColor θ θ.a = Color.c0 ∨ relabelColor θ θ.a = Color.c1
  · exact Or.inl ⟨fun col => relabelColor_ab_of_pos θ col ha, fun col => relabelColor_cd_of_pos θ col ha⟩
  · exact Or.inr ⟨fun col => relabelColor_ab_of_neg θ col ha, fun col => relabelColor_cd_of_neg θ col ha⟩

/-- Swapping `(equiv_ab, equiv_cd)` preserves `IsValidSwapChoice`. -/
theorem validSwapChoice_symm (c : Configuration) (b1 b2 : BoundaryColoring c) (θ1 θ2 : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (S : Nat → Bool)
    (h : IsValidSwapChoice c b1 θ1 equiv_cd equiv_ab S) :
    IsValidSwapChoice c b2 θ2 equiv_ab equiv_cd S where
  ring_only := h.ring_only
  respects_ab := h.respects_cd
  respects_cd := h.respects_ab

/-- Keeping `(equiv_ab, equiv_cd)` in order preserves `IsValidSwapChoice` across relabelling. -/
theorem validSwapChoice_relabel (c : Configuration) (b1 b2 : BoundaryColoring c) (θ1 θ2 : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (S : Nat → Bool)
    (h : IsValidSwapChoice c b1 θ1 equiv_ab equiv_cd S) :
    IsValidSwapChoice c b2 θ2 equiv_ab equiv_cd S where
  ring_only := h.ring_only
  respects_ab := h.respects_ab
  respects_cd := h.respects_cd

/-- Relabelling a joint planar ring partition under `θ` yields a joint planar ring partition
    for `(relabelBoundary θ b, theta1)`, either on `(equiv_ab, equiv_cd)` or on `(equiv_cd, equiv_ab)`. -/
theorem relabelBoundary_partition (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (hPart : IsJointPlanarRingPartition c b θ equiv_ab equiv_cd) :
    IsJointPlanarRingPartition c (relabelBoundary θ b) theta1 equiv_ab equiv_cd ∨
    IsJointPlanarRingPartition c (relabelBoundary θ b) theta1 equiv_cd equiv_ab := by
  rcases relabelColor_pair_cases θ with ⟨hab, hcd⟩ | ⟨hab, hcd⟩
  · left
    refine {
      ab_refl := fun i hi h => hPart.ab_refl i hi ((hab (b i)).mpr h)
      ab_symm := hPart.ab_symm
      ab_trans := hPart.ab_trans
      ab_color := fun i hi j hj h => (hab (b i)).mp (hPart.ab_color i hi j hj h)
      cd_refl := fun i hi h => hPart.cd_refl i hi ((hcd (b i)).mpr h)
      cd_symm := hPart.cd_symm
      cd_trans := hPart.cd_trans
      cd_color := fun i hi j hj h => (hcd (b i)).mp (hPart.cd_color i hi j hj h)
      ab_adj := fun i hi j hj hadj hi_c hj_c =>
        hPart.ab_adj i hi j hj hadj ((hab (b i)).mpr hi_c) ((hab (b j)).mpr hj_c)
      cd_adj := fun i hi j hj hadj hi_c hj_c =>
        hPart.cd_adj i hi j hj hadj ((hcd (b i)).mpr hi_c) ((hcd (b j)).mpr hj_c)
      ab_noncross := hPart.ab_noncross
      cd_noncross := hPart.cd_noncross
      cross_ab_cd := hPart.cross_ab_cd
      cross_cd_ab := hPart.cross_cd_ab
    }
  · right
    refine {
      ab_refl := fun i hi h => hPart.cd_refl i hi ((hcd (b i)).mpr h)
      ab_symm := hPart.cd_symm
      ab_trans := hPart.cd_trans
      ab_color := fun i hi j hj h => (hcd (b i)).mp (hPart.cd_color i hi j hj h)
      cd_refl := fun i hi h => hPart.ab_refl i hi ((hab (b i)).mpr h)
      cd_symm := hPart.ab_symm
      cd_trans := hPart.ab_trans
      cd_color := fun i hi j hj h => (hab (b i)).mp (hPart.ab_color i hi j hj h)
      ab_adj := fun i hi j hj hadj hi_c hj_c =>
        hPart.cd_adj i hi j hj hadj ((hcd (b i)).mpr hi_c) ((hcd (b j)).mpr hj_c)
      cd_adj := fun i hi j hj hadj hi_c hj_c =>
        hPart.ab_adj i hi j hj hadj ((hab (b i)).mpr hi_c) ((hab (b j)).mpr hj_c)
      ab_noncross := hPart.cd_noncross
      cd_noncross := hPart.ab_noncross
      cross_ab_cd := hPart.cross_cd_ab
      cross_cd_ab := hPart.cross_ab_cd
    }

/-- S₃ Reduction Theorem for Lemma (a):
    To establish `FullRepresentationHypothesis c sms pow3` for all 24 color pairings `θ`,
    it suffices to prove representation for the single canonical pairing `theta1`. -/
theorem full_representation_of_theta1 (c : Configuration) (sms : Array SMData) (pow3 : Array Nat)
    (h_theta1 : ∀ (b : BoundaryColoring c) (equiv_ab equiv_cd : Nat → Nat → Prop),
      IsValidBoundaryColoring c b →
      IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd →
      ∃ (sm : SMData), sm ∈ sms.toList ∧
        RepresentsPartition c b theta1 equiv_ab equiv_cd sm pow3) :
    FullRepresentationHypothesis c sms pow3 := by
  intro b θ equiv_ab equiv_cd hb hPart
  have hb_rel := relabelBoundary_valid c b θ hb
  rcases relabelBoundary_partition c b θ equiv_ab equiv_cd hPart with hPart1 | hPart2
  · rcases h_theta1 (relabelBoundary θ b) equiv_ab equiv_cd hb_rel hPart1 with
      ⟨sm, hsm, S, hSwap, hS0, hTrace⟩
    refine ⟨sm, hsm, S, ?_, hS0, ?_⟩
    · intro t ht
      exact validSwapChoice_relabel c (relabelBoundary θ b) b theta1 θ equiv_ab equiv_cd (S t) (hSwap t ht)
    · intro t ht
      dsimp [boundaryTraceTheta]
      rw [relabelBoundary_swap]
      exact hTrace t ht
  · rcases h_theta1 (relabelBoundary θ b) equiv_cd equiv_ab hb_rel hPart2 with
      ⟨sm, hsm, S, hSwap, hS0, hTrace⟩
    refine ⟨sm, hsm, S, ?_, hS0, ?_⟩
    · intro t ht
      exact validSwapChoice_symm c (relabelBoundary θ b) b theta1 θ equiv_ab equiv_cd (S t) (hSwap t ht)
    · intro t ht
      dsimp [boundaryTraceTheta]
      rw [relabelBoundary_swap]
      exact hTrace t ht

/-- Explicit `p`-chord XOR swap choice over an indexed family of chord ring regions `K : Nat → Nat → Bool`:
    for parameter `t < 2^p`, vertex `i` is swapped iff an odd number of active chords (`(t >>> k) &&& 1 == 1`)
    contain `i` (`K k i = true`). -/
def xorSwapChoice (K : Nat → Nat → Bool) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | p + 1, t, i =>
    let prev := xorSwapChoice K p t i
    if ((t >>> p) &&& 1 == 1) && K p i then !prev else prev

/-- At parameter `t = 0`, `xorSwapChoice K p 0 i = false` for all `p` and `i`. -/
theorem xorSwapChoice_zero (K : Nat → Nat → Bool) (p i : Nat) :
    xorSwapChoice K p 0 i = false := by
  induction p with
  | zero => rfl
  | succ p ih =>
    dsimp [xorSwapChoice]
    rw [Nat.zero_shiftRight, ih]
    rfl

/-- If each chord region `K k` (`k < p`) is supported on the ring (`K k i = true → i < c.ringSize`)
    and is constant on every `equiv_ab` and `equiv_cd` class, then `xorSwapChoice K p t` is a valid
    boundary Kempe swap choice for every `t`. -/
theorem xorSwapChoice_valid (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (K : Nat → Nat → Bool) (p : Nat)
    (hK_ring : ∀ k < p, ∀ i, K k i = true → i < c.ringSize)
    (hK_ab : ∀ k < p, ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_ab i j → K k i = K k j)
    (hK_cd : ∀ k < p, ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_cd i j → K k i = K k j)
    (t : Nat) :
    IsValidSwapChoice c b θ equiv_ab equiv_cd (xorSwapChoice K p t) := by
  induction p with
  | zero =>
    refine ⟨fun _ h => by contradiction, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | succ p ih =>
    have h_prev := ih
      (fun k hk => hK_ring k (Nat.lt_succ_of_lt hk))
      (fun k hk => hK_ab k (Nat.lt_succ_of_lt hk))
      (fun k hk => hK_cd k (Nat.lt_succ_of_lt hk))
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      dsimp [xorSwapChoice] at hi
      cases h_cond : (((t >>> p) &&& 1 == 1) && K p i)
      · rw [h_cond] at hi
        exact h_prev.ring_only i hi
      · rw [Bool.and_eq_true] at h_cond
        exact hK_ring p (Nat.lt_succ_self p) i h_cond.2
    · intro i hi j hj hab
      dsimp [xorSwapChoice]
      have h_prev_eq := h_prev.respects_ab i hi j hj hab
      have hK_eq := hK_ab p (Nat.lt_succ_self p) i hi j hj hab
      rw [h_prev_eq, hK_eq]
    · intro i hi j hj hcd
      dsimp [xorSwapChoice]
      have h_prev_eq := h_prev.respects_cd i hi j hj hcd
      have hK_eq := hK_cd p (Nat.lt_succ_self p) i hi j hj hcd
      rw [h_prev_eq, hK_eq]

end Soundness
end Math
