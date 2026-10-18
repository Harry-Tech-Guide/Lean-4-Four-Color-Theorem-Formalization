import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.FastReducer
import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Soundness

open FastReducer
open Batch

set_option linter.unusedVariables false

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
def boundaryTrace (c : Configuration) (b : BoundaryColoring c) (pow3 : Array Nat) : Nat := Id.run do
  let r := c.ringSize
  let mut idx := 0
  for i in [0:r] do
    let nxt := (i + 1) % r
    let diff := (b i).toNat ^^^ (b nxt).toNat
    let d_i := if diff > 0 then diff - 1 else 0
    idx := idx + d_i * pow3.getD i 0
  return idx

/-- The trace index of the t-th fitting coloring of a signed matching `sm`.
    Bit k of parameter t selects delta `a[k]` (bit = 0) or delta `b[k]` (bit = 1). -/
def smFitIndex (sm : SMData) (t : Nat) : Nat := Id.run do
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
      boundaryTrace c (boundaryKempeSwap c b θ (S t)) pow3 = smFitIndex sm t)

/-- Full Lemma (a) Representation Property (RSST / Gonthier):
    For every configuration `c`, valid boundary coloring `b`, color pairing `θ`, and
    joint planar ring partition `(equiv_ab, equiv_cd)`, there exists an enumerated
    balanced signed matching `sm ∈ sms` that faithfully represents the partition. -/
def FullRepresentationHypothesis (c : Configuration) (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  ∀ (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop),
    IsValidBoundaryColoring c b →
    IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
    ∃ (sm : SMData), sm ∈ sms.data ∧
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
    (h_trace : boundaryTrace c b pow3 = smFitIndex sm 0) :
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

end Soundness
end Math
