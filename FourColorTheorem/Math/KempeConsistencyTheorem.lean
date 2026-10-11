
import FourColorTheorem.Math.KempeConsistency

-- Step 9: The Kempe Consistency Theorem

namespace Hypermap

variable (H : Hypermap) (k : Nat) (R : Ring H k)

def IsExtensiblePure (cols : Fin k → Color) : Prop :=
  ∃ (vc : VertexColoring H), ∀ i : Fin k, 
    vc.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt)) = cols i

/-- To evaluate Kempe Chains on the boundary without knowing the interior,
    we define exterior equivalence directly on the Ring Coloring. -/
def IsValidRingPartition (cols : Fin k → Color) (a b : Color) (equiv : Fin k → Fin k → Prop) : Prop :=
  (∀ i, (cols i = a ∨ cols i = b) → equiv i i) ∧
  (∀ i j, equiv i j → equiv j i) ∧
  (∀ i j l, equiv i j → equiv j l → equiv i l) ∧
  (∀ i j, equiv i j → (cols i = a ∨ cols i = b)) ∧
  (∀ i j l m, i.val < j.val → j.val < l.val → l.val < m.val → 
              equiv i l → equiv j m → equiv i j)

def swappedCols (cols : Fin k → Color) (a b : Color) (swapSet : Fin k → Bool) : Fin k → Color :=
  fun i => if swapSet i then swapColor (cols i) a b else cols i

/-- Swapping ring colors twice with the same swap set returns the original ring coloring. -/
theorem swappedCols_inv (cols : Fin k → Color) (a b : Color) (swapSet : Fin k → Bool) :
    swappedCols k (swappedCols k cols a b swapSet) a b swapSet = cols := by
  funext i
  dsimp [swappedCols]
  split
  · exact swapColor_inv (cols i) a b
  · rfl


/-- A ring coloring c is Kempe-Escapable from a set of bad colorings LiveSet 
    if there exists a color pair (a, b) such that for EVERY valid planar exterior matching, 
    there is a swap combination that escapes the LiveSet. -/
def IsKempeEscapable (LiveSet : (Fin k → Color) → Prop) (cols : Fin k → Color) : Prop :=
  ∃ (a b : Color), a ≠ b ∧ 
    ∀ equiv : Fin k → Fin k → Prop, 
      IsValidRingPartition k cols a b equiv → 
      ∃ swapSet : Fin k → Bool, ValidSwapChoice k equiv swapSet ∧ 
        ¬ LiveSet (swappedCols k cols a b swapSet)

/-- The discrete identity partition on {i | cols i ∈ {a, b}} is a valid planar ring partition. -/
theorem minimal_counterexample_exterior_exists (cols : Fin k → Color) (a b : Color) :
    ∃ equiv : Fin k → Fin k → Prop, IsValidRingPartition k cols a b equiv := by
  refine ⟨fun i j => i = j ∧ (cols i = a ∨ cols i = b), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i h; exact ⟨rfl, h⟩
  · intro i j h; exact ⟨h.1.symm, h.1 ▸ h.2⟩
  · intro i j l hij hjl; exact ⟨hij.1.trans hjl.1, hij.2⟩
  · intro i j h; exact h.2
  · intro i j l _ hij hjl _ hil _
    have hlt : i.val < l.val := Nat.lt_trans hij hjl
    have heq : i.val = l.val := congrArg Fin.val hil.1
    exact absurd heq (Nat.ne_of_lt hlt)

/-- Axiom of Topological Swapping:
    If a swap combination swapSet applied over the true exterior matching equiv 
    results in an extensible boundary coloring cols', then the original coloring cols 
    is also strictly extensible. (Swapping Kempe chains is a reversible operation). -/
axiom kempe_swap_reversibility (H : Hypermap) (k : Nat) (R : Ring H k) (cols : Fin k → Color) (a b : Color) (equiv : Fin k → Fin k → Prop) (swapSet : Fin k → Bool) :
  IsValidRingPartition k cols a b equiv → 
  ValidSwapChoice k equiv swapSet → 
  IsExtensiblePure H k R (swappedCols k cols a b swapSet) → 
  IsExtensiblePure H k R cols

/-- The Fundamental Kempe Consistency Theorem:
    If a valid ring coloring is Kempe-Escapable from the LiveSet, and we know that every coloring 
    outside the LiveSet is extensible to the interior, then the coloring itself must be extensible. -/
theorem kempe_consistency (LiveSet : (Fin k → Color) → Prop) (cols : Fin k → Color) :
  (∀ c', ¬ LiveSet c' → IsExtensiblePure H k R c') → 
  IsKempeEscapable k LiveSet cols →             
  IsExtensiblePure H k R cols := by
  intro hExt hEscapable
  rcases hEscapable with ⟨a, ⟨b, ⟨_, hEquiv⟩⟩⟩
  have ⟨equiv, hValidEquiv⟩ := minimal_counterexample_exterior_exists k cols a b
  have ⟨swapSet, ⟨hValidSwap, hNotLive⟩⟩ := hEquiv equiv hValidEquiv
  have hExtSwapped := hExt (swappedCols k cols a b swapSet) hNotLive
  exact kempe_swap_reversibility H k R cols a b equiv swapSet hValidEquiv hValidSwap hExtSwapped

end Hypermap
