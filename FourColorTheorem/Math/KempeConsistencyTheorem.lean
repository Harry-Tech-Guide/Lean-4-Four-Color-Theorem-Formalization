
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
  (∀ i, equiv i i) ∧
  (∀ i j, equiv i j → equiv j i) ∧
  (∀ i j l, equiv i j → equiv j l → equiv i l) ∧
  (∀ i j, equiv i j → (cols i = a ∨ cols i = b)) ∧
  (∀ i j l m, i.val < j.val → j.val < l.val → l.val < m.val → 
              equiv i l → equiv j m → equiv i j)

def swappedCols (cols : Fin k → Color) (a b : Color) (swapSet : Fin k → Bool) : Fin k → Color :=
  fun i => if swapSet i then swapColor (cols i) a b else cols i

def IsKempeTrapped (LiveSet : (Fin k → Color) → Prop) (cols : Fin k → Color) : Prop :=
  ∀ (a b : Color), a ≠ b → 
    ∃ equiv : Fin k → Fin k → Prop, 
      IsValidRingPartition k cols a b equiv ∧
      ∀ swapSet : Fin k → Bool, ValidSwapChoice k equiv swapSet → 
        LiveSet (swappedCols k cols a b swapSet)

/-- The Fundamental Kempe Consistency Theorem:
    If a valid ring coloring is NOT Kempe-Trapped inside the LiveSet, and we know that every coloring 
    outside the LiveSet is extensible to the interior, then the coloring itself must be extensible. -/
theorem kempe_consistency (LiveSet : (Fin k → Color) → Prop) (cols : Fin k → Color) :
  (∀ c', ¬ LiveSet c' → IsExtensiblePure H k R c') → 
  ¬ IsKempeTrapped k LiveSet cols →             
  IsExtensiblePure H k R cols := by
  sorry

end Hypermap
