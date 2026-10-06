
import FourColorTheorem.Math.KempeConsistency

-- Step 9: The Kempe Consistency Theorem

namespace Hypermap

variable (H : Hypermap) (k : Nat) (R : Ring H k)

/-- A mathematically pure definition of Extensibility that avoids Array indexing bounds. -/
def IsExtensiblePure (cols : Fin k → Color) : Prop :=
  ∃ (vc : VertexColoring H), ∀ i : Fin k, 
    vc.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt)) = cols i

/-- A ring coloring c is Kempe-Trapped inside a set of bad colorings LiveSet 
    if it is impossible to escape the LiveSet via Kempe swaps. 
    Specifically, for every color pair (a, b), there exists a valid planar exterior matching, 
    such that EVERY valid swap over that matching results in a coloring that is STILL in the LiveSet. -/
def IsKempeTrapped (LiveSet : (Fin k → Color) → Prop) (c : VertexColoring H) : Prop :=
  ∀ (a b : Color), a ≠ b → 
    ∃ equiv : Fin k → Fin k → Prop, 
      IsValidExteriorKempePartition H k R c a b equiv ∧
      ∀ swapSet : Fin k → Bool, ValidSwapChoice k equiv swapSet → 
        LiveSet (swappedRingColoring H k R c a b swapSet)

/-- The Fundamental Kempe Consistency Theorem:
    If a coloring is NOT Kempe-Trapped inside the LiveSet, and we know that every coloring 
    outside the LiveSet is extensible to the interior, then the coloring itself must be extensible.
    
    Proof sketch: Since it is not trapped, there exists a color pair (a,b) where for EVERY 
    planar exterior matching, there is a swap combination that escapes the LiveSet. 
    Whatever the actual exterior of our map looks like, it forms SOME valid planar matching. 
    We apply the guaranteed escaping swap combination for that exact matching. The resulting 
    coloring is outside the LiveSet, meaning it is extensible. Thus, by swapping back, 
    the original coloring is extensible. -/
theorem kempe_consistency (LiveSet : (Fin k → Color) → Prop) (c : VertexColoring H) :
  (∀ c', ¬ LiveSet c' → IsExtensiblePure H k R c') → 
  ¬ IsKempeTrapped H k R LiveSet c →             
  IsExtensiblePure H k R (fun i => c.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt))) := by
  -- This requires the full formal proof of exterior swap validity which spans thousands of lines.
  sorry

end Hypermap
