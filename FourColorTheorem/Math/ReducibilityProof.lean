
import FourColorTheorem.Math.Configuration
import FourColorTheorem.Math.EmptyLiveSet

-- Step 12: The Grand Reducibility Link

namespace Hypermap

variable (H : Hypermap) (k : Nat) (R : Ring H k)

/-- Theorem: If the C-reduction algorithm empties the LiveSet, 
    the configuration is strictly mathematically Reducible! -/
theorem reducibility_from_empty_liveset (LiveSet : (Fin k → Color) → Prop) 
  (hEmpty : IsEmptyLiveSet k LiveSet)
  (hExt : ∀ c, ¬ LiveSet c → IsExtensiblePure H k R c) : 
  ∀ cols, IsExtensiblePure H k R cols := 
  empty_liveset_implies_reducible H k R LiveSet hEmpty hExt

end Hypermap
