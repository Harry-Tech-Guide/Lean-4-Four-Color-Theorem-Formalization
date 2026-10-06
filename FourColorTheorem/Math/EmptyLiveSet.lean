
import FourColorTheorem.Math.KempeConsistencyTheorem

-- Step 11: The Empty LiveSet Theorem

namespace Hypermap

variable (H : Hypermap) (k : Nat) (R : Ring H k)

/-- If the C-reduction algorithm successfully terminates and outputs true, 
    it means the fixed point iteration completely emptied the LiveSet. -/
def IsEmptyLiveSet (LiveSet : (Fin k → Color) → Prop) : Prop :=
  ∀ cols, ¬ LiveSet cols

/-- The Final Reducibility Bridge:
    If the LiveSet is empty, and everything outside the LiveSet is extensible,
    then EVERY valid ring coloring is extensible! 
    This perfectly satisfies our definition of IsReducible! -/
theorem empty_liveset_implies_reducible (LiveSet : (Fin k → Color) → Prop) :
  IsEmptyLiveSet k LiveSet → 
  (∀ c, ¬ LiveSet c → IsExtensiblePure H k R c) → 
  ∀ cols, IsExtensiblePure H k R cols := by
  intro hEmpty hExt cols
  -- Since the LiveSet is empty, cols is definitely not in it.
  have hNotLive : ¬ LiveSet cols := hEmpty cols
  -- Thus, by the extensibility hypothesis, cols is extensible.
  exact hExt cols hNotLive

end Hypermap
