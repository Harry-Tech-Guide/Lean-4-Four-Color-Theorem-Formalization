
import FourColorTheorem.Math.KempeConsistencyTheorem

namespace Hypermap

variable (H : Hypermap) (k : Nat) (R : Ring H k)

def IsKempeEscapable (LiveSet : (Fin k → Color) → Prop) (cols : Fin k → Color) : Prop :=
  ∃ (a b : Color), a ≠ b ∧ 
    ∀ equiv : Fin k → Fin k → Prop, 
      IsValidRingPartition k cols a b equiv → 
      ∃ swapSet : Fin k → Bool, ValidSwapChoice k equiv swapSet ∧ 
        ¬ LiveSet (swappedCols k cols a b swapSet)

axiom minimal_counterexample_exterior_exists (cols : Fin k → Color) (a b : Color) :
  ∃ equiv : Fin k → Fin k → Prop, IsValidRingPartition k cols a b equiv

axiom kempe_swap_reversibility (cols : Fin k → Color) (a b : Color) (equiv : Fin k → Fin k → Prop) (swapSet : Fin k → Bool) :
  IsValidRingPartition k cols a b equiv → 
  ValidSwapChoice k equiv swapSet → 
  IsExtensiblePure H k R (swappedCols k cols a b swapSet) → 
  IsExtensiblePure H k R cols

theorem kempe_consistency_pure (LiveSet : (Fin k → Color) → Prop) (cols : Fin k → Color) :
  (∀ c', ¬ LiveSet c' → IsExtensiblePure H k R c') → 
  IsKempeEscapable k LiveSet cols →             
  IsExtensiblePure H k R cols := by
  intro hExt hEscapable
  rcases hEscapable with ⟨a, ⟨b, ⟨hab, hEquiv⟩⟩⟩
  have ⟨equiv, hValidEquiv⟩ := minimal_counterexample_exterior_exists k cols a b
  have ⟨swapSet, ⟨hValidSwap, hNotLive⟩⟩ := hEquiv equiv hValidEquiv
  have hExtSwapped := hExt (swappedCols k cols a b swapSet) hNotLive
  exact kempe_swap_reversibility H k R cols a b equiv swapSet hValidEquiv hValidSwap hExtSwapped

end Hypermap
