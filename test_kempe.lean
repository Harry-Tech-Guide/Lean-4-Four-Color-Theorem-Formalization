import FourColorTheorem.Math.KempeConsistencyTheorem

namespace Hypermap

variable (H : Hypermap) (k : Nat) (R : Ring H k)

theorem test_kempe_consistency_pure (LiveSet : (Fin k → Color) → Prop) (cols : Fin k → Color) :
  KempeSwapReversible H k R cols →
  (∀ c', ¬ LiveSet c' → IsExtensiblePure H k R c') → 
  IsKempeEscapable k LiveSet cols →             
  IsExtensiblePure H k R cols :=
  kempe_consistency H k R LiveSet cols

end Hypermap
