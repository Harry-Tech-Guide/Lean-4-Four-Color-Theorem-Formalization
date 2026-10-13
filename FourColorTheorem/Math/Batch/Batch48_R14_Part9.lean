import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 48: Ring 14 (Part 9)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 397, 400.
-/

/-- The 2 ring-14 configuration indices certified in Batch 48. -/
def batch48_indices : List Nat :=
  [397, 400]

/-- Unified in-kernel certification for Batch 48 (Ring 14, Part 9). -/
theorem cert_batch48_r14 : checkRingBatch14 batch48_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_397_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 397 = true :=
  certified_of_batch14 batch48_indices cert_batch48_r14 397 (by decide)

theorem cert_config_400_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 400 = true :=
  certified_of_batch14 batch48_indices cert_batch48_r14 400 (by decide)

end Batch
end Math
