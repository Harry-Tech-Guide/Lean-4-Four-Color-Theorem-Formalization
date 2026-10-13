import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 32: Ring 13 (Part 6)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 395, 399, 438, 471.
-/

/-- The 4 ring-13 configuration indices certified in Batch 32. -/
def batch32_indices : List Nat :=
  [395, 399, 438, 471]

/-- Unified in-kernel certification for Batch 32 (Ring 13, Part 6). -/
theorem cert_batch32_r13 : checkRingBatch 13 batch32_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_395_d_red : checkIdxFast (buildSMData 13 sharedPow3) 395 = true :=
  certified_of_batch 13 batch32_indices cert_batch32_r13 395 (by decide)

theorem cert_config_399_d_red : checkIdxFast (buildSMData 13 sharedPow3) 399 = true :=
  certified_of_batch 13 batch32_indices cert_batch32_r13 399 (by decide)

theorem cert_config_438_d_red : checkIdxFast (buildSMData 13 sharedPow3) 438 = true :=
  certified_of_batch 13 batch32_indices cert_batch32_r13 438 (by decide)

theorem cert_config_471_d_red : checkIdxFast (buildSMData 13 sharedPow3) 471 = true :=
  certified_of_batch 13 batch32_indices cert_batch32_r13 471 (by decide)

end Batch
end Math
