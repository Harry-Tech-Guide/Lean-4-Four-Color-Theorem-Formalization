import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 30: Ring 13 (Part 4)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 219, 271, 272, 273.
-/

/-- The 4 ring-13 configuration indices certified in Batch 30. -/
def batch30_indices : List Nat :=
  [219, 271, 272, 273]

/-- Unified in-kernel certification for Batch 30 (Ring 13, Part 4). -/
theorem cert_batch30_r13 : checkRingBatch13 batch30_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_219_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 219 = true :=
  certified_of_batch13 batch30_indices cert_batch30_r13 219 (by decide)

theorem cert_config_271_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 271 = true :=
  certified_of_batch13 batch30_indices cert_batch30_r13 271 (by decide)

theorem cert_config_272_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 272 = true :=
  certified_of_batch13 batch30_indices cert_batch30_r13 272 (by decide)

theorem cert_config_273_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 273 = true :=
  certified_of_batch13 batch30_indices cert_batch30_r13 273 (by decide)

end Batch
end Math
