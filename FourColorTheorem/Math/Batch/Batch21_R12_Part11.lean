import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 21: Ring 12 (Part 11)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 408, 413, 415, 416, 417, 419.
-/

/-- The 6 ring-12 configuration indices certified in Batch 21. -/
def batch21_indices : List Nat :=
  [408, 413, 415, 416, 417, 419]

/-- Unified in-kernel certification for Batch 21 (Ring 12, Part 11). -/
theorem cert_batch21_r12 : checkRingBatch 12 batch21_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_408_d_red : checkIdxFast (buildSMData 12 sharedPow3) 408 = true :=
  certified_of_batch 12 batch21_indices cert_batch21_r12 408 (by decide)

theorem cert_config_413_d_red : checkIdxFast (buildSMData 12 sharedPow3) 413 = true :=
  certified_of_batch 12 batch21_indices cert_batch21_r12 413 (by decide)

theorem cert_config_415_d_red : checkIdxFast (buildSMData 12 sharedPow3) 415 = true :=
  certified_of_batch 12 batch21_indices cert_batch21_r12 415 (by decide)

theorem cert_config_416_d_red : checkIdxFast (buildSMData 12 sharedPow3) 416 = true :=
  certified_of_batch 12 batch21_indices cert_batch21_r12 416 (by decide)

theorem cert_config_417_d_red : checkIdxFast (buildSMData 12 sharedPow3) 417 = true :=
  certified_of_batch 12 batch21_indices cert_batch21_r12 417 (by decide)

theorem cert_config_419_d_red : checkIdxFast (buildSMData 12 sharedPow3) 419 = true :=
  certified_of_batch 12 batch21_indices cert_batch21_r12 419 (by decide)

end Batch
end Math
