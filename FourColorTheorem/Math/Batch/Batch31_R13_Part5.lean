import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 31: Ring 13 (Part 5)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 275, 383, 385, 394.
-/

/-- The 4 ring-13 configuration indices certified in Batch 31. -/
def batch31_indices : List Nat :=
  [275, 383, 385, 394]

/-- Unified in-kernel certification for Batch 31 (Ring 13, Part 5). -/
theorem cert_batch31_r13 : checkRingBatch13 batch31_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_275_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 275 = true :=
  certified_of_batch13 batch31_indices cert_batch31_r13 275 (by decide)

theorem cert_config_383_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 383 = true :=
  certified_of_batch13 batch31_indices cert_batch31_r13 383 (by decide)

theorem cert_config_385_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 385 = true :=
  certified_of_batch13 batch31_indices cert_batch31_r13 385 (by decide)

theorem cert_config_394_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 394 = true :=
  certified_of_batch13 batch31_indices cert_batch31_r13 394 (by decide)

end Batch
end Math
