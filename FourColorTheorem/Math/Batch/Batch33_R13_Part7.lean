import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 33: Ring 13 (Part 7)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 472, 482, 491, 511.
-/

/-- The 4 ring-13 configuration indices certified in Batch 33. -/
def batch33_indices : List Nat :=
  [472, 482, 491, 511]

/-- Unified in-kernel certification for Batch 33 (Ring 13, Part 7). -/
theorem cert_batch33_r13 : checkRingBatch 13 batch33_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_472_d_red : checkIdxFast (buildSMData 13 sharedPow3) 472 = true :=
  certified_of_batch 13 batch33_indices cert_batch33_r13 472 (by decide)

theorem cert_config_482_d_red : checkIdxFast (buildSMData 13 sharedPow3) 482 = true :=
  certified_of_batch 13 batch33_indices cert_batch33_r13 482 (by decide)

theorem cert_config_491_d_red : checkIdxFast (buildSMData 13 sharedPow3) 491 = true :=
  certified_of_batch 13 batch33_indices cert_batch33_r13 491 (by decide)

theorem cert_config_511_d_red : checkIdxFast (buildSMData 13 sharedPow3) 511 = true :=
  certified_of_batch 13 batch33_indices cert_batch33_r13 511 (by decide)

end Batch
end Math
