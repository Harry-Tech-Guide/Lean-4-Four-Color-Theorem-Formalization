import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 36: Ring 13 (Part 10)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 536, 564, 565, 589.
-/

/-- The 4 ring-13 configuration indices certified in Batch 36. -/
def batch36_indices : List Nat :=
  [536, 564, 565, 589]

/-- Unified in-kernel certification for Batch 36 (Ring 13, Part 10). -/
theorem cert_batch36_r13 : checkRingBatch13 batch36_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_536_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 536 = true :=
  certified_of_batch13 batch36_indices cert_batch36_r13 536 (by decide)

theorem cert_config_564_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 564 = true :=
  certified_of_batch13 batch36_indices cert_batch36_r13 564 (by decide)

theorem cert_config_565_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 565 = true :=
  certified_of_batch13 batch36_indices cert_batch36_r13 565 (by decide)

theorem cert_config_589_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 589 = true :=
  certified_of_batch13 batch36_indices cert_batch36_r13 589 (by decide)

end Batch
end Math
