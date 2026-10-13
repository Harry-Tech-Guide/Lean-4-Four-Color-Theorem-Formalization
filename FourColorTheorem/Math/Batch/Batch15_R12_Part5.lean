import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 15: Ring 12 (Part 5)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 153, 154, 155, 156, 157, 172.
-/

/-- The 6 ring-12 configuration indices certified in Batch 15. -/
def batch15_indices : List Nat :=
  [153, 154, 155, 156, 157, 172]

/-- Unified in-kernel certification for Batch 15 (Ring 12, Part 5). -/
theorem cert_batch15_r12 : checkRingBatch 12 batch15_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_153_d_red : checkIdxFast (buildSMData 12 sharedPow3) 153 = true :=
  certified_of_batch 12 batch15_indices cert_batch15_r12 153 (by decide)

theorem cert_config_154_d_red : checkIdxFast (buildSMData 12 sharedPow3) 154 = true :=
  certified_of_batch 12 batch15_indices cert_batch15_r12 154 (by decide)

theorem cert_config_155_d_red : checkIdxFast (buildSMData 12 sharedPow3) 155 = true :=
  certified_of_batch 12 batch15_indices cert_batch15_r12 155 (by decide)

theorem cert_config_156_d_red : checkIdxFast (buildSMData 12 sharedPow3) 156 = true :=
  certified_of_batch 12 batch15_indices cert_batch15_r12 156 (by decide)

theorem cert_config_157_d_red : checkIdxFast (buildSMData 12 sharedPow3) 157 = true :=
  certified_of_batch 12 batch15_indices cert_batch15_r12 157 (by decide)

theorem cert_config_172_d_red : checkIdxFast (buildSMData 12 sharedPow3) 172 = true :=
  certified_of_batch 12 batch15_indices cert_batch15_r12 172 (by decide)

end Batch
end Math
