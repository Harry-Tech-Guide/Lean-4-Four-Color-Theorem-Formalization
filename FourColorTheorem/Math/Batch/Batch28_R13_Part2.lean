import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 28: Ring 13 (Part 2)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 106, 107, 167, 170.
-/

/-- The 4 ring-13 configuration indices certified in Batch 28. -/
def batch28_indices : List Nat :=
  [106, 107, 167, 170]

/-- Unified in-kernel certification for Batch 28 (Ring 13, Part 2). -/
theorem cert_batch28_r13 : checkRingBatch 13 batch28_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_106_d_red : checkIdxFast (buildSMData 13 sharedPow3) 106 = true :=
  certified_of_batch 13 batch28_indices cert_batch28_r13 106 (by decide)

theorem cert_config_107_d_red : checkIdxFast (buildSMData 13 sharedPow3) 107 = true :=
  certified_of_batch 13 batch28_indices cert_batch28_r13 107 (by decide)

theorem cert_config_167_d_red : checkIdxFast (buildSMData 13 sharedPow3) 167 = true :=
  certified_of_batch 13 batch28_indices cert_batch28_r13 167 (by decide)

theorem cert_config_170_d_red : checkIdxFast (buildSMData 13 sharedPow3) 170 = true :=
  certified_of_batch 13 batch28_indices cert_batch28_r13 170 (by decide)

end Batch
end Math
