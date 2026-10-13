import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 14: Ring 12 (Part 4)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 99, 108, 132, 146, 149, 150.
-/

/-- The 6 ring-12 configuration indices certified in Batch 14. -/
def batch14_indices : List Nat :=
  [99, 108, 132, 146, 149, 150]

/-- Unified in-kernel certification for Batch 14 (Ring 12, Part 4). -/
theorem cert_batch14_r12 : checkRingBatch 12 batch14_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_99_d_red : checkIdxFast (buildSMData 12 sharedPow3) 99 = true :=
  certified_of_batch 12 batch14_indices cert_batch14_r12 99 (by decide)

theorem cert_config_108_d_red : checkIdxFast (buildSMData 12 sharedPow3) 108 = true :=
  certified_of_batch 12 batch14_indices cert_batch14_r12 108 (by decide)

theorem cert_config_132_d_red : checkIdxFast (buildSMData 12 sharedPow3) 132 = true :=
  certified_of_batch 12 batch14_indices cert_batch14_r12 132 (by decide)

theorem cert_config_146_d_red : checkIdxFast (buildSMData 12 sharedPow3) 146 = true :=
  certified_of_batch 12 batch14_indices cert_batch14_r12 146 (by decide)

theorem cert_config_149_d_red : checkIdxFast (buildSMData 12 sharedPow3) 149 = true :=
  certified_of_batch 12 batch14_indices cert_batch14_r12 149 (by decide)

theorem cert_config_150_d_red : checkIdxFast (buildSMData 12 sharedPow3) 150 = true :=
  certified_of_batch 12 batch14_indices cert_batch14_r12 150 (by decide)

end Batch
end Math
