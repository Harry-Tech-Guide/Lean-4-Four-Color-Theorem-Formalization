import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 11: Ring 12 (Part 1)

This module certifies the D-reducibility of the first 5 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 21, 64, 66, 67, 68.
-/

/-- The 5 ring-12 configuration indices certified in Batch 11. -/
def batch11_indices : List Nat :=
  [21, 64, 66, 67, 68]

/-- Unified in-kernel certification for Batch 11 (Ring 12, Part 1). -/
theorem cert_batch11_r12 : checkRingBatch 12 batch11_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_21_d_red : checkIdxFast (buildSMData 12 sharedPow3) 21 = true :=
  certified_of_batch 12 batch11_indices cert_batch11_r12 21 (by decide)

theorem cert_config_64_d_red : checkIdxFast (buildSMData 12 sharedPow3) 64 = true :=
  certified_of_batch 12 batch11_indices cert_batch11_r12 64 (by decide)

theorem cert_config_66_d_red : checkIdxFast (buildSMData 12 sharedPow3) 66 = true :=
  certified_of_batch 12 batch11_indices cert_batch11_r12 66 (by decide)

theorem cert_config_67_d_red : checkIdxFast (buildSMData 12 sharedPow3) 67 = true :=
  certified_of_batch 12 batch11_indices cert_batch11_r12 67 (by decide)

theorem cert_config_68_d_red : checkIdxFast (buildSMData 12 sharedPow3) 68 = true :=
  certified_of_batch 12 batch11_indices cert_batch11_r12 68 (by decide)

end Batch
end Math
