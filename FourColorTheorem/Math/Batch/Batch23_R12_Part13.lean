import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 23: Ring 12 (Part 13)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 481, 483, 484, 490, 522, 555.
-/

/-- The 6 ring-12 configuration indices certified in Batch 23. -/
def batch23_indices : List Nat :=
  [481, 483, 484, 490, 522, 555]

/-- Unified in-kernel certification for Batch 23 (Ring 12, Part 13). -/
theorem cert_batch23_r12 : checkRingBatch 12 batch23_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_481_d_red : checkIdxFast (buildSMData 12 sharedPow3) 481 = true :=
  certified_of_batch 12 batch23_indices cert_batch23_r12 481 (by decide)

theorem cert_config_483_d_red : checkIdxFast (buildSMData 12 sharedPow3) 483 = true :=
  certified_of_batch 12 batch23_indices cert_batch23_r12 483 (by decide)

theorem cert_config_484_d_red : checkIdxFast (buildSMData 12 sharedPow3) 484 = true :=
  certified_of_batch 12 batch23_indices cert_batch23_r12 484 (by decide)

theorem cert_config_490_d_red : checkIdxFast (buildSMData 12 sharedPow3) 490 = true :=
  certified_of_batch 12 batch23_indices cert_batch23_r12 490 (by decide)

theorem cert_config_522_d_red : checkIdxFast (buildSMData 12 sharedPow3) 522 = true :=
  certified_of_batch 12 batch23_indices cert_batch23_r12 522 (by decide)

theorem cert_config_555_d_red : checkIdxFast (buildSMData 12 sharedPow3) 555 = true :=
  certified_of_batch 12 batch23_indices cert_batch23_r12 555 (by decide)

end Batch
end Math
