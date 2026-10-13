import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 19: Ring 12 (Part 9)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 375, 382, 386, 387, 388, 389.
-/

/-- The 6 ring-12 configuration indices certified in Batch 19. -/
def batch19_indices : List Nat :=
  [375, 382, 386, 387, 388, 389]

/-- Unified in-kernel certification for Batch 19 (Ring 12, Part 9). -/
theorem cert_batch19_r12 : checkRingBatch 12 batch19_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_375_d_red : checkIdxFast (buildSMData 12 sharedPow3) 375 = true :=
  certified_of_batch 12 batch19_indices cert_batch19_r12 375 (by decide)

theorem cert_config_382_d_red : checkIdxFast (buildSMData 12 sharedPow3) 382 = true :=
  certified_of_batch 12 batch19_indices cert_batch19_r12 382 (by decide)

theorem cert_config_386_d_red : checkIdxFast (buildSMData 12 sharedPow3) 386 = true :=
  certified_of_batch 12 batch19_indices cert_batch19_r12 386 (by decide)

theorem cert_config_387_d_red : checkIdxFast (buildSMData 12 sharedPow3) 387 = true :=
  certified_of_batch 12 batch19_indices cert_batch19_r12 387 (by decide)

theorem cert_config_388_d_red : checkIdxFast (buildSMData 12 sharedPow3) 388 = true :=
  certified_of_batch 12 batch19_indices cert_batch19_r12 388 (by decide)

theorem cert_config_389_d_red : checkIdxFast (buildSMData 12 sharedPow3) 389 = true :=
  certified_of_batch 12 batch19_indices cert_batch19_r12 389 (by decide)

end Batch
end Math
