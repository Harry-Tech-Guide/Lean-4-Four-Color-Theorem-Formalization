import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 20: Ring 12 (Part 10)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 390, 391, 392, 405, 406, 407.
-/

/-- The 6 ring-12 configuration indices certified in Batch 20. -/
def batch20_indices : List Nat :=
  [390, 391, 392, 405, 406, 407]

/-- Unified in-kernel certification for Batch 20 (Ring 12, Part 10). -/
theorem cert_batch20_r12 : checkRingBatch 12 batch20_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_390_d_red : checkIdxFast (buildSMData 12 sharedPow3) 390 = true :=
  certified_of_batch 12 batch20_indices cert_batch20_r12 390 (by decide)

theorem cert_config_391_d_red : checkIdxFast (buildSMData 12 sharedPow3) 391 = true :=
  certified_of_batch 12 batch20_indices cert_batch20_r12 391 (by decide)

theorem cert_config_392_d_red : checkIdxFast (buildSMData 12 sharedPow3) 392 = true :=
  certified_of_batch 12 batch20_indices cert_batch20_r12 392 (by decide)

theorem cert_config_405_d_red : checkIdxFast (buildSMData 12 sharedPow3) 405 = true :=
  certified_of_batch 12 batch20_indices cert_batch20_r12 405 (by decide)

theorem cert_config_406_d_red : checkIdxFast (buildSMData 12 sharedPow3) 406 = true :=
  certified_of_batch 12 batch20_indices cert_batch20_r12 406 (by decide)

theorem cert_config_407_d_red : checkIdxFast (buildSMData 12 sharedPow3) 407 = true :=
  certified_of_batch 12 batch20_indices cert_batch20_r12 407 (by decide)

end Batch
end Math
