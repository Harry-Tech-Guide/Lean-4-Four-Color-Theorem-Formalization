import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 18: Ring 12 (Part 8)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 359, 360, 363, 366, 369, 374.
-/

/-- The 6 ring-12 configuration indices certified in Batch 18. -/
def batch18_indices : List Nat :=
  [359, 360, 363, 366, 369, 374]

/-- Unified in-kernel certification for Batch 18 (Ring 12, Part 8). -/
theorem cert_batch18_r12 : checkRingBatch 12 batch18_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_359_d_red : checkIdxFast (buildSMData 12 sharedPow3) 359 = true :=
  certified_of_batch 12 batch18_indices cert_batch18_r12 359 (by decide)

theorem cert_config_360_d_red : checkIdxFast (buildSMData 12 sharedPow3) 360 = true :=
  certified_of_batch 12 batch18_indices cert_batch18_r12 360 (by decide)

theorem cert_config_363_d_red : checkIdxFast (buildSMData 12 sharedPow3) 363 = true :=
  certified_of_batch 12 batch18_indices cert_batch18_r12 363 (by decide)

theorem cert_config_366_d_red : checkIdxFast (buildSMData 12 sharedPow3) 366 = true :=
  certified_of_batch 12 batch18_indices cert_batch18_r12 366 (by decide)

theorem cert_config_369_d_red : checkIdxFast (buildSMData 12 sharedPow3) 369 = true :=
  certified_of_batch 12 batch18_indices cert_batch18_r12 369 (by decide)

theorem cert_config_374_d_red : checkIdxFast (buildSMData 12 sharedPow3) 374 = true :=
  certified_of_batch 12 batch18_indices cert_batch18_r12 374 (by decide)

end Batch
end Math
