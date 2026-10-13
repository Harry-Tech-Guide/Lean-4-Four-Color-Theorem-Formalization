import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 35: Ring 13 (Part 9)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 525, 526, 528, 529.
-/

/-- The 4 ring-13 configuration indices certified in Batch 35. -/
def batch35_indices : List Nat :=
  [525, 526, 528, 529]

/-- Unified in-kernel certification for Batch 35 (Ring 13, Part 9). -/
theorem cert_batch35_r13 : checkRingBatch 13 batch35_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_525_d_red : checkIdxFast (buildSMData 13 sharedPow3) 525 = true :=
  certified_of_batch 13 batch35_indices cert_batch35_r13 525 (by decide)

theorem cert_config_526_d_red : checkIdxFast (buildSMData 13 sharedPow3) 526 = true :=
  certified_of_batch 13 batch35_indices cert_batch35_r13 526 (by decide)

theorem cert_config_528_d_red : checkIdxFast (buildSMData 13 sharedPow3) 528 = true :=
  certified_of_batch 13 batch35_indices cert_batch35_r13 528 (by decide)

theorem cert_config_529_d_red : checkIdxFast (buildSMData 13 sharedPow3) 529 = true :=
  certified_of_batch 13 batch35_indices cert_batch35_r13 529 (by decide)

end Batch
end Math
