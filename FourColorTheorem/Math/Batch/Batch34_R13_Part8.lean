import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 34: Ring 13 (Part 8)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 513, 514, 517, 524.
-/

/-- The 4 ring-13 configuration indices certified in Batch 34. -/
def batch34_indices : List Nat :=
  [513, 514, 517, 524]

/-- Unified in-kernel certification for Batch 34 (Ring 13, Part 8). -/
theorem cert_batch34_r13 : checkRingBatch 13 batch34_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_513_d_red : checkIdxFast (buildSMData 13 sharedPow3) 513 = true :=
  certified_of_batch 13 batch34_indices cert_batch34_r13 513 (by decide)

theorem cert_config_514_d_red : checkIdxFast (buildSMData 13 sharedPow3) 514 = true :=
  certified_of_batch 13 batch34_indices cert_batch34_r13 514 (by decide)

theorem cert_config_517_d_red : checkIdxFast (buildSMData 13 sharedPow3) 517 = true :=
  certified_of_batch 13 batch34_indices cert_batch34_r13 517 (by decide)

theorem cert_config_524_d_red : checkIdxFast (buildSMData 13 sharedPow3) 524 = true :=
  certified_of_batch 13 batch34_indices cert_batch34_r13 524 (by decide)

end Batch
end Math
