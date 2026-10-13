import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 29: Ring 13 (Part 3)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 190, 207, 208, 210.
-/

/-- The 4 ring-13 configuration indices certified in Batch 29. -/
def batch29_indices : List Nat :=
  [190, 207, 208, 210]

/-- Unified in-kernel certification for Batch 29 (Ring 13, Part 3). -/
theorem cert_batch29_r13 : checkRingBatch 13 batch29_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_190_d_red : checkIdxFast (buildSMData 13 sharedPow3) 190 = true :=
  certified_of_batch 13 batch29_indices cert_batch29_r13 190 (by decide)

theorem cert_config_207_d_red : checkIdxFast (buildSMData 13 sharedPow3) 207 = true :=
  certified_of_batch 13 batch29_indices cert_batch29_r13 207 (by decide)

theorem cert_config_208_d_red : checkIdxFast (buildSMData 13 sharedPow3) 208 = true :=
  certified_of_batch 13 batch29_indices cert_batch29_r13 208 (by decide)

theorem cert_config_210_d_red : checkIdxFast (buildSMData 13 sharedPow3) 210 = true :=
  certified_of_batch 13 batch29_indices cert_batch29_r13 210 (by decide)

end Batch
end Math
