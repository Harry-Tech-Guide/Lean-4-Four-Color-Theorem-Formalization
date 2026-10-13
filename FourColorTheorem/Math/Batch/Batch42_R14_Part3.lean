import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 42: Ring 14 (Part 3)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 224, 237.
-/

/-- The 2 ring-14 configuration indices certified in Batch 42. -/
def batch42_indices : List Nat :=
  [224, 237]

/-- Unified in-kernel certification for Batch 42 (Ring 14, Part 3). -/
theorem cert_batch42_r14 : checkRingBatch14 batch42_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_224_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 224 = true :=
  certified_of_batch14 batch42_indices cert_batch42_r14 224 (by decide)

theorem cert_config_237_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 237 = true :=
  certified_of_batch14 batch42_indices cert_batch42_r14 237 (by decide)

end Batch
end Math
