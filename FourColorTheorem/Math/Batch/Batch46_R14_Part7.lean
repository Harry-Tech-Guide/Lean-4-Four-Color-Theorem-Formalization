import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 46: Ring 14 (Part 7)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 312, 313.
-/

/-- The 2 ring-14 configuration indices certified in Batch 46. -/
def batch46_indices : List Nat :=
  [312, 313]

/-- Unified in-kernel certification for Batch 46 (Ring 14, Part 7). -/
theorem cert_batch46_r14 : checkRingBatch14 batch46_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_312_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 312 = true :=
  certified_of_batch14 batch46_indices cert_batch46_r14 312 (by decide)

theorem cert_config_313_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 313 = true :=
  certified_of_batch14 batch46_indices cert_batch46_r14 313 (by decide)

end Batch
end Math
