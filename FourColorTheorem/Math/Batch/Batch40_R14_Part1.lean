import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 40: Ring 14 (Part 1)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 109, 214.
-/

/-- The 2 ring-14 configuration indices certified in Batch 40. -/
def batch40_indices : List Nat :=
  [109, 214]

/-- Unified in-kernel certification for Batch 40 (Ring 14, Part 1). -/
theorem cert_batch40_r14 : checkRingBatch14 batch40_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_109_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 109 = true :=
  certified_of_batch14 batch40_indices cert_batch40_r14 109 (by decide)

theorem cert_config_214_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 214 = true :=
  certified_of_batch14 batch40_indices cert_batch40_r14 214 (by decide)

end Batch
end Math
