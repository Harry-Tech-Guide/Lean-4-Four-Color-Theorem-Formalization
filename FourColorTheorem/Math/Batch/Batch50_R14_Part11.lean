import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 50: Ring 14 (Part 11)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 494, 495.
-/

/-- The 2 ring-14 configuration indices certified in Batch 50. -/
def batch50_indices : List Nat :=
  [494, 495]

/-- Unified in-kernel certification for Batch 50 (Ring 14, Part 11). -/
theorem cert_batch50_r14 : checkRingBatch14 batch50_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_494_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 494 = true :=
  certified_of_batch14 batch50_indices cert_batch50_r14 494 (by decide)

theorem cert_config_495_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 495 = true :=
  certified_of_batch14 batch50_indices cert_batch50_r14 495 (by decide)

end Batch
end Math
