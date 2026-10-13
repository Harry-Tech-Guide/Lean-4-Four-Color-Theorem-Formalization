import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 45: Ring 14 (Part 6)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 279, 305.
-/

/-- The 2 ring-14 configuration indices certified in Batch 45. -/
def batch45_indices : List Nat :=
  [279, 305]

/-- Unified in-kernel certification for Batch 45 (Ring 14, Part 6). -/
theorem cert_batch45_r14 : checkRingBatch14 batch45_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_279_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 279 = true :=
  certified_of_batch14 batch45_indices cert_batch45_r14 279 (by decide)

theorem cert_config_305_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 305 = true :=
  certified_of_batch14 batch45_indices cert_batch45_r14 305 (by decide)

end Batch
end Math
