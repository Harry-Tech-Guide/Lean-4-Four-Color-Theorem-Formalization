import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 44: Ring 14 (Part 5)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 240, 278.
-/

/-- The 2 ring-14 configuration indices certified in Batch 44. -/
def batch44_indices : List Nat :=
  [240, 278]

/-- Unified in-kernel certification for Batch 44 (Ring 14, Part 5). -/
theorem cert_batch44_r14 : checkRingBatch14 batch44_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_240_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 240 = true :=
  certified_of_batch14 batch44_indices cert_batch44_r14 240 (by decide)

theorem cert_config_278_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 278 = true :=
  certified_of_batch14 batch44_indices cert_batch44_r14 278 (by decide)

end Batch
end Math
