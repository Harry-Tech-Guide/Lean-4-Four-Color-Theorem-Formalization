import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 41: Ring 14 (Part 2)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 222, 223.
-/

/-- The 2 ring-14 configuration indices certified in Batch 41. -/
def batch41_indices : List Nat :=
  [222, 223]

/-- Unified in-kernel certification for Batch 41 (Ring 14, Part 2). -/
theorem cert_batch41_r14 : checkRingBatch14 batch41_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_222_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 222 = true :=
  certified_of_batch14 batch41_indices cert_batch41_r14 222 (by decide)

theorem cert_config_223_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 223 = true :=
  certified_of_batch14 batch41_indices cert_batch41_r14 223 (by decide)

end Batch
end Math
