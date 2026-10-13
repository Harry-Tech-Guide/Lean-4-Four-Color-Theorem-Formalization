import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 49: Ring 14 (Part 10)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 486, 493.
-/

/-- The 2 ring-14 configuration indices certified in Batch 49. -/
def batch49_indices : List Nat :=
  [486, 493]

/-- Unified in-kernel certification for Batch 49 (Ring 14, Part 10). -/
theorem cert_batch49_r14 : checkRingBatch14 batch49_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_486_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 486 = true :=
  certified_of_batch14 batch49_indices cert_batch49_r14 486 (by decide)

theorem cert_config_493_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 493 = true :=
  certified_of_batch14 batch49_indices cert_batch49_r14 493 (by decide)

end Batch
end Math
