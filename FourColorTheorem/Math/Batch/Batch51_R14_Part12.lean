import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 51: Ring 14 (Part 12)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 545, 547.
-/

/-- The 2 ring-14 configuration indices certified in Batch 51. -/
def batch51_indices : List Nat :=
  [545, 547]

/-- Unified in-kernel certification for Batch 51 (Ring 14, Part 12). -/
theorem cert_batch51_r14 : checkRingBatch14 batch51_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_545_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 545 = true :=
  certified_of_batch14 batch51_indices cert_batch51_r14 545 (by decide)

theorem cert_config_547_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 547 = true :=
  certified_of_batch14 batch51_indices cert_batch51_r14 547 (by decide)

end Batch
end Math
