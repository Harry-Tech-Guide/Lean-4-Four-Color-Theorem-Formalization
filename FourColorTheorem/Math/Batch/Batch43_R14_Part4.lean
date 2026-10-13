import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 43: Ring 14 (Part 4)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 238, 239.
-/

/-- The 2 ring-14 configuration indices certified in Batch 43. -/
def batch43_indices : List Nat :=
  [238, 239]

/-- Unified in-kernel certification for Batch 43 (Ring 14, Part 4). -/
theorem cert_batch43_r14 : checkRingBatch14 batch43_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_238_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 238 = true :=
  certified_of_batch14 batch43_indices cert_batch43_r14 238 (by decide)

theorem cert_config_239_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 239 = true :=
  certified_of_batch14 batch43_indices cert_batch43_r14 239 (by decide)

end Batch
end Math
