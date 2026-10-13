import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 37: Ring 13 (Part 11)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 593, 594, 604, 606.
-/

/-- The 4 ring-13 configuration indices certified in Batch 37. -/
def batch37_indices : List Nat :=
  [593, 594, 604, 606]

/-- Unified in-kernel certification for Batch 37 (Ring 13, Part 11). -/
theorem cert_batch37_r13 : checkRingBatch13 batch37_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_593_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 593 = true :=
  certified_of_batch13 batch37_indices cert_batch37_r13 593 (by decide)

theorem cert_config_594_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 594 = true :=
  certified_of_batch13 batch37_indices cert_batch37_r13 594 (by decide)

theorem cert_config_604_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 604 = true :=
  certified_of_batch13 batch37_indices cert_batch37_r13 604 (by decide)

theorem cert_config_606_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 606 = true :=
  certified_of_batch13 batch37_indices cert_batch37_r13 606 (by decide)

end Batch
end Math
