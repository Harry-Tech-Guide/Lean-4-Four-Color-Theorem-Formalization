import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 26: Ring 12 (Part 16)

This module certifies the D-reducibility of 5 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 605, 609, 610, 623, 632.
-/

/-- The 5 ring-12 configuration indices certified in Batch 26. -/
def batch26_indices : List Nat :=
  [605, 609, 610, 623, 632]

/-- Unified in-kernel certification for Batch 26 (Ring 12, Part 16). -/
theorem cert_batch26_r12 : checkRingBatch 12 batch26_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_605_d_red : checkIdxFast (buildSMData 12 sharedPow3) 605 = true :=
  certified_of_batch 12 batch26_indices cert_batch26_r12 605 (by decide)

theorem cert_config_609_d_red : checkIdxFast (buildSMData 12 sharedPow3) 609 = true :=
  certified_of_batch 12 batch26_indices cert_batch26_r12 609 (by decide)

theorem cert_config_610_d_red : checkIdxFast (buildSMData 12 sharedPow3) 610 = true :=
  certified_of_batch 12 batch26_indices cert_batch26_r12 610 (by decide)

theorem cert_config_623_d_red : checkIdxFast (buildSMData 12 sharedPow3) 623 = true :=
  certified_of_batch 12 batch26_indices cert_batch26_r12 623 (by decide)

theorem cert_config_632_d_red : checkIdxFast (buildSMData 12 sharedPow3) 632 = true :=
  certified_of_batch 12 batch26_indices cert_batch26_r12 632 (by decide)

end Batch
end Math
