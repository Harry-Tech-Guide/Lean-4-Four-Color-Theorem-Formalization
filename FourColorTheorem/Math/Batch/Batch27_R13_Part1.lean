import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 27: Ring 13 (Part 1)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 86, 87, 90, 105.
-/

/-- The 4 ring-13 configuration indices certified in Batch 27. -/
def batch27_indices : List Nat :=
  [86, 87, 90, 105]

/-- Unified in-kernel certification for Batch 27 (Ring 13, Part 1). -/
theorem cert_batch27_r13 : checkRingBatch 13 batch27_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_86_d_red : checkIdxFast (buildSMData 13 sharedPow3) 86 = true :=
  certified_of_batch 13 batch27_indices cert_batch27_r13 86 (by decide)

theorem cert_config_87_d_red : checkIdxFast (buildSMData 13 sharedPow3) 87 = true :=
  certified_of_batch 13 batch27_indices cert_batch27_r13 87 (by decide)

theorem cert_config_90_d_red : checkIdxFast (buildSMData 13 sharedPow3) 90 = true :=
  certified_of_batch 13 batch27_indices cert_batch27_r13 90 (by decide)

theorem cert_config_105_d_red : checkIdxFast (buildSMData 13 sharedPow3) 105 = true :=
  certified_of_batch 13 batch27_indices cert_batch27_r13 105 (by decide)

end Batch
end Math
