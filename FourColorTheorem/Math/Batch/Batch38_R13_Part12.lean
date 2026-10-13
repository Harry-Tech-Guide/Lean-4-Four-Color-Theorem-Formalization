import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 38: Ring 13 (Part 12)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 607, 608, 611, 615.
-/

/-- The 4 ring-13 configuration indices certified in Batch 38. -/
def batch38_indices : List Nat :=
  [607, 608, 611, 615]

/-- Unified in-kernel certification for Batch 38 (Ring 13, Part 12). -/
theorem cert_batch38_r13 : checkRingBatch 13 batch38_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_607_d_red : checkIdxFast (buildSMData 13 sharedPow3) 607 = true :=
  certified_of_batch 13 batch38_indices cert_batch38_r13 607 (by decide)

theorem cert_config_608_d_red : checkIdxFast (buildSMData 13 sharedPow3) 608 = true :=
  certified_of_batch 13 batch38_indices cert_batch38_r13 608 (by decide)

theorem cert_config_611_d_red : checkIdxFast (buildSMData 13 sharedPow3) 611 = true :=
  certified_of_batch 13 batch38_indices cert_batch38_r13 611 (by decide)

theorem cert_config_615_d_red : checkIdxFast (buildSMData 13 sharedPow3) 615 = true :=
  certified_of_batch 13 batch38_indices cert_batch38_r13 615 (by decide)

end Batch
end Math
