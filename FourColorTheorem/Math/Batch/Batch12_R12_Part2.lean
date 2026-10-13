import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 12: Ring 12 (Part 2)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 75, 78, 80, 83, 84, 85.
-/

/-- The 6 ring-12 configuration indices certified in Batch 12. -/
def batch12_indices : List Nat :=
  [75, 78, 80, 83, 84, 85]

/-- Unified in-kernel certification for Batch 12 (Ring 12, Part 2). -/
theorem cert_batch12_r12 : checkRingBatch 12 batch12_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_75_d_red : checkIdxFast (buildSMData 12 sharedPow3) 75 = true :=
  certified_of_batch 12 batch12_indices cert_batch12_r12 75 (by decide)

theorem cert_config_78_d_red : checkIdxFast (buildSMData 12 sharedPow3) 78 = true :=
  certified_of_batch 12 batch12_indices cert_batch12_r12 78 (by decide)

theorem cert_config_80_d_red : checkIdxFast (buildSMData 12 sharedPow3) 80 = true :=
  certified_of_batch 12 batch12_indices cert_batch12_r12 80 (by decide)

theorem cert_config_83_d_red : checkIdxFast (buildSMData 12 sharedPow3) 83 = true :=
  certified_of_batch 12 batch12_indices cert_batch12_r12 83 (by decide)

theorem cert_config_84_d_red : checkIdxFast (buildSMData 12 sharedPow3) 84 = true :=
  certified_of_batch 12 batch12_indices cert_batch12_r12 84 (by decide)

theorem cert_config_85_d_red : checkIdxFast (buildSMData 12 sharedPow3) 85 = true :=
  certified_of_batch 12 batch12_indices cert_batch12_r12 85 (by decide)

end Batch
end Math
