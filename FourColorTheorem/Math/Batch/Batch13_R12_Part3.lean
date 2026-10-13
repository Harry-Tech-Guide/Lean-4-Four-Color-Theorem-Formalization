import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 13: Ring 12 (Part 3)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 91, 92, 93, 96, 97, 98.
-/

/-- The 6 ring-12 configuration indices certified in Batch 13. -/
def batch13_indices : List Nat :=
  [91, 92, 93, 96, 97, 98]

/-- Unified in-kernel certification for Batch 13 (Ring 12, Part 3). -/
theorem cert_batch13_r12 : checkRingBatch 12 batch13_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_91_d_red : checkIdxFast (buildSMData 12 sharedPow3) 91 = true :=
  certified_of_batch 12 batch13_indices cert_batch13_r12 91 (by decide)

theorem cert_config_92_d_red : checkIdxFast (buildSMData 12 sharedPow3) 92 = true :=
  certified_of_batch 12 batch13_indices cert_batch13_r12 92 (by decide)

theorem cert_config_93_d_red : checkIdxFast (buildSMData 12 sharedPow3) 93 = true :=
  certified_of_batch 12 batch13_indices cert_batch13_r12 93 (by decide)

theorem cert_config_96_d_red : checkIdxFast (buildSMData 12 sharedPow3) 96 = true :=
  certified_of_batch 12 batch13_indices cert_batch13_r12 96 (by decide)

theorem cert_config_97_d_red : checkIdxFast (buildSMData 12 sharedPow3) 97 = true :=
  certified_of_batch 12 batch13_indices cert_batch13_r12 97 (by decide)

theorem cert_config_98_d_red : checkIdxFast (buildSMData 12 sharedPow3) 98 = true :=
  certified_of_batch 12 batch13_indices cert_batch13_r12 98 (by decide)

end Batch
end Math
