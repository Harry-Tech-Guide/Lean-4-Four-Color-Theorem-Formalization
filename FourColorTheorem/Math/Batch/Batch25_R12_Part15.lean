import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 25: Ring 12 (Part 15)

This module certifies the D-reducibility of 5 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 579, 580, 590, 597, 599.
-/

/-- The 5 ring-12 configuration indices certified in Batch 25. -/
def batch25_indices : List Nat :=
  [579, 580, 590, 597, 599]

/-- Unified in-kernel certification for Batch 25 (Ring 12, Part 15). -/
theorem cert_batch25_r12 : checkRingBatch 12 batch25_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_579_d_red : checkIdxFast (buildSMData 12 sharedPow3) 579 = true :=
  certified_of_batch 12 batch25_indices cert_batch25_r12 579 (by decide)

theorem cert_config_580_d_red : checkIdxFast (buildSMData 12 sharedPow3) 580 = true :=
  certified_of_batch 12 batch25_indices cert_batch25_r12 580 (by decide)

theorem cert_config_590_d_red : checkIdxFast (buildSMData 12 sharedPow3) 590 = true :=
  certified_of_batch 12 batch25_indices cert_batch25_r12 590 (by decide)

theorem cert_config_597_d_red : checkIdxFast (buildSMData 12 sharedPow3) 597 = true :=
  certified_of_batch 12 batch25_indices cert_batch25_r12 597 (by decide)

theorem cert_config_599_d_red : checkIdxFast (buildSMData 12 sharedPow3) 599 = true :=
  certified_of_batch 12 batch25_indices cert_batch25_r12 599 (by decide)

end Batch
end Math
