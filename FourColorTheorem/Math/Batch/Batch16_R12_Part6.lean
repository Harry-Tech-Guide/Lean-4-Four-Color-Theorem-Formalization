import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 16: Ring 12 (Part 6)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 173, 174, 175, 176, 235, 242.
-/

/-- The 6 ring-12 configuration indices certified in Batch 16. -/
def batch16_indices : List Nat :=
  [173, 174, 175, 176, 235, 242]

/-- Unified in-kernel certification for Batch 16 (Ring 12, Part 6). -/
theorem cert_batch16_r12 : checkRingBatch 12 batch16_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_173_d_red : checkIdxFast (buildSMData 12 sharedPow3) 173 = true :=
  certified_of_batch 12 batch16_indices cert_batch16_r12 173 (by decide)

theorem cert_config_174_d_red : checkIdxFast (buildSMData 12 sharedPow3) 174 = true :=
  certified_of_batch 12 batch16_indices cert_batch16_r12 174 (by decide)

theorem cert_config_175_d_red : checkIdxFast (buildSMData 12 sharedPow3) 175 = true :=
  certified_of_batch 12 batch16_indices cert_batch16_r12 175 (by decide)

theorem cert_config_176_d_red : checkIdxFast (buildSMData 12 sharedPow3) 176 = true :=
  certified_of_batch 12 batch16_indices cert_batch16_r12 176 (by decide)

theorem cert_config_235_d_red : checkIdxFast (buildSMData 12 sharedPow3) 235 = true :=
  certified_of_batch 12 batch16_indices cert_batch16_r12 235 (by decide)

theorem cert_config_242_d_red : checkIdxFast (buildSMData 12 sharedPow3) 242 = true :=
  certified_of_batch 12 batch16_indices cert_batch16_r12 242 (by decide)

end Batch
end Math
