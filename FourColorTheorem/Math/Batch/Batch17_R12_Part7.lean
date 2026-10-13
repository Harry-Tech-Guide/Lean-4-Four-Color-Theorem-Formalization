import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 17: Ring 12 (Part 7)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 243, 246, 247, 347, 350, 351.
-/

/-- The 6 ring-12 configuration indices certified in Batch 17. -/
def batch17_indices : List Nat :=
  [243, 246, 247, 347, 350, 351]

/-- Unified in-kernel certification for Batch 17 (Ring 12, Part 7). -/
theorem cert_batch17_r12 : checkRingBatch 12 batch17_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_243_d_red : checkIdxFast (buildSMData 12 sharedPow3) 243 = true :=
  certified_of_batch 12 batch17_indices cert_batch17_r12 243 (by decide)

theorem cert_config_246_d_red : checkIdxFast (buildSMData 12 sharedPow3) 246 = true :=
  certified_of_batch 12 batch17_indices cert_batch17_r12 246 (by decide)

theorem cert_config_247_d_red : checkIdxFast (buildSMData 12 sharedPow3) 247 = true :=
  certified_of_batch 12 batch17_indices cert_batch17_r12 247 (by decide)

theorem cert_config_347_d_red : checkIdxFast (buildSMData 12 sharedPow3) 347 = true :=
  certified_of_batch 12 batch17_indices cert_batch17_r12 347 (by decide)

theorem cert_config_350_d_red : checkIdxFast (buildSMData 12 sharedPow3) 350 = true :=
  certified_of_batch 12 batch17_indices cert_batch17_r12 350 (by decide)

theorem cert_config_351_d_red : checkIdxFast (buildSMData 12 sharedPow3) 351 = true :=
  certified_of_batch 12 batch17_indices cert_batch17_r12 351 (by decide)

end Batch
end Math
