import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 24: Ring 12 (Part 14)

This module certifies the D-reducibility of 6 D-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 559, 560, 572, 573, 576, 577.
-/

/-- The 6 ring-12 configuration indices certified in Batch 24. -/
def batch24_indices : List Nat :=
  [559, 560, 572, 573, 576, 577]

/-- Unified in-kernel certification for Batch 24 (Ring 12, Part 14). -/
theorem cert_batch24_r12 : checkRingBatch 12 batch24_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_559_d_red : checkIdxFast (buildSMData 12 sharedPow3) 559 = true :=
  certified_of_batch 12 batch24_indices cert_batch24_r12 559 (by decide)

theorem cert_config_560_d_red : checkIdxFast (buildSMData 12 sharedPow3) 560 = true :=
  certified_of_batch 12 batch24_indices cert_batch24_r12 560 (by decide)

theorem cert_config_572_d_red : checkIdxFast (buildSMData 12 sharedPow3) 572 = true :=
  certified_of_batch 12 batch24_indices cert_batch24_r12 572 (by decide)

theorem cert_config_573_d_red : checkIdxFast (buildSMData 12 sharedPow3) 573 = true :=
  certified_of_batch 12 batch24_indices cert_batch24_r12 573 (by decide)

theorem cert_config_576_d_red : checkIdxFast (buildSMData 12 sharedPow3) 576 = true :=
  certified_of_batch 12 batch24_indices cert_batch24_r12 576 (by decide)

theorem cert_config_577_d_red : checkIdxFast (buildSMData 12 sharedPow3) 577 = true :=
  certified_of_batch 12 batch24_indices cert_batch24_r12 577 (by decide)

end Batch
end Math
