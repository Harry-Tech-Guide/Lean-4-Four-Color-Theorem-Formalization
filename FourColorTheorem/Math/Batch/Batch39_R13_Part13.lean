import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 39: Ring 13 (Part 13)

This module certifies the D-reducibility of 4 D-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 627, 628, 630, 631.
-/

/-- The 4 ring-13 configuration indices certified in Batch 39. -/
def batch39_indices : List Nat :=
  [627, 628, 630, 631]

/-- Unified in-kernel certification for Batch 39 (Ring 13, Part 13). -/
theorem cert_batch39_r13 : checkRingBatch 13 batch39_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_627_d_red : checkIdxFast (buildSMData 13 sharedPow3) 627 = true :=
  certified_of_batch 13 batch39_indices cert_batch39_r13 627 (by decide)

theorem cert_config_628_d_red : checkIdxFast (buildSMData 13 sharedPow3) 628 = true :=
  certified_of_batch 13 batch39_indices cert_batch39_r13 628 (by decide)

theorem cert_config_630_d_red : checkIdxFast (buildSMData 13 sharedPow3) 630 = true :=
  certified_of_batch 13 batch39_indices cert_batch39_r13 630 (by decide)

theorem cert_config_631_d_red : checkIdxFast (buildSMData 13 sharedPow3) 631 = true :=
  certified_of_batch 13 batch39_indices cert_batch39_r13 631 (by decide)

end Batch
end Math
