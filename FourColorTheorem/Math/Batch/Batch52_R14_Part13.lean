import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 52: Ring 14 (Part 13)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 548, 552.
-/

/-- The 2 ring-14 configuration indices certified in Batch 52. -/
def batch52_indices : List Nat :=
  [548, 552]

/-- Unified in-kernel certification for Batch 52 (Ring 14, Part 13). -/
theorem cert_batch52_r14 : checkRingBatch14 batch52_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_548_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 548 = true :=
  certified_of_batch14 batch52_indices cert_batch52_r14 548 (by decide)

theorem cert_config_552_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 552 = true :=
  certified_of_batch14 batch52_indices cert_batch52_r14 552 (by decide)

end Batch
end Math
