import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 47: Ring 14 (Part 8)

This module certifies the D-reducibility of 2 D-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 315, 316.
-/

/-- The 2 ring-14 configuration indices certified in Batch 47. -/
def batch47_indices : List Nat :=
  [315, 316]

/-- Unified in-kernel certification for Batch 47 (Ring 14, Part 8). -/
theorem cert_batch47_r14 : checkRingBatch14 batch47_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_315_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 315 = true :=
  certified_of_batch14 batch47_indices cert_batch47_r14 315 (by decide)

theorem cert_config_316_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 316 = true :=
  certified_of_batch14 batch47_indices cert_batch47_r14 316 (by decide)

end Batch
end Math
