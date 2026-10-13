import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 58: Ring 14 (Part 9)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 282, 283, 285.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 58. -/
def cbatch58_indices : List Nat :=
  [282, 283, 285]

/-- Unified in-kernel certification for CBatch 58 (Ring 14, Part 9). -/
theorem cert_cbatch58_r14 : checkCRingBatch14 cbatch58_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_282_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 282 = true :=
  certified_of_cbatch14 cbatch58_indices cert_cbatch58_r14 282 (by decide)

theorem cert_config_283_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 283 = true :=
  certified_of_cbatch14 cbatch58_indices cert_cbatch58_r14 283 (by decide)

theorem cert_config_285_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 285 = true :=
  certified_of_cbatch14 cbatch58_indices cert_cbatch58_r14 285 (by decide)

end Batch
end Math
