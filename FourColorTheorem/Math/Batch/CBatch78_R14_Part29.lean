import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 78: Ring 14 (Part 29)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 530, 531, 532.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 78. -/
def cbatch78_indices : List Nat :=
  [530, 531, 532]

/-- Unified in-kernel certification for CBatch 78 (Ring 14, Part 29). -/
theorem cert_cbatch78_r14 : checkCRingBatch14 cbatch78_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_530_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 530 = true :=
  certified_of_cbatch14 cbatch78_indices cert_cbatch78_r14 530 (by decide)

theorem cert_config_531_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 531 = true :=
  certified_of_cbatch14 cbatch78_indices cert_cbatch78_r14 531 (by decide)

theorem cert_config_532_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 532 = true :=
  certified_of_cbatch14 cbatch78_indices cert_cbatch78_r14 532 (by decide)

end Batch
end Math
