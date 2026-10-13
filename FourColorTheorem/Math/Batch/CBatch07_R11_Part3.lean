import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 07: Ring 11 (Part 3)

This module certifies the C-reducibility of 5 C-reducible configurations
from the RSST unavoidable set with ring size 11:
Configs 55, 57, 59, 113, 115.
-/

/-- The 5 ring-11 configuration indices certified in CBatch 07. -/
def cbatch07_indices : List Nat :=
  [55, 57, 59, 113, 115]

/-- Unified in-kernel certification for CBatch 07 (Ring 11, Part 3). -/
theorem cert_cbatch07_r11 : checkCRingBatch 11 cbatch07_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_55_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 55 = true :=
  certified_of_cbatch 11 cbatch07_indices cert_cbatch07_r11 55 (by decide)

theorem cert_config_57_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 57 = true :=
  certified_of_cbatch 11 cbatch07_indices cert_cbatch07_r11 57 (by decide)

theorem cert_config_59_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 59 = true :=
  certified_of_cbatch 11 cbatch07_indices cert_cbatch07_r11 59 (by decide)

theorem cert_config_113_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 113 = true :=
  certified_of_cbatch 11 cbatch07_indices cert_cbatch07_r11 113 (by decide)

theorem cert_config_115_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 115 = true :=
  certified_of_cbatch 11 cbatch07_indices cert_cbatch07_r11 115 (by decide)

end Batch
end Math
