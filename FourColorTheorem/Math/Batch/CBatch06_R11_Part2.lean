import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 06: Ring 11 (Part 2)

This module certifies the C-reducibility of 5 C-reducible configurations
from the RSST unavoidable set with ring size 11:
Configs 46, 48, 51, 53, 54.
-/

/-- The 5 ring-11 configuration indices certified in CBatch 06. -/
def cbatch06_indices : List Nat :=
  [46, 48, 51, 53, 54]

/-- Unified in-kernel certification for CBatch 06 (Ring 11, Part 2). -/
theorem cert_cbatch06_r11 : checkCRingBatch 11 cbatch06_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_46_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 46 = true :=
  certified_of_cbatch 11 cbatch06_indices cert_cbatch06_r11 46 (by decide)

theorem cert_config_48_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 48 = true :=
  certified_of_cbatch 11 cbatch06_indices cert_cbatch06_r11 48 (by decide)

theorem cert_config_51_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 51 = true :=
  certified_of_cbatch 11 cbatch06_indices cert_cbatch06_r11 51 (by decide)

theorem cert_config_53_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 53 = true :=
  certified_of_cbatch 11 cbatch06_indices cert_cbatch06_r11 53 (by decide)

theorem cert_config_54_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 54 = true :=
  certified_of_cbatch 11 cbatch06_indices cert_cbatch06_r11 54 (by decide)

end Batch
end Math
