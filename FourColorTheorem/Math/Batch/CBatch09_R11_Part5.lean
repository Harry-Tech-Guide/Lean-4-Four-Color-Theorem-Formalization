import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 09: Ring 11 (Part 5)

This module certifies the C-reducibility of 5 C-reducible configurations
from the RSST unavoidable set with ring size 11:
Configs 125, 134, 135, 241, 329.
-/

/-- The 5 ring-11 configuration indices certified in CBatch 09. -/
def cbatch09_indices : List Nat :=
  [125, 134, 135, 241, 329]

/-- Unified in-kernel certification for CBatch 09 (Ring 11, Part 5). -/
theorem cert_cbatch09_r11 : checkCRingBatch 11 cbatch09_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_125_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 125 = true :=
  certified_of_cbatch 11 cbatch09_indices cert_cbatch09_r11 125 (by decide)

theorem cert_config_134_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 134 = true :=
  certified_of_cbatch 11 cbatch09_indices cert_cbatch09_r11 134 (by decide)

theorem cert_config_135_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 135 = true :=
  certified_of_cbatch 11 cbatch09_indices cert_cbatch09_r11 135 (by decide)

theorem cert_config_241_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 241 = true :=
  certified_of_cbatch 11 cbatch09_indices cert_cbatch09_r11 241 (by decide)

theorem cert_config_329_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 329 = true :=
  certified_of_cbatch 11 cbatch09_indices cert_cbatch09_r11 329 (by decide)

end Batch
end Math
