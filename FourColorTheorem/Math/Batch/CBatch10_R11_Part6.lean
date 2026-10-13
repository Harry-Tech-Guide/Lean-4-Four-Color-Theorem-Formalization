import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 10: Ring 11 (Part 6)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 11:
Configs 331, 333, 335, 338, 339, 340.
-/

/-- The 6 ring-11 configuration indices certified in CBatch 10. -/
def cbatch10_indices : List Nat :=
  [331, 333, 335, 338, 339, 340]

/-- Unified in-kernel certification for CBatch 10 (Ring 11, Part 6). -/
theorem cert_cbatch10_r11 : checkCRingBatch 11 cbatch10_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_331_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 331 = true :=
  certified_of_cbatch 11 cbatch10_indices cert_cbatch10_r11 331 (by decide)

theorem cert_config_333_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 333 = true :=
  certified_of_cbatch 11 cbatch10_indices cert_cbatch10_r11 333 (by decide)

theorem cert_config_335_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 335 = true :=
  certified_of_cbatch 11 cbatch10_indices cert_cbatch10_r11 335 (by decide)

theorem cert_config_338_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 338 = true :=
  certified_of_cbatch 11 cbatch10_indices cert_cbatch10_r11 338 (by decide)

theorem cert_config_339_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 339 = true :=
  certified_of_cbatch 11 cbatch10_indices cert_cbatch10_r11 339 (by decide)

theorem cert_config_340_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 340 = true :=
  certified_of_cbatch 11 cbatch10_indices cert_cbatch10_r11 340 (by decide)

end Batch
end Math
