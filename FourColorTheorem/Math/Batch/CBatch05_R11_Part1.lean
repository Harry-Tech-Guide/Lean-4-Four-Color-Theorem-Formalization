import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 05: Ring 11 (Part 1)

This module certifies the C-reducibility of 5 C-reducible configurations
from the RSST unavoidable set with ring size 11:
Configs 14, 38, 39, 41, 42.
-/

/-- The 5 ring-11 configuration indices certified in CBatch 05. -/
def cbatch05_indices : List Nat :=
  [14, 38, 39, 41, 42]

/-- Unified in-kernel certification for CBatch 05 (Ring 11, Part 1). -/
theorem cert_cbatch05_r11 : checkCRingBatch 11 cbatch05_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_14_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 14 = true :=
  certified_of_cbatch 11 cbatch05_indices cert_cbatch05_r11 14 (by decide)

theorem cert_config_38_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 38 = true :=
  certified_of_cbatch 11 cbatch05_indices cert_cbatch05_r11 38 (by decide)

theorem cert_config_39_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 39 = true :=
  certified_of_cbatch 11 cbatch05_indices cert_cbatch05_r11 39 (by decide)

theorem cert_config_41_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 41 = true :=
  certified_of_cbatch 11 cbatch05_indices cert_cbatch05_r11 41 (by decide)

theorem cert_config_42_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 42 = true :=
  certified_of_cbatch 11 cbatch05_indices cert_cbatch05_r11 42 (by decide)

end Batch
end Math
