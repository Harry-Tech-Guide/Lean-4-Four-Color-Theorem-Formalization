import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 08: Ring 11 (Part 4)

This module certifies the C-reducibility of 5 C-reducible configurations
from the RSST unavoidable set with ring size 11:
Configs 118, 121, 122, 123, 124.
-/

/-- The 5 ring-11 configuration indices certified in CBatch 08. -/
def cbatch08_indices : List Nat :=
  [118, 121, 122, 123, 124]

/-- Unified in-kernel certification for CBatch 08 (Ring 11, Part 4). -/
theorem cert_cbatch08_r11 : checkCRingBatch 11 cbatch08_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_118_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 118 = true :=
  certified_of_cbatch 11 cbatch08_indices cert_cbatch08_r11 118 (by decide)

theorem cert_config_121_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 121 = true :=
  certified_of_cbatch 11 cbatch08_indices cert_cbatch08_r11 121 (by decide)

theorem cert_config_122_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 122 = true :=
  certified_of_cbatch 11 cbatch08_indices cert_cbatch08_r11 122 (by decide)

theorem cert_config_123_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 123 = true :=
  certified_of_cbatch 11 cbatch08_indices cert_cbatch08_r11 123 (by decide)

theorem cert_config_124_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 124 = true :=
  certified_of_cbatch 11 cbatch08_indices cert_cbatch08_r11 124 (by decide)

end Batch
end Math
