import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 11: Ring 11 (Part 7)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 11:
Configs 341, 367, 402, 403, 426, 569.
-/

/-- The 6 ring-11 configuration indices certified in CBatch 11. -/
def cbatch11_indices : List Nat :=
  [341, 367, 402, 403, 426, 569]

/-- Unified in-kernel certification for CBatch 11 (Ring 11, Part 7). -/
theorem cert_cbatch11_r11 : checkCRingBatch 11 cbatch11_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_341_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 341 = true :=
  certified_of_cbatch 11 cbatch11_indices cert_cbatch11_r11 341 (by decide)

theorem cert_config_367_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 367 = true :=
  certified_of_cbatch 11 cbatch11_indices cert_cbatch11_r11 367 (by decide)

theorem cert_config_402_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 402 = true :=
  certified_of_cbatch 11 cbatch11_indices cert_cbatch11_r11 402 (by decide)

theorem cert_config_403_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 403 = true :=
  certified_of_cbatch 11 cbatch11_indices cert_cbatch11_r11 403 (by decide)

theorem cert_config_426_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 426 = true :=
  certified_of_cbatch 11 cbatch11_indices cert_cbatch11_r11 426 (by decide)

theorem cert_config_569_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 569 = true :=
  certified_of_cbatch 11 cbatch11_indices cert_cbatch11_r11 569 (by decide)

end Batch
end Math
