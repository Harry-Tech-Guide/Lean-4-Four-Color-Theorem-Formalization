import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 35: Ring 13 (Part 10)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 255, 256, 258, 259, 260, 261.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 35. -/
def cbatch35_indices : List Nat :=
  [255, 256, 258, 259, 260, 261]

/-- Unified in-kernel certification for CBatch 35 (Ring 13, Part 10). -/
theorem cert_cbatch35_r13 : checkCRingBatch13 cbatch35_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_255_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 255 = true :=
  certified_of_cbatch13 cbatch35_indices cert_cbatch35_r13 255 (by decide)

theorem cert_config_256_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 256 = true :=
  certified_of_cbatch13 cbatch35_indices cert_cbatch35_r13 256 (by decide)

theorem cert_config_258_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 258 = true :=
  certified_of_cbatch13 cbatch35_indices cert_cbatch35_r13 258 (by decide)

theorem cert_config_259_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 259 = true :=
  certified_of_cbatch13 cbatch35_indices cert_cbatch35_r13 259 (by decide)

theorem cert_config_260_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 260 = true :=
  certified_of_cbatch13 cbatch35_indices cert_cbatch35_r13 260 (by decide)

theorem cert_config_261_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 261 = true :=
  certified_of_cbatch13 cbatch35_indices cert_cbatch35_r13 261 (by decide)

end Batch
end Math
