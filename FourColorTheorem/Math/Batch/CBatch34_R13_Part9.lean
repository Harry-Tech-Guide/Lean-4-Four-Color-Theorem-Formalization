import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 34: Ring 13 (Part 9)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 217, 248, 251, 252, 253, 254.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 34. -/
def cbatch34_indices : List Nat :=
  [217, 248, 251, 252, 253, 254]

/-- Unified in-kernel certification for CBatch 34 (Ring 13, Part 9). -/
theorem cert_cbatch34_r13 : checkCRingBatch13 cbatch34_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_217_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 217 = true :=
  certified_of_cbatch13 cbatch34_indices cert_cbatch34_r13 217 (by decide)

theorem cert_config_248_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 248 = true :=
  certified_of_cbatch13 cbatch34_indices cert_cbatch34_r13 248 (by decide)

theorem cert_config_251_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 251 = true :=
  certified_of_cbatch13 cbatch34_indices cert_cbatch34_r13 251 (by decide)

theorem cert_config_252_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 252 = true :=
  certified_of_cbatch13 cbatch34_indices cert_cbatch34_r13 252 (by decide)

theorem cert_config_253_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 253 = true :=
  certified_of_cbatch13 cbatch34_indices cert_cbatch34_r13 253 (by decide)

theorem cert_config_254_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 254 = true :=
  certified_of_cbatch13 cbatch34_indices cert_cbatch34_r13 254 (by decide)

end Batch
end Math
