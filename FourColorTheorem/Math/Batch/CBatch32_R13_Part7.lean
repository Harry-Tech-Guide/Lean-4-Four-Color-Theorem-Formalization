import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 32: Ring 13 (Part 7)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 195, 196, 197, 198, 199, 200.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 32. -/
def cbatch32_indices : List Nat :=
  [195, 196, 197, 198, 199, 200]

/-- Unified in-kernel certification for CBatch 32 (Ring 13, Part 7). -/
theorem cert_cbatch32_r13 : checkCRingBatch13 cbatch32_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_195_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 195 = true :=
  certified_of_cbatch13 cbatch32_indices cert_cbatch32_r13 195 (by decide)

theorem cert_config_196_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 196 = true :=
  certified_of_cbatch13 cbatch32_indices cert_cbatch32_r13 196 (by decide)

theorem cert_config_197_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 197 = true :=
  certified_of_cbatch13 cbatch32_indices cert_cbatch32_r13 197 (by decide)

theorem cert_config_198_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 198 = true :=
  certified_of_cbatch13 cbatch32_indices cert_cbatch32_r13 198 (by decide)

theorem cert_config_199_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 199 = true :=
  certified_of_cbatch13 cbatch32_indices cert_cbatch32_r13 199 (by decide)

theorem cert_config_200_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 200 = true :=
  certified_of_cbatch13 cbatch32_indices cert_cbatch32_r13 200 (by decide)

end Batch
end Math
