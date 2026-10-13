import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 36: Ring 13 (Part 11)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 262, 263, 264, 265, 266, 267.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 36. -/
def cbatch36_indices : List Nat :=
  [262, 263, 264, 265, 266, 267]

/-- Unified in-kernel certification for CBatch 36 (Ring 13, Part 11). -/
theorem cert_cbatch36_r13 : checkCRingBatch13 cbatch36_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_262_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 262 = true :=
  certified_of_cbatch13 cbatch36_indices cert_cbatch36_r13 262 (by decide)

theorem cert_config_263_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 263 = true :=
  certified_of_cbatch13 cbatch36_indices cert_cbatch36_r13 263 (by decide)

theorem cert_config_264_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 264 = true :=
  certified_of_cbatch13 cbatch36_indices cert_cbatch36_r13 264 (by decide)

theorem cert_config_265_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 265 = true :=
  certified_of_cbatch13 cbatch36_indices cert_cbatch36_r13 265 (by decide)

theorem cert_config_266_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 266 = true :=
  certified_of_cbatch13 cbatch36_indices cert_cbatch36_r13 266 (by decide)

theorem cert_config_267_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 267 = true :=
  certified_of_cbatch13 cbatch36_indices cert_cbatch36_r13 267 (by decide)

end Batch
end Math
