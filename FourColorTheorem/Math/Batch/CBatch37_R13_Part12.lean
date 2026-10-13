import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 37: Ring 13 (Part 12)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 268, 270, 274, 284, 372, 373.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 37. -/
def cbatch37_indices : List Nat :=
  [268, 270, 274, 284, 372, 373]

/-- Unified in-kernel certification for CBatch 37 (Ring 13, Part 12). -/
theorem cert_cbatch37_r13 : checkCRingBatch13 cbatch37_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_268_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 268 = true :=
  certified_of_cbatch13 cbatch37_indices cert_cbatch37_r13 268 (by decide)

theorem cert_config_270_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 270 = true :=
  certified_of_cbatch13 cbatch37_indices cert_cbatch37_r13 270 (by decide)

theorem cert_config_274_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 274 = true :=
  certified_of_cbatch13 cbatch37_indices cert_cbatch37_r13 274 (by decide)

theorem cert_config_284_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 284 = true :=
  certified_of_cbatch13 cbatch37_indices cert_cbatch37_r13 284 (by decide)

theorem cert_config_372_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 372 = true :=
  certified_of_cbatch13 cbatch37_indices cert_cbatch37_r13 372 (by decide)

theorem cert_config_373_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 373 = true :=
  certified_of_cbatch13 cbatch37_indices cert_cbatch37_r13 373 (by decide)

end Batch
end Math
