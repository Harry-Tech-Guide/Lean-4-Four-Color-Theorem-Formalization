import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 55: Ring 14 (Part 6)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 232, 233, 234.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 55. -/
def cbatch55_indices : List Nat :=
  [232, 233, 234]

/-- Unified in-kernel certification for CBatch 55 (Ring 14, Part 6). -/
theorem cert_cbatch55_r14 : checkCRingBatch14 cbatch55_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_232_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 232 = true :=
  certified_of_cbatch14 cbatch55_indices cert_cbatch55_r14 232 (by decide)

theorem cert_config_233_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 233 = true :=
  certified_of_cbatch14 cbatch55_indices cert_cbatch55_r14 233 (by decide)

theorem cert_config_234_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 234 = true :=
  certified_of_cbatch14 cbatch55_indices cert_cbatch55_r14 234 (by decide)

end Batch
end Math
