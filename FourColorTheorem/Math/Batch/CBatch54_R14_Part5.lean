import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 54: Ring 14 (Part 5)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 229, 230, 231.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 54. -/
def cbatch54_indices : List Nat :=
  [229, 230, 231]

/-- Unified in-kernel certification for CBatch 54 (Ring 14, Part 5). -/
theorem cert_cbatch54_r14 : checkCRingBatch14 cbatch54_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_229_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 229 = true :=
  certified_of_cbatch14 cbatch54_indices cert_cbatch54_r14 229 (by decide)

theorem cert_config_230_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 230 = true :=
  certified_of_cbatch14 cbatch54_indices cert_cbatch54_r14 230 (by decide)

theorem cert_config_231_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 231 = true :=
  certified_of_cbatch14 cbatch54_indices cert_cbatch54_r14 231 (by decide)

end Batch
end Math
