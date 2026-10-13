import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 59: Ring 14 (Part 10)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 286, 287, 288.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 59. -/
def cbatch59_indices : List Nat :=
  [286, 287, 288]

/-- Unified in-kernel certification for CBatch 59 (Ring 14, Part 10). -/
theorem cert_cbatch59_r14 : checkCRingBatch14 cbatch59_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_286_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 286 = true :=
  certified_of_cbatch14 cbatch59_indices cert_cbatch59_r14 286 (by decide)

theorem cert_config_287_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 287 = true :=
  certified_of_cbatch14 cbatch59_indices cert_cbatch59_r14 287 (by decide)

theorem cert_config_288_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 288 = true :=
  certified_of_cbatch14 cbatch59_indices cert_cbatch59_r14 288 (by decide)

end Batch
end Math
