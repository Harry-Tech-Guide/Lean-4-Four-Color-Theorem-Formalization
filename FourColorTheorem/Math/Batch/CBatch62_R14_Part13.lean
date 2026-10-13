import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 62: Ring 14 (Part 13)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 295, 296, 297.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 62. -/
def cbatch62_indices : List Nat :=
  [295, 296, 297]

/-- Unified in-kernel certification for CBatch 62 (Ring 14, Part 13). -/
theorem cert_cbatch62_r14 : checkCRingBatch14 cbatch62_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_295_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 295 = true :=
  certified_of_cbatch14 cbatch62_indices cert_cbatch62_r14 295 (by decide)

theorem cert_config_296_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 296 = true :=
  certified_of_cbatch14 cbatch62_indices cert_cbatch62_r14 296 (by decide)

theorem cert_config_297_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 297 = true :=
  certified_of_cbatch14 cbatch62_indices cert_cbatch62_r14 297 (by decide)

end Batch
end Math
