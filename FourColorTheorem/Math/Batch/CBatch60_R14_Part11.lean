import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 60: Ring 14 (Part 11)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 289, 290, 291.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 60. -/
def cbatch60_indices : List Nat :=
  [289, 290, 291]

/-- Unified in-kernel certification for CBatch 60 (Ring 14, Part 11). -/
theorem cert_cbatch60_r14 : checkCRingBatch14 cbatch60_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_289_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 289 = true :=
  certified_of_cbatch14 cbatch60_indices cert_cbatch60_r14 289 (by decide)

theorem cert_config_290_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 290 = true :=
  certified_of_cbatch14 cbatch60_indices cert_cbatch60_r14 290 (by decide)

theorem cert_config_291_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 291 = true :=
  certified_of_cbatch14 cbatch60_indices cert_cbatch60_r14 291 (by decide)

end Batch
end Math
