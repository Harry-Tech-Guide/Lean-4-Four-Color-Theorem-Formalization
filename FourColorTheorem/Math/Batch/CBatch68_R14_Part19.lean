import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 68: Ring 14 (Part 19)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 318, 319, 320.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 68. -/
def cbatch68_indices : List Nat :=
  [318, 319, 320]

/-- Unified in-kernel certification for CBatch 68 (Ring 14, Part 19). -/
theorem cert_cbatch68_r14 : checkCRingBatch14 cbatch68_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_318_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 318 = true :=
  certified_of_cbatch14 cbatch68_indices cert_cbatch68_r14 318 (by decide)

theorem cert_config_319_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 319 = true :=
  certified_of_cbatch14 cbatch68_indices cert_cbatch68_r14 319 (by decide)

theorem cert_config_320_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 320 = true :=
  certified_of_cbatch14 cbatch68_indices cert_cbatch68_r14 320 (by decide)

end Batch
end Math
