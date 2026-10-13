import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 65: Ring 14 (Part 16)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 304, 306, 307.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 65. -/
def cbatch65_indices : List Nat :=
  [304, 306, 307]

/-- Unified in-kernel certification for CBatch 65 (Ring 14, Part 16). -/
theorem cert_cbatch65_r14 : checkCRingBatch14 cbatch65_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_304_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 304 = true :=
  certified_of_cbatch14 cbatch65_indices cert_cbatch65_r14 304 (by decide)

theorem cert_config_306_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 306 = true :=
  certified_of_cbatch14 cbatch65_indices cert_cbatch65_r14 306 (by decide)

theorem cert_config_307_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 307 = true :=
  certified_of_cbatch14 cbatch65_indices cert_cbatch65_r14 307 (by decide)

end Batch
end Math
