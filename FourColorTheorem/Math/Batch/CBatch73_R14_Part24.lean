import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 73: Ring 14 (Part 24)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 499, 500, 501.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 73. -/
def cbatch73_indices : List Nat :=
  [499, 500, 501]

/-- Unified in-kernel certification for CBatch 73 (Ring 14, Part 24). -/
theorem cert_cbatch73_r14 : checkCRingBatch14 cbatch73_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_499_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 499 = true :=
  certified_of_cbatch14 cbatch73_indices cert_cbatch73_r14 499 (by decide)

theorem cert_config_500_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 500 = true :=
  certified_of_cbatch14 cbatch73_indices cert_cbatch73_r14 500 (by decide)

theorem cert_config_501_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 501 = true :=
  certified_of_cbatch14 cbatch73_indices cert_cbatch73_r14 501 (by decide)

end Batch
end Math
