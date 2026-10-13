import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 72: Ring 14 (Part 23)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 496, 497, 498.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 72. -/
def cbatch72_indices : List Nat :=
  [496, 497, 498]

/-- Unified in-kernel certification for CBatch 72 (Ring 14, Part 23). -/
theorem cert_cbatch72_r14 : checkCRingBatch14 cbatch72_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_496_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 496 = true :=
  certified_of_cbatch14 cbatch72_indices cert_cbatch72_r14 496 (by decide)

theorem cert_config_497_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 497 = true :=
  certified_of_cbatch14 cbatch72_indices cert_cbatch72_r14 497 (by decide)

theorem cert_config_498_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 498 = true :=
  certified_of_cbatch14 cbatch72_indices cert_cbatch72_r14 498 (by decide)

end Batch
end Math
