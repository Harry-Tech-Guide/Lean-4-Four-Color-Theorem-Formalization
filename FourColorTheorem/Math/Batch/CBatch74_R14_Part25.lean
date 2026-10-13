import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 74: Ring 14 (Part 25)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 502, 503, 504.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 74. -/
def cbatch74_indices : List Nat :=
  [502, 503, 504]

/-- Unified in-kernel certification for CBatch 74 (Ring 14, Part 25). -/
theorem cert_cbatch74_r14 : checkCRingBatch14 cbatch74_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_502_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 502 = true :=
  certified_of_cbatch14 cbatch74_indices cert_cbatch74_r14 502 (by decide)

theorem cert_config_503_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 503 = true :=
  certified_of_cbatch14 cbatch74_indices cert_cbatch74_r14 503 (by decide)

theorem cert_config_504_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 504 = true :=
  certified_of_cbatch14 cbatch74_indices cert_cbatch74_r14 504 (by decide)

end Batch
end Math
