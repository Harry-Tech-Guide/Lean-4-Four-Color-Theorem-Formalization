import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 13: Ring 12 (Part 2)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 73, 74, 79, 88, 89, 126.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 13. -/
def cbatch13_indices : List Nat :=
  [73, 74, 79, 88, 89, 126]

/-- Unified in-kernel certification for CBatch 13 (Ring 12, Part 2). -/
theorem cert_cbatch13_r12 : checkCRingBatch 12 cbatch13_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_73_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 73 = true :=
  certified_of_cbatch 12 cbatch13_indices cert_cbatch13_r12 73 (by decide)

theorem cert_config_74_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 74 = true :=
  certified_of_cbatch 12 cbatch13_indices cert_cbatch13_r12 74 (by decide)

theorem cert_config_79_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 79 = true :=
  certified_of_cbatch 12 cbatch13_indices cert_cbatch13_r12 79 (by decide)

theorem cert_config_88_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 88 = true :=
  certified_of_cbatch 12 cbatch13_indices cert_cbatch13_r12 88 (by decide)

theorem cert_config_89_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 89 = true :=
  certified_of_cbatch 12 cbatch13_indices cert_cbatch13_r12 89 (by decide)

theorem cert_config_126_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 126 = true :=
  certified_of_cbatch 12 cbatch13_indices cert_cbatch13_r12 126 (by decide)

end Batch
end Math
