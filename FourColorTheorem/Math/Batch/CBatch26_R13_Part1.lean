import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 26: Ring 13 (Part 1)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 22, 82, 94, 95, 100, 101.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 26. -/
def cbatch26_indices : List Nat :=
  [22, 82, 94, 95, 100, 101]

/-- Unified in-kernel certification for CBatch 26 (Ring 13, Part 1). -/
theorem cert_cbatch26_r13 : checkCRingBatch13 cbatch26_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_22_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 22 = true :=
  certified_of_cbatch13 cbatch26_indices cert_cbatch26_r13 22 (by decide)

theorem cert_config_82_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 82 = true :=
  certified_of_cbatch13 cbatch26_indices cert_cbatch26_r13 82 (by decide)

theorem cert_config_94_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 94 = true :=
  certified_of_cbatch13 cbatch26_indices cert_cbatch26_r13 94 (by decide)

theorem cert_config_95_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 95 = true :=
  certified_of_cbatch13 cbatch26_indices cert_cbatch26_r13 95 (by decide)

theorem cert_config_100_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 100 = true :=
  certified_of_cbatch13 cbatch26_indices cert_cbatch26_r13 100 (by decide)

theorem cert_config_101_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 101 = true :=
  certified_of_cbatch13 cbatch26_indices cert_cbatch26_r13 101 (by decide)

end Batch
end Math
