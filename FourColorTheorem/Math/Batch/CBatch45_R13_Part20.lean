import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 45: Ring 13 (Part 20)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 480, 519, 520, 521, 523, 537.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 45. -/
def cbatch45_indices : List Nat :=
  [480, 519, 520, 521, 523, 537]

/-- Unified in-kernel certification for CBatch 45 (Ring 13, Part 20). -/
theorem cert_cbatch45_r13 : checkCRingBatch13 cbatch45_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_480_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 480 = true :=
  certified_of_cbatch13 cbatch45_indices cert_cbatch45_r13 480 (by decide)

theorem cert_config_519_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 519 = true :=
  certified_of_cbatch13 cbatch45_indices cert_cbatch45_r13 519 (by decide)

theorem cert_config_520_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 520 = true :=
  certified_of_cbatch13 cbatch45_indices cert_cbatch45_r13 520 (by decide)

theorem cert_config_521_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 521 = true :=
  certified_of_cbatch13 cbatch45_indices cert_cbatch45_r13 521 (by decide)

theorem cert_config_523_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 523 = true :=
  certified_of_cbatch13 cbatch45_indices cert_cbatch45_r13 523 (by decide)

theorem cert_config_537_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 537 = true :=
  certified_of_cbatch13 cbatch45_indices cert_cbatch45_r13 537 (by decide)

end Batch
end Math
