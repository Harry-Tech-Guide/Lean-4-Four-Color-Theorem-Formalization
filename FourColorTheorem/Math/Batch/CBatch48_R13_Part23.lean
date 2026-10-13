import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 48: Ring 13 (Part 23)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 592, 595, 600, 601, 602, 603.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 48. -/
def cbatch48_indices : List Nat :=
  [592, 595, 600, 601, 602, 603]

/-- Unified in-kernel certification for CBatch 48 (Ring 13, Part 23). -/
theorem cert_cbatch48_r13 : checkCRingBatch13 cbatch48_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_592_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 592 = true :=
  certified_of_cbatch13 cbatch48_indices cert_cbatch48_r13 592 (by decide)

theorem cert_config_595_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 595 = true :=
  certified_of_cbatch13 cbatch48_indices cert_cbatch48_r13 595 (by decide)

theorem cert_config_600_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 600 = true :=
  certified_of_cbatch13 cbatch48_indices cert_cbatch48_r13 600 (by decide)

theorem cert_config_601_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 601 = true :=
  certified_of_cbatch13 cbatch48_indices cert_cbatch48_r13 601 (by decide)

theorem cert_config_602_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 602 = true :=
  certified_of_cbatch13 cbatch48_indices cert_cbatch48_r13 602 (by decide)

theorem cert_config_603_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 603 = true :=
  certified_of_cbatch13 cbatch48_indices cert_cbatch48_r13 603 (by decide)

end Batch
end Math
