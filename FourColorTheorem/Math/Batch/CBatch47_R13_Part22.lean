import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 47: Ring 13 (Part 22)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 583, 584, 585, 586, 587, 588.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 47. -/
def cbatch47_indices : List Nat :=
  [583, 584, 585, 586, 587, 588]

/-- Unified in-kernel certification for CBatch 47 (Ring 13, Part 22). -/
theorem cert_cbatch47_r13 : checkCRingBatch13 cbatch47_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_583_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 583 = true :=
  certified_of_cbatch13 cbatch47_indices cert_cbatch47_r13 583 (by decide)

theorem cert_config_584_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 584 = true :=
  certified_of_cbatch13 cbatch47_indices cert_cbatch47_r13 584 (by decide)

theorem cert_config_585_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 585 = true :=
  certified_of_cbatch13 cbatch47_indices cert_cbatch47_r13 585 (by decide)

theorem cert_config_586_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 586 = true :=
  certified_of_cbatch13 cbatch47_indices cert_cbatch47_r13 586 (by decide)

theorem cert_config_587_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 587 = true :=
  certified_of_cbatch13 cbatch47_indices cert_cbatch47_r13 587 (by decide)

theorem cert_config_588_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 588 = true :=
  certified_of_cbatch13 cbatch47_indices cert_cbatch47_r13 588 (by decide)

end Batch
end Math
