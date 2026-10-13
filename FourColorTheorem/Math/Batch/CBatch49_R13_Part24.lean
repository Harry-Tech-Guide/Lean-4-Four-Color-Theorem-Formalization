import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 49: Ring 13 (Part 24)

This module certifies the C-reducibility of 4 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 616, 624, 625, 626.
-/

/-- The 4 ring-13 configuration indices certified in CBatch 49. -/
def cbatch49_indices : List Nat :=
  [616, 624, 625, 626]

/-- Unified in-kernel certification for CBatch 49 (Ring 13, Part 24). -/
theorem cert_cbatch49_r13 : checkCRingBatch13 cbatch49_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_616_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 616 = true :=
  certified_of_cbatch13 cbatch49_indices cert_cbatch49_r13 616 (by decide)

theorem cert_config_624_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 624 = true :=
  certified_of_cbatch13 cbatch49_indices cert_cbatch49_r13 624 (by decide)

theorem cert_config_625_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 625 = true :=
  certified_of_cbatch13 cbatch49_indices cert_cbatch49_r13 625 (by decide)

theorem cert_config_626_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 626 = true :=
  certified_of_cbatch13 cbatch49_indices cert_cbatch49_r13 626 (by decide)

end Batch
end Math
