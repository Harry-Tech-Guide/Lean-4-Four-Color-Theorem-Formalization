import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 43: Ring 13 (Part 18)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 466, 467, 468, 469, 470, 473.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 43. -/
def cbatch43_indices : List Nat :=
  [466, 467, 468, 469, 470, 473]

/-- Unified in-kernel certification for CBatch 43 (Ring 13, Part 18). -/
theorem cert_cbatch43_r13 : checkCRingBatch13 cbatch43_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_466_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 466 = true :=
  certified_of_cbatch13 cbatch43_indices cert_cbatch43_r13 466 (by decide)

theorem cert_config_467_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 467 = true :=
  certified_of_cbatch13 cbatch43_indices cert_cbatch43_r13 467 (by decide)

theorem cert_config_468_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 468 = true :=
  certified_of_cbatch13 cbatch43_indices cert_cbatch43_r13 468 (by decide)

theorem cert_config_469_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 469 = true :=
  certified_of_cbatch13 cbatch43_indices cert_cbatch43_r13 469 (by decide)

theorem cert_config_470_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 470 = true :=
  certified_of_cbatch13 cbatch43_indices cert_cbatch43_r13 470 (by decide)

theorem cert_config_473_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 473 = true :=
  certified_of_cbatch13 cbatch43_indices cert_cbatch43_r13 473 (by decide)

end Batch
end Math
