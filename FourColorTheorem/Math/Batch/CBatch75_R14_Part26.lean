import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 75: Ring 14 (Part 26)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 505, 506, 508.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 75. -/
def cbatch75_indices : List Nat :=
  [505, 506, 508]

/-- Unified in-kernel certification for CBatch 75 (Ring 14, Part 26). -/
theorem cert_cbatch75_r14 : checkCRingBatch14 cbatch75_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_505_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 505 = true :=
  certified_of_cbatch14 cbatch75_indices cert_cbatch75_r14 505 (by decide)

theorem cert_config_506_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 506 = true :=
  certified_of_cbatch14 cbatch75_indices cert_cbatch75_r14 506 (by decide)

theorem cert_config_508_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 508 = true :=
  certified_of_cbatch14 cbatch75_indices cert_cbatch75_r14 508 (by decide)

end Batch
end Math
