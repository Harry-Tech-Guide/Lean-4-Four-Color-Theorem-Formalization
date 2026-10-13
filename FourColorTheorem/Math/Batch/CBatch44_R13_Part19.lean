import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 44: Ring 13 (Part 19)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 474, 475, 476, 477, 478, 479.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 44. -/
def cbatch44_indices : List Nat :=
  [474, 475, 476, 477, 478, 479]

/-- Unified in-kernel certification for CBatch 44 (Ring 13, Part 19). -/
theorem cert_cbatch44_r13 : checkCRingBatch13 cbatch44_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_474_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 474 = true :=
  certified_of_cbatch13 cbatch44_indices cert_cbatch44_r13 474 (by decide)

theorem cert_config_475_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 475 = true :=
  certified_of_cbatch13 cbatch44_indices cert_cbatch44_r13 475 (by decide)

theorem cert_config_476_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 476 = true :=
  certified_of_cbatch13 cbatch44_indices cert_cbatch44_r13 476 (by decide)

theorem cert_config_477_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 477 = true :=
  certified_of_cbatch13 cbatch44_indices cert_cbatch44_r13 477 (by decide)

theorem cert_config_478_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 478 = true :=
  certified_of_cbatch13 cbatch44_indices cert_cbatch44_r13 478 (by decide)

theorem cert_config_479_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 479 = true :=
  certified_of_cbatch13 cbatch44_indices cert_cbatch44_r13 479 (by decide)

end Batch
end Math
