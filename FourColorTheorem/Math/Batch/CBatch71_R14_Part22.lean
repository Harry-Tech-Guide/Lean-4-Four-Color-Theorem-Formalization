import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 71: Ring 14 (Part 22)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 488, 489, 492.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 71. -/
def cbatch71_indices : List Nat :=
  [488, 489, 492]

/-- Unified in-kernel certification for CBatch 71 (Ring 14, Part 22). -/
theorem cert_cbatch71_r14 : checkCRingBatch14 cbatch71_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_488_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 488 = true :=
  certified_of_cbatch14 cbatch71_indices cert_cbatch71_r14 488 (by decide)

theorem cert_config_489_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 489 = true :=
  certified_of_cbatch14 cbatch71_indices cert_cbatch71_r14 489 (by decide)

theorem cert_config_492_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 492 = true :=
  certified_of_cbatch14 cbatch71_indices cert_cbatch71_r14 492 (by decide)

end Batch
end Math
