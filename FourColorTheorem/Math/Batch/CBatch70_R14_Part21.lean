import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 70: Ring 14 (Part 21)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 398, 485, 487.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 70. -/
def cbatch70_indices : List Nat :=
  [398, 485, 487]

/-- Unified in-kernel certification for CBatch 70 (Ring 14, Part 21). -/
theorem cert_cbatch70_r14 : checkCRingBatch14 cbatch70_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_398_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 398 = true :=
  certified_of_cbatch14 cbatch70_indices cert_cbatch70_r14 398 (by decide)

theorem cert_config_485_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 485 = true :=
  certified_of_cbatch14 cbatch70_indices cert_cbatch70_r14 485 (by decide)

theorem cert_config_487_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 487 = true :=
  certified_of_cbatch14 cbatch70_indices cert_cbatch70_r14 487 (by decide)

end Batch
end Math
