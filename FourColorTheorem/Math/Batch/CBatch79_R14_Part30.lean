import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 79: Ring 14 (Part 30)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 533, 534, 535.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 79. -/
def cbatch79_indices : List Nat :=
  [533, 534, 535]

/-- Unified in-kernel certification for CBatch 79 (Ring 14, Part 30). -/
theorem cert_cbatch79_r14 : checkCRingBatch14 cbatch79_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_533_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 533 = true :=
  certified_of_cbatch14 cbatch79_indices cert_cbatch79_r14 533 (by decide)

theorem cert_config_534_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 534 = true :=
  certified_of_cbatch14 cbatch79_indices cert_cbatch79_r14 534 (by decide)

theorem cert_config_535_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 535 = true :=
  certified_of_cbatch14 cbatch79_indices cert_cbatch79_r14 535 (by decide)

end Batch
end Math
