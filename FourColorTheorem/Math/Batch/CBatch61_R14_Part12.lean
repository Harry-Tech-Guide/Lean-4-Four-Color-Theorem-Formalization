import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 61: Ring 14 (Part 12)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 292, 293, 294.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 61. -/
def cbatch61_indices : List Nat :=
  [292, 293, 294]

/-- Unified in-kernel certification for CBatch 61 (Ring 14, Part 12). -/
theorem cert_cbatch61_r14 : checkCRingBatch14 cbatch61_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_292_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 292 = true :=
  certified_of_cbatch14 cbatch61_indices cert_cbatch61_r14 292 (by decide)

theorem cert_config_293_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 293 = true :=
  certified_of_cbatch14 cbatch61_indices cert_cbatch61_r14 293 (by decide)

theorem cert_config_294_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 294 = true :=
  certified_of_cbatch14 cbatch61_indices cert_cbatch61_r14 294 (by decide)

end Batch
end Math
