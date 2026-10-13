import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 57: Ring 14 (Part 8)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 277, 280, 281.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 57. -/
def cbatch57_indices : List Nat :=
  [277, 280, 281]

/-- Unified in-kernel certification for CBatch 57 (Ring 14, Part 8). -/
theorem cert_cbatch57_r14 : checkCRingBatch14 cbatch57_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_277_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 277 = true :=
  certified_of_cbatch14 cbatch57_indices cert_cbatch57_r14 277 (by decide)

theorem cert_config_280_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 280 = true :=
  certified_of_cbatch14 cbatch57_indices cert_cbatch57_r14 280 (by decide)

theorem cert_config_281_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 281 = true :=
  certified_of_cbatch14 cbatch57_indices cert_cbatch57_r14 281 (by decide)

end Batch
end Math
