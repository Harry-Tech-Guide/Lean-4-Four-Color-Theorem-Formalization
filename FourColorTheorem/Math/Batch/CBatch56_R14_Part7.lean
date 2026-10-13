import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 56: Ring 14 (Part 7)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 236, 269, 276.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 56. -/
def cbatch56_indices : List Nat :=
  [236, 269, 276]

/-- Unified in-kernel certification for CBatch 56 (Ring 14, Part 7). -/
theorem cert_cbatch56_r14 : checkCRingBatch14 cbatch56_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_236_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 236 = true :=
  certified_of_cbatch14 cbatch56_indices cert_cbatch56_r14 236 (by decide)

theorem cert_config_269_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 269 = true :=
  certified_of_cbatch14 cbatch56_indices cert_cbatch56_r14 269 (by decide)

theorem cert_config_276_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 276 = true :=
  certified_of_cbatch14 cbatch56_indices cert_cbatch56_r14 276 (by decide)

end Batch
end Math
