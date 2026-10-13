import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 51: Ring 14 (Part 2)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 215, 216, 218.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 51. -/
def cbatch51_indices : List Nat :=
  [215, 216, 218]

/-- Unified in-kernel certification for CBatch 51 (Ring 14, Part 2). -/
theorem cert_cbatch51_r14 : checkCRingBatch14 cbatch51_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_215_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 215 = true :=
  certified_of_cbatch14 cbatch51_indices cert_cbatch51_r14 215 (by decide)

theorem cert_config_216_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 216 = true :=
  certified_of_cbatch14 cbatch51_indices cert_cbatch51_r14 216 (by decide)

theorem cert_config_218_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 218 = true :=
  certified_of_cbatch14 cbatch51_indices cert_cbatch51_r14 218 (by decide)

end Batch
end Math
