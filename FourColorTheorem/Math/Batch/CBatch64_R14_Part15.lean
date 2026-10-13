import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 64: Ring 14 (Part 15)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 301, 302, 303.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 64. -/
def cbatch64_indices : List Nat :=
  [301, 302, 303]

/-- Unified in-kernel certification for CBatch 64 (Ring 14, Part 15). -/
theorem cert_cbatch64_r14 : checkCRingBatch14 cbatch64_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_301_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 301 = true :=
  certified_of_cbatch14 cbatch64_indices cert_cbatch64_r14 301 (by decide)

theorem cert_config_302_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 302 = true :=
  certified_of_cbatch14 cbatch64_indices cert_cbatch64_r14 302 (by decide)

theorem cert_config_303_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 303 = true :=
  certified_of_cbatch14 cbatch64_indices cert_cbatch64_r14 303 (by decide)

end Batch
end Math
