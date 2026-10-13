import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 52: Ring 14 (Part 3)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 220, 221, 225.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 52. -/
def cbatch52_indices : List Nat :=
  [220, 221, 225]

/-- Unified in-kernel certification for CBatch 52 (Ring 14, Part 3). -/
theorem cert_cbatch52_r14 : checkCRingBatch14 cbatch52_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_220_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 220 = true :=
  certified_of_cbatch14 cbatch52_indices cert_cbatch52_r14 220 (by decide)

theorem cert_config_221_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 221 = true :=
  certified_of_cbatch14 cbatch52_indices cert_cbatch52_r14 221 (by decide)

theorem cert_config_225_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 225 = true :=
  certified_of_cbatch14 cbatch52_indices cert_cbatch52_r14 225 (by decide)

end Batch
end Math
