import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 66: Ring 14 (Part 17)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 308, 309, 310.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 66. -/
def cbatch66_indices : List Nat :=
  [308, 309, 310]

/-- Unified in-kernel certification for CBatch 66 (Ring 14, Part 17). -/
theorem cert_cbatch66_r14 : checkCRingBatch14 cbatch66_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_308_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 308 = true :=
  certified_of_cbatch14 cbatch66_indices cert_cbatch66_r14 308 (by decide)

theorem cert_config_309_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 309 = true :=
  certified_of_cbatch14 cbatch66_indices cert_cbatch66_r14 309 (by decide)

theorem cert_config_310_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 310 = true :=
  certified_of_cbatch14 cbatch66_indices cert_cbatch66_r14 310 (by decide)

end Batch
end Math
