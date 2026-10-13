import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 86: Ring 14 (Part 37)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 619, 620, 629.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 86. -/
def cbatch86_indices : List Nat :=
  [619, 620, 629]

/-- Unified in-kernel certification for CBatch 86 (Ring 14, Part 37). -/
theorem cert_cbatch86_r14 : checkCRingBatch14 cbatch86_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_619_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 619 = true :=
  certified_of_cbatch14 cbatch86_indices cert_cbatch86_r14 619 (by decide)

theorem cert_config_620_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 620 = true :=
  certified_of_cbatch14 cbatch86_indices cert_cbatch86_r14 620 (by decide)

theorem cert_config_629_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 629 = true :=
  certified_of_cbatch14 cbatch86_indices cert_cbatch86_r14 629 (by decide)

end Batch
end Math
