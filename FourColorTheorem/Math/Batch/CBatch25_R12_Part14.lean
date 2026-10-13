import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 25: Ring 12 (Part 14)

This module certifies the C-reducibility of 4 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 581, 591, 598, 622.
-/

/-- The 4 ring-12 configuration indices certified in CBatch 25. -/
def cbatch25_indices : List Nat :=
  [581, 591, 598, 622]

/-- Unified in-kernel certification for CBatch 25 (Ring 12, Part 14). -/
theorem cert_cbatch25_r12 : checkCRingBatch 12 cbatch25_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_581_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 581 = true :=
  certified_of_cbatch 12 cbatch25_indices cert_cbatch25_r12 581 (by decide)

theorem cert_config_591_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 591 = true :=
  certified_of_cbatch 12 cbatch25_indices cert_cbatch25_r12 591 (by decide)

theorem cert_config_598_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 598 = true :=
  certified_of_cbatch 12 cbatch25_indices cert_cbatch25_r12 598 (by decide)

theorem cert_config_622_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 622 = true :=
  certified_of_cbatch 12 cbatch25_indices cert_cbatch25_r12 622 (by decide)

end Batch
end Math
