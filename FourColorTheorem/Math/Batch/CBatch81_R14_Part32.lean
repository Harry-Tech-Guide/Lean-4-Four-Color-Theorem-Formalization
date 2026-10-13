import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 81: Ring 14 (Part 32)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 543, 546, 549.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 81. -/
def cbatch81_indices : List Nat :=
  [543, 546, 549]

/-- Unified in-kernel certification for CBatch 81 (Ring 14, Part 32). -/
theorem cert_cbatch81_r14 : checkCRingBatch14 cbatch81_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_543_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 543 = true :=
  certified_of_cbatch14 cbatch81_indices cert_cbatch81_r14 543 (by decide)

theorem cert_config_546_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 546 = true :=
  certified_of_cbatch14 cbatch81_indices cert_cbatch81_r14 546 (by decide)

theorem cert_config_549_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 549 = true :=
  certified_of_cbatch14 cbatch81_indices cert_cbatch81_r14 549 (by decide)

end Batch
end Math
