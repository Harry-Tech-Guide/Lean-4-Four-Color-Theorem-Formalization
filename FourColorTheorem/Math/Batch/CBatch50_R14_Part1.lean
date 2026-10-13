import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 50: Ring 14 (Part 1)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 202, 206, 212.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 50. -/
def cbatch50_indices : List Nat :=
  [202, 206, 212]

/-- Unified in-kernel certification for CBatch 50 (Ring 14, Part 1). -/
theorem cert_cbatch50_r14 : checkCRingBatch14 cbatch50_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_202_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 202 = true :=
  certified_of_cbatch14 cbatch50_indices cert_cbatch50_r14 202 (by decide)

theorem cert_config_206_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 206 = true :=
  certified_of_cbatch14 cbatch50_indices cert_cbatch50_r14 206 (by decide)

theorem cert_config_212_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 212 = true :=
  certified_of_cbatch14 cbatch50_indices cert_cbatch50_r14 212 (by decide)

end Batch
end Math
