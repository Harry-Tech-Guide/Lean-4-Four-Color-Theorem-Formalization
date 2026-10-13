import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 67: Ring 14 (Part 18)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 311, 314, 317.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 67. -/
def cbatch67_indices : List Nat :=
  [311, 314, 317]

/-- Unified in-kernel certification for CBatch 67 (Ring 14, Part 18). -/
theorem cert_cbatch67_r14 : checkCRingBatch14 cbatch67_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_311_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 311 = true :=
  certified_of_cbatch14 cbatch67_indices cert_cbatch67_r14 311 (by decide)

theorem cert_config_314_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 314 = true :=
  certified_of_cbatch14 cbatch67_indices cert_cbatch67_r14 314 (by decide)

theorem cert_config_317_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 317 = true :=
  certified_of_cbatch14 cbatch67_indices cert_cbatch67_r14 317 (by decide)

end Batch
end Math
