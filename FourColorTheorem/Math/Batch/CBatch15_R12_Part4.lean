import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 15: Ring 12 (Part 4)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 138, 139, 140, 141, 142, 143.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 15. -/
def cbatch15_indices : List Nat :=
  [138, 139, 140, 141, 142, 143]

/-- Unified in-kernel certification for CBatch 15 (Ring 12, Part 4). -/
theorem cert_cbatch15_r12 : checkCRingBatch 12 cbatch15_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_138_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 138 = true :=
  certified_of_cbatch 12 cbatch15_indices cert_cbatch15_r12 138 (by decide)

theorem cert_config_139_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 139 = true :=
  certified_of_cbatch 12 cbatch15_indices cert_cbatch15_r12 139 (by decide)

theorem cert_config_140_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 140 = true :=
  certified_of_cbatch 12 cbatch15_indices cert_cbatch15_r12 140 (by decide)

theorem cert_config_141_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 141 = true :=
  certified_of_cbatch 12 cbatch15_indices cert_cbatch15_r12 141 (by decide)

theorem cert_config_142_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 142 = true :=
  certified_of_cbatch 12 cbatch15_indices cert_cbatch15_r12 142 (by decide)

theorem cert_config_143_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 143 = true :=
  certified_of_cbatch 12 cbatch15_indices cert_cbatch15_r12 143 (by decide)

end Batch
end Math
