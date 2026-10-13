import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 30: Ring 13 (Part 5)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 182, 183, 184, 185, 186, 187.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 30. -/
def cbatch30_indices : List Nat :=
  [182, 183, 184, 185, 186, 187]

/-- Unified in-kernel certification for CBatch 30 (Ring 13, Part 5). -/
theorem cert_cbatch30_r13 : checkCRingBatch13 cbatch30_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_182_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 182 = true :=
  certified_of_cbatch13 cbatch30_indices cert_cbatch30_r13 182 (by decide)

theorem cert_config_183_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 183 = true :=
  certified_of_cbatch13 cbatch30_indices cert_cbatch30_r13 183 (by decide)

theorem cert_config_184_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 184 = true :=
  certified_of_cbatch13 cbatch30_indices cert_cbatch30_r13 184 (by decide)

theorem cert_config_185_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 185 = true :=
  certified_of_cbatch13 cbatch30_indices cert_cbatch30_r13 185 (by decide)

theorem cert_config_186_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 186 = true :=
  certified_of_cbatch13 cbatch30_indices cert_cbatch30_r13 186 (by decide)

theorem cert_config_187_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 187 = true :=
  certified_of_cbatch13 cbatch30_indices cert_cbatch30_r13 187 (by decide)

end Batch
end Math
