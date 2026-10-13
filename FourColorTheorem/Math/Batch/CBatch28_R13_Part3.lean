import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 28: Ring 13 (Part 3)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 162, 163, 164, 165, 166, 168.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 28. -/
def cbatch28_indices : List Nat :=
  [162, 163, 164, 165, 166, 168]

/-- Unified in-kernel certification for CBatch 28 (Ring 13, Part 3). -/
theorem cert_cbatch28_r13 : checkCRingBatch13 cbatch28_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_162_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 162 = true :=
  certified_of_cbatch13 cbatch28_indices cert_cbatch28_r13 162 (by decide)

theorem cert_config_163_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 163 = true :=
  certified_of_cbatch13 cbatch28_indices cert_cbatch28_r13 163 (by decide)

theorem cert_config_164_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 164 = true :=
  certified_of_cbatch13 cbatch28_indices cert_cbatch28_r13 164 (by decide)

theorem cert_config_165_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 165 = true :=
  certified_of_cbatch13 cbatch28_indices cert_cbatch28_r13 165 (by decide)

theorem cert_config_166_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 166 = true :=
  certified_of_cbatch13 cbatch28_indices cert_cbatch28_r13 166 (by decide)

theorem cert_config_168_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 168 = true :=
  certified_of_cbatch13 cbatch28_indices cert_cbatch28_r13 168 (by decide)

end Batch
end Math
