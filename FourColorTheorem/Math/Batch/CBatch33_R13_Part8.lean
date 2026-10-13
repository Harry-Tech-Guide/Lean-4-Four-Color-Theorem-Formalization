import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 33: Ring 13 (Part 8)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 203, 204, 205, 209, 211, 213.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 33. -/
def cbatch33_indices : List Nat :=
  [203, 204, 205, 209, 211, 213]

/-- Unified in-kernel certification for CBatch 33 (Ring 13, Part 8). -/
theorem cert_cbatch33_r13 : checkCRingBatch13 cbatch33_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_203_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 203 = true :=
  certified_of_cbatch13 cbatch33_indices cert_cbatch33_r13 203 (by decide)

theorem cert_config_204_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 204 = true :=
  certified_of_cbatch13 cbatch33_indices cert_cbatch33_r13 204 (by decide)

theorem cert_config_205_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 205 = true :=
  certified_of_cbatch13 cbatch33_indices cert_cbatch33_r13 205 (by decide)

theorem cert_config_209_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 209 = true :=
  certified_of_cbatch13 cbatch33_indices cert_cbatch33_r13 209 (by decide)

theorem cert_config_211_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 211 = true :=
  certified_of_cbatch13 cbatch33_indices cert_cbatch33_r13 211 (by decide)

theorem cert_config_213_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 213 = true :=
  certified_of_cbatch13 cbatch33_indices cert_cbatch33_r13 213 (by decide)

end Batch
end Math
