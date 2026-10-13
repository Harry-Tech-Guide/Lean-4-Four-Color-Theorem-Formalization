import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 31: Ring 13 (Part 6)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 188, 189, 191, 192, 193, 194.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 31. -/
def cbatch31_indices : List Nat :=
  [188, 189, 191, 192, 193, 194]

/-- Unified in-kernel certification for CBatch 31 (Ring 13, Part 6). -/
theorem cert_cbatch31_r13 : checkCRingBatch13 cbatch31_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_188_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 188 = true :=
  certified_of_cbatch13 cbatch31_indices cert_cbatch31_r13 188 (by decide)

theorem cert_config_189_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 189 = true :=
  certified_of_cbatch13 cbatch31_indices cert_cbatch31_r13 189 (by decide)

theorem cert_config_191_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 191 = true :=
  certified_of_cbatch13 cbatch31_indices cert_cbatch31_r13 191 (by decide)

theorem cert_config_192_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 192 = true :=
  certified_of_cbatch13 cbatch31_indices cert_cbatch31_r13 192 (by decide)

theorem cert_config_193_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 193 = true :=
  certified_of_cbatch13 cbatch31_indices cert_cbatch31_r13 193 (by decide)

theorem cert_config_194_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 194 = true :=
  certified_of_cbatch13 cbatch31_indices cert_cbatch31_r13 194 (by decide)

end Batch
end Math
