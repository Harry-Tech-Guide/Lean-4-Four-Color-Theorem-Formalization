import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 16: Ring 12 (Part 5)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 144, 145, 147, 148, 152, 158.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 16. -/
def cbatch16_indices : List Nat :=
  [144, 145, 147, 148, 152, 158]

/-- Unified in-kernel certification for CBatch 16 (Ring 12, Part 5). -/
theorem cert_cbatch16_r12 : checkCRingBatch 12 cbatch16_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_144_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 144 = true :=
  certified_of_cbatch 12 cbatch16_indices cert_cbatch16_r12 144 (by decide)

theorem cert_config_145_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 145 = true :=
  certified_of_cbatch 12 cbatch16_indices cert_cbatch16_r12 145 (by decide)

theorem cert_config_147_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 147 = true :=
  certified_of_cbatch 12 cbatch16_indices cert_cbatch16_r12 147 (by decide)

theorem cert_config_148_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 148 = true :=
  certified_of_cbatch 12 cbatch16_indices cert_cbatch16_r12 148 (by decide)

theorem cert_config_152_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 152 = true :=
  certified_of_cbatch 12 cbatch16_indices cert_cbatch16_r12 152 (by decide)

theorem cert_config_158_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 158 = true :=
  certified_of_cbatch 12 cbatch16_indices cert_cbatch16_r12 158 (by decide)

end Batch
end Math
