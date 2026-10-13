import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 29: Ring 13 (Part 4)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 169, 171, 177, 179, 180, 181.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 29. -/
def cbatch29_indices : List Nat :=
  [169, 171, 177, 179, 180, 181]

/-- Unified in-kernel certification for CBatch 29 (Ring 13, Part 4). -/
theorem cert_cbatch29_r13 : checkCRingBatch13 cbatch29_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_169_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 169 = true :=
  certified_of_cbatch13 cbatch29_indices cert_cbatch29_r13 169 (by decide)

theorem cert_config_171_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 171 = true :=
  certified_of_cbatch13 cbatch29_indices cert_cbatch29_r13 171 (by decide)

theorem cert_config_177_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 177 = true :=
  certified_of_cbatch13 cbatch29_indices cert_cbatch29_r13 177 (by decide)

theorem cert_config_179_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 179 = true :=
  certified_of_cbatch13 cbatch29_indices cert_cbatch29_r13 179 (by decide)

theorem cert_config_180_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 180 = true :=
  certified_of_cbatch13 cbatch29_indices cert_cbatch29_r13 180 (by decide)

theorem cert_config_181_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 181 = true :=
  certified_of_cbatch13 cbatch29_indices cert_cbatch29_r13 181 (by decide)

end Batch
end Math
