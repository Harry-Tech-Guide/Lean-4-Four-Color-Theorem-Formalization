import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 24: Ring 12 (Part 13)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 507, 527, 556, 574, 575, 578.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 24. -/
def cbatch24_indices : List Nat :=
  [507, 527, 556, 574, 575, 578]

/-- Unified in-kernel certification for CBatch 24 (Ring 12, Part 13). -/
theorem cert_cbatch24_r12 : checkCRingBatch 12 cbatch24_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_507_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 507 = true :=
  certified_of_cbatch 12 cbatch24_indices cert_cbatch24_r12 507 (by decide)

theorem cert_config_527_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 527 = true :=
  certified_of_cbatch 12 cbatch24_indices cert_cbatch24_r12 527 (by decide)

theorem cert_config_556_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 556 = true :=
  certified_of_cbatch 12 cbatch24_indices cert_cbatch24_r12 556 (by decide)

theorem cert_config_574_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 574 = true :=
  certified_of_cbatch 12 cbatch24_indices cert_cbatch24_r12 574 (by decide)

theorem cert_config_575_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 575 = true :=
  certified_of_cbatch 12 cbatch24_indices cert_cbatch24_r12 575 (by decide)

theorem cert_config_578_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 578 = true :=
  certified_of_cbatch 12 cbatch24_indices cert_cbatch24_r12 578 (by decide)

end Batch
end Math
