import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 21: Ring 12 (Part 10)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 411, 412, 414, 418, 425, 427.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 21. -/
def cbatch21_indices : List Nat :=
  [411, 412, 414, 418, 425, 427]

/-- Unified in-kernel certification for CBatch 21 (Ring 12, Part 10). -/
theorem cert_cbatch21_r12 : checkCRingBatch 12 cbatch21_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_411_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 411 = true :=
  certified_of_cbatch 12 cbatch21_indices cert_cbatch21_r12 411 (by decide)

theorem cert_config_412_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 412 = true :=
  certified_of_cbatch 12 cbatch21_indices cert_cbatch21_r12 412 (by decide)

theorem cert_config_414_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 414 = true :=
  certified_of_cbatch 12 cbatch21_indices cert_cbatch21_r12 414 (by decide)

theorem cert_config_418_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 418 = true :=
  certified_of_cbatch 12 cbatch21_indices cert_cbatch21_r12 418 (by decide)

theorem cert_config_425_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 425 = true :=
  certified_of_cbatch 12 cbatch21_indices cert_cbatch21_r12 425 (by decide)

theorem cert_config_427_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 427 = true :=
  certified_of_cbatch 12 cbatch21_indices cert_cbatch21_r12 427 (by decide)

end Batch
end Math
