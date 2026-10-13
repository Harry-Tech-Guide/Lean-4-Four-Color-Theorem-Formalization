import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 42: Ring 13 (Part 17)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 457, 458, 459, 460, 463, 465.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 42. -/
def cbatch42_indices : List Nat :=
  [457, 458, 459, 460, 463, 465]

/-- Unified in-kernel certification for CBatch 42 (Ring 13, Part 17). -/
theorem cert_cbatch42_r13 : checkCRingBatch13 cbatch42_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_457_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 457 = true :=
  certified_of_cbatch13 cbatch42_indices cert_cbatch42_r13 457 (by decide)

theorem cert_config_458_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 458 = true :=
  certified_of_cbatch13 cbatch42_indices cert_cbatch42_r13 458 (by decide)

theorem cert_config_459_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 459 = true :=
  certified_of_cbatch13 cbatch42_indices cert_cbatch42_r13 459 (by decide)

theorem cert_config_460_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 460 = true :=
  certified_of_cbatch13 cbatch42_indices cert_cbatch42_r13 460 (by decide)

theorem cert_config_463_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 463 = true :=
  certified_of_cbatch13 cbatch42_indices cert_cbatch42_r13 463 (by decide)

theorem cert_config_465_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 465 = true :=
  certified_of_cbatch13 cbatch42_indices cert_cbatch42_r13 465 (by decide)

end Batch
end Math
