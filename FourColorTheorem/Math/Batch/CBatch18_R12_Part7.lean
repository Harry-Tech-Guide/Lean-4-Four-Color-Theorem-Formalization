import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 18: Ring 12 (Part 7)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 342, 344, 345, 346, 352, 353.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 18. -/
def cbatch18_indices : List Nat :=
  [342, 344, 345, 346, 352, 353]

/-- Unified in-kernel certification for CBatch 18 (Ring 12, Part 7). -/
theorem cert_cbatch18_r12 : checkCRingBatch 12 cbatch18_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_342_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 342 = true :=
  certified_of_cbatch 12 cbatch18_indices cert_cbatch18_r12 342 (by decide)

theorem cert_config_344_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 344 = true :=
  certified_of_cbatch 12 cbatch18_indices cert_cbatch18_r12 344 (by decide)

theorem cert_config_345_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 345 = true :=
  certified_of_cbatch 12 cbatch18_indices cert_cbatch18_r12 345 (by decide)

theorem cert_config_346_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 346 = true :=
  certified_of_cbatch 12 cbatch18_indices cert_cbatch18_r12 346 (by decide)

theorem cert_config_352_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 352 = true :=
  certified_of_cbatch 12 cbatch18_indices cert_cbatch18_r12 352 (by decide)

theorem cert_config_353_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 353 = true :=
  certified_of_cbatch 12 cbatch18_indices cert_cbatch18_r12 353 (by decide)

end Batch
end Math
