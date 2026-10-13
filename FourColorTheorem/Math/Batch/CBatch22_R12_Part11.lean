import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 22: Ring 12 (Part 11)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 429, 430, 431, 432, 433, 434.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 22. -/
def cbatch22_indices : List Nat :=
  [429, 430, 431, 432, 433, 434]

/-- Unified in-kernel certification for CBatch 22 (Ring 12, Part 11). -/
theorem cert_cbatch22_r12 : checkCRingBatch 12 cbatch22_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_429_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 429 = true :=
  certified_of_cbatch 12 cbatch22_indices cert_cbatch22_r12 429 (by decide)

theorem cert_config_430_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 430 = true :=
  certified_of_cbatch 12 cbatch22_indices cert_cbatch22_r12 430 (by decide)

theorem cert_config_431_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 431 = true :=
  certified_of_cbatch 12 cbatch22_indices cert_cbatch22_r12 431 (by decide)

theorem cert_config_432_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 432 = true :=
  certified_of_cbatch 12 cbatch22_indices cert_cbatch22_r12 432 (by decide)

theorem cert_config_433_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 433 = true :=
  certified_of_cbatch 12 cbatch22_indices cert_cbatch22_r12 433 (by decide)

theorem cert_config_434_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 434 = true :=
  certified_of_cbatch 12 cbatch22_indices cert_cbatch22_r12 434 (by decide)

end Batch
end Math
