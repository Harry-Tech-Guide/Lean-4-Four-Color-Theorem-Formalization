import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 41: Ring 13 (Part 16)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 448, 449, 453, 454, 455, 456.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 41. -/
def cbatch41_indices : List Nat :=
  [448, 449, 453, 454, 455, 456]

/-- Unified in-kernel certification for CBatch 41 (Ring 13, Part 16). -/
theorem cert_cbatch41_r13 : checkCRingBatch13 cbatch41_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_448_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 448 = true :=
  certified_of_cbatch13 cbatch41_indices cert_cbatch41_r13 448 (by decide)

theorem cert_config_449_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 449 = true :=
  certified_of_cbatch13 cbatch41_indices cert_cbatch41_r13 449 (by decide)

theorem cert_config_453_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 453 = true :=
  certified_of_cbatch13 cbatch41_indices cert_cbatch41_r13 453 (by decide)

theorem cert_config_454_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 454 = true :=
  certified_of_cbatch13 cbatch41_indices cert_cbatch41_r13 454 (by decide)

theorem cert_config_455_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 455 = true :=
  certified_of_cbatch13 cbatch41_indices cert_cbatch41_r13 455 (by decide)

theorem cert_config_456_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 456 = true :=
  certified_of_cbatch13 cbatch41_indices cert_cbatch41_r13 456 (by decide)

end Batch
end Math
