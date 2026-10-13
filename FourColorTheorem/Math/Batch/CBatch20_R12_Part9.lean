import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 20: Ring 12 (Part 9)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 365, 368, 370, 371, 409, 410.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 20. -/
def cbatch20_indices : List Nat :=
  [365, 368, 370, 371, 409, 410]

/-- Unified in-kernel certification for CBatch 20 (Ring 12, Part 9). -/
theorem cert_cbatch20_r12 : checkCRingBatch 12 cbatch20_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_365_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 365 = true :=
  certified_of_cbatch 12 cbatch20_indices cert_cbatch20_r12 365 (by decide)

theorem cert_config_368_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 368 = true :=
  certified_of_cbatch 12 cbatch20_indices cert_cbatch20_r12 368 (by decide)

theorem cert_config_370_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 370 = true :=
  certified_of_cbatch 12 cbatch20_indices cert_cbatch20_r12 370 (by decide)

theorem cert_config_371_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 371 = true :=
  certified_of_cbatch 12 cbatch20_indices cert_cbatch20_r12 371 (by decide)

theorem cert_config_409_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 409 = true :=
  certified_of_cbatch 12 cbatch20_indices cert_cbatch20_r12 409 (by decide)

theorem cert_config_410_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 410 = true :=
  certified_of_cbatch 12 cbatch20_indices cert_cbatch20_r12 410 (by decide)

end Batch
end Math
