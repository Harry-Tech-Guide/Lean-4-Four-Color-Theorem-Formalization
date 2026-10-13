import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 39: Ring 13 (Part 14)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 384, 396, 435, 436, 437, 439.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 39. -/
def cbatch39_indices : List Nat :=
  [384, 396, 435, 436, 437, 439]

/-- Unified in-kernel certification for CBatch 39 (Ring 13, Part 14). -/
theorem cert_cbatch39_r13 : checkCRingBatch13 cbatch39_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_384_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 384 = true :=
  certified_of_cbatch13 cbatch39_indices cert_cbatch39_r13 384 (by decide)

theorem cert_config_396_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 396 = true :=
  certified_of_cbatch13 cbatch39_indices cert_cbatch39_r13 396 (by decide)

theorem cert_config_435_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 435 = true :=
  certified_of_cbatch13 cbatch39_indices cert_cbatch39_r13 435 (by decide)

theorem cert_config_436_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 436 = true :=
  certified_of_cbatch13 cbatch39_indices cert_cbatch39_r13 436 (by decide)

theorem cert_config_437_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 437 = true :=
  certified_of_cbatch13 cbatch39_indices cert_cbatch39_r13 437 (by decide)

theorem cert_config_439_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 439 = true :=
  certified_of_cbatch13 cbatch39_indices cert_cbatch39_r13 439 (by decide)

end Batch
end Math
