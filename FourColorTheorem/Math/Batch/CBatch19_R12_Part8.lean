import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 19: Ring 12 (Part 8)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 355, 356, 357, 358, 361, 364.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 19. -/
def cbatch19_indices : List Nat :=
  [355, 356, 357, 358, 361, 364]

/-- Unified in-kernel certification for CBatch 19 (Ring 12, Part 8). -/
theorem cert_cbatch19_r12 : checkCRingBatch 12 cbatch19_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_355_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 355 = true :=
  certified_of_cbatch 12 cbatch19_indices cert_cbatch19_r12 355 (by decide)

theorem cert_config_356_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 356 = true :=
  certified_of_cbatch 12 cbatch19_indices cert_cbatch19_r12 356 (by decide)

theorem cert_config_357_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 357 = true :=
  certified_of_cbatch 12 cbatch19_indices cert_cbatch19_r12 357 (by decide)

theorem cert_config_358_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 358 = true :=
  certified_of_cbatch 12 cbatch19_indices cert_cbatch19_r12 358 (by decide)

theorem cert_config_361_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 361 = true :=
  certified_of_cbatch 12 cbatch19_indices cert_cbatch19_r12 361 (by decide)

theorem cert_config_364_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 364 = true :=
  certified_of_cbatch 12 cbatch19_indices cert_cbatch19_r12 364 (by decide)

end Batch
end Math
