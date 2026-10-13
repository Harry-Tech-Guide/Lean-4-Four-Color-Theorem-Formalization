import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 23: Ring 12 (Part 12)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 441, 442, 451, 461, 462, 464.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 23. -/
def cbatch23_indices : List Nat :=
  [441, 442, 451, 461, 462, 464]

/-- Unified in-kernel certification for CBatch 23 (Ring 12, Part 12). -/
theorem cert_cbatch23_r12 : checkCRingBatch 12 cbatch23_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_441_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 441 = true :=
  certified_of_cbatch 12 cbatch23_indices cert_cbatch23_r12 441 (by decide)

theorem cert_config_442_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 442 = true :=
  certified_of_cbatch 12 cbatch23_indices cert_cbatch23_r12 442 (by decide)

theorem cert_config_451_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 451 = true :=
  certified_of_cbatch 12 cbatch23_indices cert_cbatch23_r12 451 (by decide)

theorem cert_config_461_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 461 = true :=
  certified_of_cbatch 12 cbatch23_indices cert_cbatch23_r12 461 (by decide)

theorem cert_config_462_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 462 = true :=
  certified_of_cbatch 12 cbatch23_indices cert_cbatch23_r12 462 (by decide)

theorem cert_config_464_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 464 = true :=
  certified_of_cbatch 12 cbatch23_indices cert_cbatch23_r12 464 (by decide)

end Batch
end Math
