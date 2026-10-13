import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 14: Ring 12 (Part 3)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 127, 128, 130, 131, 136, 137.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 14. -/
def cbatch14_indices : List Nat :=
  [127, 128, 130, 131, 136, 137]

/-- Unified in-kernel certification for CBatch 14 (Ring 12, Part 3). -/
theorem cert_cbatch14_r12 : checkCRingBatch 12 cbatch14_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_127_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 127 = true :=
  certified_of_cbatch 12 cbatch14_indices cert_cbatch14_r12 127 (by decide)

theorem cert_config_128_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 128 = true :=
  certified_of_cbatch 12 cbatch14_indices cert_cbatch14_r12 128 (by decide)

theorem cert_config_130_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 130 = true :=
  certified_of_cbatch 12 cbatch14_indices cert_cbatch14_r12 130 (by decide)

theorem cert_config_131_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 131 = true :=
  certified_of_cbatch 12 cbatch14_indices cert_cbatch14_r12 131 (by decide)

theorem cert_config_136_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 136 = true :=
  certified_of_cbatch 12 cbatch14_indices cert_cbatch14_r12 136 (by decide)

theorem cert_config_137_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 137 = true :=
  certified_of_cbatch 12 cbatch14_indices cert_cbatch14_r12 137 (by decide)

end Batch
end Math
