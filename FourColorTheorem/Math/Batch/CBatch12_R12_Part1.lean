import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 12: Ring 12 (Part 1)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 19, 61, 62, 63, 65, 72.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 12. -/
def cbatch12_indices : List Nat :=
  [19, 61, 62, 63, 65, 72]

/-- Unified in-kernel certification for CBatch 12 (Ring 12, Part 1). -/
theorem cert_cbatch12_r12 : checkCRingBatch 12 cbatch12_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_19_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 19 = true :=
  certified_of_cbatch 12 cbatch12_indices cert_cbatch12_r12 19 (by decide)

theorem cert_config_61_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 61 = true :=
  certified_of_cbatch 12 cbatch12_indices cert_cbatch12_r12 61 (by decide)

theorem cert_config_62_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 62 = true :=
  certified_of_cbatch 12 cbatch12_indices cert_cbatch12_r12 62 (by decide)

theorem cert_config_63_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 63 = true :=
  certified_of_cbatch 12 cbatch12_indices cert_cbatch12_r12 63 (by decide)

theorem cert_config_65_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 65 = true :=
  certified_of_cbatch 12 cbatch12_indices cert_cbatch12_r12 65 (by decide)

theorem cert_config_72_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 72 = true :=
  certified_of_cbatch 12 cbatch12_indices cert_cbatch12_r12 72 (by decide)

end Batch
end Math
