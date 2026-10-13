import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 27: Ring 13 (Part 2)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 102, 103, 151, 159, 160, 161.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 27. -/
def cbatch27_indices : List Nat :=
  [102, 103, 151, 159, 160, 161]

/-- Unified in-kernel certification for CBatch 27 (Ring 13, Part 2). -/
theorem cert_cbatch27_r13 : checkCRingBatch13 cbatch27_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_102_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 102 = true :=
  certified_of_cbatch13 cbatch27_indices cert_cbatch27_r13 102 (by decide)

theorem cert_config_103_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 103 = true :=
  certified_of_cbatch13 cbatch27_indices cert_cbatch27_r13 103 (by decide)

theorem cert_config_151_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 151 = true :=
  certified_of_cbatch13 cbatch27_indices cert_cbatch27_r13 151 (by decide)

theorem cert_config_159_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 159 = true :=
  certified_of_cbatch13 cbatch27_indices cert_cbatch27_r13 159 (by decide)

theorem cert_config_160_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 160 = true :=
  certified_of_cbatch13 cbatch27_indices cert_cbatch27_r13 160 (by decide)

theorem cert_config_161_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 161 = true :=
  certified_of_cbatch13 cbatch27_indices cert_cbatch27_r13 161 (by decide)

end Batch
end Math
