import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 17: Ring 12 (Part 6)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 12:
Configs 178, 244, 245, 249, 250, 257.
-/

/-- The 6 ring-12 configuration indices certified in CBatch 17. -/
def cbatch17_indices : List Nat :=
  [178, 244, 245, 249, 250, 257]

/-- Unified in-kernel certification for CBatch 17 (Ring 12, Part 6). -/
theorem cert_cbatch17_r12 : checkCRingBatch 12 cbatch17_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_178_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 178 = true :=
  certified_of_cbatch 12 cbatch17_indices cert_cbatch17_r12 178 (by decide)

theorem cert_config_244_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 244 = true :=
  certified_of_cbatch 12 cbatch17_indices cert_cbatch17_r12 244 (by decide)

theorem cert_config_245_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 245 = true :=
  certified_of_cbatch 12 cbatch17_indices cert_cbatch17_r12 245 (by decide)

theorem cert_config_249_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 249 = true :=
  certified_of_cbatch 12 cbatch17_indices cert_cbatch17_r12 249 (by decide)

theorem cert_config_250_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 250 = true :=
  certified_of_cbatch 12 cbatch17_indices cert_cbatch17_r12 250 (by decide)

theorem cert_config_257_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 257 = true :=
  certified_of_cbatch 12 cbatch17_indices cert_cbatch17_r12 257 (by decide)

end Batch
end Math
