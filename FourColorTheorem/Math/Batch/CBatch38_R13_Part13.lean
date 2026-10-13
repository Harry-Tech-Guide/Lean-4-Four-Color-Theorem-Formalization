import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 38: Ring 13 (Part 13)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 376, 377, 378, 379, 380, 381.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 38. -/
def cbatch38_indices : List Nat :=
  [376, 377, 378, 379, 380, 381]

/-- Unified in-kernel certification for CBatch 38 (Ring 13, Part 13). -/
theorem cert_cbatch38_r13 : checkCRingBatch13 cbatch38_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_376_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 376 = true :=
  certified_of_cbatch13 cbatch38_indices cert_cbatch38_r13 376 (by decide)

theorem cert_config_377_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 377 = true :=
  certified_of_cbatch13 cbatch38_indices cert_cbatch38_r13 377 (by decide)

theorem cert_config_378_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 378 = true :=
  certified_of_cbatch13 cbatch38_indices cert_cbatch38_r13 378 (by decide)

theorem cert_config_379_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 379 = true :=
  certified_of_cbatch13 cbatch38_indices cert_cbatch38_r13 379 (by decide)

theorem cert_config_380_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 380 = true :=
  certified_of_cbatch13 cbatch38_indices cert_cbatch38_r13 380 (by decide)

theorem cert_config_381_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 381 = true :=
  certified_of_cbatch13 cbatch38_indices cert_cbatch38_r13 381 (by decide)

end Batch
end Math
