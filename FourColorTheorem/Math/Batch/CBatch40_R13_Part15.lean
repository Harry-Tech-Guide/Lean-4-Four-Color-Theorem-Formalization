import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 40: Ring 13 (Part 15)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 440, 443, 444, 445, 446, 447.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 40. -/
def cbatch40_indices : List Nat :=
  [440, 443, 444, 445, 446, 447]

/-- Unified in-kernel certification for CBatch 40 (Ring 13, Part 15). -/
theorem cert_cbatch40_r13 : checkCRingBatch13 cbatch40_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_440_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 440 = true :=
  certified_of_cbatch13 cbatch40_indices cert_cbatch40_r13 440 (by decide)

theorem cert_config_443_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 443 = true :=
  certified_of_cbatch13 cbatch40_indices cert_cbatch40_r13 443 (by decide)

theorem cert_config_444_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 444 = true :=
  certified_of_cbatch13 cbatch40_indices cert_cbatch40_r13 444 (by decide)

theorem cert_config_445_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 445 = true :=
  certified_of_cbatch13 cbatch40_indices cert_cbatch40_r13 445 (by decide)

theorem cert_config_446_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 446 = true :=
  certified_of_cbatch13 cbatch40_indices cert_cbatch40_r13 446 (by decide)

theorem cert_config_447_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 447 = true :=
  certified_of_cbatch13 cbatch40_indices cert_cbatch40_r13 447 (by decide)

end Batch
end Math
