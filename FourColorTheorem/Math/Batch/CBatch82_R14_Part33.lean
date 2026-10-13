import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 82: Ring 14 (Part 33)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 551, 553, 554.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 82. -/
def cbatch82_indices : List Nat :=
  [551, 553, 554]

/-- Unified in-kernel certification for CBatch 82 (Ring 14, Part 33). -/
theorem cert_cbatch82_r14 : checkCRingBatch14 cbatch82_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_551_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 551 = true :=
  certified_of_cbatch14 cbatch82_indices cert_cbatch82_r14 551 (by decide)

theorem cert_config_553_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 553 = true :=
  certified_of_cbatch14 cbatch82_indices cert_cbatch82_r14 553 (by decide)

theorem cert_config_554_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 554 = true :=
  certified_of_cbatch14 cbatch82_indices cert_cbatch82_r14 554 (by decide)

end Batch
end Math
