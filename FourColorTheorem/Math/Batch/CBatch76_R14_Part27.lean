import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 76: Ring 14 (Part 27)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 509, 510, 512.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 76. -/
def cbatch76_indices : List Nat :=
  [509, 510, 512]

/-- Unified in-kernel certification for CBatch 76 (Ring 14, Part 27). -/
theorem cert_cbatch76_r14 : checkCRingBatch14 cbatch76_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_509_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 509 = true :=
  certified_of_cbatch14 cbatch76_indices cert_cbatch76_r14 509 (by decide)

theorem cert_config_510_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 510 = true :=
  certified_of_cbatch14 cbatch76_indices cert_cbatch76_r14 510 (by decide)

theorem cert_config_512_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 512 = true :=
  certified_of_cbatch14 cbatch76_indices cert_cbatch76_r14 512 (by decide)

end Batch
end Math
