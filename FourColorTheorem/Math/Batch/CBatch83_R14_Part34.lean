import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 83: Ring 14 (Part 34)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 561, 562, 563.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 83. -/
def cbatch83_indices : List Nat :=
  [561, 562, 563]

/-- Unified in-kernel certification for CBatch 83 (Ring 14, Part 34). -/
theorem cert_cbatch83_r14 : checkCRingBatch14 cbatch83_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_561_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 561 = true :=
  certified_of_cbatch14 cbatch83_indices cert_cbatch83_r14 561 (by decide)

theorem cert_config_562_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 562 = true :=
  certified_of_cbatch14 cbatch83_indices cert_cbatch83_r14 562 (by decide)

theorem cert_config_563_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 563 = true :=
  certified_of_cbatch14 cbatch83_indices cert_cbatch83_r14 563 (by decide)

end Batch
end Math
