import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 84: Ring 14 (Part 35)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 596, 612, 613.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 84. -/
def cbatch84_indices : List Nat :=
  [596, 612, 613]

/-- Unified in-kernel certification for CBatch 84 (Ring 14, Part 35). -/
theorem cert_cbatch84_r14 : checkCRingBatch14 cbatch84_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_596_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 596 = true :=
  certified_of_cbatch14 cbatch84_indices cert_cbatch84_r14 596 (by decide)

theorem cert_config_612_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 612 = true :=
  certified_of_cbatch14 cbatch84_indices cert_cbatch84_r14 612 (by decide)

theorem cert_config_613_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 613 = true :=
  certified_of_cbatch14 cbatch84_indices cert_cbatch84_r14 613 (by decide)

end Batch
end Math
