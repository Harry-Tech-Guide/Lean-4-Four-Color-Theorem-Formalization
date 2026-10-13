import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 80: Ring 14 (Part 31)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 540, 541, 542.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 80. -/
def cbatch80_indices : List Nat :=
  [540, 541, 542]

/-- Unified in-kernel certification for CBatch 80 (Ring 14, Part 31). -/
theorem cert_cbatch80_r14 : checkCRingBatch14 cbatch80_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_540_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 540 = true :=
  certified_of_cbatch14 cbatch80_indices cert_cbatch80_r14 540 (by decide)

theorem cert_config_541_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 541 = true :=
  certified_of_cbatch14 cbatch80_indices cert_cbatch80_r14 541 (by decide)

theorem cert_config_542_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 542 = true :=
  certified_of_cbatch14 cbatch80_indices cert_cbatch80_r14 542 (by decide)

end Batch
end Math
