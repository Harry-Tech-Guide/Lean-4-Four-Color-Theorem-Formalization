import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 69: Ring 14 (Part 20)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 321, 322, 393.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 69. -/
def cbatch69_indices : List Nat :=
  [321, 322, 393]

/-- Unified in-kernel certification for CBatch 69 (Ring 14, Part 20). -/
theorem cert_cbatch69_r14 : checkCRingBatch14 cbatch69_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_321_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 321 = true :=
  certified_of_cbatch14 cbatch69_indices cert_cbatch69_r14 321 (by decide)

theorem cert_config_322_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 322 = true :=
  certified_of_cbatch14 cbatch69_indices cert_cbatch69_r14 322 (by decide)

theorem cert_config_393_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 393 = true :=
  certified_of_cbatch14 cbatch69_indices cert_cbatch69_r14 393 (by decide)

end Batch
end Math
