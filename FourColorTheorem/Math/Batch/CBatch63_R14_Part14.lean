import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 63: Ring 14 (Part 14)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 298, 299, 300.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 63. -/
def cbatch63_indices : List Nat :=
  [298, 299, 300]

/-- Unified in-kernel certification for CBatch 63 (Ring 14, Part 14). -/
theorem cert_cbatch63_r14 : checkCRingBatch14 cbatch63_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_298_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 298 = true :=
  certified_of_cbatch14 cbatch63_indices cert_cbatch63_r14 298 (by decide)

theorem cert_config_299_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 299 = true :=
  certified_of_cbatch14 cbatch63_indices cert_cbatch63_r14 299 (by decide)

theorem cert_config_300_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 300 = true :=
  certified_of_cbatch14 cbatch63_indices cert_cbatch63_r14 300 (by decide)

end Batch
end Math
