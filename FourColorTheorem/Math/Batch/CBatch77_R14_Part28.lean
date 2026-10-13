import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 77: Ring 14 (Part 28)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 515, 516, 518.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 77. -/
def cbatch77_indices : List Nat :=
  [515, 516, 518]

/-- Unified in-kernel certification for CBatch 77 (Ring 14, Part 28). -/
theorem cert_cbatch77_r14 : checkCRingBatch14 cbatch77_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_515_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 515 = true :=
  certified_of_cbatch14 cbatch77_indices cert_cbatch77_r14 515 (by decide)

theorem cert_config_516_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 516 = true :=
  certified_of_cbatch14 cbatch77_indices cert_cbatch77_r14 516 (by decide)

theorem cert_config_518_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 518 = true :=
  certified_of_cbatch14 cbatch77_indices cert_cbatch77_r14 518 (by decide)

end Batch
end Math
