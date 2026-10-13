import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 85: Ring 14 (Part 36)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 614, 617, 618.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 85. -/
def cbatch85_indices : List Nat :=
  [614, 617, 618]

/-- Unified in-kernel certification for CBatch 85 (Ring 14, Part 36). -/
theorem cert_cbatch85_r14 : checkCRingBatch14 cbatch85_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_614_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 614 = true :=
  certified_of_cbatch14 cbatch85_indices cert_cbatch85_r14 614 (by decide)

theorem cert_config_617_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 617 = true :=
  certified_of_cbatch14 cbatch85_indices cert_cbatch85_r14 617 (by decide)

theorem cert_config_618_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 618 = true :=
  certified_of_cbatch14 cbatch85_indices cert_cbatch85_r14 618 (by decide)

end Batch
end Math
