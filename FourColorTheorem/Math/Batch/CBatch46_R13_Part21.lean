import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 46: Ring 13 (Part 21)

This module certifies the C-reducibility of 6 C-reducible configurations
from the RSST unavoidable set with ring size 13:
Configs 538, 539, 544, 550, 557, 558.
-/

/-- The 6 ring-13 configuration indices certified in CBatch 46. -/
def cbatch46_indices : List Nat :=
  [538, 539, 544, 550, 557, 558]

/-- Unified in-kernel certification for CBatch 46 (Ring 13, Part 21). -/
theorem cert_cbatch46_r13 : checkCRingBatch13 cbatch46_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_538_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 538 = true :=
  certified_of_cbatch13 cbatch46_indices cert_cbatch46_r13 538 (by decide)

theorem cert_config_539_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 539 = true :=
  certified_of_cbatch13 cbatch46_indices cert_cbatch46_r13 539 (by decide)

theorem cert_config_544_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 544 = true :=
  certified_of_cbatch13 cbatch46_indices cert_cbatch46_r13 544 (by decide)

theorem cert_config_550_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 550 = true :=
  certified_of_cbatch13 cbatch46_indices cert_cbatch46_r13 550 (by decide)

theorem cert_config_557_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 557 = true :=
  certified_of_cbatch13 cbatch46_indices cert_cbatch46_r13 557 (by decide)

theorem cert_config_558_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 558 = true :=
  certified_of_cbatch13 cbatch46_indices cert_cbatch46_r13 558 (by decide)

end Batch
end Math
