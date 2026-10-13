import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 03: Ring 10 (Part 1)

This module certifies the C-reducibility of 5 configurations from the RSST unavoidable set with ring size 10:
Configs 10, 28, 31, 33, 34.
-/

def cbatch03_indices : List Nat :=
  [10, 28, 31, 33, 34]

theorem cert_cbatch03_r10 : checkCRingBatch 10 cbatch03_indices = true := by
  native_decide

theorem cert_config_10_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 10 = true :=
  certified_of_cbatch 10 cbatch03_indices cert_cbatch03_r10 10 (by decide)

theorem cert_config_28_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 28 = true :=
  certified_of_cbatch 10 cbatch03_indices cert_cbatch03_r10 28 (by decide)

theorem cert_config_31_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 31 = true :=
  certified_of_cbatch 10 cbatch03_indices cert_cbatch03_r10 31 (by decide)

theorem cert_config_33_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 33 = true :=
  certified_of_cbatch 10 cbatch03_indices cert_cbatch03_r10 33 (by decide)

theorem cert_config_34_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 34 = true :=
  certified_of_cbatch 10 cbatch03_indices cert_cbatch03_r10 34 (by decide)

end Batch
end Math
