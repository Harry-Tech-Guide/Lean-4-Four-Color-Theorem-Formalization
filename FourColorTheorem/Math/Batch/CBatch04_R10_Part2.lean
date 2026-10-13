import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 04: Ring 10 (Part 2)

This module certifies the C-reducibility of 5 configurations from the RSST unavoidable set with ring size 10:
Configs 35, 111, 116, 326, 327.
-/

def cbatch04_indices : List Nat :=
  [35, 111, 116, 326, 327]

theorem cert_cbatch04_r10 : checkCRingBatch 10 cbatch04_indices = true := by
  native_decide

theorem cert_config_35_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 35 = true :=
  certified_of_cbatch 10 cbatch04_indices cert_cbatch04_r10 35 (by decide)

theorem cert_config_111_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 111 = true :=
  certified_of_cbatch 10 cbatch04_indices cert_cbatch04_r10 111 (by decide)

theorem cert_config_116_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 116 = true :=
  certified_of_cbatch 10 cbatch04_indices cert_cbatch04_r10 116 (by decide)

theorem cert_config_326_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 326 = true :=
  certified_of_cbatch 10 cbatch04_indices cert_cbatch04_r10 326 (by decide)

theorem cert_config_327_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 327 = true :=
  certified_of_cbatch 10 cbatch04_indices cert_cbatch04_r10 327 (by decide)

end Batch
end Math
