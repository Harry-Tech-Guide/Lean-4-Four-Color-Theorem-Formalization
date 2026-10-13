import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 01: Ring 8

This module certifies the C-reducibility of Config 3 with ring size 8 (contract = 4).
-/

def cbatch01_indices : List Nat := [3]

theorem cert_cbatch01_r8 : checkCRingBatch 8 cbatch01_indices = true := by
  native_decide

theorem cert_config_3_c_red : checkIdxCFast (buildSMData 8 sharedPow3) 3 = true :=
  certified_of_cbatch 8 cbatch01_indices cert_cbatch01_r8 3 (by decide)

end Batch
end Math
