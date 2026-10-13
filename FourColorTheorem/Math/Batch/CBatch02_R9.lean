import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 02: Ring 9

This module certifies the C-reducibility of Config 25 with ring size 9 (contract = 1).
-/

def cbatch02_indices : List Nat := [25]

theorem cert_cbatch02_r9 : checkCRingBatch 9 cbatch02_indices = true := by
  native_decide

theorem cert_config_25_c_red : checkIdxCFast (buildSMData 9 sharedPow3) 25 = true :=
  certified_of_cbatch 9 cbatch02_indices cert_cbatch02_r9 25 (by decide)

end Batch
end Math
