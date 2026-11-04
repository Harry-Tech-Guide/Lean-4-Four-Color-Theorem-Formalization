import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

def cbatch02_indices : List Nat :=
  [25]

theorem cert_config_25_c_red : checkIdxCFast (buildSMData 9 sharedPow3) 25 = true :=
  KernelReducer.verifyIdxC_of_D 25 (by kernel_rfl)

theorem cert_cbatch02_r9 : checkCRingBatch 9 cbatch02_indices = true := by
  dsimp only [cbatch02_indices, checkCRingBatch, List.all]
  rw [cert_config_25_c_red]
  rfl

end Batch
end Math
