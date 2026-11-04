import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

def cbatch01_indices : List Nat :=
  [3]

theorem cert_config_3_c_red : checkIdxCFast (buildSMData 8 sharedPow3) 3 = true :=
  KernelReducer.verifyIdxC_of_D 3 (by kernel_rfl)

theorem cert_cbatch01_r8 : checkCRingBatch 8 cbatch01_indices = true := by
  dsimp only [cbatch01_indices, checkCRingBatch, List.all]
  rw [cert_config_3_c_red]
  rfl

end Batch
end Math
