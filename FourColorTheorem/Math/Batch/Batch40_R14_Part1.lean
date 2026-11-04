import FourColorTheorem.Math.Batch.Runner14

namespace Math
namespace Batch

open FastReducer

def batch40_indices : List Nat :=
  [109, 214]

theorem cert_config_109_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 109 = true := by kernel_rfl

theorem cert_config_214_d_red : checkIdxFast14 (buildSMData 14 sharedPow3) 214 = true := by kernel_rfl

theorem cert_batch40_r14 : checkRingBatch14 batch40_indices = true := by
  dsimp only [batch40_indices, checkRingBatch14, List.all]
  rw [cert_config_109_d_red, cert_config_214_d_red]
  rfl

end Batch
end Math
