import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

def batch33_indices : List Nat :=
  [472, 482, 491, 511]

theorem cert_config_472_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 472 = true := by kernel_rfl

theorem cert_config_482_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 482 = true := by kernel_rfl

theorem cert_config_491_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 491 = true := by kernel_rfl

theorem cert_config_511_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 511 = true := by kernel_rfl

theorem cert_batch33_r13 : checkRingBatch13 batch33_indices = true := by
  dsimp only [batch33_indices, checkRingBatch13, List.all]
  rw [cert_config_472_d_red, cert_config_482_d_red, cert_config_491_d_red, cert_config_511_d_red]
  rfl

end Batch
end Math
