import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch25_indices : List Nat :=
  [579, 580, 590, 597, 599]

theorem cert_config_579_d_red : checkIdxFast (buildSMData 12 sharedPow3) 579 = true := by kernel_rfl

theorem cert_config_580_d_red : checkIdxFast (buildSMData 12 sharedPow3) 580 = true := by kernel_rfl

theorem cert_config_590_d_red : checkIdxFast (buildSMData 12 sharedPow3) 590 = true := by kernel_rfl

theorem cert_config_597_d_red : checkIdxFast (buildSMData 12 sharedPow3) 597 = true := by kernel_rfl

theorem cert_config_599_d_red : checkIdxFast (buildSMData 12 sharedPow3) 599 = true := by kernel_rfl

theorem cert_batch25_r12 : checkRingBatch 12 batch25_indices = true := by
  dsimp only [batch25_indices, checkRingBatch, List.all]
  rw [cert_config_579_d_red, cert_config_580_d_red, cert_config_590_d_red, cert_config_597_d_red, cert_config_599_d_red]
  rfl

end Batch
end Math
