import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch11_indices : List Nat :=
  [21, 64, 66, 67, 68]

theorem cert_config_21_d_red : checkIdxFast (buildSMData 12 sharedPow3) 21 = true := by kernel_rfl

theorem cert_config_64_d_red : checkIdxFast (buildSMData 12 sharedPow3) 64 = true := by kernel_rfl

theorem cert_config_66_d_red : checkIdxFast (buildSMData 12 sharedPow3) 66 = true := by kernel_rfl

theorem cert_config_67_d_red : checkIdxFast (buildSMData 12 sharedPow3) 67 = true := by kernel_rfl

theorem cert_config_68_d_red : checkIdxFast (buildSMData 12 sharedPow3) 68 = true := by kernel_rfl

theorem cert_batch11_r12 : checkRingBatch 12 batch11_indices = true := by
  dsimp only [batch11_indices, checkRingBatch, List.all]
  rw [cert_config_21_d_red, cert_config_64_d_red, cert_config_66_d_red, cert_config_67_d_red, cert_config_68_d_red]
  rfl

end Batch
end Math
