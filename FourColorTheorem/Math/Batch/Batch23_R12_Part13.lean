import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch23_indices : List Nat :=
  [481, 483, 484, 490, 522, 555]

theorem cert_config_481_d_red : checkIdxFast (buildSMData 12 sharedPow3) 481 = true := by kernel_rfl

theorem cert_config_483_d_red : checkIdxFast (buildSMData 12 sharedPow3) 483 = true := by kernel_rfl

theorem cert_config_484_d_red : checkIdxFast (buildSMData 12 sharedPow3) 484 = true := by kernel_rfl

theorem cert_config_490_d_red : checkIdxFast (buildSMData 12 sharedPow3) 490 = true := by kernel_rfl

theorem cert_config_522_d_red : checkIdxFast (buildSMData 12 sharedPow3) 522 = true := by kernel_rfl

theorem cert_config_555_d_red : checkIdxFast (buildSMData 12 sharedPow3) 555 = true := by kernel_rfl

theorem cert_batch23_r12 : checkRingBatch 12 batch23_indices = true := by
  dsimp only [batch23_indices, checkRingBatch, List.all]
  rw [cert_config_481_d_red, cert_config_483_d_red, cert_config_484_d_red, cert_config_490_d_red, cert_config_522_d_red, cert_config_555_d_red]
  rfl

end Batch
end Math
