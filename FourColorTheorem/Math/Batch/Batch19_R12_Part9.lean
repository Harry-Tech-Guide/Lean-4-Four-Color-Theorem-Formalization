import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch19_indices : List Nat :=
  [375, 382, 386, 387, 388, 389]

theorem cert_config_375_d_red : checkIdxFast (buildSMData 12 sharedPow3) 375 = true := by kernel_rfl

theorem cert_config_382_d_red : checkIdxFast (buildSMData 12 sharedPow3) 382 = true := by kernel_rfl

theorem cert_config_386_d_red : checkIdxFast (buildSMData 12 sharedPow3) 386 = true := by kernel_rfl

theorem cert_config_387_d_red : checkIdxFast (buildSMData 12 sharedPow3) 387 = true := by kernel_rfl

theorem cert_config_388_d_red : checkIdxFast (buildSMData 12 sharedPow3) 388 = true := by kernel_rfl

theorem cert_config_389_d_red : checkIdxFast (buildSMData 12 sharedPow3) 389 = true := by kernel_rfl

theorem cert_batch19_r12 : checkRingBatch 12 batch19_indices = true := by
  dsimp only [batch19_indices, checkRingBatch, List.all]
  rw [cert_config_375_d_red, cert_config_382_d_red, cert_config_386_d_red, cert_config_387_d_red, cert_config_388_d_red, cert_config_389_d_red]
  rfl

end Batch
end Math
