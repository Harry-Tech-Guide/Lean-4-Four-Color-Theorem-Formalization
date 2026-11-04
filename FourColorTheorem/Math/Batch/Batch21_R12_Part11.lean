import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch21_indices : List Nat :=
  [408, 413, 415, 416, 417, 419]

theorem cert_config_408_d_red : checkIdxFast (buildSMData 12 sharedPow3) 408 = true := by kernel_rfl

theorem cert_config_413_d_red : checkIdxFast (buildSMData 12 sharedPow3) 413 = true := by kernel_rfl

theorem cert_config_415_d_red : checkIdxFast (buildSMData 12 sharedPow3) 415 = true := by kernel_rfl

theorem cert_config_416_d_red : checkIdxFast (buildSMData 12 sharedPow3) 416 = true := by kernel_rfl

theorem cert_config_417_d_red : checkIdxFast (buildSMData 12 sharedPow3) 417 = true := by kernel_rfl

theorem cert_config_419_d_red : checkIdxFast (buildSMData 12 sharedPow3) 419 = true := by kernel_rfl

theorem cert_batch21_r12 : checkRingBatch 12 batch21_indices = true := by
  dsimp only [batch21_indices, checkRingBatch, List.all]
  rw [cert_config_408_d_red, cert_config_413_d_red, cert_config_415_d_red, cert_config_416_d_red, cert_config_417_d_red, cert_config_419_d_red]
  rfl

end Batch
end Math
