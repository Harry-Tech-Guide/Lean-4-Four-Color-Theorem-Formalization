import FourColorTheorem.Math.Batch.Runner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch32_indices : List Nat :=
  [395, 399, 438, 471]

theorem cert_config_395_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 395 = true := by kernel_rfl

theorem cert_config_399_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 399 = true := by kernel_rfl

theorem cert_config_438_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 438 = true := by kernel_rfl

theorem cert_config_471_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 471 = true := by kernel_rfl

theorem cert_batch32_r13 : checkRingBatch13 batch32_indices = true := by
  dsimp only [batch32_indices, checkRingBatch13, List.all]
  rw [cert_config_395_d_red, cert_config_399_d_red, cert_config_438_d_red, cert_config_471_d_red]
  rfl

end Batch
end Math
