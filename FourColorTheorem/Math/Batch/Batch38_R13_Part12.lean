import FourColorTheorem.Math.Batch.Runner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch38_indices : List Nat :=
  [607, 608, 611, 615]

theorem cert_config_607_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 607 = true := by kernel_rfl

theorem cert_config_608_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 608 = true := by kernel_rfl

theorem cert_config_611_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 611 = true := by kernel_rfl

theorem cert_config_615_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 615 = true := by kernel_rfl

theorem cert_batch38_r13 : checkRingBatch13 batch38_indices = true := by
  dsimp only [batch38_indices, checkRingBatch13, List.all]
  rw [cert_config_607_d_red, cert_config_608_d_red, cert_config_611_d_red, cert_config_615_d_red]
  rfl

end Batch
end Math
