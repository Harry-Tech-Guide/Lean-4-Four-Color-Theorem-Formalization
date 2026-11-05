import FourColorTheorem.Math.Batch.Runner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch39_indices : List Nat :=
  [627, 628, 630, 631]

theorem cert_config_627_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 627 = true := by kernel_rfl

theorem cert_config_628_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 628 = true := by kernel_rfl

theorem cert_config_630_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 630 = true := by kernel_rfl

theorem cert_config_631_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 631 = true := by kernel_rfl

theorem cert_batch39_r13 : checkRingBatch13 batch39_indices = true := by
  dsimp only [batch39_indices, checkRingBatch13, List.all]
  rw [cert_config_627_d_red, cert_config_628_d_red, cert_config_630_d_red, cert_config_631_d_red]
  rfl

end Batch
end Math
