import FourColorTheorem.Math.Batch.Runner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch27_indices : List Nat :=
  [86, 87, 90, 105]

theorem cert_config_86_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 86 = true := by kernel_rfl

theorem cert_config_87_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 87 = true := by kernel_rfl

theorem cert_config_90_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 90 = true := by kernel_rfl

theorem cert_config_105_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 105 = true := by kernel_rfl

theorem cert_batch27_r13 : checkRingBatch13 batch27_indices = true := by
  dsimp only [batch27_indices, checkRingBatch13, List.all]
  rw [cert_config_86_d_red, cert_config_87_d_red, cert_config_90_d_red, cert_config_105_d_red]
  rfl

end Batch
end Math
