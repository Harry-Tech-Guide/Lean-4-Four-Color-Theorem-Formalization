module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch15_indices : List Nat :=
  [153, 154, 155, 156, 157, 172]

theorem cert_config_153_d_red : checkIdxFast (buildSMData 12 sharedPow3) 153 = true := by kernel_rfl

theorem cert_config_154_d_red : checkIdxFast (buildSMData 12 sharedPow3) 154 = true := by kernel_rfl

theorem cert_config_155_d_red : checkIdxFast (buildSMData 12 sharedPow3) 155 = true := by kernel_rfl

theorem cert_config_156_d_red : checkIdxFast (buildSMData 12 sharedPow3) 156 = true := by kernel_rfl

theorem cert_config_157_d_red : checkIdxFast (buildSMData 12 sharedPow3) 157 = true := by kernel_rfl

theorem cert_config_172_d_red : checkIdxFast (buildSMData 12 sharedPow3) 172 = true := by kernel_rfl

theorem cert_batch15_r12 : checkRingBatch 12 batch15_indices = true := by
  dsimp only [batch15_indices, checkRingBatch, List.all]
  rw [cert_config_153_d_red, cert_config_154_d_red, cert_config_155_d_red, cert_config_156_d_red, cert_config_157_d_red, cert_config_172_d_red]
  rfl

end Batch
end Math
