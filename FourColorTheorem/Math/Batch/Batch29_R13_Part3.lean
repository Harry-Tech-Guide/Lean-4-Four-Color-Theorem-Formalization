module

public import FourColorTheorem.Math.Batch.Runner13

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch29_indices : List Nat :=
  [190, 207, 208, 210]

theorem cert_config_190_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 190 = true := by kernel_rfl

theorem cert_config_207_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 207 = true := by kernel_rfl

theorem cert_config_208_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 208 = true := by kernel_rfl

theorem cert_config_210_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 210 = true := by kernel_rfl

theorem cert_batch29_r13 : checkRingBatch13 batch29_indices = true := by
  dsimp only [batch29_indices, checkRingBatch13, List.all]
  rw [cert_config_190_d_red, cert_config_207_d_red, cert_config_208_d_red, cert_config_210_d_red]
  rfl

end Batch
end Math
