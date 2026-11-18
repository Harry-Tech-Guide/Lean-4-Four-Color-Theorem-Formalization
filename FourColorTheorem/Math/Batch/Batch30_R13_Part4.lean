module

public import FourColorTheorem.Math.Batch.Runner13

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch30_indices : List Nat :=
  [219, 271, 272, 273]

theorem cert_config_219_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 219 = true := by kernel_rfl

theorem cert_config_271_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 271 = true := by kernel_rfl

theorem cert_config_272_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 272 = true := by kernel_rfl

theorem cert_config_273_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 273 = true := by kernel_rfl

theorem cert_batch30_r13 : checkRingBatch13 batch30_indices = true := by
  dsimp only [batch30_indices, checkRingBatch13, List.all]
  rw [cert_config_219_d_red, cert_config_271_d_red, cert_config_272_d_red, cert_config_273_d_red]
  rfl

end Batch
end Math
