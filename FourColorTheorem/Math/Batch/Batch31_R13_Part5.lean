module

public import FourColorTheorem.Math.Batch.Runner13

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch31_indices : List Nat :=
  [275, 383, 385, 394]

theorem cert_config_275_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 275 = true := by kernel_rfl

theorem cert_config_383_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 383 = true := by kernel_rfl

theorem cert_config_385_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 385 = true := by kernel_rfl

theorem cert_config_394_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 394 = true := by kernel_rfl

theorem cert_batch31_r13 : checkRingBatch13 batch31_indices = true := by
  dsimp only [batch31_indices, checkRingBatch13, List.all]
  rw [cert_config_275_d_red, cert_config_383_d_red, cert_config_385_d_red, cert_config_394_d_red]
  rfl

end Batch
end Math
