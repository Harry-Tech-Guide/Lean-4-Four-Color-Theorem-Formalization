module

public import FourColorTheorem.Math.Batch.Runner13

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch35_indices : List Nat :=
  [525, 526, 528, 529]

theorem cert_config_525_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 525 = true := by kernel_rfl

theorem cert_config_526_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 526 = true := by kernel_rfl

theorem cert_config_528_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 528 = true := by kernel_rfl

theorem cert_config_529_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 529 = true := by kernel_rfl

theorem cert_batch35_r13 : checkRingBatch13 batch35_indices = true := by
  dsimp only [batch35_indices, checkRingBatch13, List.all]
  rw [cert_config_525_d_red, cert_config_526_d_red, cert_config_528_d_red, cert_config_529_d_red]
  rfl

end Batch
end Math
