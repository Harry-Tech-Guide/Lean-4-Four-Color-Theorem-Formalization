module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch26_indices : List Nat :=
  [605, 609, 610, 623, 632]

theorem cert_config_605_d_red : checkIdxFast (buildSMData 12 sharedPow3) 605 = true := by kernel_rfl

theorem cert_config_609_d_red : checkIdxFast (buildSMData 12 sharedPow3) 609 = true := by kernel_rfl

theorem cert_config_610_d_red : checkIdxFast (buildSMData 12 sharedPow3) 610 = true := by kernel_rfl

theorem cert_config_623_d_red : checkIdxFast (buildSMData 12 sharedPow3) 623 = true := by kernel_rfl

theorem cert_config_632_d_red : checkIdxFast (buildSMData 12 sharedPow3) 632 = true := by kernel_rfl

theorem cert_batch26_r12 : checkRingBatch 12 batch26_indices = true := by
  dsimp only [batch26_indices, checkRingBatch, List.all]
  rw [cert_config_605_d_red, cert_config_609_d_red, cert_config_610_d_red, cert_config_623_d_red, cert_config_632_d_red]
  rfl

end Batch
end Math
