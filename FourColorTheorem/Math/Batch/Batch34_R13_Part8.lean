module

public import FourColorTheorem.Math.Batch.Runner13

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch34_indices : List Nat :=
  [513, 514, 517, 524]

theorem cert_config_513_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 513 = true := by kernel_rfl

theorem cert_config_514_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 514 = true := by kernel_rfl

theorem cert_config_517_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 517 = true := by kernel_rfl

theorem cert_config_524_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 524 = true := by kernel_rfl

theorem cert_batch34_r13 : checkRingBatch13 batch34_indices = true := by
  dsimp only [batch34_indices, checkRingBatch13, List.all]
  rw [cert_config_513_d_red, cert_config_514_d_red, cert_config_517_d_red, cert_config_524_d_red]
  rfl

end Batch
end Math
