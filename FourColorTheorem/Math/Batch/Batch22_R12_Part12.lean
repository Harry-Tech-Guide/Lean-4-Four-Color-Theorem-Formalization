module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch22_indices : List Nat :=
  [420, 421, 422, 428, 450, 452]

theorem cert_config_420_d_red : checkIdxFast (buildSMData 12 sharedPow3) 420 = true := by kernel_rfl

theorem cert_config_421_d_red : checkIdxFast (buildSMData 12 sharedPow3) 421 = true := by kernel_rfl

theorem cert_config_422_d_red : checkIdxFast (buildSMData 12 sharedPow3) 422 = true := by kernel_rfl

theorem cert_config_428_d_red : checkIdxFast (buildSMData 12 sharedPow3) 428 = true := by kernel_rfl

theorem cert_config_450_d_red : checkIdxFast (buildSMData 12 sharedPow3) 450 = true := by kernel_rfl

theorem cert_config_452_d_red : checkIdxFast (buildSMData 12 sharedPow3) 452 = true := by kernel_rfl

theorem cert_batch22_r12 : checkRingBatch 12 batch22_indices = true := by
  dsimp only [batch22_indices, checkRingBatch, List.all]
  rw [cert_config_420_d_red, cert_config_421_d_red, cert_config_422_d_red, cert_config_428_d_red, cert_config_450_d_red, cert_config_452_d_red]
  rfl

end Batch
end Math
