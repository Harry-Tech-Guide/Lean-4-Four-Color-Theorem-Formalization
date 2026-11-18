module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch20_indices : List Nat :=
  [390, 391, 392, 405, 406, 407]

theorem cert_config_390_d_red : checkIdxFast (buildSMData 12 sharedPow3) 390 = true := by kernel_rfl

theorem cert_config_391_d_red : checkIdxFast (buildSMData 12 sharedPow3) 391 = true := by kernel_rfl

theorem cert_config_392_d_red : checkIdxFast (buildSMData 12 sharedPow3) 392 = true := by kernel_rfl

theorem cert_config_405_d_red : checkIdxFast (buildSMData 12 sharedPow3) 405 = true := by kernel_rfl

theorem cert_config_406_d_red : checkIdxFast (buildSMData 12 sharedPow3) 406 = true := by kernel_rfl

theorem cert_config_407_d_red : checkIdxFast (buildSMData 12 sharedPow3) 407 = true := by kernel_rfl

theorem cert_batch20_r12 : checkRingBatch 12 batch20_indices = true := by
  dsimp only [batch20_indices, checkRingBatch, List.all]
  rw [cert_config_390_d_red, cert_config_391_d_red, cert_config_392_d_red, cert_config_405_d_red, cert_config_406_d_red, cert_config_407_d_red]
  rfl

end Batch
end Math
