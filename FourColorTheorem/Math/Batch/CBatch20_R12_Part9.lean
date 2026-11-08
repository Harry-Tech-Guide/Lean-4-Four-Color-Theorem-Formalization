import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch20_indices : List Nat :=
  [365, 368, 370, 371, 409, 410]

theorem cert_config_365_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 365 = true := by kernel_rfl

theorem cert_config_368_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 368 = true := by kernel_rfl

theorem cert_config_370_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 370 = true := by kernel_rfl

theorem cert_config_371_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 371 = true := by kernel_rfl

theorem cert_config_409_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 409 = true := by kernel_rfl

theorem cert_config_410_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 410 = true := by kernel_rfl

theorem cert_cbatch20_r12 : checkCRingBatch 12 cbatch20_indices = true := by
  dsimp only [cbatch20_indices, checkCRingBatch, List.all]
  rw [cert_config_365_c_red, cert_config_368_c_red, cert_config_370_c_red, cert_config_371_c_red, cert_config_409_c_red, cert_config_410_c_red]
  rfl

end Batch
end Math
