import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch22_indices : List Nat :=
  [429, 430, 431, 432, 433, 434]

theorem cert_config_429_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 429 = true := by kernel_rfl

theorem cert_config_430_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 430 = true := by kernel_rfl

theorem cert_config_431_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 431 = true := by kernel_rfl

theorem cert_config_432_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 432 = true := by kernel_rfl

theorem cert_config_433_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 433 = true := by kernel_rfl

theorem cert_config_434_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 434 = true := by kernel_rfl

theorem cert_cbatch22_r12 : checkCRingBatch 12 cbatch22_indices = true := by
  dsimp only [cbatch22_indices, checkCRingBatch, List.all]
  rw [cert_config_429_c_red, cert_config_430_c_red, cert_config_431_c_red, cert_config_432_c_red, cert_config_433_c_red, cert_config_434_c_red]
  rfl

end Batch
end Math
