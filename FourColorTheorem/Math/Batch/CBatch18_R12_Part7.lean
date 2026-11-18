module

public import FourColorTheorem.Math.Batch.CRunner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch18_indices : List Nat :=
  [342, 344, 345, 346, 352, 353]

theorem cert_config_342_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 342 = true := by kernel_rfl

theorem cert_config_344_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 344 = true := by kernel_rfl

theorem cert_config_345_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 345 = true := by kernel_rfl

theorem cert_config_346_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 346 = true := by kernel_rfl

theorem cert_config_352_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 352 = true := by kernel_rfl

theorem cert_config_353_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 353 = true := by kernel_rfl

theorem cert_cbatch18_r12 : checkCRingBatch 12 cbatch18_indices = true := by
  dsimp only [cbatch18_indices, checkCRingBatch, List.all]
  rw [cert_config_342_c_red, cert_config_344_c_red, cert_config_345_c_red, cert_config_346_c_red, cert_config_352_c_red, cert_config_353_c_red]
  rfl

end Batch
end Math
