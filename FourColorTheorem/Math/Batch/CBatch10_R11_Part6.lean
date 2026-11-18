module

public import FourColorTheorem.Math.Batch.CRunner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch10_indices : List Nat :=
  [331, 333, 335, 338, 339, 340]

theorem cert_config_331_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 331 = true := by kernel_rfl

theorem cert_config_333_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 333 = true := by kernel_rfl

theorem cert_config_335_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 335 = true := by kernel_rfl

theorem cert_config_338_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 338 = true := by kernel_rfl

theorem cert_config_339_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 339 = true := by kernel_rfl

theorem cert_config_340_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 340 = true := by kernel_rfl

theorem cert_cbatch10_r11 : checkCRingBatch 11 cbatch10_indices = true := by
  dsimp only [cbatch10_indices, checkCRingBatch, List.all]
  rw [cert_config_331_c_red, cert_config_333_c_red, cert_config_335_c_red, cert_config_338_c_red, cert_config_339_c_red, cert_config_340_c_red]
  rfl

end Batch
end Math
