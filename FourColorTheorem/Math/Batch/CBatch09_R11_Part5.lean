import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch09_indices : List Nat :=
  [125, 134, 135, 241, 329]

theorem cert_config_125_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 125 = true := by kernel_rfl

theorem cert_config_134_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 134 = true := by kernel_rfl

theorem cert_config_135_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 135 = true := by kernel_rfl

theorem cert_config_241_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 241 = true := by kernel_rfl

theorem cert_config_329_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 329 = true := by kernel_rfl

theorem cert_cbatch09_r11 : checkCRingBatch 11 cbatch09_indices = true := by
  dsimp only [cbatch09_indices, checkCRingBatch, List.all]
  rw [cert_config_125_c_red, cert_config_134_c_red, cert_config_135_c_red, cert_config_241_c_red, cert_config_329_c_red]
  rfl

end Batch
end Math
