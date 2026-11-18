module

public import FourColorTheorem.Math.Batch.CRunner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch08_indices : List Nat :=
  [118, 121, 122, 123, 124]

theorem cert_config_118_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 118 = true := by kernel_rfl

theorem cert_config_121_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 121 = true := by kernel_rfl

theorem cert_config_122_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 122 = true := by kernel_rfl

theorem cert_config_123_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 123 = true := by kernel_rfl

theorem cert_config_124_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 124 = true := by kernel_rfl

theorem cert_cbatch08_r11 : checkCRingBatch 11 cbatch08_indices = true := by
  dsimp only [cbatch08_indices, checkCRingBatch, List.all]
  rw [cert_config_118_c_red, cert_config_121_c_red, cert_config_122_c_red, cert_config_123_c_red, cert_config_124_c_red]
  rfl

end Batch
end Math
