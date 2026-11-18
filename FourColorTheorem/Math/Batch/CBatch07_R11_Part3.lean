module

public import FourColorTheorem.Math.Batch.CRunner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch07_indices : List Nat :=
  [55, 57, 59, 113, 115]

theorem cert_config_55_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 55 = true := by kernel_rfl

theorem cert_config_57_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 57 = true := by kernel_rfl

theorem cert_config_59_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 59 = true := by kernel_rfl

theorem cert_config_113_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 113 = true := by kernel_rfl

theorem cert_config_115_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 115 = true := by kernel_rfl

theorem cert_cbatch07_r11 : checkCRingBatch 11 cbatch07_indices = true := by
  dsimp only [cbatch07_indices, checkCRingBatch, List.all]
  rw [cert_config_55_c_red, cert_config_57_c_red, cert_config_59_c_red, cert_config_113_c_red, cert_config_115_c_red]
  rfl

end Batch
end Math
