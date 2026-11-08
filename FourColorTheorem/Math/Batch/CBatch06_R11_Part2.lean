import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch06_indices : List Nat :=
  [46, 48, 51, 53, 54]

theorem cert_config_46_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 46 = true := by kernel_rfl

theorem cert_config_48_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 48 = true := by kernel_rfl

theorem cert_config_51_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 51 = true := by kernel_rfl

theorem cert_config_53_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 53 = true := by kernel_rfl

theorem cert_config_54_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 54 = true := by kernel_rfl

theorem cert_cbatch06_r11 : checkCRingBatch 11 cbatch06_indices = true := by
  dsimp only [cbatch06_indices, checkCRingBatch, List.all]
  rw [cert_config_46_c_red, cert_config_48_c_red, cert_config_51_c_red, cert_config_53_c_red, cert_config_54_c_red]
  rfl

end Batch
end Math
