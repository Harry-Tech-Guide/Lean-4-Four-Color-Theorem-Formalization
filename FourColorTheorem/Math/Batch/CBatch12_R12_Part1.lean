import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch12_indices : List Nat :=
  [19, 61, 62, 63, 65, 72]

theorem cert_config_19_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 19 = true := by kernel_rfl

theorem cert_config_61_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 61 = true := by kernel_rfl

theorem cert_config_62_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 62 = true := by kernel_rfl

theorem cert_config_63_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 63 = true := by kernel_rfl

theorem cert_config_65_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 65 = true := by kernel_rfl

theorem cert_config_72_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 72 = true := by kernel_rfl

theorem cert_cbatch12_r12 : checkCRingBatch 12 cbatch12_indices = true := by
  dsimp only [cbatch12_indices, checkCRingBatch, List.all]
  rw [cert_config_19_c_red, cert_config_61_c_red, cert_config_62_c_red, cert_config_63_c_red, cert_config_65_c_red, cert_config_72_c_red]
  rfl

end Batch
end Math
