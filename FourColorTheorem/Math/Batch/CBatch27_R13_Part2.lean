import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch27_indices : List Nat :=
  [102, 103, 151, 159, 160, 161]

theorem cert_config_102_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 102 = true :=
  KernelReducer.verifyIdxC_of_D 102 (by kernel_rfl)

theorem cert_config_103_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 103 = true :=
  KernelReducer.verifyIdxC_of_D 103 (by kernel_rfl)

theorem cert_config_151_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 151 = true :=
  KernelReducer.verifyIdxC_of_D 151 (by kernel_rfl)

theorem cert_config_159_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 159 = true := by kernel_rfl

theorem cert_config_160_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 160 = true := by kernel_rfl

theorem cert_config_161_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 161 = true :=
  KernelReducer.verifyIdxC_of_D 161 (by kernel_rfl)

theorem cert_cbatch27_r13 : checkCRingBatch13 cbatch27_indices = true := by
  dsimp only [cbatch27_indices, checkCRingBatch13, List.all]
  rw [cert_config_102_c_red, cert_config_103_c_red, cert_config_151_c_red, cert_config_159_c_red, cert_config_160_c_red, cert_config_161_c_red]
  rfl

end Batch
end Math
