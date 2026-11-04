import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch32_indices : List Nat :=
  [195, 196, 197, 198, 199, 200]

theorem cert_config_195_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 195 = true :=
  KernelReducer.verifyIdxC_of_D 195 (by kernel_rfl)

theorem cert_config_196_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 196 = true :=
  KernelReducer.verifyIdxC_of_D 196 (by kernel_rfl)

theorem cert_config_197_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 197 = true :=
  KernelReducer.verifyIdxC_of_D 197 (by kernel_rfl)

theorem cert_config_198_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 198 = true :=
  KernelReducer.verifyIdxC_of_D 198 (by kernel_rfl)

theorem cert_config_199_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 199 = true :=
  KernelReducer.verifyIdxC_of_D 199 (by kernel_rfl)

theorem cert_config_200_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 200 = true := by kernel_rfl

theorem cert_cbatch32_r13 : checkCRingBatch13 cbatch32_indices = true := by
  dsimp only [cbatch32_indices, checkCRingBatch13, List.all]
  rw [cert_config_195_c_red, cert_config_196_c_red, cert_config_197_c_red, cert_config_198_c_red, cert_config_199_c_red, cert_config_200_c_red]
  rfl

end Batch
end Math
