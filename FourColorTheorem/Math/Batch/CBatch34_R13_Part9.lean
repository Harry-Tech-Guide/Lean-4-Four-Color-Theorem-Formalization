import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch34_indices : List Nat :=
  [217, 248, 251, 252, 253, 254]

theorem cert_config_217_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 217 = true :=
  KernelReducer.verifyIdxC_of_D 217 (by kernel_rfl)

theorem cert_config_248_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 248 = true :=
  KernelReducer.verifyIdxC_of_D 248 (by kernel_rfl)

theorem cert_config_251_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 251 = true := by kernel_rfl

theorem cert_config_252_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 252 = true :=
  KernelReducer.verifyIdxC_of_D 252 (by kernel_rfl)

theorem cert_config_253_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 253 = true :=
  KernelReducer.verifyIdxC_of_D 253 (by kernel_rfl)

theorem cert_config_254_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 254 = true := by kernel_rfl

theorem cert_cbatch34_r13 : checkCRingBatch13 cbatch34_indices = true := by
  dsimp only [cbatch34_indices, checkCRingBatch13, List.all]
  rw [cert_config_217_c_red, cert_config_248_c_red, cert_config_251_c_red, cert_config_252_c_red, cert_config_253_c_red, cert_config_254_c_red]
  rfl

end Batch
end Math
