import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch36_indices : List Nat :=
  [262, 263, 264, 265, 266, 267]

theorem cert_config_262_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 262 = true :=
  KernelReducer.verifyIdxC_of_D 262 (by kernel_rfl)

theorem cert_config_263_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 263 = true :=
  KernelReducer.verifyIdxC_of_D 263 (by kernel_rfl)

theorem cert_config_264_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 264 = true :=
  KernelReducer.verifyIdxC_of_D 264 (by kernel_rfl)

theorem cert_config_265_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 265 = true := by kernel_rfl

theorem cert_config_266_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 266 = true :=
  KernelReducer.verifyIdxC_of_D 266 (by kernel_rfl)

theorem cert_config_267_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 267 = true :=
  KernelReducer.verifyIdxC_of_D 267 (by kernel_rfl)

theorem cert_cbatch36_r13 : checkCRingBatch13 cbatch36_indices = true := by
  dsimp only [cbatch36_indices, checkCRingBatch13, List.all]
  rw [cert_config_262_c_red, cert_config_263_c_red, cert_config_264_c_red, cert_config_265_c_red, cert_config_266_c_red, cert_config_267_c_red]
  rfl

end Batch
end Math
