import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

def cbatch13_indices : List Nat :=
  [73, 74, 79, 88, 89, 126]

theorem cert_config_73_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 73 = true :=
  KernelReducer.verifyIdxC_of_D 73 (by kernel_rfl)

theorem cert_config_74_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 74 = true :=
  KernelReducer.verifyIdxC_of_D 74 (by kernel_rfl)

theorem cert_config_79_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 79 = true :=
  KernelReducer.verifyIdxC_of_D 79 (by kernel_rfl)

theorem cert_config_88_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 88 = true :=
  KernelReducer.verifyIdxC_of_D 88 (by kernel_rfl)

theorem cert_config_89_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 89 = true :=
  KernelReducer.verifyIdxC_of_D 89 (by kernel_rfl)

theorem cert_config_126_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 126 = true :=
  KernelReducer.verifyIdxC_of_D 126 (by kernel_rfl)

theorem cert_cbatch13_r12 : checkCRingBatch 12 cbatch13_indices = true := by
  dsimp only [cbatch13_indices, checkCRingBatch, List.all]
  rw [cert_config_73_c_red, cert_config_74_c_red, cert_config_79_c_red, cert_config_88_c_red, cert_config_89_c_red, cert_config_126_c_red]
  rfl

end Batch
end Math
