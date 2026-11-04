import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

def cbatch15_indices : List Nat :=
  [138, 139, 140, 141, 142, 143]

theorem cert_config_138_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 138 = true :=
  KernelReducer.verifyIdxC_of_D 138 (by kernel_rfl)

theorem cert_config_139_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 139 = true :=
  KernelReducer.verifyIdxC_of_D 139 (by kernel_rfl)

theorem cert_config_140_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 140 = true := by kernel_rfl

theorem cert_config_141_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 141 = true :=
  KernelReducer.verifyIdxC_of_D 141 (by kernel_rfl)

theorem cert_config_142_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 142 = true :=
  KernelReducer.verifyIdxC_of_D 142 (by kernel_rfl)

theorem cert_config_143_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 143 = true :=
  KernelReducer.verifyIdxC_of_D 143 (by kernel_rfl)

theorem cert_cbatch15_r12 : checkCRingBatch 12 cbatch15_indices = true := by
  dsimp only [cbatch15_indices, checkCRingBatch, List.all]
  rw [cert_config_138_c_red, cert_config_139_c_red, cert_config_140_c_red, cert_config_141_c_red, cert_config_142_c_red, cert_config_143_c_red]
  rfl

end Batch
end Math
