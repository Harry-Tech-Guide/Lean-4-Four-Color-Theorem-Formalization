import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

def cbatch14_indices : List Nat :=
  [127, 128, 130, 131, 136, 137]

theorem cert_config_127_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 127 = true :=
  KernelReducer.verifyIdxC_of_D 127 (by kernel_rfl)

theorem cert_config_128_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 128 = true :=
  KernelReducer.verifyIdxC_of_D 128 (by kernel_rfl)

theorem cert_config_130_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 130 = true := by kernel_rfl

theorem cert_config_131_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 131 = true :=
  KernelReducer.verifyIdxC_of_D 131 (by kernel_rfl)

theorem cert_config_136_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 136 = true := by kernel_rfl

theorem cert_config_137_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 137 = true :=
  KernelReducer.verifyIdxC_of_D 137 (by kernel_rfl)

theorem cert_cbatch14_r12 : checkCRingBatch 12 cbatch14_indices = true := by
  dsimp only [cbatch14_indices, checkCRingBatch, List.all]
  rw [cert_config_127_c_red, cert_config_128_c_red, cert_config_130_c_red, cert_config_131_c_red, cert_config_136_c_red, cert_config_137_c_red]
  rfl

end Batch
end Math
