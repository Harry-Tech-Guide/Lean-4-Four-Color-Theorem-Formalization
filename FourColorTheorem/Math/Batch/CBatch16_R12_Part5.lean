import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch16_indices : List Nat :=
  [144, 145, 147, 148, 152, 158]

theorem cert_config_144_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 144 = true :=
  KernelReducer.verifyIdxC_of_D 144 (by kernel_rfl)

theorem cert_config_145_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 145 = true :=
  KernelReducer.verifyIdxC_of_D 145 (by kernel_rfl)

theorem cert_config_147_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 147 = true :=
  KernelReducer.verifyIdxC_of_D 147 (by kernel_rfl)

theorem cert_config_148_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 148 = true :=
  KernelReducer.verifyIdxC_of_D 148 (by kernel_rfl)

theorem cert_config_152_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 152 = true :=
  KernelReducer.verifyIdxC_of_D 152 (by kernel_rfl)

theorem cert_config_158_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 158 = true := by kernel_rfl

theorem cert_cbatch16_r12 : checkCRingBatch 12 cbatch16_indices = true := by
  dsimp only [cbatch16_indices, checkCRingBatch, List.all]
  rw [cert_config_144_c_red, cert_config_145_c_red, cert_config_147_c_red, cert_config_148_c_red, cert_config_152_c_red, cert_config_158_c_red]
  rfl

end Batch
end Math
