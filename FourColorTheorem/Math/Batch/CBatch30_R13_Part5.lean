import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch30_indices : List Nat :=
  [182, 183, 184, 185, 186, 187]

theorem cert_config_182_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 182 = true :=
  KernelReducer.verifyIdxC_of_D 182 (by kernel_rfl)

theorem cert_config_183_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 183 = true :=
  KernelReducer.verifyIdxC_of_D 183 (by kernel_rfl)

theorem cert_config_184_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 184 = true := by kernel_rfl

theorem cert_config_185_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 185 = true :=
  KernelReducer.verifyIdxC_of_D 185 (by kernel_rfl)

theorem cert_config_186_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 186 = true :=
  KernelReducer.verifyIdxC_of_D 186 (by kernel_rfl)

theorem cert_config_187_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 187 = true :=
  KernelReducer.verifyIdxC_of_D 187 (by kernel_rfl)

theorem cert_cbatch30_r13 : checkCRingBatch13 cbatch30_indices = true := by
  dsimp only [cbatch30_indices, checkCRingBatch13, List.all]
  rw [cert_config_182_c_red, cert_config_183_c_red, cert_config_184_c_red, cert_config_185_c_red, cert_config_186_c_red, cert_config_187_c_red]
  rfl

end Batch
end Math
