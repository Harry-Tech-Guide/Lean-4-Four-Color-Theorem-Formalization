import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch31_indices : List Nat :=
  [188, 189, 191, 192, 193, 194]

theorem cert_config_188_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 188 = true :=
  KernelReducer.verifyIdxC_of_D 188 (by kernel_rfl)

theorem cert_config_189_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 189 = true :=
  KernelReducer.verifyIdxC_of_D 189 (by kernel_rfl)

theorem cert_config_191_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 191 = true :=
  KernelReducer.verifyIdxC_of_D 191 (by kernel_rfl)

theorem cert_config_192_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 192 = true :=
  KernelReducer.verifyIdxC_of_D 192 (by kernel_rfl)

theorem cert_config_193_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 193 = true :=
  KernelReducer.verifyIdxC_of_D 193 (by kernel_rfl)

theorem cert_config_194_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 194 = true :=
  KernelReducer.verifyIdxC_of_D 194 (by kernel_rfl)

theorem cert_cbatch31_r13 : checkCRingBatch13 cbatch31_indices = true := by
  dsimp only [cbatch31_indices, checkCRingBatch13, List.all]
  rw [cert_config_188_c_red, cert_config_189_c_red, cert_config_191_c_red, cert_config_192_c_red, cert_config_193_c_red, cert_config_194_c_red]
  rfl

end Batch
end Math
