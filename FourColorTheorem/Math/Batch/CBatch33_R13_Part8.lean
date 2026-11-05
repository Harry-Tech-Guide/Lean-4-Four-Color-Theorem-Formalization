import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch33_indices : List Nat :=
  [203, 204, 205, 209, 211, 213]

theorem cert_config_203_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 203 = true :=
  KernelReducer.verifyIdxC_of_D 203 (by kernel_rfl)

theorem cert_config_204_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 204 = true :=
  KernelReducer.verifyIdxC_of_D 204 (by kernel_rfl)

theorem cert_config_205_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 205 = true :=
  KernelReducer.verifyIdxC_of_D 205 (by kernel_rfl)

theorem cert_config_209_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 209 = true :=
  KernelReducer.verifyIdxC_of_D 209 (by kernel_rfl)

theorem cert_config_211_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 211 = true :=
  KernelReducer.verifyIdxC_of_D 211 (by kernel_rfl)

theorem cert_config_213_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 213 = true :=
  KernelReducer.verifyIdxC_of_D 213 (by kernel_rfl)

theorem cert_cbatch33_r13 : checkCRingBatch13 cbatch33_indices = true := by
  dsimp only [cbatch33_indices, checkCRingBatch13, List.all]
  rw [cert_config_203_c_red, cert_config_204_c_red, cert_config_205_c_red, cert_config_209_c_red, cert_config_211_c_red, cert_config_213_c_red]
  rfl

end Batch
end Math
