import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch28_indices : List Nat :=
  [162, 163, 164, 165, 166, 168]

theorem cert_config_162_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 162 = true :=
  KernelReducer.verifyIdxC_of_D 162 (by kernel_rfl)

theorem cert_config_163_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 163 = true :=
  KernelReducer.verifyIdxC_of_D 163 (by kernel_rfl)

theorem cert_config_164_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 164 = true :=
  KernelReducer.verifyIdxC_of_D 164 (by kernel_rfl)

theorem cert_config_165_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 165 = true :=
  KernelReducer.verifyIdxC_of_D 165 (by kernel_rfl)

theorem cert_config_166_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 166 = true :=
  KernelReducer.verifyIdxC_of_D 166 (by kernel_rfl)

theorem cert_config_168_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 168 = true :=
  KernelReducer.verifyIdxC_of_D 168 (by kernel_rfl)

theorem cert_cbatch28_r13 : checkCRingBatch13 cbatch28_indices = true := by
  dsimp only [cbatch28_indices, checkCRingBatch13, List.all]
  rw [cert_config_162_c_red, cert_config_163_c_red, cert_config_164_c_red, cert_config_165_c_red, cert_config_166_c_red, cert_config_168_c_red]
  rfl

end Batch
end Math
