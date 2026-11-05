import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch29_indices : List Nat :=
  [169, 171, 177, 179, 180, 181]

theorem cert_config_169_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 169 = true :=
  KernelReducer.verifyIdxC_of_D 169 (by kernel_rfl)

theorem cert_config_171_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 171 = true :=
  KernelReducer.verifyIdxC_of_D 171 (by kernel_rfl)

theorem cert_config_177_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 177 = true := by kernel_rfl

theorem cert_config_179_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 179 = true := by kernel_rfl

theorem cert_config_180_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 180 = true :=
  KernelReducer.verifyIdxC_of_D 180 (by kernel_rfl)

theorem cert_config_181_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 181 = true :=
  KernelReducer.verifyIdxC_of_D 181 (by kernel_rfl)

theorem cert_cbatch29_r13 : checkCRingBatch13 cbatch29_indices = true := by
  dsimp only [cbatch29_indices, checkCRingBatch13, List.all]
  rw [cert_config_169_c_red, cert_config_171_c_red, cert_config_177_c_red, cert_config_179_c_red, cert_config_180_c_red, cert_config_181_c_red]
  rfl

end Batch
end Math
