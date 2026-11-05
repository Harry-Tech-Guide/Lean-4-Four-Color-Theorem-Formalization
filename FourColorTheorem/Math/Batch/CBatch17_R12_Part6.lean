import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch17_indices : List Nat :=
  [178, 244, 245, 249, 250, 257]

theorem cert_config_178_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 178 = true :=
  KernelReducer.verifyIdxC_of_D 178 (by kernel_rfl)

theorem cert_config_244_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 244 = true :=
  KernelReducer.verifyIdxC_of_D 244 (by kernel_rfl)

theorem cert_config_245_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 245 = true :=
  KernelReducer.verifyIdxC_of_D 245 (by kernel_rfl)

theorem cert_config_249_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 249 = true :=
  KernelReducer.verifyIdxC_of_D 249 (by kernel_rfl)

theorem cert_config_250_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 250 = true := by kernel_rfl

theorem cert_config_257_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 257 = true :=
  KernelReducer.verifyIdxC_of_D 257 (by kernel_rfl)

theorem cert_cbatch17_r12 : checkCRingBatch 12 cbatch17_indices = true := by
  dsimp only [cbatch17_indices, checkCRingBatch, List.all]
  rw [cert_config_178_c_red, cert_config_244_c_red, cert_config_245_c_red, cert_config_249_c_red, cert_config_250_c_red, cert_config_257_c_red]
  rfl

end Batch
end Math
