import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch37_indices : List Nat :=
  [268, 270, 274, 284, 372, 373]

theorem cert_config_268_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 268 = true :=
  KernelReducer.verifyIdxC_of_D 268 (by kernel_rfl)

theorem cert_config_270_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 270 = true :=
  KernelReducer.verifyIdxC_of_D 270 (by kernel_rfl)

theorem cert_config_274_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 274 = true :=
  KernelReducer.verifyIdxC_of_D 274 (by kernel_rfl)

theorem cert_config_284_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 284 = true :=
  KernelReducer.verifyIdxC_of_D 284 (by kernel_rfl)

theorem cert_config_372_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 372 = true :=
  KernelReducer.verifyIdxC_of_D 372 (by kernel_rfl)

theorem cert_config_373_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 373 = true :=
  KernelReducer.verifyIdxC_of_D 373 (by kernel_rfl)

theorem cert_cbatch37_r13 : checkCRingBatch13 cbatch37_indices = true := by
  dsimp only [cbatch37_indices, checkCRingBatch13, List.all]
  rw [cert_config_268_c_red, cert_config_270_c_red, cert_config_274_c_red, cert_config_284_c_red, cert_config_372_c_red, cert_config_373_c_red]
  rfl

end Batch
end Math
