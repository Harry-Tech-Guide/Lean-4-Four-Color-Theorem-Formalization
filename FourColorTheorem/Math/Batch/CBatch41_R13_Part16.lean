import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch41_indices : List Nat :=
  [448, 449, 453, 454, 455, 456]

theorem cert_config_448_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 448 = true :=
  KernelReducer.verifyIdxC_of_D 448 (by kernel_rfl)

theorem cert_config_449_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 449 = true :=
  KernelReducer.verifyIdxC_of_D 449 (by kernel_rfl)

theorem cert_config_453_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 453 = true := by kernel_rfl

theorem cert_config_454_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 454 = true := by kernel_rfl

theorem cert_config_455_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 455 = true :=
  KernelReducer.verifyIdxC_of_D 455 (by kernel_rfl)

theorem cert_config_456_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 456 = true :=
  KernelReducer.verifyIdxC_of_D 456 (by kernel_rfl)

theorem cert_cbatch41_r13 : checkCRingBatch13 cbatch41_indices = true := by
  dsimp only [cbatch41_indices, checkCRingBatch13, List.all]
  rw [cert_config_448_c_red, cert_config_449_c_red, cert_config_453_c_red, cert_config_454_c_red, cert_config_455_c_red, cert_config_456_c_red]
  rfl

end Batch
end Math
