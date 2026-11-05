import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch23_indices : List Nat :=
  [441, 442, 451, 461, 462, 464]

theorem cert_config_441_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 441 = true :=
  KernelReducer.verifyIdxC_of_D 441 (by kernel_rfl)

theorem cert_config_442_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 442 = true :=
  KernelReducer.verifyIdxC_of_D 442 (by kernel_rfl)

theorem cert_config_451_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 451 = true :=
  KernelReducer.verifyIdxC_of_D 451 (by kernel_rfl)

theorem cert_config_461_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 461 = true :=
  KernelReducer.verifyIdxC_of_D 461 (by kernel_rfl)

theorem cert_config_462_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 462 = true :=
  KernelReducer.verifyIdxC_of_D 462 (by kernel_rfl)

theorem cert_config_464_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 464 = true :=
  KernelReducer.verifyIdxC_of_D 464 (by kernel_rfl)

theorem cert_cbatch23_r12 : checkCRingBatch 12 cbatch23_indices = true := by
  dsimp only [cbatch23_indices, checkCRingBatch, List.all]
  rw [cert_config_441_c_red, cert_config_442_c_red, cert_config_451_c_red, cert_config_461_c_red, cert_config_462_c_red, cert_config_464_c_red]
  rfl

end Batch
end Math
