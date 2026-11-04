import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch43_indices : List Nat :=
  [466, 467, 468, 469, 470, 473]

theorem cert_config_466_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 466 = true :=
  KernelReducer.verifyIdxC_of_D 466 (by kernel_rfl)

theorem cert_config_467_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 467 = true := by kernel_rfl

theorem cert_config_468_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 468 = true :=
  KernelReducer.verifyIdxC_of_D 468 (by kernel_rfl)

theorem cert_config_469_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 469 = true :=
  KernelReducer.verifyIdxC_of_D 469 (by kernel_rfl)

theorem cert_config_470_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 470 = true :=
  KernelReducer.verifyIdxC_of_D 470 (by kernel_rfl)

theorem cert_config_473_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 473 = true :=
  KernelReducer.verifyIdxC_of_D 473 (by kernel_rfl)

theorem cert_cbatch43_r13 : checkCRingBatch13 cbatch43_indices = true := by
  dsimp only [cbatch43_indices, checkCRingBatch13, List.all]
  rw [cert_config_466_c_red, cert_config_467_c_red, cert_config_468_c_red, cert_config_469_c_red, cert_config_470_c_red, cert_config_473_c_red]
  rfl

end Batch
end Math
