import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch42_indices : List Nat :=
  [457, 458, 459, 460, 463, 465]

theorem cert_config_457_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 457 = true :=
  KernelReducer.verifyIdxC_of_D 457 (by kernel_rfl)

theorem cert_config_458_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 458 = true :=
  KernelReducer.verifyIdxC_of_D 458 (by kernel_rfl)

theorem cert_config_459_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 459 = true :=
  KernelReducer.verifyIdxC_of_D 459 (by kernel_rfl)

theorem cert_config_460_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 460 = true :=
  KernelReducer.verifyIdxC_of_D 460 (by kernel_rfl)

theorem cert_config_463_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 463 = true :=
  KernelReducer.verifyIdxC_of_D 463 (by kernel_rfl)

theorem cert_config_465_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 465 = true :=
  KernelReducer.verifyIdxC_of_D 465 (by kernel_rfl)

theorem cert_cbatch42_r13 : checkCRingBatch13 cbatch42_indices = true := by
  dsimp only [cbatch42_indices, checkCRingBatch13, List.all]
  rw [cert_config_457_c_red, cert_config_458_c_red, cert_config_459_c_red, cert_config_460_c_red, cert_config_463_c_red, cert_config_465_c_red]
  rfl

end Batch
end Math
