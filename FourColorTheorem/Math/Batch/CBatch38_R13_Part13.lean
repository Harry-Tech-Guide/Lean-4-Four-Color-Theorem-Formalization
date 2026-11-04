import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch38_indices : List Nat :=
  [376, 377, 378, 379, 380, 381]

theorem cert_config_376_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 376 = true :=
  KernelReducer.verifyIdxC_of_D 376 (by kernel_rfl)

theorem cert_config_377_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 377 = true :=
  KernelReducer.verifyIdxC_of_D 377 (by kernel_rfl)

theorem cert_config_378_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 378 = true :=
  KernelReducer.verifyIdxC_of_D 378 (by kernel_rfl)

theorem cert_config_379_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 379 = true :=
  KernelReducer.verifyIdxC_of_D 379 (by kernel_rfl)

theorem cert_config_380_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 380 = true :=
  KernelReducer.verifyIdxC_of_D 380 (by kernel_rfl)

theorem cert_config_381_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 381 = true :=
  KernelReducer.verifyIdxC_of_D 381 (by kernel_rfl)

theorem cert_cbatch38_r13 : checkCRingBatch13 cbatch38_indices = true := by
  dsimp only [cbatch38_indices, checkCRingBatch13, List.all]
  rw [cert_config_376_c_red, cert_config_377_c_red, cert_config_378_c_red, cert_config_379_c_red, cert_config_380_c_red, cert_config_381_c_red]
  rfl

end Batch
end Math
