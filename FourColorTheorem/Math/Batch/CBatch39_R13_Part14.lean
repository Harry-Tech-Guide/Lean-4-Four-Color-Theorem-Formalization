import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch39_indices : List Nat :=
  [384, 396, 435, 436, 437, 439]

theorem cert_config_384_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 384 = true :=
  KernelReducer.verifyIdxC_of_D 384 (by kernel_rfl)

theorem cert_config_396_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 396 = true :=
  KernelReducer.verifyIdxC_of_D 396 (by kernel_rfl)

theorem cert_config_435_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 435 = true :=
  KernelReducer.verifyIdxC_of_D 435 (by kernel_rfl)

theorem cert_config_436_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 436 = true :=
  KernelReducer.verifyIdxC_of_D 436 (by kernel_rfl)

theorem cert_config_437_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 437 = true :=
  KernelReducer.verifyIdxC_of_D 437 (by kernel_rfl)

theorem cert_config_439_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 439 = true :=
  KernelReducer.verifyIdxC_of_D 439 (by kernel_rfl)

theorem cert_cbatch39_r13 : checkCRingBatch13 cbatch39_indices = true := by
  dsimp only [cbatch39_indices, checkCRingBatch13, List.all]
  rw [cert_config_384_c_red, cert_config_396_c_red, cert_config_435_c_red, cert_config_436_c_red, cert_config_437_c_red, cert_config_439_c_red]
  rfl

end Batch
end Math
