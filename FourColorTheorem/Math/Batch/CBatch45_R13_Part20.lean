import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch45_indices : List Nat :=
  [480, 519, 520, 521, 523, 537]

theorem cert_config_480_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 480 = true :=
  KernelReducer.verifyIdxC_of_D 480 (by kernel_rfl)

theorem cert_config_519_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 519 = true :=
  KernelReducer.verifyIdxC_of_D 519 (by kernel_rfl)

theorem cert_config_520_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 520 = true :=
  KernelReducer.verifyIdxC_of_D 520 (by kernel_rfl)

theorem cert_config_521_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 521 = true :=
  KernelReducer.verifyIdxC_of_D 521 (by kernel_rfl)

theorem cert_config_523_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 523 = true :=
  KernelReducer.verifyIdxC_of_D 523 (by kernel_rfl)

theorem cert_config_537_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 537 = true := by kernel_rfl

theorem cert_cbatch45_r13 : checkCRingBatch13 cbatch45_indices = true := by
  dsimp only [cbatch45_indices, checkCRingBatch13, List.all]
  rw [cert_config_480_c_red, cert_config_519_c_red, cert_config_520_c_red, cert_config_521_c_red, cert_config_523_c_red, cert_config_537_c_red]
  rfl

end Batch
end Math
