import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch05_indices : List Nat :=
  [14, 38, 39, 41, 42]

theorem cert_config_14_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 14 = true :=
  KernelReducer.verifyIdxC_of_D 14 (by kernel_rfl)

theorem cert_config_38_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 38 = true :=
  KernelReducer.verifyIdxC_of_D 38 (by kernel_rfl)

theorem cert_config_39_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 39 = true :=
  KernelReducer.verifyIdxC_of_D 39 (by kernel_rfl)

theorem cert_config_41_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 41 = true :=
  KernelReducer.verifyIdxC_of_D 41 (by kernel_rfl)

theorem cert_config_42_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 42 = true :=
  KernelReducer.verifyIdxC_of_D 42 (by kernel_rfl)

theorem cert_cbatch05_r11 : checkCRingBatch 11 cbatch05_indices = true := by
  dsimp only [cbatch05_indices, checkCRingBatch, List.all]
  rw [cert_config_14_c_red, cert_config_38_c_red, cert_config_39_c_red, cert_config_41_c_red, cert_config_42_c_red]
  rfl

end Batch
end Math
