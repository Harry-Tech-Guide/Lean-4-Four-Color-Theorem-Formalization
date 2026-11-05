import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch35_indices : List Nat :=
  [255, 256, 258, 259, 260, 261]

theorem cert_config_255_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 255 = true := by kernel_rfl

theorem cert_config_256_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 256 = true :=
  KernelReducer.verifyIdxC_of_D 256 (by kernel_rfl)

theorem cert_config_258_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 258 = true :=
  KernelReducer.verifyIdxC_of_D 258 (by kernel_rfl)

theorem cert_config_259_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 259 = true :=
  KernelReducer.verifyIdxC_of_D 259 (by kernel_rfl)

theorem cert_config_260_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 260 = true :=
  KernelReducer.verifyIdxC_of_D 260 (by kernel_rfl)

theorem cert_config_261_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 261 = true :=
  KernelReducer.verifyIdxC_of_D 261 (by kernel_rfl)

theorem cert_cbatch35_r13 : checkCRingBatch13 cbatch35_indices = true := by
  dsimp only [cbatch35_indices, checkCRingBatch13, List.all]
  rw [cert_config_255_c_red, cert_config_256_c_red, cert_config_258_c_red, cert_config_259_c_red, cert_config_260_c_red, cert_config_261_c_red]
  rfl

end Batch
end Math
