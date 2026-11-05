import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch25_indices : List Nat :=
  [581, 591, 598, 622]

theorem cert_config_581_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 581 = true :=
  KernelReducer.verifyIdxC_of_D 581 (by kernel_rfl)

theorem cert_config_591_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 591 = true :=
  KernelReducer.verifyIdxC_of_D 591 (by kernel_rfl)

theorem cert_config_598_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 598 = true :=
  KernelReducer.verifyIdxC_of_D 598 (by kernel_rfl)

theorem cert_config_622_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 622 = true :=
  KernelReducer.verifyIdxC_of_D 622 (by kernel_rfl)

theorem cert_cbatch25_r12 : checkCRingBatch 12 cbatch25_indices = true := by
  dsimp only [cbatch25_indices, checkCRingBatch, List.all]
  rw [cert_config_581_c_red, cert_config_591_c_red, cert_config_598_c_red, cert_config_622_c_red]
  rfl

end Batch
end Math
