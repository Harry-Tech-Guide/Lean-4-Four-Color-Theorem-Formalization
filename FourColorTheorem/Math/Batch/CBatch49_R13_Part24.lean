import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch49_indices : List Nat :=
  [616, 624, 625, 626]

theorem cert_config_616_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 616 = true :=
  KernelReducer.verifyIdxC_of_D 616 (by kernel_rfl)

theorem cert_config_624_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 624 = true :=
  KernelReducer.verifyIdxC_of_D 624 (by kernel_rfl)

theorem cert_config_625_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 625 = true :=
  KernelReducer.verifyIdxC_of_D 625 (by kernel_rfl)

theorem cert_config_626_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 626 = true :=
  KernelReducer.verifyIdxC_of_D 626 (by kernel_rfl)

theorem cert_cbatch49_r13 : checkCRingBatch13 cbatch49_indices = true := by
  dsimp only [cbatch49_indices, checkCRingBatch13, List.all]
  rw [cert_config_616_c_red, cert_config_624_c_red, cert_config_625_c_red, cert_config_626_c_red]
  rfl

end Batch
end Math
