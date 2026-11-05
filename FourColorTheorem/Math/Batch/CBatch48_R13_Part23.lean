import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch48_indices : List Nat :=
  [592, 595, 600, 601, 602, 603]

theorem cert_config_592_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 592 = true :=
  KernelReducer.verifyIdxC_of_D 592 (by kernel_rfl)

theorem cert_config_595_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 595 = true :=
  KernelReducer.verifyIdxC_of_D 595 (by kernel_rfl)

theorem cert_config_600_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 600 = true :=
  KernelReducer.verifyIdxC_of_D 600 (by kernel_rfl)

theorem cert_config_601_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 601 = true :=
  KernelReducer.verifyIdxC_of_D 601 (by kernel_rfl)

theorem cert_config_602_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 602 = true :=
  KernelReducer.verifyIdxC_of_D 602 (by kernel_rfl)

theorem cert_config_603_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 603 = true :=
  KernelReducer.verifyIdxC_of_D 603 (by kernel_rfl)

theorem cert_cbatch48_r13 : checkCRingBatch13 cbatch48_indices = true := by
  dsimp only [cbatch48_indices, checkCRingBatch13, List.all]
  rw [cert_config_592_c_red, cert_config_595_c_red, cert_config_600_c_red, cert_config_601_c_red, cert_config_602_c_red, cert_config_603_c_red]
  rfl

end Batch
end Math
