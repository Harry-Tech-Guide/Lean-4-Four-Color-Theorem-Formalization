import FourColorTheorem.Math.Batch.CRunner13

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch44_indices : List Nat :=
  [474, 475, 476, 477, 478, 479]

theorem cert_config_474_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 474 = true :=
  KernelReducer.verifyIdxC_of_D 474 (by kernel_rfl)

theorem cert_config_475_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 475 = true :=
  KernelReducer.verifyIdxC_of_D 475 (by kernel_rfl)

theorem cert_config_476_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 476 = true :=
  KernelReducer.verifyIdxC_of_D 476 (by kernel_rfl)

theorem cert_config_477_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 477 = true :=
  KernelReducer.verifyIdxC_of_D 477 (by kernel_rfl)

theorem cert_config_478_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 478 = true :=
  KernelReducer.verifyIdxC_of_D 478 (by kernel_rfl)

theorem cert_config_479_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 479 = true :=
  KernelReducer.verifyIdxC_of_D 479 (by kernel_rfl)

theorem cert_cbatch44_r13 : checkCRingBatch13 cbatch44_indices = true := by
  dsimp only [cbatch44_indices, checkCRingBatch13, List.all]
  rw [cert_config_474_c_red, cert_config_475_c_red, cert_config_476_c_red, cert_config_477_c_red, cert_config_478_c_red, cert_config_479_c_red]
  rfl

end Batch
end Math
