import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch21_indices : List Nat :=
  [411, 412, 414, 418, 425, 427]

theorem cert_config_411_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 411 = true :=
  KernelReducer.verifyIdxC_of_D 411 (by kernel_rfl)

theorem cert_config_412_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 412 = true :=
  KernelReducer.verifyIdxC_of_D 412 (by kernel_rfl)

theorem cert_config_414_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 414 = true :=
  KernelReducer.verifyIdxC_of_D 414 (by kernel_rfl)

theorem cert_config_418_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 418 = true :=
  KernelReducer.verifyIdxC_of_D 418 (by kernel_rfl)

theorem cert_config_425_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 425 = true := by kernel_rfl

theorem cert_config_427_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 427 = true :=
  KernelReducer.verifyIdxC_of_D 427 (by kernel_rfl)

theorem cert_cbatch21_r12 : checkCRingBatch 12 cbatch21_indices = true := by
  dsimp only [cbatch21_indices, checkCRingBatch, List.all]
  rw [cert_config_411_c_red, cert_config_412_c_red, cert_config_414_c_red, cert_config_418_c_red, cert_config_425_c_red, cert_config_427_c_red]
  rfl

end Batch
end Math
