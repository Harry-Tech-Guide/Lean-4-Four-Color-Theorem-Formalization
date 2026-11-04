import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch46_indices : List Nat :=
  [538, 539, 544, 550, 557, 558]

theorem cert_config_538_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 538 = true := by kernel_rfl

theorem cert_config_539_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 539 = true :=
  KernelReducer.verifyIdxC_of_D 539 (by kernel_rfl)

theorem cert_config_544_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 544 = true :=
  KernelReducer.verifyIdxC_of_D 544 (by kernel_rfl)

theorem cert_config_550_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 550 = true :=
  KernelReducer.verifyIdxC_of_D 550 (by kernel_rfl)

theorem cert_config_557_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 557 = true := by kernel_rfl

theorem cert_config_558_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 558 = true := by kernel_rfl

theorem cert_cbatch46_r13 : checkCRingBatch13 cbatch46_indices = true := by
  dsimp only [cbatch46_indices, checkCRingBatch13, List.all]
  rw [cert_config_538_c_red, cert_config_539_c_red, cert_config_544_c_red, cert_config_550_c_red, cert_config_557_c_red, cert_config_558_c_red]
  rfl

end Batch
end Math
