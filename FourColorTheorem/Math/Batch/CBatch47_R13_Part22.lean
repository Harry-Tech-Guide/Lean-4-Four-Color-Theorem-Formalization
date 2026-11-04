import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch47_indices : List Nat :=
  [583, 584, 585, 586, 587, 588]

theorem cert_config_583_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 583 = true :=
  KernelReducer.verifyIdxC_of_D 583 (by kernel_rfl)

theorem cert_config_584_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 584 = true := by kernel_rfl

theorem cert_config_585_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 585 = true :=
  KernelReducer.verifyIdxC_of_D 585 (by kernel_rfl)

theorem cert_config_586_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 586 = true := by kernel_rfl

theorem cert_config_587_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 587 = true :=
  KernelReducer.verifyIdxC_of_D 587 (by kernel_rfl)

theorem cert_config_588_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 588 = true :=
  KernelReducer.verifyIdxC_of_D 588 (by kernel_rfl)

theorem cert_cbatch47_r13 : checkCRingBatch13 cbatch47_indices = true := by
  dsimp only [cbatch47_indices, checkCRingBatch13, List.all]
  rw [cert_config_583_c_red, cert_config_584_c_red, cert_config_585_c_red, cert_config_586_c_red, cert_config_587_c_red, cert_config_588_c_red]
  rfl

end Batch
end Math
