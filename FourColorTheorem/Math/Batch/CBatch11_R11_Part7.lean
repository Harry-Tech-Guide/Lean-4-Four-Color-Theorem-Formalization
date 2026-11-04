import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

def cbatch11_indices : List Nat :=
  [341, 367, 402, 403, 426, 569]

theorem cert_config_341_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 341 = true :=
  KernelReducer.verifyIdxC_of_D 341 (by kernel_rfl)

theorem cert_config_367_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 367 = true :=
  KernelReducer.verifyIdxC_of_D 367 (by kernel_rfl)

theorem cert_config_402_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 402 = true :=
  KernelReducer.verifyIdxC_of_D 402 (by kernel_rfl)

theorem cert_config_403_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 403 = true :=
  KernelReducer.verifyIdxC_of_D 403 (by kernel_rfl)

theorem cert_config_426_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 426 = true :=
  KernelReducer.verifyIdxC_of_D 426 (by kernel_rfl)

theorem cert_config_569_c_red : checkIdxCFast (buildSMData 11 sharedPow3) 569 = true :=
  KernelReducer.verifyIdxC_of_D 569 (by kernel_rfl)

theorem cert_cbatch11_r11 : checkCRingBatch 11 cbatch11_indices = true := by
  dsimp only [cbatch11_indices, checkCRingBatch, List.all]
  rw [cert_config_341_c_red, cert_config_367_c_red, cert_config_402_c_red, cert_config_403_c_red, cert_config_426_c_red, cert_config_569_c_red]
  rfl

end Batch
end Math
