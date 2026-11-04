import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

def cbatch19_indices : List Nat :=
  [355, 356, 357, 358, 361, 364]

theorem cert_config_355_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 355 = true :=
  KernelReducer.verifyIdxC_of_D 355 (by kernel_rfl)

theorem cert_config_356_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 356 = true :=
  KernelReducer.verifyIdxC_of_D 356 (by kernel_rfl)

theorem cert_config_357_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 357 = true :=
  KernelReducer.verifyIdxC_of_D 357 (by kernel_rfl)

theorem cert_config_358_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 358 = true :=
  KernelReducer.verifyIdxC_of_D 358 (by kernel_rfl)

theorem cert_config_361_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 361 = true :=
  KernelReducer.verifyIdxC_of_D 361 (by kernel_rfl)

theorem cert_config_364_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 364 = true :=
  KernelReducer.verifyIdxC_of_D 364 (by kernel_rfl)

theorem cert_cbatch19_r12 : checkCRingBatch 12 cbatch19_indices = true := by
  dsimp only [cbatch19_indices, checkCRingBatch, List.all]
  rw [cert_config_355_c_red, cert_config_356_c_red, cert_config_357_c_red, cert_config_358_c_red, cert_config_361_c_red, cert_config_364_c_red]
  rfl

end Batch
end Math
