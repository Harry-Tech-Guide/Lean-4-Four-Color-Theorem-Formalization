import FourColorTheorem.Math.Batch.CRunner

namespace Math
namespace Batch

open FastReducer

def cbatch04_indices : List Nat :=
  [35, 111, 116, 326, 327]

theorem cert_config_35_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 35 = true :=
  KernelReducer.verifyIdxC_of_D 35 (by kernel_rfl)

theorem cert_config_111_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 111 = true :=
  KernelReducer.verifyIdxC_of_D 111 (by kernel_rfl)

theorem cert_config_116_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 116 = true :=
  KernelReducer.verifyIdxC_of_D 116 (by kernel_rfl)

theorem cert_config_326_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 326 = true :=
  KernelReducer.verifyIdxC_of_D 326 (by kernel_rfl)

theorem cert_config_327_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 327 = true :=
  KernelReducer.verifyIdxC_of_D 327 (by kernel_rfl)

theorem cert_cbatch04_r10 : checkCRingBatch 10 cbatch04_indices = true := by
  dsimp only [cbatch04_indices, checkCRingBatch, List.all]
  rw [cert_config_35_c_red, cert_config_111_c_red, cert_config_116_c_red, cert_config_326_c_red, cert_config_327_c_red]
  rfl

end Batch
end Math
