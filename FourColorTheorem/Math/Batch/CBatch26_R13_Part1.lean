import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch26_indices : List Nat :=
  [22, 82, 94, 95, 100, 101]

theorem cert_config_22_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 22 = true :=
  KernelReducer.verifyIdxC_of_D 22 (by kernel_rfl)

theorem cert_config_82_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 82 = true :=
  KernelReducer.verifyIdxC_of_D 82 (by kernel_rfl)

theorem cert_config_94_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 94 = true :=
  KernelReducer.verifyIdxC_of_D 94 (by kernel_rfl)

theorem cert_config_95_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 95 = true :=
  KernelReducer.verifyIdxC_of_D 95 (by kernel_rfl)

theorem cert_config_100_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 100 = true :=
  KernelReducer.verifyIdxC_of_D 100 (by kernel_rfl)

theorem cert_config_101_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 101 = true :=
  KernelReducer.verifyIdxC_of_D 101 (by kernel_rfl)

theorem cert_cbatch26_r13 : checkCRingBatch13 cbatch26_indices = true := by
  dsimp only [cbatch26_indices, checkCRingBatch13, List.all]
  rw [cert_config_22_c_red, cert_config_82_c_red, cert_config_94_c_red, cert_config_95_c_red, cert_config_100_c_red, cert_config_101_c_red]
  rfl

end Batch
end Math
