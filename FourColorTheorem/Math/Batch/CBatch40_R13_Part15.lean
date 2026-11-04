import FourColorTheorem.Math.Batch.CRunner13

namespace Math
namespace Batch

open FastReducer

def cbatch40_indices : List Nat :=
  [440, 443, 444, 445, 446, 447]

theorem cert_config_440_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 440 = true := by kernel_rfl

theorem cert_config_443_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 443 = true :=
  KernelReducer.verifyIdxC_of_D 443 (by kernel_rfl)

theorem cert_config_444_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 444 = true :=
  KernelReducer.verifyIdxC_of_D 444 (by kernel_rfl)

theorem cert_config_445_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 445 = true :=
  KernelReducer.verifyIdxC_of_D 445 (by kernel_rfl)

theorem cert_config_446_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 446 = true := by kernel_rfl

theorem cert_config_447_c_red : checkIdxCFast13 (buildSMData 13 sharedPow3) 447 = true :=
  KernelReducer.verifyIdxC_of_D 447 (by kernel_rfl)

theorem cert_cbatch40_r13 : checkCRingBatch13 cbatch40_indices = true := by
  dsimp only [cbatch40_indices, checkCRingBatch13, List.all]
  rw [cert_config_440_c_red, cert_config_443_c_red, cert_config_444_c_red, cert_config_445_c_red, cert_config_446_c_red, cert_config_447_c_red]
  rfl

end Batch
end Math
