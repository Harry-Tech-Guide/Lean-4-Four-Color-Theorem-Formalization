import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch13_indices : List Nat :=
  [91, 92, 93, 96, 97, 98]

theorem cert_config_91_d_red : checkIdxFast (buildSMData 12 sharedPow3) 91 = true := by kernel_rfl

theorem cert_config_92_d_red : checkIdxFast (buildSMData 12 sharedPow3) 92 = true := by kernel_rfl

theorem cert_config_93_d_red : checkIdxFast (buildSMData 12 sharedPow3) 93 = true := by kernel_rfl

theorem cert_config_96_d_red : checkIdxFast (buildSMData 12 sharedPow3) 96 = true := by kernel_rfl

theorem cert_config_97_d_red : checkIdxFast (buildSMData 12 sharedPow3) 97 = true := by kernel_rfl

theorem cert_config_98_d_red : checkIdxFast (buildSMData 12 sharedPow3) 98 = true := by kernel_rfl

theorem cert_batch13_r12 : checkRingBatch 12 batch13_indices = true := by
  dsimp only [batch13_indices, checkRingBatch, List.all]
  rw [cert_config_91_d_red, cert_config_92_d_red, cert_config_93_d_red, cert_config_96_d_red, cert_config_97_d_red, cert_config_98_d_red]
  rfl

end Batch
end Math
