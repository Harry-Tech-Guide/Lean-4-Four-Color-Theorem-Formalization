import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch14_indices : List Nat :=
  [99, 108, 132, 146, 149, 150]

theorem cert_config_99_d_red : checkIdxFast (buildSMData 12 sharedPow3) 99 = true := by kernel_rfl

theorem cert_config_108_d_red : checkIdxFast (buildSMData 12 sharedPow3) 108 = true := by kernel_rfl

theorem cert_config_132_d_red : checkIdxFast (buildSMData 12 sharedPow3) 132 = true := by kernel_rfl

theorem cert_config_146_d_red : checkIdxFast (buildSMData 12 sharedPow3) 146 = true := by kernel_rfl

theorem cert_config_149_d_red : checkIdxFast (buildSMData 12 sharedPow3) 149 = true := by kernel_rfl

theorem cert_config_150_d_red : checkIdxFast (buildSMData 12 sharedPow3) 150 = true := by kernel_rfl

theorem cert_batch14_r12 : checkRingBatch 12 batch14_indices = true := by
  dsimp only [batch14_indices, checkRingBatch, List.all]
  rw [cert_config_99_d_red, cert_config_108_d_red, cert_config_132_d_red, cert_config_146_d_red, cert_config_149_d_red, cert_config_150_d_red]
  rfl

end Batch
end Math
