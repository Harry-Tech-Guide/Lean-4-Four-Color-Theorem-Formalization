import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

def batch28_indices : List Nat :=
  [106, 107, 167, 170]

theorem cert_config_106_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 106 = true := by kernel_rfl

theorem cert_config_107_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 107 = true := by kernel_rfl

theorem cert_config_167_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 167 = true := by kernel_rfl

theorem cert_config_170_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 170 = true := by kernel_rfl

theorem cert_batch28_r13 : checkRingBatch13 batch28_indices = true := by
  dsimp only [batch28_indices, checkRingBatch13, List.all]
  rw [cert_config_106_d_red, cert_config_107_d_red, cert_config_167_d_red, cert_config_170_d_red]
  rfl

end Batch
end Math
