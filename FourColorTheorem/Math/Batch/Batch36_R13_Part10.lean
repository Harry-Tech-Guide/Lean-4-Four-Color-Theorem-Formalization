import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

def batch36_indices : List Nat :=
  [536, 564, 565, 589]

theorem cert_config_536_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 536 = true := by kernel_rfl

theorem cert_config_564_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 564 = true := by kernel_rfl

theorem cert_config_565_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 565 = true := by kernel_rfl

theorem cert_config_589_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 589 = true := by kernel_rfl

theorem cert_batch36_r13 : checkRingBatch13 batch36_indices = true := by
  dsimp only [batch36_indices, checkRingBatch13, List.all]
  rw [cert_config_536_d_red, cert_config_564_d_red, cert_config_565_d_red, cert_config_589_d_red]
  rfl

end Batch
end Math
