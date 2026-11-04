import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

def batch37_indices : List Nat :=
  [593, 594, 604, 606]

theorem cert_config_593_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 593 = true := by kernel_rfl

theorem cert_config_594_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 594 = true := by kernel_rfl

theorem cert_config_604_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 604 = true := by kernel_rfl

theorem cert_config_606_d_red : checkIdxFast13 (buildSMData 13 sharedPow3) 606 = true := by kernel_rfl

theorem cert_batch37_r13 : checkRingBatch13 batch37_indices = true := by
  dsimp only [batch37_indices, checkRingBatch13, List.all]
  rw [cert_config_593_d_red, cert_config_594_d_red, cert_config_604_d_red, cert_config_606_d_red]
  rfl

end Batch
end Math
