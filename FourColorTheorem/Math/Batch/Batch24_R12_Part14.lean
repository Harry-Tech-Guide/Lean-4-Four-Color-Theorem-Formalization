import FourColorTheorem.Math.Batch.Runner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch24_indices : List Nat :=
  [559, 560, 572, 573, 576, 577]

theorem cert_config_559_d_red : checkIdxFast (buildSMData 12 sharedPow3) 559 = true := by kernel_rfl

theorem cert_config_560_d_red : checkIdxFast (buildSMData 12 sharedPow3) 560 = true := by kernel_rfl

theorem cert_config_572_d_red : checkIdxFast (buildSMData 12 sharedPow3) 572 = true := by kernel_rfl

theorem cert_config_573_d_red : checkIdxFast (buildSMData 12 sharedPow3) 573 = true := by kernel_rfl

theorem cert_config_576_d_red : checkIdxFast (buildSMData 12 sharedPow3) 576 = true := by kernel_rfl

theorem cert_config_577_d_red : checkIdxFast (buildSMData 12 sharedPow3) 577 = true := by kernel_rfl

theorem cert_batch24_r12 : checkRingBatch 12 batch24_indices = true := by
  dsimp only [batch24_indices, checkRingBatch, List.all]
  rw [cert_config_559_d_red, cert_config_560_d_red, cert_config_572_d_red, cert_config_573_d_red, cert_config_576_d_red, cert_config_577_d_red]
  rfl

end Batch
end Math
