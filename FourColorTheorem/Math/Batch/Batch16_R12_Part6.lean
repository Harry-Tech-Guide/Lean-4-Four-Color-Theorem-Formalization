import FourColorTheorem.Math.Batch.Runner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch16_indices : List Nat :=
  [173, 174, 175, 176, 235, 242]

theorem cert_config_173_d_red : checkIdxFast (buildSMData 12 sharedPow3) 173 = true := by kernel_rfl

theorem cert_config_174_d_red : checkIdxFast (buildSMData 12 sharedPow3) 174 = true := by kernel_rfl

theorem cert_config_175_d_red : checkIdxFast (buildSMData 12 sharedPow3) 175 = true := by kernel_rfl

theorem cert_config_176_d_red : checkIdxFast (buildSMData 12 sharedPow3) 176 = true := by kernel_rfl

theorem cert_config_235_d_red : checkIdxFast (buildSMData 12 sharedPow3) 235 = true := by kernel_rfl

theorem cert_config_242_d_red : checkIdxFast (buildSMData 12 sharedPow3) 242 = true := by kernel_rfl

theorem cert_batch16_r12 : checkRingBatch 12 batch16_indices = true := by
  dsimp only [batch16_indices, checkRingBatch, List.all]
  rw [cert_config_173_d_red, cert_config_174_d_red, cert_config_175_d_red, cert_config_176_d_red, cert_config_235_d_red, cert_config_242_d_red]
  rfl

end Batch
end Math
