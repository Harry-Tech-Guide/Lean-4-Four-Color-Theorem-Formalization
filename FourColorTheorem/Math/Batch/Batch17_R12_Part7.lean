import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch17_indices : List Nat :=
  [243, 246, 247, 347, 350, 351]

theorem cert_config_243_d_red : checkIdxFast (buildSMData 12 sharedPow3) 243 = true := by kernel_rfl

theorem cert_config_246_d_red : checkIdxFast (buildSMData 12 sharedPow3) 246 = true := by kernel_rfl

theorem cert_config_247_d_red : checkIdxFast (buildSMData 12 sharedPow3) 247 = true := by kernel_rfl

theorem cert_config_347_d_red : checkIdxFast (buildSMData 12 sharedPow3) 347 = true := by kernel_rfl

theorem cert_config_350_d_red : checkIdxFast (buildSMData 12 sharedPow3) 350 = true := by kernel_rfl

theorem cert_config_351_d_red : checkIdxFast (buildSMData 12 sharedPow3) 351 = true := by kernel_rfl

theorem cert_batch17_r12 : checkRingBatch 12 batch17_indices = true := by
  dsimp only [batch17_indices, checkRingBatch, List.all]
  rw [cert_config_243_d_red, cert_config_246_d_red, cert_config_247_d_red, cert_config_347_d_red, cert_config_350_d_red, cert_config_351_d_red]
  rfl

end Batch
end Math
