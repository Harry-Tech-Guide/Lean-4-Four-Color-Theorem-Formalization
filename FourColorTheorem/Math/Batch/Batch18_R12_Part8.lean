import FourColorTheorem.Math.Batch.Runner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch18_indices : List Nat :=
  [359, 360, 363, 366, 369, 374]

theorem cert_config_359_d_red : checkIdxFast (buildSMData 12 sharedPow3) 359 = true := by kernel_rfl

theorem cert_config_360_d_red : checkIdxFast (buildSMData 12 sharedPow3) 360 = true := by kernel_rfl

theorem cert_config_363_d_red : checkIdxFast (buildSMData 12 sharedPow3) 363 = true := by kernel_rfl

theorem cert_config_366_d_red : checkIdxFast (buildSMData 12 sharedPow3) 366 = true := by kernel_rfl

theorem cert_config_369_d_red : checkIdxFast (buildSMData 12 sharedPow3) 369 = true := by kernel_rfl

theorem cert_config_374_d_red : checkIdxFast (buildSMData 12 sharedPow3) 374 = true := by kernel_rfl

theorem cert_batch18_r12 : checkRingBatch 12 batch18_indices = true := by
  dsimp only [batch18_indices, checkRingBatch, List.all]
  rw [cert_config_359_d_red, cert_config_360_d_red, cert_config_363_d_red, cert_config_366_d_red, cert_config_369_d_red, cert_config_374_d_red]
  rfl

end Batch
end Math
