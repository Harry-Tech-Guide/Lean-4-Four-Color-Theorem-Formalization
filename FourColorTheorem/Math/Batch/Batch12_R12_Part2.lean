import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

def batch12_indices : List Nat :=
  [75, 78, 80, 83, 84, 85]

theorem cert_config_75_d_red : checkIdxFast (buildSMData 12 sharedPow3) 75 = true := by kernel_rfl

theorem cert_config_78_d_red : checkIdxFast (buildSMData 12 sharedPow3) 78 = true := by kernel_rfl

theorem cert_config_80_d_red : checkIdxFast (buildSMData 12 sharedPow3) 80 = true := by kernel_rfl

theorem cert_config_83_d_red : checkIdxFast (buildSMData 12 sharedPow3) 83 = true := by kernel_rfl

theorem cert_config_84_d_red : checkIdxFast (buildSMData 12 sharedPow3) 84 = true := by kernel_rfl

theorem cert_config_85_d_red : checkIdxFast (buildSMData 12 sharedPow3) 85 = true := by kernel_rfl

theorem cert_batch12_r12 : checkRingBatch 12 batch12_indices = true := by
  dsimp only [batch12_indices, checkRingBatch, List.all]
  rw [cert_config_75_d_red, cert_config_78_d_red, cert_config_80_d_red, cert_config_83_d_red, cert_config_84_d_red, cert_config_85_d_red]
  rfl

end Batch
end Math
