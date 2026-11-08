import FourColorTheorem.Math.Batch.CRunner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch24_indices : List Nat :=
  [507, 527, 556, 574, 575, 578]

theorem cert_config_507_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 507 = true := by kernel_rfl

theorem cert_config_527_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 527 = true := by kernel_rfl

theorem cert_config_556_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 556 = true := by kernel_rfl

theorem cert_config_574_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 574 = true := by kernel_rfl

theorem cert_config_575_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 575 = true := by kernel_rfl

theorem cert_config_578_c_red : checkIdxCFast (buildSMData 12 sharedPow3) 578 = true := by kernel_rfl

theorem cert_cbatch24_r12 : checkCRingBatch 12 cbatch24_indices = true := by
  dsimp only [cbatch24_indices, checkCRingBatch, List.all]
  rw [cert_config_507_c_red, cert_config_527_c_red, cert_config_556_c_red, cert_config_574_c_red, cert_config_575_c_red, cert_config_578_c_red]
  rfl

end Batch
end Math
