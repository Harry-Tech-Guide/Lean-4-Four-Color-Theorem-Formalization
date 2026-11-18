module

public import FourColorTheorem.Math.Batch.CRunner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def cbatch03_indices : List Nat :=
  [10, 28, 31, 33, 34]

theorem cert_config_10_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 10 = true := by kernel_rfl

theorem cert_config_28_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 28 = true := by kernel_rfl

theorem cert_config_31_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 31 = true := by kernel_rfl

theorem cert_config_33_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 33 = true := by kernel_rfl

theorem cert_config_34_c_red : checkIdxCFast (buildSMData 10 sharedPow3) 34 = true := by kernel_rfl

theorem cert_cbatch03_r10 : checkCRingBatch 10 cbatch03_indices = true := by
  dsimp only [cbatch03_indices, checkCRingBatch, List.all]
  rw [cert_config_10_c_red, cert_config_28_c_red, cert_config_31_c_red, cert_config_33_c_red, cert_config_34_c_red]
  rfl

end Batch
end Math
