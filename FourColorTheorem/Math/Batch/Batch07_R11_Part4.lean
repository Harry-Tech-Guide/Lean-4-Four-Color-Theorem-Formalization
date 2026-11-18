module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

theorem cert_config_133_d_red : checkIdxFast (buildSMData 11 sharedPow3) 133 = true := by kernel_rfl

theorem cert_config_201_d_red : checkIdxFast (buildSMData 11 sharedPow3) 201 = true := by kernel_rfl

theorem cert_config_330_d_red : checkIdxFast (buildSMData 11 sharedPow3) 330 = true := by kernel_rfl

theorem cert_config_332_d_red : checkIdxFast (buildSMData 11 sharedPow3) 332 = true := by kernel_rfl

theorem cert_config_334_d_red : checkIdxFast (buildSMData 11 sharedPow3) 334 = true := by kernel_rfl

theorem cert_config_336_d_red : checkIdxFast (buildSMData 11 sharedPow3) 336 = true := by kernel_rfl

end Batch
end Math
