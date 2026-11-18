module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

theorem cert_config_568_d_red : checkIdxFast (buildSMData 11 sharedPow3) 568 = true := by kernel_rfl

theorem cert_config_570_d_red : checkIdxFast (buildSMData 11 sharedPow3) 570 = true := by kernel_rfl

theorem cert_config_571_d_red : checkIdxFast (buildSMData 11 sharedPow3) 571 = true := by kernel_rfl

theorem cert_config_582_d_red : checkIdxFast (buildSMData 11 sharedPow3) 582 = true := by kernel_rfl

theorem cert_config_621_d_red : checkIdxFast (buildSMData 11 sharedPow3) 621 = true := by kernel_rfl

end Batch
end Math
