module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

theorem cert_config_60_d_red : checkIdxFast (buildSMData 11 sharedPow3) 60 = true := by kernel_rfl

theorem cert_config_69_d_red : checkIdxFast (buildSMData 11 sharedPow3) 69 = true := by kernel_rfl

theorem cert_config_70_d_red : checkIdxFast (buildSMData 11 sharedPow3) 70 = true := by kernel_rfl

theorem cert_config_71_d_red : checkIdxFast (buildSMData 11 sharedPow3) 71 = true := by kernel_rfl

theorem cert_config_77_d_red : checkIdxFast (buildSMData 11 sharedPow3) 77 = true := by kernel_rfl

theorem cert_config_81_d_red : checkIdxFast (buildSMData 11 sharedPow3) 81 = true := by kernel_rfl

end Batch
end Math
