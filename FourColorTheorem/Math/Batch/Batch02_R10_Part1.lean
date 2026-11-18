module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

theorem cert_config_8_d_red : checkIdxFast (buildSMData 10 sharedPow3) 8 = true := by kernel_rfl

theorem cert_config_9_d_red : checkIdxFast (buildSMData 10 sharedPow3) 9 = true := by kernel_rfl

theorem cert_config_12_d_red : checkIdxFast (buildSMData 10 sharedPow3) 12 = true := by kernel_rfl

theorem cert_config_13_d_red : checkIdxFast (buildSMData 10 sharedPow3) 13 = true := by kernel_rfl

theorem cert_config_18_d_red : checkIdxFast (buildSMData 10 sharedPow3) 18 = true := by kernel_rfl

theorem cert_config_27_d_red : checkIdxFast (buildSMData 10 sharedPow3) 27 = true := by kernel_rfl

theorem cert_config_29_d_red : checkIdxFast (buildSMData 10 sharedPow3) 29 = true := by kernel_rfl

theorem cert_config_30_d_red : checkIdxFast (buildSMData 10 sharedPow3) 30 = true := by kernel_rfl

theorem cert_config_32_d_red : checkIdxFast (buildSMData 10 sharedPow3) 32 = true := by kernel_rfl

theorem cert_config_36_d_red : checkIdxFast (buildSMData 10 sharedPow3) 36 = true := by kernel_rfl

theorem cert_config_44_d_red : checkIdxFast (buildSMData 10 sharedPow3) 44 = true := by kernel_rfl

end Batch
end Math
