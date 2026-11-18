module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

theorem cert_config_15_d_red : checkIdxFast (buildSMData 11 sharedPow3) 15 = true := by kernel_rfl

theorem cert_config_16_d_red : checkIdxFast (buildSMData 11 sharedPow3) 16 = true := by kernel_rfl

theorem cert_config_17_d_red : checkIdxFast (buildSMData 11 sharedPow3) 17 = true := by kernel_rfl

theorem cert_config_20_d_red : checkIdxFast (buildSMData 11 sharedPow3) 20 = true := by kernel_rfl

theorem cert_config_40_d_red : checkIdxFast (buildSMData 11 sharedPow3) 40 = true := by kernel_rfl

theorem cert_config_43_d_red : checkIdxFast (buildSMData 11 sharedPow3) 43 = true := by kernel_rfl

theorem cert_config_49_d_red : checkIdxFast (buildSMData 11 sharedPow3) 49 = true := by kernel_rfl

theorem cert_config_50_d_red : checkIdxFast (buildSMData 11 sharedPow3) 50 = true := by kernel_rfl

theorem cert_config_52_d_red : checkIdxFast (buildSMData 11 sharedPow3) 52 = true := by kernel_rfl

theorem cert_config_56_d_red : checkIdxFast (buildSMData 11 sharedPow3) 56 = true := by kernel_rfl

theorem cert_config_58_d_red : checkIdxFast (buildSMData 11 sharedPow3) 58 = true := by kernel_rfl

end Batch
end Math
