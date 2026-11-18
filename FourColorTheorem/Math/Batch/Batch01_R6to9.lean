module

public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

namespace Math
namespace Batch

open FastReducer

theorem cert_config_0_d_red : checkIdxFast (buildSMData 6 sharedPow3) 0 = true := by kernel_rfl

theorem cert_config_1_d_red : checkIdxFast (buildSMData 7 sharedPow3) 1 = true := by kernel_rfl

theorem cert_config_2_d_red : checkIdxFast (buildSMData 8 sharedPow3) 2 = true := by kernel_rfl

theorem cert_config_4_d_red : checkIdxFast (buildSMData 8 sharedPow3) 4 = true := by kernel_rfl

theorem cert_config_7_d_red : checkIdxFast (buildSMData 8 sharedPow3) 7 = true := by kernel_rfl

theorem cert_config_23_d_red : checkIdxFast (buildSMData 8 sharedPow3) 23 = true := by kernel_rfl

theorem cert_config_5_d_red : checkIdxFast (buildSMData 9 sharedPow3) 5 = true := by kernel_rfl

theorem cert_config_6_d_red : checkIdxFast (buildSMData 9 sharedPow3) 6 = true := by kernel_rfl

theorem cert_config_11_d_red : checkIdxFast (buildSMData 9 sharedPow3) 11 = true := by kernel_rfl

theorem cert_config_24_d_red : checkIdxFast (buildSMData 9 sharedPow3) 24 = true := by kernel_rfl

theorem cert_config_26_d_red : checkIdxFast (buildSMData 9 sharedPow3) 26 = true := by kernel_rfl

theorem cert_config_37_d_red : checkIdxFast (buildSMData 9 sharedPow3) 37 = true := by kernel_rfl

theorem cert_config_323_d_red : checkIdxFast (buildSMData 9 sharedPow3) 323 = true := by kernel_rfl

end Batch
end Math
