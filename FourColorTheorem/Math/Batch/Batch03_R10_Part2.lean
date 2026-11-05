import FourColorTheorem.Math.Batch.Runner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

theorem cert_config_45_d_red : checkIdxFast (buildSMData 10 sharedPow3) 45 = true := by kernel_rfl

theorem cert_config_47_d_red : checkIdxFast (buildSMData 10 sharedPow3) 47 = true := by kernel_rfl

theorem cert_config_76_d_red : checkIdxFast (buildSMData 10 sharedPow3) 76 = true := by kernel_rfl

theorem cert_config_110_d_red : checkIdxFast (buildSMData 10 sharedPow3) 110 = true := by kernel_rfl

theorem cert_config_112_d_red : checkIdxFast (buildSMData 10 sharedPow3) 112 = true := by kernel_rfl

theorem cert_config_324_d_red : checkIdxFast (buildSMData 10 sharedPow3) 324 = true := by kernel_rfl

theorem cert_config_325_d_red : checkIdxFast (buildSMData 10 sharedPow3) 325 = true := by kernel_rfl

theorem cert_config_328_d_red : checkIdxFast (buildSMData 10 sharedPow3) 328 = true := by kernel_rfl

theorem cert_config_343_d_red : checkIdxFast (buildSMData 10 sharedPow3) 343 = true := by kernel_rfl

theorem cert_config_566_d_red : checkIdxFast (buildSMData 10 sharedPow3) 566 = true := by kernel_rfl

end Batch
end Math
