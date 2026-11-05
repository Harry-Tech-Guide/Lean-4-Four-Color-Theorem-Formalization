import FourColorTheorem.Math.Batch.Runner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

theorem cert_config_337_d_red : checkIdxFast (buildSMData 11 sharedPow3) 337 = true := by kernel_rfl

theorem cert_config_348_d_red : checkIdxFast (buildSMData 11 sharedPow3) 348 = true := by kernel_rfl

theorem cert_config_349_d_red : checkIdxFast (buildSMData 11 sharedPow3) 349 = true := by kernel_rfl

theorem cert_config_354_d_red : checkIdxFast (buildSMData 11 sharedPow3) 354 = true := by kernel_rfl

theorem cert_config_362_d_red : checkIdxFast (buildSMData 11 sharedPow3) 362 = true := by kernel_rfl

end Batch
end Math
