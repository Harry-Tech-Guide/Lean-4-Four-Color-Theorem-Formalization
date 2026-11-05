import FourColorTheorem.Math.Batch.Runner

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

theorem cert_config_104_d_red : checkIdxFast (buildSMData 11 sharedPow3) 104 = true := by kernel_rfl

theorem cert_config_114_d_red : checkIdxFast (buildSMData 11 sharedPow3) 114 = true := by kernel_rfl

theorem cert_config_117_d_red : checkIdxFast (buildSMData 11 sharedPow3) 117 = true := by kernel_rfl

theorem cert_config_119_d_red : checkIdxFast (buildSMData 11 sharedPow3) 119 = true := by kernel_rfl

theorem cert_config_120_d_red : checkIdxFast (buildSMData 11 sharedPow3) 120 = true := by kernel_rfl

theorem cert_config_129_d_red : checkIdxFast (buildSMData 11 sharedPow3) 129 = true := by kernel_rfl

end Batch
end Math
