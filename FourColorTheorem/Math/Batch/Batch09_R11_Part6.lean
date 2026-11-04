import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

theorem cert_config_401_d_red : checkIdxFast (buildSMData 11 sharedPow3) 401 = true := by kernel_rfl

theorem cert_config_404_d_red : checkIdxFast (buildSMData 11 sharedPow3) 404 = true := by kernel_rfl

theorem cert_config_423_d_red : checkIdxFast (buildSMData 11 sharedPow3) 423 = true := by kernel_rfl

theorem cert_config_424_d_red : checkIdxFast (buildSMData 11 sharedPow3) 424 = true := by kernel_rfl

theorem cert_config_567_d_red : checkIdxFast (buildSMData 11 sharedPow3) 567 = true := by kernel_rfl

end Batch
end Math
