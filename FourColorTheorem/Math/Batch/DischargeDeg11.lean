import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.KernelRfl

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math.Discharging

theorem cert_deg11_verified : test11 theUnavoidableSet.toList () = true := by kernel_rfl

end Math.Discharging
