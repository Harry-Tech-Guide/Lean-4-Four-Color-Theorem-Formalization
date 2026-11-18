module

public import FourColorTheorem.Math.TestDischarging
public import FourColorTheorem.Math.U633Parser
public import FourColorTheorem.Math.KernelRfl

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math.Discharging

theorem cert_deg11_verified : test11 theUnavoidableSet.toList () = true := by kernel_rfl

end Math.Discharging
