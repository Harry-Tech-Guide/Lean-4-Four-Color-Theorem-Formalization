import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser

namespace Math.Discharging

theorem cert_deg10_verified : test10 theUnavoidableSet.toList () = true := by
  native_decide

end Math.Discharging
