import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser

namespace Math.Discharging

theorem cert_deg8_verified : test8 theUnavoidableSet.toList () = true := by
  native_decide

end Math.Discharging
