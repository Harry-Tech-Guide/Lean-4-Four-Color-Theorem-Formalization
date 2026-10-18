import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser

namespace Math.Discharging

theorem cert_deg7_verified : test7 theUnavoidableSet.toList () = true := by
  native_decide

end Math.Discharging
