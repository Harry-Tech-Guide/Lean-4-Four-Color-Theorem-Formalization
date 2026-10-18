import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser

namespace Math.Discharging

theorem cert_deg11_verified : test11 theUnavoidableSet.toList () = true := by
  native_decide

end Math.Discharging
