
import FourColorTheorem.Math.Reflection
import FourColorTheorem.Math.ReducibilityProof

namespace FourColorTheorem

/-- The final architecture link for D-Reducibility:
    If check outputs dReducible = true, it means live was completely emptied. -/
theorem dreduction_is_sound (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  (Math.FastReducer.check c md pow3).dReducible = true → 
  Hypermap.IsReducible H k R := by
  sorry

end FourColorTheorem
