import FourColorTheorem.Math.Topology

import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.Planarity
import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Configuration
import FourColorTheorem.Math.Reflection
import FourColorTheorem.Math.DReductionProof

namespace FourColorTheorem

/-- The Four Color Theorem (Reducibility Part):
    If a configuration mathematically exists inside the hypermap H, 
    and the native verified solver (which executes exactly the C-reduction and 
    D-reduction algorithms) computes 	rue for its reducibility, 
    then the configuration is strictly mathematically reducible.
    
    This theorem entirely links the topology of planar hypermaps, the graph coloring 
    axioms, the Kempe chain invariants, and the base-3 hash algebra directly 
    to the verified computational loop FastReducer.lean which evaluates the 633 
    RSST configurations. -/
theorem reducibility_verified (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (live : ByteArray) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (LiveSet : (Fin k → Color) → Prop) :
  MatchesTopology H k R c → 
  (Math.FastReducer.check c md pow3).dReducible = true ∨ Math.FastReducer.runCReduction c pow3 live = true → 
  Hypermap.IsReducible H k R := by
  intro hMatch hResult
  cases hResult with
  | inl hD => exact dreduction_is_sound c md pow3 H k R LiveSet hMatch hD
  | inr hC => exact creduction_is_sound c pow3 live H k R hMatch hC

end FourColorTheorem
