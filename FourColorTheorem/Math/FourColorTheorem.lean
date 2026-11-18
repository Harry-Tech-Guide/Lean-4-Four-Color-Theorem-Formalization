module

public import FourColorTheorem.Math.Topology

public import FourColorTheorem.Math.Hypermap
public import FourColorTheorem.Math.Planarity
public import FourColorTheorem.Math.Coloring
public import FourColorTheorem.Math.Configuration
public import FourColorTheorem.Math.Reflection
public import FourColorTheorem.Math.DReductionProof

@[expose] public section

namespace FourColorTheorem

/-- Reducibility Verification Theorem:
    Under the semantic bridge assumption `MatchesTopology H k R c`,
    if the verified computational solver certifies either D-reducibility or C-reducibility,
    then the topological ring `R` in hypermap `H` is mathematically reducible `Hypermap.IsReducible H k R`. -/
theorem reducibility_verified (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (live : ByteArray) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  (Math.FastReducer.check c md pow3).dReducible = true ∨ Math.FastReducer.runCReduction c pow3 live = true → 
  Hypermap.IsReducible H k R := by
  intro hMatch hResult
  cases hResult with
  | inl hD => exact dreduction_is_sound c md pow3 H k R hMatch hD
  | inr hC => exact creduction_is_sound c pow3 live H k R hMatch hC

end FourColorTheorem
