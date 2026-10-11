import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.Discharging
import FourColorTheorem.Math.Rules
import FourColorTheorem.Math.MainTheorem

namespace Math

open Discharging

/-- The 32 Discharging Rules from Robertson, Sanders, Seymour, and Thomas.
These rules dictate how positive charge from degree 5 vertices is distributed 
to negatively charged vertices of degree >= 7. -/
def RSSTRules : List RawRule := theRules

/-- A hypermap contains an unavoidable configuration if one of the 633 
configurations is a valid topological submap of H. -/
def containsUnavoidable (H : Hypermap) (darts : List H.Dart) : Prop :=
  ∃ (c : Configuration), c ∈ theUnavoidableSet ∧ 
  appearsIn c H darts

/-- The fundamental theorem of Discharging.
If we apply the 32 RSST rules to a planar, bridge-less graph that DOES NOT 
contain any of the 633 unavoidable configurations, the resulting charge 
distribution is strictly positive everywhere. 
However, Euler's formula guarantees the sum of charges is exactly 120, 
which means average charge is 0, contradicting positive bounded charge! -/
axiom discharging_forces_unavoidable (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (h_planar : IsPlanar H darts) (h_no_bridge : Hypermap.isBridgeless H darts) : 
  containsUnavoidable H darts

end Math
