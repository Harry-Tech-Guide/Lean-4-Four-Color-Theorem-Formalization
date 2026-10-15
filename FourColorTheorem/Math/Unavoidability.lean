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
def containsUnavoidable (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) : Prop :=
  ∃ (c : Configuration), c ∈ theUnavoidableSet ∧ 
  appearsIn c H darts

/-- The fundamental theorem of Discharging.
Every minimal counterexample (an internally 6-connected planar triangulation)
contains at least one configuration from the RSST 633 unavoidable set. -/
theorem discharging_forces_unavoidable (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (mc : MinimalCounterexample H darts) : 
  containsUnavoidable H darts :=
  unavoidability_theorem H darts mc

end Math
