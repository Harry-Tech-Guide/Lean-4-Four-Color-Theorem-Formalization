module

public import FourColorTheorem.Math.Hypermap
public import FourColorTheorem.Math.Discharging
public import FourColorTheorem.Math.Rules
public import FourColorTheorem.Math.MainTheorem
public import FourColorTheorem.Math.Unavoidability.HintBounds
public import FourColorTheorem.Math.Unavoidability.AllDegreesDischarge
public import FourColorTheorem.Math.Unavoidability.FastConfEquiv
public import FourColorTheorem.Math.Unavoidability.ConfGeomCert
public import FourColorTheorem.Math.Unavoidability.CheckIsoSoundness
public import FourColorTheorem.Math.Unavoidability.FreeCompletionProjection

@[expose] public section

namespace Math

open Discharging

/-- The 32 Discharging Rules from Robertson, Sanders, Seymour, and Thomas.
These rules dictate how positive charge from degree 5 vertices is distributed 
to negatively charged vertices of degree >= 7. -/
def RSSTRules : List RawRule := theRules

/-- A hypermap contains an unavoidable configuration in its dual triangulation if one of
    the 633 configurations in `theUnavoidableSet` admits a faithful RSST `(3.3)–(3.4)`
    `CorrespondingProjection` on `H.dual`. -/
def containsUnavoidableDual (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) : Prop :=
  ∃ (c : Configuration), c ∈ theUnavoidableSet ∧
    Nonempty (Unavoidability.CorrespondingProjection c H.dual darts)

/-- The fundamental theorem of Discharging (Phase 5, 100% unconditional):
    Every minimal counterexample admits an unavoidable configuration `c ∈ theUnavoidableSet` via
    a faithful `CorrespondingProjection c H.dual darts` on its dual triangulation `H.dual`. -/
theorem discharging_forces_unavoidable (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    containsUnavoidableDual H darts :=
  rsst_unavoidability_dual_projection H darts mc

end Math
