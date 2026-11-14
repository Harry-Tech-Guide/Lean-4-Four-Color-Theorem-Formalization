import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.Discharging
import FourColorTheorem.Math.Rules
import FourColorTheorem.Math.MainTheorem
import FourColorTheorem.Math.Unavoidability.HintBounds
import FourColorTheorem.Math.Unavoidability.AllDegreesDischarge
import FourColorTheorem.Math.Unavoidability.FastConfEquiv
import FourColorTheorem.Math.Unavoidability.ConfGeomCert
import FourColorTheorem.Math.Unavoidability.CheckIsoSoundness
import FourColorTheorem.Math.Unavoidability.FreeCompletionProjection

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

/-- The fundamental theorem of Discharging (Phase 5, unconditional):
    Every minimal counterexample whose dual cartwheel embedding `(h_rsst H darts mc).1` holds
    admits an unavoidable configuration `c ∈ theUnavoidableSet` via
    a faithful `CorrespondingProjection c H.dual darts` on its dual triangulation `H.dual`. -/
theorem discharging_forces_unavoidable (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_rsst : RSSTStandardizationBridge) (mc : MinimalCounterexample H darts) :
    containsUnavoidableDual H darts :=
  rsst_unavoidability_dual_projection H darts h_rsst mc

end Math
