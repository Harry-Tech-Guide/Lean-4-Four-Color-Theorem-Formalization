module

public import Spec
import FourColorTheorem.Math.MainTheorem
import FourColorTheorem.Math.SpecBridge

@[expose] public section

/-!
# Palomar / Comparator Solution Module: The Four Color Theorem

`four_color_theorem` below has the *identical* name, universe levels, and type as
`Challenge.four_color_theorem` (hypothesis-free) and is proved unconditionally via
`SpecBridge.four_color_theorem_spec` (backed by `Math.four_color_theorem`), completely and
unconditionally, using only the standard Lean axioms `[propext, Classical.choice, Quot.sound]`.
-/

/-- **The Four Color Theorem** (unconditional Solution matching `Challenge.four_color_theorem`). -/
theorem four_color_theorem (H : Spec.Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_complete : Spec.IsCompleteDarts H darts)
    (h_planar : Spec.IsPlanar H darts)
    (h_bridgeless : Spec.Hypermap.isBridgeless H darts) :
    Nonempty (Spec.MapColoring H) :=
  SpecBridge.four_color_theorem_spec H darts h_complete h_planar h_bridgeless

/--
info: 'four_color_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms four_color_theorem
