import Spec
import ConditionalSolution

/-!
# Palomar / Comparator Solution Module: The Four Color Theorem

**STATUS: OPEN.** `four_color_theorem` below has the *identical* name, universe levels, and type
as `Challenge.four_color_theorem` (hypothesis-free) but is **not yet proved**; it is stated with
`sorry` on purpose so that this repository never claims more than it has.

What exists today is the *conditional* theorem `four_color_theorem_conditional`
(`ConditionalSolution.lean`, sorry-free, standard axioms only), which assumes
`Spec.RSSTStandardizationBridge`. That bridge is equivalent to "no minimal counterexample exists"
(`SanityChecks.bridge_iff_no_mc`), so it must be *eliminated*, not assumed. See the roadmap in
`README.md`.
-/

/-- The Four Color Theorem (Solution; **still `sorry`** until the roadmap in `README.md` is done). -/
theorem four_color_theorem (H : Spec.Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_complete : Spec.IsCompleteDarts H darts)
    (h_planar : Spec.IsPlanar H darts)
    (h_bridgeless : Spec.Hypermap.isBridgeless H darts) :
    Nonempty (Spec.MapColoring H) := sorry
