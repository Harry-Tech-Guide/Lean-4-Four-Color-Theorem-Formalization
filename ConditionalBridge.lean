import Spec

/-!
# Conditional Bridge (NOT part of the Four Color Theorem statement)

This module holds the *conditional* reduction Spec.RSSTStandardizationBridge, kept only so the
existing sorry-free conditional proof (ConditionalSolution.lean) still type-checks.

**Warning:** Spec.ValidRSSTCertificateSuite is satisfiable by trivial data, so
Spec.RSSTStandardizationBridge is equivalent to `no minimal counterexample exists''. It is
therefore *not* an independent hypothesis; see SanityChecks.bridge_iff_no_mc.
-/

namespace Spec

/-- All strictly smaller complete planar bridgeless hypermaps admit a 4-coloring. -/
def AllSmallerColorable (n : Nat) : Prop :=
  ∀ (H' : Hypermap) [DecidableEq H'.Dart] (darts' : List H'.Dart),
    IsCompleteDarts H' darts' → darts'.length < n → IsPlanar H' darts' →
    Hypermap.isBridgeless H' darts' → Nonempty (MapColoring H')

/-- A minimal planar counterexample to the Four Color Theorem. -/
structure MinimalCounterexample (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) : Prop where
  complete : IsCompleteDarts H darts
  is_planar : IsPlanar H darts
  is_bridgeless : Hypermap.isBridgeless H darts
  not_colorable : MapColoring H → False
  all_smaller_colorable : AllSmallerColorable darts.length

/-- Specification of a verified RSST certificate suite:
    1. Exactly 633 unavoidable configurations (`numConfigs = 633`).
    2. Every configuration `idx < 633` has interior size at least 4 (`interiorSize idx ≥ 4`).
    3. Every configuration `idx < 633` is certified D-reducible or C-reducible (`certD idx = true ∨ certC idx = true`).
    4. The cartwheel discharging trees (degrees 7 through 11) pass verification (`treesVerified`).
    5. A skew-symmetric discharging rule (`shift H u v = - (shift H v u)`) is provided. -/
def ValidRSSTCertificateSuite
    (numConfigs : Nat) (interiorSize : Nat → Nat) (certD certC : Nat → Bool)
    (treesVerified : Prop) (shift : (H : Hypermap) → [DecidableEq H.Dart] → H.Dart → H.Dart → Int) : Prop :=
  numConfigs = 633 ∧
  (∀ idx < 633, interiorSize idx ≥ 4) ∧
  (∀ idx < 633, certD idx = true ∨ certC idx = true) ∧
  treesVerified ∧
  (∀ (H : Hypermap) [DecidableEq H.Dart] (u v : H.Dart), shift H u v = - (shift H v u))

/-- Explicit topological and certificate soundness bridge connecting minimal planar
    counterexamples to a verified 633-configuration RSST certificate suite. -/
def RSSTStandardizationBridge : Prop :=
  ∀ (numConfigs : Nat) (interiorSize : Nat → Nat) (certD certC : Nat → Bool) (treesVerified : Prop)
    (shift : (H : Hypermap) → [DecidableEq H.Dart] → H.Dart → H.Dart → Int),
    ValidRSSTCertificateSuite numConfigs interiorSize certD certC treesVerified shift →
    ∀ (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart),
      MinimalCounterexample H darts → False


end Spec
