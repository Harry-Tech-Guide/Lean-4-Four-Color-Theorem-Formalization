import FourColorTheorem.Math.Topology.Paths

namespace Hypermap

/-
  TODO: Combinatorial Jordan Curve Theorem.

  The previous placeholder theorem here concluded `True`, so it stated nothing and was
  removed (correctness audit, 2026-10-11).

  The intended target (Gonthier, "Formal Proof — The Four-Color Theorem", §4) is:
    a hypermap satisfying the Euler/genus-0 condition (`GonthierPlanar`, Euler.lean)
    has no "Moebius path", and equivalently every simple cycle separates its
    complement into an inside and an outside.
  Stating this precisely needs the contour/ring machinery, which is not
  in this repository yet.
-/

end Hypermap
