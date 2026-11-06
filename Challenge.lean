import Spec

/-!
# Palomar / Comparator Challenge Specification: The Four Color Theorem

This file is the top-level challenge for the Lean 4 formalization of the Four Color Theorem
(`Challenge.lean`), following the Lean FRO `Comparator` / Palomar convention: it imports only
`Spec` (which has zero internal proof imports and no custom syntax, macros, or notations) and
states the theorem with `sorry`. The proof belongs in `Solution.lean`.

The statement is **hypothesis-free**: every complete, planar, bridgeless hypermap has a proper
4-coloring of its faces.

## Core Mathematical Specification Summary (`Spec.lean`)
- **`Spec.Hypermap`**:
  A combinatorial hypermap consists of a dart type `Dart : Type` equipped with three
  invertible permutations `edge, node, face : Spec.Perm Dart` satisfying the involution law
  `∀ d, edge.f (edge.f d) = d` and the topological triangular composition identity
  `∀ d, edge.f (node.f (face.f d)) = d`.
- **`Spec.IsCompleteDarts H darts`**:
  A finite list `darts : List H.Dart` enumerates the dart type of `H` when
  `darts.Nodup ∧ (∀ d : H.Dart, d ∈ darts) ∧ darts ≠ []`.
- **`Spec.IsPlanar H darts`**:
  Combinatorial Euler genus-0 planarity (`V - E + F = 2 * C`) over the node, edge,
  and face cycle orbits and connected components of `H` on `darts`.
- **`Spec.Hypermap.isBridgeless H darts`**:
  Every dart `d ∈ darts` has opposite edge dart `H.edge.f d` in a distinct face orbit
  (no isthmus/bridge edges).
- **`Spec.MapColoring H`**:
  A proper 4-coloring (`Spec.Color = {c0, c1, c2, c3}`) of the faces of `H` (constant on each
  `face` orbit and assigning distinct colors across every `edge` pair `d` and `H.edge.f d`).

## Known limitation of the specification
`Spec.Hypermap.isPlanar` and friends count orbits with a **fixed fuel** equal to `darts.length`
(and `sameVertex`/`sameFace` default to fuel `1000`). The fuel-free reformulation is tracked as
part of the roadmap in `README.md`; until then this statement is the one being targeted.
-/

/-- The Four Color Theorem (Challenge Specification). -/
theorem four_color_theorem (H : Spec.Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_complete : Spec.IsCompleteDarts H darts)
    (h_planar : Spec.IsPlanar H darts)
    (h_bridgeless : Spec.Hypermap.isBridgeless H darts) :
    Nonempty (Spec.MapColoring H) := sorry
