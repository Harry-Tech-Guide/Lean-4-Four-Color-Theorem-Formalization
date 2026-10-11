import FourColorTheorem.Math.Topology.Surgery
import FourColorTheorem.Math.Topology.OrbitLemmas

namespace Hypermap

/-- Number of vertices / edges / faces / components, counted on an explicit dart list
    with a fuel bound (see `Planarity.lean`). -/
def numNodes (H : Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart) : Nat :=
  countOrbits H.node fuel l
def numEdges (H : Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart) : Nat :=
  countOrbits H.edge fuel l
def numFaces (H : Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart) : Nat :=
  countOrbits H.face fuel l
def numComponents (H : Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart) : Nat :=
  countComponents H fuel l

/-- The graph-style Euler characteristic `V - E + F`. -/
def EulerChar (H : Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart) : Int :=
  (numNodes H fuel l : Int) - (numEdges H fuel l : Int) + (numFaces H fuel l : Int)

/-- Gonthier's hypermap Euler formula: `V + E + F = #darts + 2C`.
    This is how planarity is *defined* for hypermaps in the Coq proof: it is a property
    some hypermaps have (genus 0) and others (e.g. torus maps) do not. -/
def GonthierPlanar (H : Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart) : Prop :=
  numNodes H fuel l + numEdges H fuel l + numFaces H fuel l = l.length + 2 * numComponents H fuel l

/-
  NOTE (correctness audit, 2026-10-11).
  The previous statement `euler_characteristic_eq : EulerChar H fuel l = 2 * Components H fuel l`
  for *every* hypermap was FALSE (any toroidal map is a counterexample, and it also fails
  for arbitrary `l`/`fuel`). In Gonthier's development, Euler's formula is the
  *definition* of planarity, not a theorem; the real topological work is proving
  that this definition implies the Jordan property and is preserved by the surgery
  operations used in the reducibility argument. Those theorems are still TODO.
-/

end Hypermap
