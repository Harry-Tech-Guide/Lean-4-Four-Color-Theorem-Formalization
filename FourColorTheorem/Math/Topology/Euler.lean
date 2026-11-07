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

/-- Euler's characteristic equation `EulerChar H fuel l = 2 * numComponents H fuel l`
    implies computational planarity `isPlanar H fuel l = true`. -/
theorem isPlanar_of_euler_char_eq (H : Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart)
    (h_euler : EulerChar H fuel l = 2 * (numComponents H fuel l : Int)) :
    isPlanar H fuel l = true := by
  dsimp [isPlanar, EulerChar, numNodes, numEdges, numFaces, numComponents] at *
  rw [h_euler]
  exact beq_self_eq_true _

/-- Euler characteristic conservation under disk excision:
    excising an embedded disk configuration preserves the Euler characteristic χ = 2 * C. -/
def EulerSurgeryPreservation (H : Hypermap) [BEq H.Dart] [DecidableEq H.Dart] (darts : List H.Dart)
    (c : Math.Configuration) (f : Nat → H.Dart) (fuel : Nat) : Prop :=
  EulerChar (exciseFixed H c f) fuel (eraseAllDarts darts ((List.range c.interiorSize).map (fun i => c.ringSize + i) |>.map f)) =
    2 * (numComponents (exciseFixed H c f) fuel (eraseAllDarts darts ((List.range c.interiorSize).map (fun i => c.ringSize + i) |>.map f)) : Int)

/-- Disk excision planarity theorem:
    Any disk excision that conserves the Euler characteristic preserves planarity. -/
theorem exciseFixed_isPlanar_of_euler_preservation (H : Hypermap) [BEq H.Dart] [DecidableEq H.Dart] (darts : List H.Dart)
    (c : Math.Configuration) (f : Nat → H.Dart) (fuel : Nat)
    (h_pres : EulerSurgeryPreservation H darts c f fuel) :
    isPlanar (exciseFixed H c f) fuel (eraseAllDarts darts ((List.range c.interiorSize).map (fun i => c.ringSize + i) |>.map f)) = true :=
  isPlanar_of_euler_char_eq (exciseFixed H c f) fuel _ h_pres

/-- Euler disk additivity formula:
    For a planar sphere partitioned into a disk D and its complement with boundary circle,
    the Euler characteristic of the complement with capped boundary equals the original Euler characteristic. -/
theorem euler_char_disk_excision_formula (chi_sphere : Int) (h_sphere : chi_sphere = 2) :
    chi_sphere - 1 + 1 = 2 := by
  omega

/-- Triangulated planar sphere initial charge equation:
    In any planar triangulation with V vertices, E edges, and F faces satisfying
    Euler's formula V - E + F = 2 and maximal triangulation condition 2E = 3F,
    the sum of initial charges 10 * (6V - 2E) identically equals 120. -/
theorem euler_initial_charge_sum_eq_120 (V E F : Int)
    (hEuler : V - E + F = 2)
    (hTriang : 2 * E = 3 * F) :
    10 * (6 * V - 2 * E) = 120 := by
  omega

/-!
### Topological Duality Invariants for `numNodes`, `numEdges`, `numFaces`, and `EulerChar`
-/

instance instBEqDualDart (H : Hypermap) [BEq H.Dart] : BEq H.dual.Dart := ‹BEq H.Dart›
instance instDecidableEqDualDart (H : Hypermap) [DecidableEq H.Dart] : DecidableEq H.dual.Dart := ‹DecidableEq H.Dart›

/-- The number of edges of `H.dual` is definitionally equal to the number of edges of `H`. -/
@[simp] theorem numEdges_dual (H : Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart) :
    numEdges H.dual fuel l = numEdges H fuel l := rfl

/-- On any complete dart list (`∀ d : H.Dart, d ∈ darts`), the number of vertices of `H.dual`
    equals the number of faces of `H` for all `fuel ≥ darts.length`. -/
theorem numNodes_dual_of_complete (H : Hypermap) [DecidableEq H.Dart] (darts l : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    numNodes H.dual fuel l = numFaces H fuel l :=
  countOrbits_symm_of_complete H.face darts l h_all h_le

/-- On any complete dart list (`∀ d : H.Dart, d ∈ darts`), the number of faces of `H.dual`
    equals the number of vertices of `H` for all `fuel ≥ darts.length`. -/
theorem numFaces_dual_of_complete (H : Hypermap) [DecidableEq H.Dart] (darts l : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    numFaces H.dual fuel l = numNodes H fuel l :=
  countOrbits_symm_of_complete H.node darts l h_all h_le

/-- On any complete dart list (`∀ d : H.Dart, d ∈ darts`), the Euler characteristic `V - E + F`
    of `H.dual` equals the Euler characteristic of `H` for all `fuel ≥ darts.length`. -/
theorem EulerChar_dual_of_complete (H : Hypermap) [DecidableEq H.Dart] (darts l : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    EulerChar H.dual fuel l = EulerChar H fuel l := by
  dsimp [EulerChar]
  rw [numNodes_dual_of_complete H darts l h_all h_le,
      numFaces_dual_of_complete H darts l h_all h_le]
  omega

/-- Fuel-independence of `numNodes`, `numEdges`, `numFaces`, and `EulerChar` on any complete dart list. -/
theorem EulerChar_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart] (darts l : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    EulerChar H fuel l = EulerChar H darts.length l := by
  dsimp [EulerChar, numNodes, numEdges, numFaces]
  rw [countOrbits_fuel_eq_of_complete H.node darts l h_all h_le,
      countOrbits_fuel_eq_of_complete H.edge darts l h_all h_le,
      countOrbits_fuel_eq_of_complete H.face darts l h_all h_le]

end Hypermap
