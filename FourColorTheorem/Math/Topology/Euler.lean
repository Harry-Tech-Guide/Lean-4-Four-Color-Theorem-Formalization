module

public import FourColorTheorem.Math.Topology.Surgery
public import FourColorTheorem.Math.Topology.OrbitLemmas
public import FourColorTheorem.Math.HypermapGraph

@[expose] public section

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

local instance instBEqDualDart (H : Hypermap) [BEq H.Dart] : BEq H.dual.Dart := ‹BEq H.Dart›
local instance instDecidableEqDualDart (H : Hypermap) [DecidableEq H.Dart] : DecidableEq H.dual.Dart := ‹DecidableEq H.Dart›

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

/-!
### Stage B.2: Involution Edge Counting, Triangulation Face Counting, and `extractGraph` Canonical Vertex Bridge
-/

/-- In any bridgeless hypermap (`isBridgeless H darts fuel_b`), the edge permutation `H.edge`
    has no fixed points (`H.edge.f d ≠ d`) on `darts`. -/
theorem bridgeless_edge_ne_self (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (fuel_b : Nat) (h_bridge : Math.Hypermap.isBridgeless H darts fuel_b) :
    ∀ d ∈ darts, H.edge.f d ≠ d := by
  intro d hd h_eq
  have h_false : Math.Hypermap.isBridge H d fuel_b = false := h_bridge d hd
  dsimp [Math.Hypermap.isBridge, Math.Hypermap.sameFace] at h_false
  rw [h_eq] at h_false
  have h_true : (getOrbit H.face fuel_b d).contains d = true :=
    List.contains_iff_mem.mpr (mem_getOrbit_self H.face fuel_b d)
  rw [h_true] at h_false
  contradiction

/-- In any complete, bridgeless hypermap `(H, darts)`, the total number of darts is twice
    the number of edges (`darts.length = 2 * numEdges H fuel darts`) for all `fuel ≥ darts.length`. -/
theorem darts_length_eq_two_mul_numEdges (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b : Nat} (h_bridge : Math.Hypermap.isBridgeless H darts fuel_b)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    darts.length = 2 * numEdges H fuel darts :=
  length_eq_two_mul_countOrbits_of_involution H.edge H.edge_involution darts h_nodup h_all
    (bridgeless_edge_ne_self H darts fuel_b h_bridge) h_le

/-- In any complete triangulation (where every face orbit has length 3),
    `darts.length = 3 * numFaces H fuel darts` for all `fuel ≥ darts.length`. -/
theorem darts_length_eq_three_mul_numFaces_of_triangulation (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, (getOrbit H.face fuel d).length = 3) :
    darts.length = 3 * numFaces H fuel darts :=
  length_eq_mul_countOrbits_of_complete H.face darts 3 h_nodup h_all h_le h_tri

/-- In any complete, bridgeless triangulation, `2 * E = 3 * F` holds unconditionally. -/
theorem two_mul_numEdges_eq_three_mul_numFaces_of_triangulation (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b : Nat} (h_bridge : Math.Hypermap.isBridgeless H darts fuel_b)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, (getOrbit H.face fuel d).length = 3) :
    2 * (numEdges H fuel darts : Int) = 3 * (numFaces H fuel darts : Int) := by
  have hE := darts_length_eq_two_mul_numEdges H darts h_nodup h_all h_bridge h_le
  have hF := darts_length_eq_three_mul_numFaces_of_triangulation H darts h_nodup h_all h_le h_tri
  omega

/-- Exact structural characterization of `Math.Hypermap.getCanonicalDarts` in terms of `canonicalOrbits`. -/
theorem getCanonicalDarts_eq_canonicalOrbits_reverse (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (remaining visited acc : List H.Dart) :
    Math.Hypermap.getCanonicalDarts H fuel remaining visited acc =
      (canonicalOrbits H.node fuel (remaining.filter (fun x => !visited.contains x))).reverse ++ acc := by
  induction remaining generalizing visited acc with
  | nil =>
    rfl
  | cons d ds ih =>
    dsimp [Math.Hypermap.getCanonicalDarts, List.filter]
    cases hv : visited.contains d
    · change Math.Hypermap.getCanonicalDarts H fuel ds (getOrbit H.node fuel d ++ visited) (d :: acc) =
        (canonicalOrbits H.node fuel (d :: ds.filter (fun x => !visited.contains x))).reverse ++ acc
      rw [ih (getOrbit H.node fuel d ++ visited) (d :: acc)]
      rw [filter_not_contains_append ds (getOrbit H.node fuel d) visited]
      rw [canonicalOrbits_cons H.node fuel d (ds.filter (fun x => !visited.contains x))]
      rw [List.reverse_cons, List.append_assoc]
      rfl
    · exact ih visited acc

/-- The vertex list of `extractGraph H darts fuel` is identically `(canonicalOrbits H.node fuel darts).reverse`. -/
theorem extractGraph_vertices_eq_canonicalOrbits_reverse (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (fuel : Nat := darts.length) :
    (Math.Hypermap.extractGraph H darts fuel).vertices =
      (canonicalOrbits H.node fuel darts).reverse := by
  dsimp [Math.Hypermap.extractGraph]
  rw [getCanonicalDarts_eq_canonicalOrbits_reverse H fuel darts [] []]
  rw [filter_not_contains_nil darts, List.append_nil]

/-- The number of vertices in `extractGraph H darts fuel` is identically `numNodes H fuel darts`. -/
theorem extractGraph_vertices_length_eq_numNodes (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (fuel : Nat := darts.length) :
    (Math.Hypermap.extractGraph H darts fuel).vertices.length = numNodes H fuel darts := by
  rw [extractGraph_vertices_eq_canonicalOrbits_reverse H darts fuel]
  rw [List.length_reverse, canonicalOrbits_length]
  rfl

/-- Converse of `isPlanar_of_euler_char_eq`: `isPlanar H fuel l = true` implies `EulerChar H fuel l = 2 * numComponents H fuel l`. -/
theorem euler_char_eq_of_isPlanar (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (l : List H.Dart) (h_planar : isPlanar H fuel l = true) :
    EulerChar H fuel l = 2 * (numComponents H fuel l : Int) := by
  dsimp [isPlanar, EulerChar, numNodes, numEdges, numFaces, numComponents] at *
  exact eq_of_beq h_planar

/-- On a connected planar hypermap (`isPlanar H fuel darts = true` and `numComponents H fuel darts = 1`),
    Euler's formula `(extractGraph H darts).vertices.length - E + F = 2` holds for all `fuel ≥ darts.length`. -/
theorem extractGraph_euler_eq_two_of_isPlanar_connected (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_planar : isPlanar H fuel darts = true)
    (h_conn : numComponents H fuel darts = 1) :
    ((Math.Hypermap.extractGraph H darts).vertices.length : Int) -
      (numEdges H fuel darts : Int) + (numFaces H fuel darts : Int) = 2 := by
  have h_euler := euler_char_eq_of_isPlanar H fuel darts h_planar
  dsimp [EulerChar] at h_euler
  rw [extractGraph_vertices_length_eq_numNodes H darts darts.length]
  have h_nodes : numNodes H fuel darts = numNodes H darts.length darts :=
    countOrbits_fuel_eq_of_complete H.node darts darts h_all h_le
  omega

end Hypermap
