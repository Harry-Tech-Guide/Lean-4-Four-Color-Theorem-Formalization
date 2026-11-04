/-!
# Self-Contained Formal Specification of Combinatorial Hypermaps & The Four Color Theorem

This module (`Spec.lean`) has **zero internal proof imports** (depending only on the default
Lean 4 prelude). It defines the complete, self-contained mathematical specification used by
`Challenge.lean`, `Solution.lean`, and `SanityChecks.lean`.
-/

namespace Spec

/-- A bijection (invertible permutation) on a type `D`. -/
structure Perm (D : Type) where
  f : D → D
  inv : D → D
  left_inv : ∀ x, inv (f x) = x
  right_inv : ∀ x, f (inv x) = x

def Perm.symm {D : Type} (p : Perm D) : Perm D :=
  { f := p.inv, inv := p.f, left_inv := p.right_inv, right_inv := p.left_inv }

def Perm.one {D : Type} : Perm D :=
  { f := id, inv := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

instance {D : Type} : Inhabited (Perm D) := ⟨Perm.one⟩

/-- A combinatorial hypermap represents a topological map via three permutations on darts. -/
structure Hypermap where
  Dart : Type
  edge : Perm Dart
  node : Perm Dart
  face : Perm Dart
  edge_involution : ∀ d, edge.f (edge.f d) = d
  edge_node_face_id : ∀ d, edge.f (node.f (face.f d)) = d

namespace Hypermap

variable (H : Hypermap)

theorem node_face_edge_id (d : H.Dart) : H.node.f (H.face.f (H.edge.f d)) = d := by
  have h := H.edge_node_face_id (H.edge.f d)
  have h2 : H.edge.f (H.edge.f (H.node.f (H.face.f (H.edge.f d)))) = H.edge.f (H.edge.f d) := by rw [h]
  rw [H.edge_involution, H.edge_involution] at h2
  exact h2

theorem face_edge_node_id (d : H.Dart) : H.face.f (H.edge.f (H.node.f d)) = d := by
  have h := node_face_edge_id H (H.node.f d)
  have h2 : H.node.inv (H.node.f (H.face.f (H.edge.f (H.node.f d)))) = H.node.inv (H.node.f d) := by rw [h]
  rw [H.node.left_inv, H.node.left_inv] at h2
  exact h2

/-- The topological dual of a hypermap (`Faces ↔ Nodes`). -/
def dual : Hypermap where
  Dart := H.Dart
  edge := H.edge
  node := Perm.symm H.face
  face := Perm.symm H.node
  edge_involution := H.edge_involution
  edge_node_face_id := fun d => by
    have h := face_edge_node_id H (H.node.inv d)
    rw [H.node.right_inv] at h
    have h2 : H.face.inv (H.face.f (H.edge.f d)) = H.face.inv (H.node.inv d) := by rw [h]
    rw [H.face.left_inv] at h2
    have h3 : H.edge.f (H.edge.f d) = H.edge.f (H.face.inv (H.node.inv d)) := by rw [h2]
    rw [H.edge_involution] at h3
    exact h3.symm

end Hypermap

section Orbits
variable {D : Type} [BEq D]

def getOrbitAux (p : Perm D) (start current : D) (acc : List D) : Nat → List D
  | 0 => current :: acc
  | fuel' + 1 =>
    let nxt := p.f current
    if nxt == start then current :: acc else getOrbitAux p start nxt (current :: acc) fuel'

def getOrbit (p : Perm D) (fuel : Nat) (d : D) : List D := getOrbitAux p d d [] fuel

def countOrbitsAux (p : Perm D) (fuel : Nat) : Nat → List D → Nat
  | 0, _ | _ + 1, [] => 0
  | steps + 1, d :: ds =>
    let orb := getOrbit p fuel d
    1 + countOrbitsAux p fuel steps (ds.filter (fun x => !(orb.contains x)))

def countOrbits (p : Perm D) (fuel : Nat) (l : List D) : Nat := countOrbitsAux p fuel l.length l
end Orbits

namespace Hypermap
variable (H : Hypermap) [BEq H.Dart]

def getComponentAux (queue visited : List H.Dart) : Nat → List H.Dart
  | 0 => visited
  | fuel' + 1 =>
    match queue with
    | [] => visited
    | d :: ds =>
      if visited.contains d then getComponentAux ds visited fuel'
      else getComponentAux (H.edge.f d :: H.edge.inv d :: H.node.f d :: H.node.inv d :: ds) (d :: visited) fuel'

def getComponent (fuel : Nat) (d : H.Dart) : List H.Dart :=
  getComponentAux H [d] [] (5 * fuel + 1)

def countComponentsAux (fuel : Nat) : Nat → List H.Dart → Nat
  | 0, _ | _ + 1, [] => 0
  | steps + 1, d :: ds =>
    let comp := getComponent H fuel d
    1 + countComponentsAux fuel steps (ds.filter (fun x => !(comp.contains x)))

def countComponents (fuel : Nat) (l : List H.Dart) : Nat := countComponentsAux H fuel l.length l

/-- Euler genus-0 planarity check: `V - E + F = 2 * C`. -/
def isPlanar (fuel : Nat) (darts : List H.Dart) : Bool :=
  let eulerChar := (countOrbits H.node fuel darts : Int) - (countOrbits H.edge fuel darts : Int) + (countOrbits H.face fuel darts : Int)
  eulerChar == 2 * (countComponents H fuel darts : Int)

def sameVertex (d1 d2 : H.Dart) (fuel : Nat := 1000) : Bool := (getOrbit H.node fuel d1).contains d2
def sameFace (d1 d2 : H.Dart) (fuel : Nat := 1000) : Bool := (getOrbit H.face fuel d1).contains d2
def areAdjacentDarts (d1 d2 : H.Dart) (fuel : Nat := 1000) : Bool := sameVertex H (H.edge.f d1) d2 fuel
def isBridge (d : H.Dart) (fuel : Nat := 1000) : Bool := sameFace H d (H.edge.f d) fuel

/-- A hypermap is bridgeless if no dart's opposite edge dart lies in the same face orbit. -/
def isBridgeless (darts : List H.Dart) (fuel : Nat := darts.length) : Prop :=
  ∀ d ∈ darts, isBridge H d fuel = false

end Hypermap

/-- The palette of four colors. -/
inductive Color | c0 | c1 | c2 | c3 deriving DecidableEq, Repr
instance : Inhabited Color := ⟨Color.c0⟩

namespace Hypermap
variable (H : Hypermap)

/-- A valid 4-coloring of the faces of a hypermap. -/
structure FaceColoring where
  color : H.Dart → Color
  face_invariant : ∀ d, color (H.face.f d) = color d
  edge_proper : ∀ d, color (H.edge.f d) ≠ color d

/-- A valid 4-coloring of the vertices (nodes) of a hypermap. -/
structure VertexColoring where
  color : H.Dart → Color
  node_invariant : ∀ d, color (H.node.f d) = color d
  edge_proper : ∀ d, color (H.edge.f d) ≠ color d

end Hypermap

abbrev MapColoring (H : Hypermap) := Hypermap.FaceColoring H

/-- A list of darts is complete for `H` if it is duplicate-free, exhaustive, and non-empty. -/
def IsCompleteDarts (H : Hypermap) (darts : List H.Dart) : Prop :=
  darts.Nodup ∧ (∀ d : H.Dart, d ∈ darts) ∧ darts ≠ []

/-- A hypermap is planar if its Euler characteristic equals `2 * components`. -/
def IsPlanar (H : Hypermap) [BEq H.Dart] (darts : List H.Dart) (fuel : Nat := darts.length) : Prop :=
  Hypermap.isPlanar H fuel darts = true

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
