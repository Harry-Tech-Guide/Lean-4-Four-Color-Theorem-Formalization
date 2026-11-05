import Challenge

/-!
# Semantic Non-Vacuity & Sharpness Sanity Checks (`SanityChecks.lean`)

This standalone verification module proves four semantic sanity checks confirming
that the hypermap, planarity, and coloring definitions in `Challenge.lean` / `Solution.lean`
are neither vacuously false on the left of the implication nor trivially true on the right:

1. **Non-Vacuity of Planarity (Existence):**
   Explicit construction of the tetrahedral planar triangulation `K4_hypermap` ($K_4$ on 12 darts,
   4 vertices, 6 edges, 4 triangular faces) and constructive proof that it satisfies
   `Math.IsCompleteDarts`, `Math.IsPlanar`, `Math.Hypermap.isBridgeless`, and `Nonempty (Math.MapColoring K4_hypermap)`.
2. **Non-Triviality of Planarity (Exclusion):**
   Explicit construction of the complete graph $K_5$ as a 20-dart hypermap `K5_hypermap` (5 vertices,
   10 edges connecting all vertex pairs) and proof that `¬ Math.IsPlanar K5_hypermap K5_darts`,
   together with Euler's triangulation edge bound $E \le 3V - 6$.
3. **Sharpness of Coloring (3-Color Counterexample):**
   Parameterized $k$-coloring definitions `VertexColoringK` and `FaceColoringK` (proven equivalent
   to `Hypermap.VertexColoring` and `Math.MapColoring` at $k = 4$), and proof that the planar
   tetrahedron `K4_hypermap` is NOT 3-colorable (`¬ Nonempty (VertexColoringK K4_hypermap 3)` and
   `¬ Nonempty (FaceColoringK K4_hypermap 3)`).
4. **Sharpness of Coloring (4-Color Non-Planar Counterexample):**
   Proof that the non-planar hypermap `K5_hypermap` is NOT 4-colorable
   (`¬ Nonempty (Hypermap.VertexColoring K5_hypermap)` and
   `¬ Nonempty (Math.MapColoring K5_hypermap.dual)`).
-/

namespace SanityChecks

open Spec

/-!
## Parameterized $k$-Coloring Specification & Equivalence at $k = 4$
-/

/-- A proper $k$-coloring of the vertices (node orbits) of a hypermap `H`. -/
structure VertexColoringK (H : Spec.Hypermap) (k : Nat) where
  color : H.Dart → Fin k
  node_invariant : ∀ d, color (H.node.f d) = color d
  edge_proper : ∀ d, color (H.edge.f d) ≠ color d

/-- A proper $k$-coloring of the faces (face orbits) of a hypermap `H`. -/
structure FaceColoringK (H : Spec.Hypermap) (k : Nat) where
  color : H.Dart → Fin k
  face_invariant : ∀ d, color (H.face.f d) = color d
  edge_proper : ∀ d, color (H.edge.f d) ≠ color d

def colorToFin4 : Spec.Color → Fin 4
  | Spec.Color.c0 => ⟨0, by decide⟩
  | Spec.Color.c1 => ⟨1, by decide⟩
  | Spec.Color.c2 => ⟨2, by decide⟩
  | Spec.Color.c3 => ⟨3, by decide⟩

def fin4ToColor (x : Fin 4) : Spec.Color :=
  match x.val with
  | 0 => Spec.Color.c0
  | 1 => Spec.Color.c1
  | 2 => Spec.Color.c2
  | _ => Spec.Color.c3

theorem colorToFin4_inj (a b : Spec.Color) (h : colorToFin4 a = colorToFin4 b) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

theorem fin4ToColor_inj (a b : Fin 4) (h : fin4ToColor a = fin4ToColor b) : a = b := by
  rcases a with ⟨av, ha⟩
  rcases b with ⟨bv, hb⟩
  revert h
  match av, bv with
  | 0, 0 => intro _; rfl
  | 1, 1 => intro _; rfl
  | 2, 2 => intro _; rfl
  | 3, 3 => intro _; rfl
  | 0, 1 | 0, 2 | 0, 3 | 1, 0 | 1, 2 | 1, 3 | 2, 0 | 2, 1 | 2, 3 | 3, 0 | 3, 1 | 3, 2 =>
    intro h; cases h
  | n + 4, _ => omega
  | _, n + 4 => omega

/-- Equivalence between `Spec.Hypermap.VertexColoring H` and `VertexColoringK H 4`. -/
theorem vertexColoring_iff_k4 (H : Spec.Hypermap) :
    Nonempty (Spec.Hypermap.VertexColoring H) ↔ Nonempty (VertexColoringK H 4) := by
  constructor
  · rintro ⟨vc⟩
    refine ⟨{
      color := fun d => colorToFin4 (vc.color d)
      node_invariant := fun d => by rw [vc.node_invariant d]
      edge_proper := fun d h => vc.edge_proper d (colorToFin4_inj _ _ h)
    }⟩
  · rintro ⟨vck⟩
    refine ⟨{
      color := fun d => fin4ToColor (vck.color d)
      node_invariant := fun d => by rw [vck.node_invariant d]
      edge_proper := fun d h => vck.edge_proper d (fin4ToColor_inj _ _ h)
    }⟩

/-- Equivalence between `Spec.MapColoring H` (`Spec.Hypermap.FaceColoring H`) and `FaceColoringK H 4`. -/
theorem mapColoring_iff_k4 (H : Spec.Hypermap) :
    Nonempty (Spec.MapColoring H) ↔ Nonempty (FaceColoringK H 4) := by
  constructor
  · rintro ⟨fc⟩
    refine ⟨{
      color := fun d => colorToFin4 (fc.color d)
      face_invariant := fun d => by rw [fc.face_invariant d]
      edge_proper := fun d h => fc.edge_proper d (colorToFin4_inj _ _ h)
    }⟩
  · rintro ⟨fck⟩
    refine ⟨{
      color := fun d => fin4ToColor (fck.color d)
      face_invariant := fun d => by rw [fck.face_invariant d]
      edge_proper := fun d h => fck.edge_proper d (fin4ToColor_inj _ _ h)
    }⟩

/-!
## Pure Arithmetic Pigeonhole Helpers
-/

theorem pigeonhole_4_in_3 (c0 c1 c2 c3 : Nat)
    (_h0 : c0 < 3) (_h1 : c1 < 3) (_h2 : c2 < 3) (_h3 : c3 < 3)
    (_n01 : c1 ≠ c0) (_n02 : c2 ≠ c0) (_n03 : c3 ≠ c0)
    (_n12 : c2 ≠ c1) (_n13 : c3 ≠ c1) (_n23 : c3 ≠ c2) : False := by
  omega

theorem pigeonhole_5_in_4 (c0 c1 c2 c3 c4 : Nat)
    (_h0 : c0 < 4) (_h1 : c1 < 4) (_h2 : c2 < 4) (_h3 : c3 < 4) (_h4 : c4 < 4)
    (_n01 : c1 ≠ c0) (_n02 : c2 ≠ c0) (_n03 : c3 ≠ c0) (_n04 : c4 ≠ c0)
    (_n12 : c2 ≠ c1) (_n13 : c3 ≠ c1) (_n14 : c4 ≠ c1)
    (_n23 : c3 ≠ c2) (_n24 : c4 ≠ c2) (_n34 : c4 ≠ c3) : False := by
  omega

/-!
## 1. Non-Vacuity of Planarity (Existence): Explicit Tetrahedral Hypermap $K_4$
-/

def k4EdgeFun : Fin 12 → Fin 12
  | ⟨0, _⟩ => ⟨3, by decide⟩
  | ⟨1, _⟩ => ⟨6, by decide⟩
  | ⟨2, _⟩ => ⟨9, by decide⟩
  | ⟨3, _⟩ => ⟨0, by decide⟩
  | ⟨4, _⟩ => ⟨11, by decide⟩
  | ⟨5, _⟩ => ⟨7, by decide⟩
  | ⟨6, _⟩ => ⟨1, by decide⟩
  | ⟨7, _⟩ => ⟨5, by decide⟩
  | ⟨8, _⟩ => ⟨10, by decide⟩
  | ⟨9, _⟩ => ⟨2, by decide⟩
  | ⟨10, _⟩ => ⟨8, by decide⟩
  | ⟨11, _⟩ => ⟨4, by decide⟩

def k4NodeFun : Fin 12 → Fin 12
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩
  | ⟨3, _⟩ => ⟨4, by decide⟩
  | ⟨4, _⟩ => ⟨5, by decide⟩
  | ⟨5, _⟩ => ⟨3, by decide⟩
  | ⟨6, _⟩ => ⟨7, by decide⟩
  | ⟨7, _⟩ => ⟨8, by decide⟩
  | ⟨8, _⟩ => ⟨6, by decide⟩
  | ⟨9, _⟩ => ⟨10, by decide⟩
  | ⟨10, _⟩ => ⟨11, by decide⟩
  | ⟨11, _⟩ => ⟨9, by decide⟩

def k4NodeInv : Fin 12 → Fin 12
  | ⟨0, _⟩ => ⟨2, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨2, _⟩ => ⟨1, by decide⟩
  | ⟨3, _⟩ => ⟨5, by decide⟩
  | ⟨4, _⟩ => ⟨3, by decide⟩
  | ⟨5, _⟩ => ⟨4, by decide⟩
  | ⟨6, _⟩ => ⟨8, by decide⟩
  | ⟨7, _⟩ => ⟨6, by decide⟩
  | ⟨8, _⟩ => ⟨7, by decide⟩
  | ⟨9, _⟩ => ⟨11, by decide⟩
  | ⟨10, _⟩ => ⟨9, by decide⟩
  | ⟨11, _⟩ => ⟨10, by decide⟩

def k4FaceFun (d : Fin 12) : Fin 12 := k4NodeInv (k4EdgeFun d)
def k4FaceInv (d : Fin 12) : Fin 12 := k4EdgeFun (k4NodeFun d)

theorem k4_edge_inv : ∀ d : Fin 12, k4EdgeFun (k4EdgeFun d) = d := by decide
theorem k4_node_left_inv : ∀ d : Fin 12, k4NodeInv (k4NodeFun d) = d := by decide
theorem k4_node_right_inv : ∀ d : Fin 12, k4NodeFun (k4NodeInv d) = d := by decide
theorem k4_face_left_inv : ∀ d : Fin 12, k4FaceInv (k4FaceFun d) = d := by decide
theorem k4_face_right_inv : ∀ d : Fin 12, k4FaceFun (k4FaceInv d) = d := by decide
theorem k4_enf_id : ∀ d : Fin 12, k4EdgeFun (k4NodeFun (k4FaceFun d)) = d := by decide

def K4_hypermap : Spec.Hypermap where
  Dart := Fin 12
  edge := { f := k4EdgeFun, inv := k4EdgeFun, left_inv := k4_edge_inv, right_inv := k4_edge_inv }
  node := { f := k4NodeFun, inv := k4NodeInv, left_inv := k4_node_left_inv, right_inv := k4_node_right_inv }
  face := { f := k4FaceFun, inv := k4FaceInv, left_inv := k4_face_left_inv, right_inv := k4_face_right_inv }
  edge_involution := k4_edge_inv
  edge_node_face_id := k4_enf_id

instance : DecidableEq K4_hypermap.Dart := inferInstanceAs (DecidableEq (Fin 12))

def K4_darts : List K4_hypermap.Dart :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
   ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩,
   ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩]

/-- Check 1a: `K4_darts` is a complete, duplicate-free dart enumeration for `K4_hypermap`. -/
theorem k4_is_complete_darts : Spec.IsCompleteDarts K4_hypermap K4_darts := by
  refine ⟨by decide, ?_, by decide⟩
  intro (d : Fin 12)
  revert d
  decide

/-- Check 1b (Non-Vacuity of Planarity): `K4_hypermap` satisfies `Spec.IsPlanar` ($V - E + F = 4 - 6 + 4 = 2$). -/
theorem k4_is_planar : Spec.IsPlanar K4_hypermap K4_darts := by
  unfold Spec.IsPlanar
  decide

/-- Check 1c: `K4_hypermap` satisfies `Spec.Hypermap.isBridgeless`. -/
theorem k4_is_bridgeless : Spec.Hypermap.isBridgeless K4_hypermap K4_darts := by
  unfold Spec.Hypermap.isBridgeless
  decide

def k4VertexColor (d : Fin 12) : Spec.Color :=
  if d.val < 3 then Spec.Color.c0
  else if d.val < 6 then Spec.Color.c1
  else if d.val < 9 then Spec.Color.c2
  else Spec.Color.c3

theorem k4_vc_node_inv : ∀ d : Fin 12, k4VertexColor (k4NodeFun d) = k4VertexColor d := by decide
theorem k4_vc_edge_proper : ∀ d : Fin 12, k4VertexColor (k4EdgeFun d) ≠ k4VertexColor d := by decide

/-- Check 1d: `K4_hypermap` admits a valid 4-vertex-coloring and 4-face-coloring (`Spec.MapColoring`). -/
theorem k4_is_4_vertex_colorable : Nonempty (Spec.Hypermap.VertexColoring K4_hypermap) :=
  ⟨{ color := k4VertexColor, node_invariant := k4_vc_node_inv, edge_proper := k4_vc_edge_proper }⟩

def k4FaceColor : Fin 12 → Spec.Color
  | ⟨0, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => Spec.Color.c0
  | ⟨1, _⟩ | ⟨8, _⟩ | ⟨9, _⟩ => Spec.Color.c1
  | ⟨2, _⟩ | ⟨11, _⟩ | ⟨3, _⟩ => Spec.Color.c2
  | ⟨4, _⟩ | ⟨10, _⟩ | ⟨7, _⟩ => Spec.Color.c3

theorem k4_fc_face_inv : ∀ d : Fin 12, k4FaceColor (k4FaceFun d) = k4FaceColor d := by decide
theorem k4_fc_edge_proper : ∀ d : Fin 12, k4FaceColor (k4EdgeFun d) ≠ k4FaceColor d := by decide

theorem k4_is_4_map_colorable : Nonempty (Spec.MapColoring K4_hypermap) :=
  ⟨{ color := k4FaceColor, face_invariant := k4_fc_face_inv, edge_proper := k4_fc_edge_proper }⟩

/-!
## 2. Non-Triviality of Planarity (Exclusion): Explicit $K_5$ Hypermap & Euler's Bound
-/

def k5EdgeFun : Fin 20 → Fin 20
  | ⟨0, _⟩ => ⟨7, by decide⟩
  | ⟨1, _⟩ => ⟨10, by decide⟩
  | ⟨2, _⟩ => ⟨13, by decide⟩
  | ⟨3, _⟩ => ⟨16, by decide⟩
  | ⟨4, _⟩ => ⟨11, by decide⟩
  | ⟨5, _⟩ => ⟨14, by decide⟩
  | ⟨6, _⟩ => ⟨17, by decide⟩
  | ⟨7, _⟩ => ⟨0, by decide⟩
  | ⟨8, _⟩ => ⟨15, by decide⟩
  | ⟨9, _⟩ => ⟨18, by decide⟩
  | ⟨10, _⟩ => ⟨1, by decide⟩
  | ⟨11, _⟩ => ⟨4, by decide⟩
  | ⟨12, _⟩ => ⟨19, by decide⟩
  | ⟨13, _⟩ => ⟨2, by decide⟩
  | ⟨14, _⟩ => ⟨5, by decide⟩
  | ⟨15, _⟩ => ⟨8, by decide⟩
  | ⟨16, _⟩ => ⟨3, by decide⟩
  | ⟨17, _⟩ => ⟨6, by decide⟩
  | ⟨18, _⟩ => ⟨9, by decide⟩
  | ⟨19, _⟩ => ⟨12, by decide⟩
  | ⟨_ + 20, h⟩ => absurd h (by omega)

def k5NodeFun : Fin 20 → Fin 20
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨3, by decide⟩
  | ⟨3, _⟩ => ⟨0, by decide⟩
  | ⟨4, _⟩ => ⟨5, by decide⟩
  | ⟨5, _⟩ => ⟨6, by decide⟩
  | ⟨6, _⟩ => ⟨7, by decide⟩
  | ⟨7, _⟩ => ⟨4, by decide⟩
  | ⟨8, _⟩ => ⟨9, by decide⟩
  | ⟨9, _⟩ => ⟨10, by decide⟩
  | ⟨10, _⟩ => ⟨11, by decide⟩
  | ⟨11, _⟩ => ⟨8, by decide⟩
  | ⟨12, _⟩ => ⟨13, by decide⟩
  | ⟨13, _⟩ => ⟨14, by decide⟩
  | ⟨14, _⟩ => ⟨15, by decide⟩
  | ⟨15, _⟩ => ⟨12, by decide⟩
  | ⟨16, _⟩ => ⟨17, by decide⟩
  | ⟨17, _⟩ => ⟨18, by decide⟩
  | ⟨18, _⟩ => ⟨19, by decide⟩
  | ⟨19, _⟩ => ⟨16, by decide⟩
  | ⟨_ + 20, h⟩ => absurd h (by omega)

def k5NodeInv : Fin 20 → Fin 20
  | ⟨0, _⟩ => ⟨3, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨2, _⟩ => ⟨1, by decide⟩
  | ⟨3, _⟩ => ⟨2, by decide⟩
  | ⟨4, _⟩ => ⟨7, by decide⟩
  | ⟨5, _⟩ => ⟨4, by decide⟩
  | ⟨6, _⟩ => ⟨5, by decide⟩
  | ⟨7, _⟩ => ⟨6, by decide⟩
  | ⟨8, _⟩ => ⟨11, by decide⟩
  | ⟨9, _⟩ => ⟨8, by decide⟩
  | ⟨10, _⟩ => ⟨9, by decide⟩
  | ⟨11, _⟩ => ⟨10, by decide⟩
  | ⟨12, _⟩ => ⟨15, by decide⟩
  | ⟨13, _⟩ => ⟨12, by decide⟩
  | ⟨14, _⟩ => ⟨13, by decide⟩
  | ⟨15, _⟩ => ⟨14, by decide⟩
  | ⟨16, _⟩ => ⟨19, by decide⟩
  | ⟨17, _⟩ => ⟨16, by decide⟩
  | ⟨18, _⟩ => ⟨17, by decide⟩
  | ⟨19, _⟩ => ⟨18, by decide⟩
  | ⟨_ + 20, h⟩ => absurd h (by omega)

def k5FaceFun (d : Fin 20) : Fin 20 := k5NodeInv (k5EdgeFun d)
def k5FaceInv (d : Fin 20) : Fin 20 := k5EdgeFun (k5NodeFun d)

theorem k5_edge_inv : ∀ d : Fin 20, k5EdgeFun (k5EdgeFun d) = d := by decide
theorem k5_node_left_inv : ∀ d : Fin 20, k5NodeInv (k5NodeFun d) = d := by decide
theorem k5_node_right_inv : ∀ d : Fin 20, k5NodeFun (k5NodeInv d) = d := by decide
theorem k5_face_left_inv : ∀ d : Fin 20, k5FaceInv (k5FaceFun d) = d := by decide
theorem k5_face_right_inv : ∀ d : Fin 20, k5FaceFun (k5FaceInv d) = d := by decide
theorem k5_enf_id : ∀ d : Fin 20, k5EdgeFun (k5NodeFun (k5FaceFun d)) = d := by decide

def K5_hypermap : Spec.Hypermap where
  Dart := Fin 20
  edge := { f := k5EdgeFun, inv := k5EdgeFun, left_inv := k5_edge_inv, right_inv := k5_edge_inv }
  node := { f := k5NodeFun, inv := k5NodeInv, left_inv := k5_node_left_inv, right_inv := k5_node_right_inv }
  face := { f := k5FaceFun, inv := k5FaceInv, left_inv := k5_face_left_inv, right_inv := k5_face_right_inv }
  edge_involution := k5_edge_inv
  edge_node_face_id := k5_enf_id

instance : DecidableEq K5_hypermap.Dart := inferInstanceAs (DecidableEq (Fin 20))

def K5_darts : List K5_hypermap.Dart :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩,
   ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩,
   ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩,
   ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩]

theorem k5_is_complete_darts : Spec.IsCompleteDarts K5_hypermap K5_darts := by
  refine ⟨by decide, ?_, by decide⟩
  intro (d : Fin 20)
  revert d
  decide

theorem k5_is_bridgeless : Spec.Hypermap.isBridgeless K5_hypermap K5_darts := by
  unfold Spec.Hypermap.isBridgeless
  decide

/-- Check 2a (Non-Triviality of Planarity): `K5_hypermap` does NOT satisfy `Spec.IsPlanar`. -/
theorem k5_not_planar : ¬ Spec.IsPlanar K5_hypermap K5_darts := by
  unfold Spec.IsPlanar
  decide

/-- Check 2b (Euler's Planar Triangulation Edge Bound):
    Every planar triangulation ($V - E + F = 2$ and $2E = 3F$) satisfies $E \le 3V - 6$. -/
theorem euler_triangulation_edge_bound (V E F : Int)
    (hEuler : V - E + F = 2) (hTriang : 2 * E = 3 * F) :
    E ≤ 3 * V - 6 := by
  omega

/-- Check 2c: $K_5$ ($V = 5, E = 10$) violates Euler's planar triangulation bound since $10 > 3(5) - 6 = 9$. -/
theorem k5_violates_euler_triangulation_bound :
    ¬ (∃ (F : Int), (5 : Int) - 10 + F = 2 ∧ 2 * (10 : Int) = 3 * F) := by
  rintro ⟨F, h1, h2⟩
  omega

/-!
## 3. Sharpness of Coloring (3-Color Counterexample): $K_4$ is NOT 3-Colorable
-/

/-- Check 3a: The planar tetrahedron `K4_hypermap` is NOT 3-vertex-colorable. -/
theorem k4_not_3_vertex_colorable : ¬ Nonempty (VertexColoringK K4_hypermap 3) := by
  rintro ⟨vc⟩
  have h01 : vc.color ⟨1, by decide⟩ = vc.color ⟨0, by decide⟩ := vc.node_invariant ⟨0, by decide⟩
  have h02 : vc.color ⟨2, by decide⟩ = vc.color ⟨0, by decide⟩ :=
    (vc.node_invariant ⟨1, by decide⟩).trans h01
  have h34 : vc.color ⟨4, by decide⟩ = vc.color ⟨3, by decide⟩ := vc.node_invariant ⟨3, by decide⟩
  have h35 : vc.color ⟨5, by decide⟩ = vc.color ⟨3, by decide⟩ :=
    (vc.node_invariant ⟨4, by decide⟩).trans h34
  have h67 : vc.color ⟨7, by decide⟩ = vc.color ⟨6, by decide⟩ := vc.node_invariant ⟨6, by decide⟩
  have h68 : vc.color ⟨8, by decide⟩ = vc.color ⟨6, by decide⟩ :=
    (vc.node_invariant ⟨7, by decide⟩).trans h67
  have h9_10 : vc.color ⟨10, by decide⟩ = vc.color ⟨9, by decide⟩ := vc.node_invariant ⟨9, by decide⟩
  have h9_11 : vc.color ⟨11, by decide⟩ = vc.color ⟨9, by decide⟩ :=
    (vc.node_invariant ⟨10, by decide⟩).trans h9_10
  have e01 : vc.color ⟨3, by decide⟩ ≠ vc.color ⟨0, by decide⟩ := vc.edge_proper ⟨0, by decide⟩
  have e02 : vc.color ⟨6, by decide⟩ ≠ vc.color ⟨0, by decide⟩ := by
    have h := vc.edge_proper ⟨1, by decide⟩
    rwa [h01] at h
  have e03 : vc.color ⟨9, by decide⟩ ≠ vc.color ⟨0, by decide⟩ := by
    have h := vc.edge_proper ⟨2, by decide⟩
    rwa [h02] at h
  have e12 : vc.color ⟨6, by decide⟩ ≠ vc.color ⟨3, by decide⟩ := by
    have h := vc.edge_proper ⟨5, by decide⟩
    change vc.color ⟨7, by decide⟩ ≠ vc.color ⟨5, by decide⟩ at h
    rwa [h67, h35] at h
  have e13 : vc.color ⟨9, by decide⟩ ≠ vc.color ⟨3, by decide⟩ := by
    have h := vc.edge_proper ⟨4, by decide⟩
    change vc.color ⟨11, by decide⟩ ≠ vc.color ⟨4, by decide⟩ at h
    rwa [h9_11, h34] at h
  have e23 : vc.color ⟨9, by decide⟩ ≠ vc.color ⟨6, by decide⟩ := by
    have h := vc.edge_proper ⟨8, by decide⟩
    change vc.color ⟨10, by decide⟩ ≠ vc.color ⟨8, by decide⟩ at h
    rwa [h9_10, h68] at h
  exact pigeonhole_4_in_3
    (vc.color ⟨0, by decide⟩).val (vc.color ⟨3, by decide⟩).val
    (vc.color ⟨6, by decide⟩).val (vc.color ⟨9, by decide⟩).val
    (vc.color ⟨0, by decide⟩).isLt (vc.color ⟨3, by decide⟩).isLt
    (vc.color ⟨6, by decide⟩).isLt (vc.color ⟨9, by decide⟩).isLt
    (fun h => e01 (Fin.ext h)) (fun h => e02 (Fin.ext h)) (fun h => e03 (Fin.ext h))
    (fun h => e12 (Fin.ext h)) (fun h => e13 (Fin.ext h)) (fun h => e23 (Fin.ext h))

/-- Check 3b: The planar tetrahedron `K4_hypermap` is NOT 3-face-colorable. -/
theorem k4_not_3_face_colorable : ¬ Nonempty (FaceColoringK K4_hypermap 3) := by
  rintro ⟨fc⟩
  have f0_5 : fc.color ⟨5, by decide⟩ = fc.color ⟨0, by decide⟩ := fc.face_invariant ⟨0, by decide⟩
  have f0_6 : fc.color ⟨6, by decide⟩ = fc.color ⟨0, by decide⟩ :=
    (fc.face_invariant ⟨5, by decide⟩).trans f0_5
  have f1_8 : fc.color ⟨8, by decide⟩ = fc.color ⟨1, by decide⟩ := fc.face_invariant ⟨1, by decide⟩
  have f1_9 : fc.color ⟨9, by decide⟩ = fc.color ⟨1, by decide⟩ :=
    (fc.face_invariant ⟨8, by decide⟩).trans f1_8
  have f2_11 : fc.color ⟨11, by decide⟩ = fc.color ⟨2, by decide⟩ := fc.face_invariant ⟨2, by decide⟩
  have f2_3 : fc.color ⟨3, by decide⟩ = fc.color ⟨2, by decide⟩ :=
    (fc.face_invariant ⟨11, by decide⟩).trans f2_11
  have f3_10 : fc.color ⟨10, by decide⟩ = fc.color ⟨4, by decide⟩ := fc.face_invariant ⟨4, by decide⟩
  have f3_7 : fc.color ⟨7, by decide⟩ = fc.color ⟨4, by decide⟩ :=
    (fc.face_invariant ⟨10, by decide⟩).trans f3_10
  have e02 : fc.color ⟨2, by decide⟩ ≠ fc.color ⟨0, by decide⟩ := by
    have h := fc.edge_proper ⟨0, by decide⟩
    change fc.color ⟨3, by decide⟩ ≠ fc.color ⟨0, by decide⟩ at h
    rwa [f2_3] at h
  have e01 : fc.color ⟨1, by decide⟩ ≠ fc.color ⟨0, by decide⟩ := by
    have h := fc.edge_proper ⟨6, by decide⟩
    change fc.color ⟨1, by decide⟩ ≠ fc.color ⟨6, by decide⟩ at h
    rwa [f0_6] at h
  have e03 : fc.color ⟨4, by decide⟩ ≠ fc.color ⟨0, by decide⟩ := by
    have h := fc.edge_proper ⟨5, by decide⟩
    change fc.color ⟨7, by decide⟩ ≠ fc.color ⟨5, by decide⟩ at h
    rwa [f3_7, f0_5] at h
  have e12 : fc.color ⟨2, by decide⟩ ≠ fc.color ⟨1, by decide⟩ := by
    have h := fc.edge_proper ⟨9, by decide⟩
    change fc.color ⟨2, by decide⟩ ≠ fc.color ⟨9, by decide⟩ at h
    rwa [f1_9] at h
  have e13 : fc.color ⟨4, by decide⟩ ≠ fc.color ⟨1, by decide⟩ := by
    have h := fc.edge_proper ⟨8, by decide⟩
    change fc.color ⟨10, by decide⟩ ≠ fc.color ⟨8, by decide⟩ at h
    rwa [f3_10, f1_8] at h
  have e23 : fc.color ⟨4, by decide⟩ ≠ fc.color ⟨2, by decide⟩ := by
    have h := fc.edge_proper ⟨11, by decide⟩
    change fc.color ⟨4, by decide⟩ ≠ fc.color ⟨11, by decide⟩ at h
    rwa [f2_11] at h
  exact pigeonhole_4_in_3
    (fc.color ⟨0, by decide⟩).val (fc.color ⟨1, by decide⟩).val
    (fc.color ⟨2, by decide⟩).val (fc.color ⟨4, by decide⟩).val
    (fc.color ⟨0, by decide⟩).isLt (fc.color ⟨1, by decide⟩).isLt
    (fc.color ⟨2, by decide⟩).isLt (fc.color ⟨4, by decide⟩).isLt
    (fun h => e01 (Fin.ext h)) (fun h => e02 (Fin.ext h)) (fun h => e03 (Fin.ext h))
    (fun h => e12 (Fin.ext h)) (fun h => e13 (Fin.ext h)) (fun h => e23 (Fin.ext h))

/-!
## 4. Sharpness of Coloring (4-Color Non-Planar Counterexample): $K_5$ is NOT 4-Colorable
-/

/-- Check 4a: The non-planar hypermap `K5_hypermap` is NOT 4-vertex-colorable (`VertexColoringK K5_hypermap 4`). -/
theorem k5_not_4_vertex_colorable_k : ¬ Nonempty (VertexColoringK K5_hypermap 4) := by
  rintro ⟨vc⟩
  have v0_1 : vc.color ⟨1, by decide⟩ = vc.color ⟨0, by decide⟩ := vc.node_invariant ⟨0, by decide⟩
  have v0_2 : vc.color ⟨2, by decide⟩ = vc.color ⟨0, by decide⟩ := (vc.node_invariant ⟨1, by decide⟩).trans v0_1
  have v0_3 : vc.color ⟨3, by decide⟩ = vc.color ⟨0, by decide⟩ := (vc.node_invariant ⟨2, by decide⟩).trans v0_2
  have v1_5 : vc.color ⟨5, by decide⟩ = vc.color ⟨4, by decide⟩ := vc.node_invariant ⟨4, by decide⟩
  have v1_6 : vc.color ⟨6, by decide⟩ = vc.color ⟨4, by decide⟩ := (vc.node_invariant ⟨5, by decide⟩).trans v1_5
  have v1_7 : vc.color ⟨7, by decide⟩ = vc.color ⟨4, by decide⟩ := (vc.node_invariant ⟨6, by decide⟩).trans v1_6
  have v2_9 : vc.color ⟨9, by decide⟩ = vc.color ⟨8, by decide⟩ := vc.node_invariant ⟨8, by decide⟩
  have v2_10 : vc.color ⟨10, by decide⟩ = vc.color ⟨8, by decide⟩ := (vc.node_invariant ⟨9, by decide⟩).trans v2_9
  have v2_11 : vc.color ⟨11, by decide⟩ = vc.color ⟨8, by decide⟩ := (vc.node_invariant ⟨10, by decide⟩).trans v2_10
  have v3_13 : vc.color ⟨13, by decide⟩ = vc.color ⟨12, by decide⟩ := vc.node_invariant ⟨12, by decide⟩
  have v3_14 : vc.color ⟨14, by decide⟩ = vc.color ⟨12, by decide⟩ := (vc.node_invariant ⟨13, by decide⟩).trans v3_13
  have v3_15 : vc.color ⟨15, by decide⟩ = vc.color ⟨12, by decide⟩ := (vc.node_invariant ⟨14, by decide⟩).trans v3_14
  have v4_17 : vc.color ⟨17, by decide⟩ = vc.color ⟨16, by decide⟩ := vc.node_invariant ⟨16, by decide⟩
  have v4_18 : vc.color ⟨18, by decide⟩ = vc.color ⟨16, by decide⟩ := (vc.node_invariant ⟨17, by decide⟩).trans v4_17
  have v4_19 : vc.color ⟨19, by decide⟩ = vc.color ⟨16, by decide⟩ := (vc.node_invariant ⟨18, by decide⟩).trans v4_18
  have e01 : vc.color ⟨4, by decide⟩ ≠ vc.color ⟨0, by decide⟩ := by
    have h := vc.edge_proper ⟨0, by decide⟩
    change vc.color ⟨7, by decide⟩ ≠ vc.color ⟨0, by decide⟩ at h
    rwa [v1_7] at h
  have e02 : vc.color ⟨8, by decide⟩ ≠ vc.color ⟨0, by decide⟩ := by
    have h := vc.edge_proper ⟨1, by decide⟩
    change vc.color ⟨10, by decide⟩ ≠ vc.color ⟨1, by decide⟩ at h
    rwa [v2_10, v0_1] at h
  have e03 : vc.color ⟨12, by decide⟩ ≠ vc.color ⟨0, by decide⟩ := by
    have h := vc.edge_proper ⟨2, by decide⟩
    change vc.color ⟨13, by decide⟩ ≠ vc.color ⟨2, by decide⟩ at h
    rwa [v3_13, v0_2] at h
  have e04 : vc.color ⟨16, by decide⟩ ≠ vc.color ⟨0, by decide⟩ := by
    have h := vc.edge_proper ⟨3, by decide⟩
    change vc.color ⟨16, by decide⟩ ≠ vc.color ⟨3, by decide⟩ at h
    rwa [v0_3] at h
  have e12 : vc.color ⟨8, by decide⟩ ≠ vc.color ⟨4, by decide⟩ := by
    have h := vc.edge_proper ⟨4, by decide⟩
    change vc.color ⟨11, by decide⟩ ≠ vc.color ⟨4, by decide⟩ at h
    rwa [v2_11] at h
  have e13 : vc.color ⟨12, by decide⟩ ≠ vc.color ⟨4, by decide⟩ := by
    have h := vc.edge_proper ⟨5, by decide⟩
    change vc.color ⟨14, by decide⟩ ≠ vc.color ⟨5, by decide⟩ at h
    rwa [v3_14, v1_5] at h
  have e14 : vc.color ⟨16, by decide⟩ ≠ vc.color ⟨4, by decide⟩ := by
    have h := vc.edge_proper ⟨6, by decide⟩
    change vc.color ⟨17, by decide⟩ ≠ vc.color ⟨6, by decide⟩ at h
    rwa [v4_17, v1_6] at h
  have e23 : vc.color ⟨12, by decide⟩ ≠ vc.color ⟨8, by decide⟩ := by
    have h := vc.edge_proper ⟨8, by decide⟩
    change vc.color ⟨15, by decide⟩ ≠ vc.color ⟨8, by decide⟩ at h
    rwa [v3_15] at h
  have e24 : vc.color ⟨16, by decide⟩ ≠ vc.color ⟨8, by decide⟩ := by
    have h := vc.edge_proper ⟨9, by decide⟩
    change vc.color ⟨18, by decide⟩ ≠ vc.color ⟨9, by decide⟩ at h
    rwa [v4_18, v2_9] at h
  have e34 : vc.color ⟨16, by decide⟩ ≠ vc.color ⟨12, by decide⟩ := by
    have h := vc.edge_proper ⟨12, by decide⟩
    change vc.color ⟨19, by decide⟩ ≠ vc.color ⟨12, by decide⟩ at h
    rwa [v4_19] at h
  exact pigeonhole_5_in_4
    (vc.color ⟨0, by decide⟩).val (vc.color ⟨4, by decide⟩).val
    (vc.color ⟨8, by decide⟩).val (vc.color ⟨12, by decide⟩).val (vc.color ⟨16, by decide⟩).val
    (vc.color ⟨0, by decide⟩).isLt (vc.color ⟨4, by decide⟩).isLt
    (vc.color ⟨8, by decide⟩).isLt (vc.color ⟨12, by decide⟩).isLt (vc.color ⟨16, by decide⟩).isLt
    (fun h => e01 (Fin.ext h)) (fun h => e02 (Fin.ext h)) (fun h => e03 (Fin.ext h)) (fun h => e04 (Fin.ext h))
    (fun h => e12 (Fin.ext h)) (fun h => e13 (Fin.ext h)) (fun h => e14 (Fin.ext h))
    (fun h => e23 (Fin.ext h)) (fun h => e24 (Fin.ext h)) (fun h => e34 (Fin.ext h))

/-- Check 4b: `K5_hypermap` is NOT 4-vertex-colorable under `Spec.Hypermap.VertexColoring`. -/
theorem k5_not_4_vertex_colorable : ¬ Nonempty (Spec.Hypermap.VertexColoring K5_hypermap) := by
  rw [vertexColoring_iff_k4]
  exact k5_not_4_vertex_colorable_k

/-- Check 4c: The dual hypermap `K5_hypermap.dual` is NOT 4-face-colorable under `Spec.MapColoring`. -/
theorem k5_dual_not_4_map_colorable : ¬ Nonempty (Spec.MapColoring K5_hypermap.dual) := by
  rintro ⟨fc⟩
  have hvc : Spec.Hypermap.VertexColoring K5_hypermap := {
    color := fc.color
    node_invariant := fun d => by
      have h := fc.face_invariant (K5_hypermap.node.f d)
      change fc.color (K5_hypermap.node.inv (K5_hypermap.node.f d)) = fc.color (K5_hypermap.node.f d) at h
      rw [K5_hypermap.node.left_inv] at h
      exact h.symm
    edge_proper := fc.edge_proper
  }
  exact k5_not_4_vertex_colorable ⟨hvc⟩

end SanityChecks
