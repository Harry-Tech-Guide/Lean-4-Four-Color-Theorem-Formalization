
-- Axiomatic foundation of Combinatorial Hypermaps for the Four Color Theorem

structure Perm (D : Type) where
  f : D → D
  inv : D → D
  left_inv : ∀ x, inv (f x) = x
  right_inv : ∀ x, f (inv x) = x

def Perm.symm {D : Type} (p : Perm D) : Perm D :=
  { f := p.inv, inv := p.f, left_inv := p.right_inv, right_inv := p.left_inv }

def Perm.mul {D : Type} (p q : Perm D) : Perm D :=
  { f := fun x => p.f (q.f x),
    inv := fun x => q.inv (p.inv x),
    left_inv := fun x => by
      dsimp
      rw [p.left_inv, q.left_inv],
    right_inv := fun x => by
      dsimp
      rw [q.right_inv, p.right_inv] }

def Perm.one {D : Type} : Perm D :=
  { f := id,
    inv := id,
    left_inv := fun _ => rfl,
    right_inv := fun _ => rfl }

instance {D : Type} : Inhabited (Perm D) where
  default := Perm.one

/-- A combinatorial hypermap represents a topological map via permutations on darts. -/
structure Hypermap where
  Dart : Type
  edge : Perm Dart
  node : Perm Dart
  face : Perm Dart
  -- Every edge is composed of exactly two darts, or is a self loop if a dart maps to itself.
  edge_involution : ∀ d, edge.f (edge.f d) = d
  -- The fundamental topological identity of hypermaps: traversing an edge, then a node, then a face returns to the start.
  edge_node_face_id : ∀ d, edge.f (node.f (face.f d)) = d

namespace Hypermap

variable (H : Hypermap)

/-- Applying edge twice is the identity -/
theorem edge_edge (d : H.Dart) : H.edge.f (H.edge.f d) = d :=
  H.edge_involution d

/-- Since edge is an involution, its inverse is itself -/
theorem edge_inv_eq_edge (d : H.Dart) : H.edge.inv d = H.edge.f d := by
  have h := H.edge.left_inv (H.edge.f d)
  rw [H.edge_involution d] at h
  exact h

/-- The face permutation can be defined from edge and node inverses -/
theorem face_eq_node_inv_edge_inv (d : H.Dart) : H.face.f d = H.node.inv (H.edge.inv d) := by
  have h := H.edge_node_face_id d
  have h1 : H.edge.inv (H.edge.f (H.node.f (H.face.f d))) = H.edge.inv d := by rw [h]
  rw [H.edge.left_inv] at h1
  have h2 : H.node.inv (H.node.f (H.face.f d)) = H.node.inv (H.edge.inv d) := by rw [h1]
  rw [H.node.left_inv] at h2
  exact h2


/-- node * face * edge = id -/
theorem node_face_edge_id (d : H.Dart) : H.node.f (H.face.f (H.edge.f d)) = d := by
  have h := H.edge_node_face_id (H.edge.f d)
  have h2 : H.edge.f (H.edge.f (H.node.f (H.face.f (H.edge.f d)))) = H.edge.f (H.edge.f d) := by rw [h]
  rw [H.edge_involution, H.edge_involution] at h2
  exact h2

/-- face * edge * node = id -/
theorem face_edge_node_id (d : H.Dart) : H.face.f (H.edge.f (H.node.f d)) = d := by
  have h := node_face_edge_id H (H.node.f d)
  have h2 : H.node.inv (H.node.f (H.face.f (H.edge.f (H.node.f d)))) = H.node.inv (H.node.f d) := by rw [h]
  rw [H.node.left_inv, H.node.left_inv] at h2
  exact h2


/-- The topological dual of a hypermap. 
    Faces become nodes, nodes become faces, and edges remain edges. -/
def dual : Hypermap where
  Dart := H.Dart
  edge := H.edge
  node := Perm.symm H.face
  face := Perm.symm H.node
  edge_involution := H.edge_involution
  edge_node_face_id := fun d => by
    -- We need to show: edge.f (face.inv (node.inv d)) = d
    -- We know face.f (edge.f (node.f d)) = d
    have h := face_edge_node_id H (H.node.inv d)
    rw [H.node.right_inv] at h
    -- h : face.f (edge.f d) = H.node.inv d
    -- apply face.inv to both sides
    have h2 : H.face.inv (H.face.f (H.edge.f d)) = H.face.inv (H.node.inv d) := by rw [h]
    rw [H.face.left_inv] at h2
    -- h2 : edge.f d = face.inv (node.inv d)
    -- apply edge.f to both sides
    have h3 : H.edge.f (H.edge.f d) = H.edge.f (H.face.inv (H.node.inv d)) := by rw [h2]
    rw [H.edge_involution] at h3
    exact h3.symm

end Hypermap



