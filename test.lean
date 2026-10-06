
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

structure Hypermap where
  Dart : Type
  edge : Perm Dart
  node : Perm Dart
  face : Perm Dart
  edge_involution : ∀ d, edge.f (edge.f d) = d
  edge_node_face_id : ∀ d, edge.f (node.f (face.f d)) = d

namespace Hypermap

variable (H : Hypermap)

lemma face_node_edge_id (d : H.Dart) : H.face.f (H.node.f (H.edge.f d)) = d := by
  have h1 := H.edge_node_face_id (H.edge.f d)
  -- edge(node(face(edge(d)))) = edge(d)
  -- apply edge to both sides?
  sorry

end Hypermap
