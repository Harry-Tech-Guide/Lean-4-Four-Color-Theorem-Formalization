
import FourColorTheorem.Math.Hypermap

-- Step 3: Map Coloring

/-- The four colors used for coloring the map. -/
inductive Color
  | c0 | c1 | c2 | c3
  deriving DecidableEq, Repr

instance : Inhabited Color := ⟨Color.c0⟩

def Color.toNat : Color → Nat
  | c0 => 0
  | c1 => 1
  | c2 => 2
  | c3 => 3

namespace Hypermap

variable (H : Hypermap)

/-- A valid 4-coloring of the faces of a hypermap. 
    Every dart in the same face orbit has the same color, 
    and darts sharing an edge have different colors. -/
structure FaceColoring where
  color : H.Dart → Color
  face_invariant : ∀ d, color (H.face.f d) = color d
  edge_proper : ∀ d, color (H.edge.f d) ≠ color d

/-- A valid 4-coloring of the nodes (vertices) of a hypermap. 
    Every dart in the same node orbit has the same color, 
    and darts sharing an edge have different colors. -/
structure VertexColoring where
  color : H.Dart → Color
  node_invariant : ∀ d, color (H.node.f d) = color d
  edge_proper : ∀ d, color (H.edge.f d) ≠ color d

/-- Theorem: A Vertex Coloring of a Hypermap's dual is a Face Coloring of the original map. -/
def vertexColoringOfDualToFaceColoring (vc : VertexColoring H.dual) : FaceColoring H where
  color := vc.color
  face_invariant := fun d => by
    have h := vc.node_invariant (H.face.f d)
    change vc.color (H.face.inv (H.face.f d)) = vc.color (H.face.f d) at h
    rw [H.face.left_inv] at h
    exact h.symm
  edge_proper := vc.edge_proper

/-- Theorem: A Face Coloring of a Hypermap is a Vertex Coloring of its topological dual. -/
def faceColoringToVertexColoringOfDual (fc : FaceColoring H) : VertexColoring H.dual where
  color := fc.color
  node_invariant := fun d => by
    have h := fc.face_invariant (H.face.inv d)
    rw [H.face.right_inv] at h
    exact h.symm
  edge_proper := fc.edge_proper

end Hypermap
