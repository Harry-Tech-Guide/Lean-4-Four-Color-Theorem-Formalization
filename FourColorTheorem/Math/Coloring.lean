import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.HypermapGraph

namespace Math

/-- The four colors used to color the map. -/
inductive Color
  | c1 | c2 | c3 | c4
  deriving DecidableEq, Repr, Inhabited

/-- A valid 4-coloring of a hypermap assigns a color to every dart such that:
1. All darts in the same node (vertex) share the same color.
2. Darts connected by an edge belong to adjacent nodes and must have different colors. -/
structure MapColoring {D : Type} (H : Hypermap D) where
  color : D → Color
  node_const : ∀ d, color (H.node.fw d) = color d
  edge_diff : ∀ d, color (H.edge.fw d) ≠ color d

/-- Equivalently, a valid 4-coloring on the extracted graph structure. -/
def ValidGraphColoring {D : Type} [DecidableEq D] (H : Hypermap D) (darts : List D) (color : D → Color) : Prop :=
  let G := Hypermap.extractGraph H darts
  ∀ d1 d2, G.contains d1 → G.contains d2 → G.adj d1 d2 = true → color d1 ≠ color d2

end Math
