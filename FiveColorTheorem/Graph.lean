import Init

namespace Math

/-- A purely combinatorial graph with an explicit finite list of vertices. -/
structure Graph (V : Type) where
  vertices : List V
  nodup : vertices.Nodup
  adj : V → V → Bool
  symm : ∀ x y, adj x y = true → adj y x = true
  irrefl : ∀ x, adj x x = false

inductive Color5
  | c1 | c2 | c3 | c4 | c5
  deriving DecidableEq, Repr

/-- A valid coloring of a graph assigns one of 5 colors to each vertex. -/
def ValidColoring {V : Type} (G : Graph V) (c : V → Color5) : Prop :=
  ∀ x y, x ∈ G.vertices → y ∈ G.vertices → G.adj x y = true → c x ≠ c y

/-- The neighbors of a vertex `v`. -/
def neighbors {V : Type} [DecidableEq V] (G : Graph V) (v : V) : List V :=
  G.vertices.filter (fun x => G.adj v x)

/-- The degree of a vertex `v`. -/
def degree {V : Type} [DecidableEq V] (G : Graph V) (v : V) : Nat :=
  (neighbors G v).length

/-- A subgraph induced by removing a vertex `v`.
We remove `v` from the list of vertices, but the adjacency function remains
the same (it just won't be queried for `v` since `v` is no longer in `vertices`). -/
def removeVertex {V : Type} [DecidableEq V] (G : Graph V) (v : V) : Graph V where
  vertices := G.vertices.erase v
  nodup := G.nodup.erase v
  adj := G.adj
  symm := G.symm
  irrefl := G.irrefl

end Math
