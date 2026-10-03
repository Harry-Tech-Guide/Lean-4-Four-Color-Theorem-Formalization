import FourColorTheorem.Math.Hypermap

namespace Math

/-- A simple graph structure defined natively without dependencies. -/
structure Graph (V : Type) where
  vertices : List V
  adj : V → V → Bool

namespace Graph

variable {V : Type} (G : Graph V)

/-- Check if a vertex is in the graph. -/
def contains (v : V) [DecidableEq V] : Bool :=
  G.vertices.contains v

/-- The degree of a vertex is the number of adjacent vertices. -/
def degree (v : V) : Nat :=
  G.vertices.countP (fun x => G.adj v x)

end Graph

end Math
