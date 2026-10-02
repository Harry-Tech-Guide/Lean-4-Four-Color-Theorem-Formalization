namespace Math

/-- A purely combinatorial representation of a planar map.
A hypermap consists of a type of darts `D` and three permutations:
`edge`, `node`, and `face`, such that their product is the identity.
-/
structure Hypermap (D : Type) where
  edge : D → D
  node : D → D
  face : D → D
  edge_node_face : ∀ x, edge (node (face x)) = x

/-- A combinatorial map is a hypermap where the edge permutation is an involution
without fixed points. This corresponds to the two directions of an edge. -/
class CombinatorialMap {D : Type} (H : Hypermap D) where
  edge_inv : ∀ x, H.edge (H.edge x) = x
  edge_no_fp : ∀ x, H.edge x ≠ x

end Math
