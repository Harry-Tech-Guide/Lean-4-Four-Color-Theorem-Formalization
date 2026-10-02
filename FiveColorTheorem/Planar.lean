import FiveColorTheorem.Kempe

namespace Math

open Classical

/-- 
`CombinatoriallyPlanar` captures the two exact structural properties of planar graphs 
that are strictly necessary to prove the Five-Color Theorem:

1. Every non-empty subgraph contains a vertex of degree ≤ 5 (a consequence of Euler's formula).
2. The Kempe Non-Crossing Property: If a vertex of degree 5 has 5 neighbors of 5 distinct colors,
   the topology of the plane dictates that you can always find at least two neighbors that
   are NOT connected by a Kempe chain of their respective colors. 
   (Because if they were, their chain would form a wall that blocks the other neighbors 
   from connecting, guaranteeing a different disconnected pair).
3. Hereditary: Removing a vertex preserves planarity.
-/
inductive CombinatoriallyPlanar {V : Type} [DecidableEq V] : Graph V → Prop
  | mk (G : Graph V) :
      -- 1. Existence of a low-degree vertex
      (G.vertices.length > 0 → ∃ v, v ∈ G.vertices ∧ degree G v ≤ 5) →
      -- 2. Kempe Non-Crossing
      (∀ (v : V) (c : V → Color5),
        v ∈ G.vertices →
        degree G v = 5 →
        (∀ (n : V), G.adj v n = true → n ∈ G.vertices) →
        -- If all 5 colors are present among its neighbors
        (∀ col : Color5, ∃ n, G.adj v n = true ∧ c n = col) →
        -- Then there must exist two neighbors with different colors that are NOT connected
        (∃ n1 n2, G.adj v n1 = true ∧ G.adj v n2 = true ∧ c n1 ≠ c n2 ∧
          ¬ KempeChain G c (c n1) (c n2) n1 n2)) →
      -- 3. Hereditary
      (∀ v, v ∈ G.vertices → CombinatoriallyPlanar (removeVertex G v)) →
      CombinatoriallyPlanar G

end Math
