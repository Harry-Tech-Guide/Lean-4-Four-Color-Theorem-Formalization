import Init.Data.List.Basic

namespace Math

/-- A Permutation is a bijection on a type `α`. -/
structure Perm (α : Type) where
  fw : α → α
  bw : α → α
  fw_bw : ∀ x, fw (bw x) = x
  bw_fw : ∀ x, bw (fw x) = x

namespace Perm

variable {α : Type}

def id : Perm α :=
  { fw := fun x => x
    bw := fun x => x
    fw_bw := fun _ => rfl
    bw_fw := fun _ => rfl }

def inv (p : Perm α) : Perm α :=
  { fw := p.bw
    bw := p.fw
    fw_bw := p.bw_fw
    bw_fw := p.fw_bw }

def mul (p q : Perm α) : Perm α :=
  { fw := fun x => p.fw (q.fw x)
    bw := fun x => q.bw (p.bw x)
    fw_bw := fun x => by dsimp; rw [q.fw_bw, p.fw_bw]
    bw_fw := fun x => by dsimp; rw [p.bw_fw, q.bw_fw] }

end Perm

/-- Combinatorial Hypermap Definition -/
structure Hypermap (D : Type) where
  edge : Perm D
  node : Perm D
  face : Perm D
  edge_involution : ∀ x, edge.fw (edge.fw x) = x
  no_fixed_edges : ∀ x, edge.fw x ≠ x
  edge_node_face : ∀ x, edge.fw (node.fw (face.fw x)) = x

namespace Hypermap

variable {D : Type} (H : Hypermap D)

/-- Compute the orbit (cycle) of a single dart under a permutation. -/
partial def orbit [DecidableEq D] (p : Perm D) (start : D) : List D :=
  let rec loop (current : D) (acc : List D) : List D :=
    let next_d := p.fw current
    if next_d == start then acc.reverse
    else loop next_d (next_d :: acc)
  loop start [start]

/-- Count the total number of distinct orbits of a permutation over a finite list of darts. -/
partial def countOrbits [DecidableEq D] (p : Perm D) (darts : List D) : Nat :=
  let rec loop (remaining : List D) (visited : List D) (count : Nat) : Nat :=
    match remaining with
    | [] => count
    | d :: ds =>
      if visited.contains d then
        loop ds visited count
      else
        let orb := orbit p d
        loop ds (orb ++ visited) (count + 1)
  loop darts [] 0

/-- Compute the connected component orbit of a dart. 
Two darts are connected if they can be reached by a sequence of `edge` and `node` operations. -/
partial def compOrbit [DecidableEq D] (start : D) : List D :=
  let rec loop (queue : List D) (visited : List D) : List D :=
    match queue with
    | [] => visited
    | d :: ds =>
      if visited.contains d then
        loop ds visited
      else
        let n1 := H.edge.fw d
        let n2 := H.node.fw d
        loop (n1 :: n2 :: ds) (d :: visited)
  loop [start] []

/-- Count the number of connected components in the hypermap. -/
partial def countComponents [DecidableEq D] (darts : List D) : Nat :=
  let rec loop (remaining : List D) (visited : List D) (count : Nat) : Nat :=
    match remaining with
    | [] => count
    | d :: ds =>
      if visited.contains d then
        loop ds visited count
      else
        let orb := compOrbit H d
        loop ds (orb ++ visited) (count + 1)
  loop darts [] 0

/-- The Euler Characteristic of a hypermap. 
χ = V - E + F 
Where V, E, F are the number of node, edge, and face orbits respectively. -/
def eulerChar [DecidableEq D] (darts : List D) : Int :=
  (countOrbits H.node darts : Int) - 
  (countOrbits H.edge darts : Int) + 
  (countOrbits H.face darts : Int)

/-- A Combinatorial Hypermap is PLANAR if its Euler characteristic satisfies Euler's formula:
χ = 2 * C 
(Where C is the number of connected components). -/
def IsPlanar [DecidableEq D] (darts : List D) : Prop :=
  eulerChar H darts = 2 * (countComponents H darts : Int)

end Hypermap

end Math
