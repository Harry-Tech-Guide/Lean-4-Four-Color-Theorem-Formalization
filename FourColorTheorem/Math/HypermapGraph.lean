import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.Graph

namespace Math
namespace Hypermap

variable {D : Type} [DecidableEq D] (H : Hypermap D)

/-- In a hypermap, a 'Vertex' is uniquely identified by the orbit of its darts under `node`.
We can use the orbit list as the vertex identifier, but practically, we can just map 
darts to vertices. Two darts represent the same vertex if they are in the same node orbit. -/
def sameVertex (d1 d2 : D) : Bool :=
  (orbit H.node d1).contains d2

/-- Two darts represent the same face if they are in the same face orbit. -/
def sameFace (d1 d2 : D) : Bool :=
  (orbit H.face d1).contains d2

/-- Two darts are adjacent if the edge permutation of one is in the node orbit of the other. -/
def areAdjacentDarts (d1 d2 : D) : Bool :=
  sameVertex H (H.edge.fw d1) d2

/-- Extract a standard simple graph from a finite list of darts.
Vertices are represented directly by darts (one dart per node orbit to avoid duplicates). -/
def extractGraph (darts : List D) : Graph D :=
  -- To get unique vertices, we filter darts so we only keep the "canonical" dart for each node orbit.
  -- For simplicity, we just keep all darts but treat adjacencies properly.
  -- Wait, `Graph V` expects a strict list of vertices.
  let rec getCanonicalDarts (remaining : List D) (visited : List D) (acc : List D) : List D :=
    match remaining with
    | [] => acc
    | d :: ds =>
      if visited.contains d then
        getCanonicalDarts ds visited acc
      else
        let orb := orbit H.node d
        getCanonicalDarts ds (orb ++ visited) (d :: acc)
        
  let canonicalDarts := getCanonicalDarts darts [] []
  
  { vertices := canonicalDarts,
    adj := fun d1 d2 => 
      -- Check if any dart in d1's orbit has an edge to any dart in d2's orbit
      let orb1 := orbit H.node d1
      let orb2 := orbit H.node d2
      Id.run do
        let mut adj := false
        for x in orb1 do
          let ex := H.edge.fw x
          if orb2.contains ex then
            adj := true
            break
        return adj
  }

/-- An edge in a hypermap is an isthmus (bridge) if removing it increases the number 
of connected components of the hypermap. 
In hypermap terms, a bridge is an edge where both darts belong to the SAME face orbit! 
If an edge separates two faces, removing it merges them. If an edge is a bridge, it is inside one face. -/
def isBridge (d : D) : Bool :=
  sameFace H d (H.edge.fw d)

/-- A hypermap is bridge-less if it has no bridges. -/
def isBridgeless (darts : List D) : Prop :=
  ∀ d ∈ darts, isBridge H d = false

end Hypermap
end Math
