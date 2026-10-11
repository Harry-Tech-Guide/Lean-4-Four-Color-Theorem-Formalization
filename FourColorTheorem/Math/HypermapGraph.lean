import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.Graph
import FourColorTheorem.Math.Planarity

namespace Math
namespace Hypermap

variable (H : Hypermap) [DecidableEq H.Dart]

/-- In a hypermap, a 'Vertex' is uniquely identified by the orbit of its darts under `node`.
Two darts represent the same vertex if they are in the same node orbit. -/
def sameVertex (d1 d2 : H.Dart) (fuel : Nat := 1000) : Bool :=
  (getOrbit H.node fuel d1).contains d2

/-- Two darts represent the same face if they are in the same face orbit. -/
def sameFace (d1 d2 : H.Dart) (fuel : Nat := 1000) : Bool :=
  (getOrbit H.face fuel d1).contains d2

/-- Two darts are adjacent if the edge permutation of one is in the node orbit of the other. -/
def areAdjacentDarts (d1 d2 : H.Dart) (fuel : Nat := 1000) : Bool :=
  sameVertex H (H.edge.f d1) d2 fuel

/-- Extract a standard simple graph from a finite list of darts.
Vertices are represented directly by darts (one canonical dart per node orbit). -/
def extractGraph (darts : List H.Dart) (fuel : Nat := darts.length) : Graph H.Dart :=
  let rec getCanonicalDarts (remaining : List H.Dart) (visited : List H.Dart) (acc : List H.Dart) : List H.Dart :=
    match remaining with
    | [] => acc
    | d :: ds =>
      if visited.contains d then
        getCanonicalDarts ds visited acc
      else
        let orb := getOrbit H.node fuel d
        getCanonicalDarts ds (orb ++ visited) (d :: acc)
        
  let canonicalDarts := getCanonicalDarts darts [] []
  
  { vertices := canonicalDarts,
    adj := fun d1 d2 => 
      let orb1 := getOrbit H.node fuel d1
      let orb2 := getOrbit H.node fuel d2
      Id.run do
        let mut adj := false
        for x in orb1 do
          let ex := H.edge.f x
          if orb2.contains ex then
            adj := true
            break
        return adj
  }

/-- An edge in a hypermap is an isthmus (bridge) if removing it increases the number 
of connected components of the hypermap. 
In hypermap terms, a bridge is an edge where both darts belong to the SAME face orbit! -/
def isBridge (d : H.Dart) (fuel : Nat := 1000) : Bool :=
  sameFace H d (H.edge.f d) fuel

/-- A hypermap is bridge-less if it has no bridges. -/
def isBridgeless (darts : List H.Dart) (fuel : Nat := darts.length) : Prop :=
  ∀ d ∈ darts, isBridge H d fuel = false

end Hypermap
end Math
