
import FourColorTheorem.Math.Hypermap

-- Step 2: Euler's Formula and Planarity

variable {D : Type} [BEq D]

/-- Compute the orbit of a dart under a permutation by repeatedly applying it. -/
partial def getOrbitAux (p : Perm D) (start current : D) (acc : List D) : List D :=
  let nxt := p.f current
  if nxt == start then current :: acc
  else getOrbitAux p start nxt (current :: acc)

partial def getOrbit (p : Perm D) (d : D) : List D :=
  getOrbitAux p d d []

/-- Count the number of distinct orbits in a list of darts. -/
partial def countOrbits (p : Perm D) (l : List D) : Nat :=
  match l with
  | [] => 0
  | d :: ds => 
    let orb := getOrbit p d
    1 + countOrbits p (ds.filter (fun x => !(orb.contains x)))

namespace Hypermap

variable (H : Hypermap) [BEq H.Dart]

/-- Breadth-first search to find all darts in the same connected component. -/
partial def getComponentAux (queue : List H.Dart) (visited : List H.Dart) : List H.Dart :=
  match queue with
  | [] => visited
  | d :: ds =>
    if visited.contains d then getComponentAux ds visited -- wait this is infinite loop if visited.contains d! Should be getComponentAux ds visited!
    else 
      let n1 := H.edge.f d
      let n2 := H.edge.inv d
      let n3 := H.node.f d
      let n4 := H.node.inv d
      getComponentAux (n1 :: n2 :: n3 :: n4 :: ds) (d :: visited)

partial def getComponent (d : H.Dart) : List H.Dart :=
  getComponentAux H [d] []

/-- Count the number of connected components in the hypermap. -/
partial def countComponents (l : List H.Dart) : Nat :=
  match l with
  | [] => 0
  | d :: ds =>
    let comp := getComponent H d
    1 + countComponents (ds.filter (fun x => !(comp.contains x)))

/-- The Euler characteristic of a hypermap: V - E + F.
    V = number of node orbits (vertices).
    E = number of edge orbits (edges).
    F = number of face orbits (faces). -/
def eulerCharacteristic (darts : List H.Dart) : Int :=
  (countOrbits H.node darts : Int) - (countOrbits H.edge darts : Int) + (countOrbits H.face darts : Int)

/-- A hypermap is planar if and only if it satisfies Euler's formula: V - E + F = 2 * C, 
    where C is the number of connected components. -/
def isPlanar (darts : List H.Dart) : Bool :=
  eulerCharacteristic H darts == 2 * (countComponents H darts : Int)

end Hypermap
