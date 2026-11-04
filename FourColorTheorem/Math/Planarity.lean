import FourColorTheorem.Math.Hypermap

-- Step 2: Euler's Formula and Planarity

variable {D : Type} [BEq D]

def getOrbitAux (p : Perm D) (start current : D) (acc : List D) (fuel : Nat) : List D :=
  match fuel with
  | 0 => current :: acc
  | fuel' + 1 =>
    let nxt := p.f current
    if nxt == start then current :: acc
    else getOrbitAux p start nxt (current :: acc) fuel'

def getOrbit (p : Perm D) (fuel : Nat) (d : D) : List D :=
  getOrbitAux p d d [] fuel

def countOrbitsAux (p : Perm D) (fuel : Nat) : Nat → List D → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | steps + 1, d :: ds =>
    let orb := getOrbit p fuel d
    1 + countOrbitsAux p fuel steps (ds.filter (fun x => !(orb.contains x)))

def countOrbits (p : Perm D) (fuel : Nat) (l : List D) : Nat :=
  countOrbitsAux p fuel l.length l

namespace Hypermap

variable (H : Hypermap) [BEq H.Dart]

def getComponentAux (queue : List H.Dart) (visited : List H.Dart) (fuel : Nat) : List H.Dart :=
  match fuel with
  | 0 => visited
  | fuel' + 1 =>
    match queue with
    | [] => visited
    | d :: ds =>
      if visited.contains d then getComponentAux ds visited fuel'
      else 
        let n1 := H.edge.f d
        let n2 := H.edge.inv d
        let n3 := H.node.f d
        let n4 := H.node.inv d
        getComponentAux (n1 :: n2 :: n3 :: n4 :: ds) (d :: visited) fuel'

def getComponent (fuel : Nat) (d : H.Dart) : List H.Dart :=
  getComponentAux H [d] [] (5 * fuel + 1)

def countComponentsAux (fuel : Nat) : Nat → List H.Dart → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | steps + 1, d :: ds =>
    let comp := getComponent H fuel d
    1 + countComponentsAux fuel steps (ds.filter (fun x => !(comp.contains x)))

def countComponents (fuel : Nat) (l : List H.Dart) : Nat :=
  countComponentsAux H fuel l.length l

def isPlanar (fuel : Nat) (darts : List H.Dart) : Bool :=
  let eulerChar := (countOrbits H.node fuel darts : Int) - (countOrbits H.edge fuel darts : Int) + (countOrbits H.face fuel darts : Int)
  eulerChar == 2 * (countComponents H fuel darts : Int)

end Hypermap
