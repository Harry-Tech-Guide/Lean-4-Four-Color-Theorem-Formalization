
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

def countOrbits (p : Perm D) (fuel : Nat) (l : List D) : Nat :=
  match l with
  | [] => 0
  | d :: ds => 
    let orb := getOrbit p fuel d
    have h_len : (ds.filter (fun x => !(orb.contains x))).length < (d :: ds).length :=
      Nat.lt_succ_of_le (List.length_filter_le _ _)
    1 + countOrbits p fuel (ds.filter (fun x => !(orb.contains x)))
termination_by l.length

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
  getComponentAux H [d] [] fuel

def countComponents (fuel : Nat) (l : List H.Dart) : Nat :=
  match l with
  | [] => 0
  | d :: ds =>
    let comp := getComponent H fuel d
    have h_len : (ds.filter (fun x => !(comp.contains x))).length < (d :: ds).length :=
      Nat.lt_succ_of_le (List.length_filter_le _ _)
    1 + countComponents fuel (ds.filter (fun x => !(comp.contains x)))
termination_by l.length

def isPlanar (fuel : Nat) (darts : List H.Dart) : Bool :=
  let eulerChar := (countOrbits H.node fuel darts : Int) - (countOrbits H.edge fuel darts : Int) + (countOrbits H.face fuel darts : Int)
  eulerChar == 2 * (countComponents H fuel darts : Int)

end Hypermap
