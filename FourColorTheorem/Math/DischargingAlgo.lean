import FourColorTheorem.Math.Rules
import FourColorTheorem.Math.ProofTree
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.PrecomputedConfMats
import FourColorTheorem.Math.PrecomputedOutlets
import FourColorTheorem.Math.PrecomputedHints7
import FourColorTheorem.Math.PrecomputedHints8
import FourColorTheorem.Math.PrecomputedHints9
import FourColorTheorem.Math.PrecomputedHints10
import FourColorTheorem.Math.PrecomputedHints11

namespace Math.Discharging

def CARTVERT := 62

def emptyAdjMat : Array (Array Int) :=
  mkArray CARTVERT (mkArray CARTVERT (-1))

def setAdjMat (adj : Array (Array Int)) (u v : Nat) (w : Int) : Array (Array Int) :=
  if u < CARTVERT && v < CARTVERT then
    adj.set! u ((adj.get! u).set! v w)
  else
    adj

def doFan (deg : Nat) (i : Nat) (k : Nat) (adj : Array (Array Int)) : Array (Array Int) :=
  let a := if i == 1 then 2 * deg else deg + i - 1
  let b := deg + i
  if k == 5 then
    let adj := setAdjMat adj i a (b : Int)
    let adj := setAdjMat adj a b (i : Int)
    let adj := setAdjMat adj b i (a : Int)
    adj
  else
    let c := 2 * deg + i
    let adj := setAdjMat adj i a (c : Int)
    let adj := setAdjMat adj a c (i : Int)
    let adj := setAdjMat adj c i (a : Int)
    if k == 6 then
      let adj := setAdjMat adj i c (b : Int)
      let adj := setAdjMat adj c b (i : Int)
      let adj := setAdjMat adj b i (c : Int)
      adj
    else
      let d := 3 * deg + i
      let adj := setAdjMat adj i c (d : Int)
      let adj := setAdjMat adj c d (i : Int)
      let adj := setAdjMat adj d i (c : Int)
      if k == 7 then
        let adj := setAdjMat adj i d (b : Int)
        let adj := setAdjMat adj d b (i : Int)
        let adj := setAdjMat adj b i (d : Int)
        adj
      else
        let e := 4 * deg + i
        let adj := setAdjMat adj i d (e : Int)
        let adj := setAdjMat adj d e (i : Int)
        let adj := setAdjMat adj e i (d : Int)
        let adj := setAdjMat adj i e (b : Int)
        let adj := setAdjMat adj e b (i : Int)
        let adj := setAdjMat adj b i (e : Int)
        adj

def getAdjMat (upp : Array Nat) : Array (Array Int) := Id.run do
  let deg := upp[0]!
  let mut adj := emptyAdjMat
  for i in [1 : deg + 1] do
    let h := if i == 1 then deg else i - 1
    adj := setAdjMat adj 0 h (i : Int)
    adj := setAdjMat adj i 0 (h : Int)
    adj := setAdjMat adj h i (0 : Int)
    let a := deg + h
    adj := setAdjMat adj i h (a : Int)
    adj := setAdjMat adj a i (h : Int)
    adj := setAdjMat adj h a (i : Int)
    if upp[i]! < 9 then
      adj := doFan deg i upp[i]! adj
  return adj

structure Outlet where
  number : Int
  nolines : Nat
  value : Int
  pos : Array Nat
  low : Array Nat
  upp : Array Nat
  deriving Repr, BEq

instance : Inhabited Outlet := ⟨{ number := 0, nolines := 0, value := 0, pos := #[], low := #[], upp := #[] }⟩

def doOutlet (deg : Nat) (number : Int) (X Y : Array Nat) (z : Array Nat) (b : Array (Nat × Nat)) : Option Outlet := Id.run do
  let mut adj := getAdjMat (mkArray (5 * deg + 2) 12 |>.set! 0 deg)
  let n := z.size
  let mut phi : Array Int := mkArray 17 (-1)
  let mut value := 1
  let mut k := 1
  if number > 0 then
    phi := phi.set! 0 1
    phi := phi.set! 1 0
    value := 1
    k := 1
  else
    phi := phi.set! 0 0
    phi := phi.set! 1 1
    value := -1
    k := 0
  
  let mut posArr : Array Nat := #[]
  let mut lowArr : Array Nat := #[]
  let mut uppArr : Array Nat := #[]
  
  posArr := posArr.push 1
  
  let mut i := 0
  for j in [0 : n] do
    let low1 := b[j]!.1
    let mut upp1 := b[j]!.2
    if upp1 == 9 then upp1 := 12
    let low2 := if low1 == 0 then upp1 else low1
    
    if low2 > upp1 then return none
    if low2 < 5 || low2 > 9 || upp1 > 12 || upp1 == 9 then return none
    
    if j == k then
      if low2 > deg || upp1 < deg then return none
      continue
    
    let mut pos_i : Nat := 0
    if j >= 2 then
      let u := phi[X[z[j]!]!]!
      let v := phi[Y[z[j]!]!]!
      if u < 0 || u > 5 * deg || v < 0 || v > 5 * deg then return none
      pos_i := adj[u.toNat]![v.toNat]!.toNat
      phi := phi.set! z[j]! pos_i
    else
      pos_i := 1

    lowArr := lowArr.push low2
    uppArr := uppArr.push upp1
    if i > 0 then
      posArr := posArr.push pos_i
    else
      posArr := posArr.set! 0 pos_i

    if pos_i <= deg && low2 == upp1 then
      adj := doFan deg pos_i low2 adj
    
    i := i + 1

  return some {
    number := number,
    nolines := i,
    value := value,
    pos := posArr,
    low := lowArr,
    upp := uppArr
  }


def readOutlets (deg : Nat) (rules : List RawRule) : Array Outlet := Id.run do
  let mut outs : Array Outlet := #[]
  for r in rules do
    let mut z := #[0, 1]
    let mut b := #[r.b0, r.b1]
    for (node, bounds) in r.triples do
      z := z.push node
      b := b.push bounds
    
    if let some o := doOutlet deg r.num U V z b then outs := outs.push o
    if let some o := doOutlet deg (- (r.num : Int)) U V z b then outs := outs.push o

    if r.invert then
      let inv_num := r.num + 1
      if let some o := doOutlet deg inv_num V U z b then outs := outs.push o
      if let some o := doOutlet deg (- (inv_num : Int)) V U z b then outs := outs.push o

  return outs

def shiftPos (p x deg : Nat) : Nat :=
  let r := (p - 1) % deg
  if x - 1 + r < deg then
    p + x - 1
  else
    p + x - 1 - deg

structure PosOut where
  T : Outlet
  x : Nat
  deriving Repr, BEq

instance : Inhabited PosOut := ⟨{ T := default, x := 0 }⟩

def outletForced (A_low A_upp : Array Nat) (T : Outlet) (x deg : Nat) : Bool := Id.run do
  for i in [0 : T.nolines] do
    let p := shiftPos T.pos[i]! x deg
    if T.low[i]! > A_low[p]! || T.upp[i]! < A_upp[p]! then
      return false
  return true

def outletPermitted (A_low A_upp : Array Nat) (T : Outlet) (x deg : Nat) : Bool := Id.run do
  for i in [0 : T.nolines] do
    let p := shiftPos T.pos[i]! x deg
    if T.low[i]! > A_upp[p]! || T.upp[i]! < A_low[p]! then
      return false
  return true

/-- Evaluates whether an outlet is forced under reflection in the dihedral group D_{2 * deg}. -/
def reflForced (A_low A_upp : Array Nat) (T : Outlet) (x deg : Nat) : Bool := Id.run do
  let x_shift := x - 1
  for i in [0 : T.nolines] do
    let p0 := T.pos[i]!
    let p := if x_shift + (p0 - 1) % deg < deg then p0 + x_shift else p0 + x_shift - deg
    if p < 1 || p > 2 * deg then
      return false
    let q :=
      if p <= deg then deg - p + 1
      else if p < 2 * deg then 3 * deg - p
      else 2 * deg
    if T.low[i]! > A_low[q]! || T.upp[i]! < A_upp[q]! then
      return false
  return true


def isAdj (adjmat : Array (Array Int)) (u w : Nat) : Bool :=
  if u < CARTVERT && w < CARTVERT then
    adjmat[u]![w]! != -1 || adjmat[w]![u]! != -1
  else false

def getNeighbors (adjmat : Array (Array Int)) (u : Nat) : List Nat :=
  (List.range CARTVERT).filter (fun v => isAdj adjmat u v)

def getDegree (c : Configuration) (v : Nat) : Nat :=
  (List.range (c.ringSize + c.interiorSize)).filter (fun u => c.adj v u) |>.length

structure IsoState where
  c : Configuration
  adjmat : Array (Array Int)
  adjBool : Array UInt64
  low : Array Nat
  upp : Array Nat
  mapping : Array Nat
  used : Array Bool
  degrees : Array Nat

def getAdjBool (adjmat : Array (Array Int)) : Array UInt64 := Id.run do
  let mut arr : Array UInt64 := mkArray CARTVERT (0 : UInt64)
  for u in [0 : CARTVERT] do
    let mut bits : UInt64 := 0
    for w in [0 : CARTVERT] do
      if adjmat[u]![w]! != -1 || adjmat[w]![u]! != -1 then
        bits := bits ||| ((1 : UInt64) <<< w.toUInt64)
    arr := arr.set! u bits
  return arr

def isWellPositioned (deg : Nat) (used : Array Bool) : Bool := Id.run do
  let mut ok := true
  for j in [1 : deg + 1] do
    let w1 := j
    let w2 := deg + j
    let w3 := if j == 1 then 2 * deg else deg + j - 1
    if not used[w1]! && used[w2]! && used[w3]! then
      ok := false
      break
  return ok

structure ConfMat where
  nverts : Nat
  ring : Nat
  mat : Array (Array Nat)
  deriving Repr, BEq

instance : Inhabited ConfMat := ⟨{ nverts := 0, ring := 0, mat := #[] }⟩

structure Query where
  u : Int
  v : Int
  z : Nat
  xi : Nat
  deriving Repr, BEq, Inhabited

def parseNatList (s : String) : List Nat :=
  (s.split (fun ch => ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t')).filterMap (fun x => 
    if x == "" then none else x.toNat?)

def parseConfMat (s : String) : ConfMat := Id.run do
  let nums := parseNatList s
  if nums.length >= 2 then
    let nverts := nums[0]!
    let ring := nums[1]!
    let a := nums.getD 4 0
    let mut idx := 5 + 2 * a
    let mut mat : Array (Array Nat) := mkArray (nverts + 1) #[]
    mat := mat.set! 0 #[nverts, ring]
    for _ in [0:nverts] do
      if idx < nums.length then
        let v := nums[idx]!
        idx := idx + 1
        if idx < nums.length then
          let degree := nums[idx]!
          idx := idx + 1
          let mut row := #[degree]
          for _ in [0:degree] do
            if idx < nums.length then
              let nb := nums[idx]!
              idx := idx + 1
              row := row.push nb
          mat := mat.set! v row
    return { nverts := nverts, ring := ring, mat := mat }
  else
    return { nverts := 0, ring := 0, mat := #[] }

def getQuestion (L : ConfMat) : Array Query := Id.run do
  let nverts := L.mat[0]![0]!
  let ring := L.mat[0]![1]!
  let mut found := mkArray (nverts + 1) false
  
  let mut maxDeg := 0
  let mut best := 0
  for v in [ring + 1 : nverts + 1] do
    let d := L.mat[v]![0]!
    if d > maxDeg then
      maxDeg := d
      best := v
      
  let q0 : Query := { u := 0, v := 0, z := best, xi := L.mat[best]![0]! }
  found := found.set! best true
  
  let mut maxSecond := 0
  let mut secondbest := 0
  let bestDeg := L.mat[best]![0]!
  for i in [1 : bestDeg + 1] do
    let v := L.mat[best]![i]!
    if v <= ring then continue
    let d := L.mat[v]![0]!
    if d > maxSecond then
      maxSecond := d
      secondbest := v
      
  let q1 : Query := { u := (nverts : Int), v := (ring : Int), z := secondbest, xi := L.mat[secondbest]![0]! }
  found := found.set! secondbest true
  
  let mut Q : Array Query := #[q0, q1]
  let mut search := 0
  
  while search < Q.size do
    let v := Q[search]!.z
    search := search + 1
    if v <= ring then continue
    
    let d := L.mat[v]![0]!
    let mut i := 1
    while i <= d && not found[L.mat[v]![i]!]! do
      i := i + 1
      
    let mut h := if i == 1 then d else i - 1
    while h != i do
      let u := L.mat[v]![h]!
      if u <= ring then break
      if not found[u]! then
        let nb_h1 := L.mat[v]![if h == d then 1 else h + 1]!
        let q : Query := {
          z := u,
          xi := if u > ring then L.mat[u]![0]! else 0,
          u := (nb_h1 : Int),
          v := (v : Int)
        }
        Q := Q.push q
        found := found.set! u true
      h := if h == 1 then d else h - 1
      
    if h == i then
      continue
      
    let mut j := if i == d then 1 else i + 1
    while true do
      let w := L.mat[v]![j]!
      if w <= ring then break
      if not found[w]! then
        let nb_j_prev := L.mat[v]![if j == 1 then d else j - 1]!
        let q : Query := {
          z := w,
          xi := if w > ring then L.mat[w]![0]! else 0,
          u := (v : Int),
          v := (nb_j_prev : Int)
        }
        Q := Q.push q
        found := found.set! w true
      j := if j == d then 1 else j + 1
      
    let r := if h >= j then h - j else h + d - j
    if r > 2 then
      let u := L.mat[v]![h]!
      let nb_h1 := L.mat[v]![if h == d then 1 else h + 1]!
      let q : Query := {
        z := u,
        xi := if u > ring then L.mat[u]![0]! else 0,
        u := (nb_h1 : Int),
        v := (v : Int)
      }
      Q := Q.push q
      
      let mut g := if h == 1 then d else h - 1
      while g != j do
        let t := L.mat[v]![g]!
        let prev_z := Q[Q.size - 1]!.z
        let q_t : Query := {
          z := t,
          xi := if t > ring then L.mat[t]![0]! else 0,
          u := (prev_z : Int),
          v := (v : Int)
        }
        Q := Q.push q_t
        found := found.set! t true
        g := if g == 1 then d else g - 1

  Q := Q.push { u := -1, v := 0, z := 0, xi := 0 }
  return Q

def addToList (edges : Array (Array (Array (Nat × Nat)))) (u v : Nat) (upp : Array Nat) : Array (Array (Array (Nat × Nat))) := Id.run do
  let a := upp[u]!
  let b := upp[v]!
  let mut res := edges
  if a >= b && b <= 8 && a <= 11 && (a <= 8 || u == 0) then
    let cur := res[a]![b]!
    res := res.set! a (res[a]!.set! b (cur.push (u, v)))
  if b >= a && a <= 8 && b <= 11 && (b <= 8 || v == 0) then
    let cur := res[b]![a]!
    res := res.set! b (res[b]!.set! a (cur.push (v, u)))
  return res

def getEdgelist (A_low A_upp : Array Nat) : Array (Array (Array (Nat × Nat))) := Id.run do
  let deg := A_upp[0]!
  let mut edges : Array (Array (Array (Nat × Nat))) := mkArray 12 (mkArray 12 #[])
  for i in [1 : deg + 1] do
    edges := addToList edges 0 i A_upp
    let h := if i == 1 then deg else i - 1
    edges := addToList edges i h A_upp
    let a := deg + h
    let b := deg + i
    edges := addToList edges i a A_upp
    edges := addToList edges i b A_upp
    if A_low[i]! != A_upp[i]! then continue
    if A_upp[i]! == 5 then
      edges := addToList edges a b A_upp
      continue
    let c := 2 * deg + i
    edges := addToList edges a c A_upp
    edges := addToList edges i c A_upp
    if A_upp[i]! == 6 then
      edges := addToList edges b c A_upp
      continue
    let d := 3 * deg + i
    edges := addToList edges c d A_upp
    edges := addToList edges i d A_upp
    if A_upp[i]! == 7 then
      edges := addToList edges b d A_upp
      continue
    if A_upp[i]! == 8 then
      let e := 4 * deg + i
      edges := addToList edges d e A_upp
      edges := addToList edges i e A_upp
      edges := addToList edges b e A_upp
  return edges

def rootedSubConf (degree : Array Nat) (adjmat : Array (Array Int))
    (q : Array Query) (x y : Nat) (clockwise : Bool) : Option (Array Int) := Id.run do
  let deg := degree[0]!
  let mut used := mkArray CARTVERT false
  let mut image := mkArray CARTVERT (-1 : Int)
  image := image.set! 0 (if clockwise then 1 else 0)
  image := image.set! q[0]!.z (x : Int)
  image := image.set! q[1]!.z (y : Int)
  used := used.set! x true
  used := used.set! y true
  
  for k in [2 : q.size] do
    let item := q[k]!
    if item.u < 0 then break
    let u_img := image[item.u.toNat]!
    let v_img := image[item.v.toNat]!
    if u_img < 0 || v_img < 0 then return none
    let (row, col) := if clockwise then (u_img.toNat, v_img.toNat) else (v_img.toNat, u_img.toNat)
    let w := adjmat[row]![col]!
    if w == -1 then return none
    let wNat := w.toNat
    if item.xi != 0 && item.xi != degree[wNat]! then return none
    if used[wNat]! then return none
    image := image.set! item.z w
    used := used.set! wNat true

  for j in [1 : deg + 1] do
    let w1 := j
    let w2 := deg + j
    let w3 := if j == 1 then 2 * deg else deg + j - 1
    if not used[w1]! && used[w2]! && used[w3]! then
      return none
      
  return some image

def subConf (adjmat : Array (Array Int)) (degree : Array Nat)
    (q : Array Query) (edgelist : Array (Array (Array (Nat × Nat)))) : Option (Array Int) := Id.run do
  let xi0 := q[0]!.xi
  let xi1 := q[1]!.xi
  if xi0 >= edgelist.size || xi1 >= edgelist[xi0]!.size then return none
  let pairs := edgelist[xi0]![xi1]!
  for (x, y) in pairs do
    if let some img := rootedSubConf degree adjmat q x y true then
      return some img
    if let some img := rootedSubConf degree adjmat q x y false then
      return some img
  return none

def checkIso (L : ConfMat) (A_low A_upp : Array Nat) (image : Array Int) (adjmat : Array (Array Int)) : Bool := Id.run do
  let deg := A_low[0]!
  let verts := L.mat[0]![0]!
  let ring := L.mat[0]![1]!
  
  let mut X : Array (Array Nat) := mkArray CARTVERT (mkArray CARTVERT 0)
  let mut used : Array Bool := mkArray CARTVERT false
  
  for u in [ring + 1 : verts + 1] do
    let fu := image[u]!
    if fu < 0 || fu > (5 * deg : Int) then return false
    let fuNat := fu.toNat
    if used[fuNat]! then return false
    used := used.set! fuNat true
    if L.mat[u]![0]! != A_upp[fuNat]! then return false
    if fuNat > 2 * deg then
      let i := (fuNat - 1) % deg + 1
      if A_low[i]! != A_upp[i]! || A_low[i]! < (fuNat - 1) / deg + 4 then
        return false

  for i in [1 : deg + 1] do
    let w1 := i
    let w2 := deg + i
    let w3 := if i == 1 then 2 * deg else deg + i - 1
    if not used[w1]! && used[w2]! && used[w3]! then
      return false

  for u in [ring + 1 : verts + 1] do
    let d := L.mat[u]![0]!
    let mut worried := if L.mat[u]![d]! > ring then false else true
    for i in [1 : d + 1] do
      let v := L.mat[u]![i]!
      if v <= ring then
        worried := true
        continue
      let (x, y) := if image[0]! != 0 then
        (image[u]!.toNat, image[v]!.toNat)
      else
        (image[v]!.toNat, image[u]!.toNat)
      X := X.set! x (X[x]!.set! y 1)
      let w := L.mat[u]![if i < d then i + 1 else 1]!
      if w <= ring then
        if worried then return false
        continue
      worried := false
      if adjmat[x]![y]! != image[w]! then
        return false

  let induCheck (aa bb : Bool) (cc : Nat) : Bool :=
    if aa && bb && cc != 1 then false else true

  for i in [1 : deg + 1] do
    if not (induCheck used[0]! used[i]! X[0]![i]!) then return false
    let h := if i == 1 then deg else i - 1
    if not (induCheck used[h]! used[i]! X[h]![i]!) then return false
    let a := h + deg
    if not (induCheck used[h]! used[a]! X[h]![a]!) then return false
    if not (induCheck used[i]! used[a]! X[i]![a]!) then return false
    if A_low[i]! != A_upp[i]! then continue
    let b := deg + i
    if A_low[i]! == 5 then
      if not (induCheck used[a]! used[b]! X[a]![b]!) then return false
      continue
    let c := 2 * deg + i
    if not (induCheck used[a]! used[c]! X[a]![c]!) then return false
    if not (induCheck used[c]! used[i]! X[c]![i]!) then return false
    if A_low[i]! == 6 then
      if not (induCheck used[c]! used[b]! X[c]![b]!) then return false
      continue
    let d := 3 * deg + i
    if not (induCheck used[c]! used[d]! X[c]![d]!) then return false
    if not (induCheck used[d]! used[i]! X[d]![i]!) then return false
    if A_low[i]! == 7 then
      if not (induCheck used[d]! used[b]! X[d]![b]!) then return false
      continue
    let e := 4 * deg + i
    if A_low[i]! != 8 then return false
    if not (induCheck used[e]! used[d]! X[e]![d]!) then return false
    if not (induCheck used[e]! used[i]! X[e]![i]!) then return false
    if not (induCheck used[e]! used[b]! X[e]![b]!) then return false

  return true

def theConfMats : Array ConfMat :=
  (Math.u633_data.split (fun x => x == '|') |>.filter (· != "")).map parseConfMat |>.toArray

def theQuestions : Array (Array Query) :=
  theConfMats.map getQuestion

partial def reduceAxle (A_low A_upp : Array Nat) : Bool := Id.run do
  let mut stack : List (Array Nat × Array Nat) := [(A_low, A_upp)]
  while not stack.isEmpty do
    let (cur_low, cur_upp) := stack.head!
    stack := stack.tail!
    let adjmat := getAdjMat cur_upp
    let edgelist := getEdgelist cur_low cur_upp
    
    let mut found_h := none
    for h in [0 : theConfMats.size] do
      if let some img := subConf adjmat cur_upp theQuestions[h]! edgelist then
        found_h := some (h, img)
        break
        
    match found_h with
    | none => return false
    | some (h, img) =>
      let c := theConfMats[h]!
      if not (checkIso c cur_low cur_upp img adjmat) then
        return false
      let redverts := c.nverts
      let redring := c.ring
      for i in [redring + 1 : redverts + 1] do
        let v := img[i]!.toNat
        if cur_low[v]! < cur_upp[v]! then
          let next_upp := cur_upp.set! v (cur_upp[v]! - 1)
          stack := (cur_low, next_upp) :: stack
          
  return true

def isReducible (_configs : List Configuration) (A_low A_upp : Array Nat) (_adjmat : Array (Array Int)) (_adjBool : Array UInt64) : Bool :=
  reduceAxle A_low A_upp

partial def checkBound (configs : List Configuration) (deg : Nat) (A_low A_upp : Array Nat) (posout : Array PosOut) (s : Array Int) (maxch : Int) (pos : Nat) (adjmat : Array (Array Int)) (adjBool : Array UInt64) : Bool := Id.run do
  let mut forcedch := 0
  let mut allowedch := 0
  let mut s_curr := s

  for i in [0 : posout.size] do
    let po := posout[i]!
    if s_curr[i]! > 0 then
      forcedch := forcedch + po.T.value
    else if s_curr[i]! == 0 then
      if outletForced A_low A_upp po.T po.x deg then
        s_curr := s_curr.set! i 1
        forcedch := forcedch + po.T.value
      else if not (outletPermitted A_low A_upp po.T po.x deg) then
        s_curr := s_curr.set! i (-1)
      else if po.T.value > 0 then
        allowedch := allowedch + po.T.value

  if forcedch + allowedch <= maxch then
    return true
  
  if forcedch > maxch then
    let res := isReducible configs A_low A_upp adjmat adjBool
    if not res then dbg_trace "Failure in isReducible"
    return res

  for curr_pos in [pos : posout.size] do
    if s_curr[curr_pos]! == 0 && posout[curr_pos]!.T.value > 0 then
      let po := posout[curr_pos]!
      let x := po.x
      
      let mut AA_low := A_low
      let mut AA_upp := A_upp
      for i in [0 : po.T.nolines] do
        let p := shiftPos po.T.pos[i]! x deg
        if po.T.low[i]! > AA_low[p]! then
          AA_low := AA_low.set! p po.T.low[i]!
        if po.T.upp[i]! < AA_upp[p]! then
          AA_upp := AA_upp.set! p po.T.upp[i]!
      
      let mut good := true
      for i in [0 : curr_pos] do
        if s_curr[i]! == -1 && outletForced AA_low AA_upp posout[i]!.T posout[i]!.x deg then
          good := false
          break
      
      if good then
        let mut s_prime := s_curr
        s_prime := s_prime.set! curr_pos 1
        if not (checkBound configs deg AA_low AA_upp posout s_prime maxch (curr_pos + 1) adjmat adjBool) then
          return false
      
      s_curr := s_curr.set! curr_pos (-1)
      allowedch := allowedch - po.T.value
      if allowedch + forcedch <= maxch then
        return true

  return false

/-- Create a symmetry outlet from active condition stack if all vertices are non-fan vertices. -/
def makeSymOutlet (lineno : Nat) (deg : Nat) (conds : List (Nat × Int)) : Option Outlet :=
  if conds.all (fun (n, _) => 1 <= n && n <= 2 * deg) then
    let condArr := conds.toArray
    let pos := condArr.map (·.1)
    let low := condArr.map (fun (_, m) => if m > 0 then m.toNat else 5)
    let upp := condArr.map (fun (_, m) => if m > 0 then 100 else (-m).toNat)
    some {
      number := (lineno : Int),
      nolines := conds.length,
      value := 1,
      pos := pos,
      low := low,
      upp := upp
    }
  else
    none

/-- Verify symmetry line using rotational (eps = 0) or reflectional (eps = 1) check. -/
def checkSymmetry (A_low A_upp : Array Nat) (deg : Nat) (k eps lev line : Nat) (syms : Array Outlet) : Bool :=
  if k >= deg || eps > 1 then
    false
  else
    match syms.find? (fun o => o.number == (line : Int)) with
    | some T =>
      if T.nolines != lev + 1 then
        false
      else if eps == 0 then
        outletForced A_low A_upp T (k + 1) deg
      else
        reflForced A_low A_upp T (k + 1) deg
    | none =>
      false

partial def verifyTreeAux (configs : List Configuration) (deg : Nat) (A_low A_upp : Array Nat)
    (t : ProofTree) (outs : Array Outlet) (lineno : Nat) (lev : Nat)
    (condStack : Array (Nat × Int)) (syms : Array Outlet) :
    Bool × Nat × Array (Nat × Int) × Array Outlet :=
  match t with
  | ProofTree.reduce =>
    let res := isReducible configs A_low A_upp (getAdjMat A_upp) (getAdjBool (getAdjMat A_upp))
    (res, lineno + 1, condStack, syms)
  | ProofTree.hubcap members => Id.run do
    let adjmat := getAdjMat A_upp
    let adjBool := getAdjBool adjmat
    let mut ok := true
    for (x, y, v) in members do
      let mut posout : Array PosOut := #[]
      for o in outs do
        posout := posout.push { T := o, x := x }
      if x != y then
        for o in outs do
          posout := posout.push { T := o, x := y }
      let s := mkArray posout.size 0
      if not (checkBound configs deg A_low A_upp posout s v 0 adjmat adjBool) then
        ok := false
        break
    return (ok, lineno + 1, condStack, syms)
  | ProofTree.sym k eps lev_in line =>
    let ok := checkSymmetry A_low A_upp deg k eps lev_in line syms
    (ok, lineno + 1, condStack, syms)
  | ProofTree.cond v m trueBranch falseBranch => Id.run do
    let (AA_low_true, AA_upp_true, AA_low_false, AA_upp_false) :=
      if m > 0 then
        (A_low.set! v m.toNat, A_upp, A_low, A_upp.set! v (m.toNat - 1))
      else
        (A_low, A_upp.set! v (-m).toNat, A_low.set! v (1 - m).toNat, A_upp)

    let good := (List.range (lev + 1)).all fun i =>
      let n := condStack[i]!.1
      1 <= n && n <= 2 * deg

    let syms' := if good then
      let pos := (List.range (lev + 1)).map (fun i => condStack[i]!.1) |>.toArray
      let low := (List.range (lev + 1)).map (fun i => if condStack[i]!.2 > 0 then condStack[i]!.2.toNat else 5) |>.toArray
      let upp := (List.range (lev + 1)).map (fun i => if condStack[i]!.2 > 0 then 12 else (-condStack[i]!.2).toNat) |>.toArray
      syms.push {
        number := (lineno : Int),
        nolines := lev + 1,
        value := 1,
        pos := pos,
        low := low,
        upp := upp
      }
    else
      syms

    let condStack_true := condStack.set! lev (v, m) |>.set! (lev + 1) (0, 0)
    let (bTrue, next_lineno, condStack_after_true, syms_after_true) :=
      verifyTreeAux configs deg AA_low_true AA_upp_true trueBranch outs (lineno + 1) (lev + 1) condStack_true syms'
    if not bTrue then
      return (false, next_lineno, condStack_after_true, syms_after_true)

    -- Pop back to lev: delete symmetries with nolines - 1 > lev (keep nolines - 1 <= lev for siblings)
    let syms_popped := syms_after_true.filter (fun o => o.nolines - 1 <= lev)
    let (bFalse, final_lineno, condStack_after_false, syms_after_false) :=
      verifyTreeAux configs deg AA_low_false AA_upp_false falseBranch outs next_lineno lev condStack_after_true syms_popped
    let syms_final := syms_after_false.filter (fun o => o.nolines - 1 < lev)
    return (bFalse, final_lineno, condStack_after_false, syms_final)

/-- Top-level proof tree verifier tracking line numbering and symmetry outlets in preorder traversal. -/
def getUpp (deg : Nat) (st : Nat) (p : Nat) : Nat :=
  if Nat.beq p 0 then deg
  else
    let m := getLaneNat st p
    if Nat.ble 16 m then 12
    else if Nat.ble 8 m then 8
    else if Nat.ble 4 m then 7
    else if Nat.ble 2 m then 6
    else 5

def getExactDeg (deg : Nat) (st : Nat) (p : Nat) : Nat :=
  if Nat.beq p 0 then deg
  else
    let m := getLaneNat st p
    if Nat.beq m 1 then 5
    else if Nat.beq m 2 then 6
    else if Nat.beq m 4 then 7
    else if Nat.beq m 8 then 8
    else 0

def fanTri63 (x y z u v : Nat) : Nat :=
  if Nat.beq u x && Nat.beq v y then z
  else if Nat.beq u y && Nat.beq v z then x
  else if Nat.beq u z && Nat.beq v x then y
  else 63

def cartAdjSpoke (deg : Nat) (st : Nat) (i u v : Nat) : Nat :=
  let k := getUpp deg st i
  let h := if Nat.beq i 1 then deg else Nat.sub i 1
  let r1 := fanTri63 0 h i u v
  if !Nat.beq r1 63 then r1
  else
    let a := Nat.add deg h
    let r2 := fanTri63 i h a u v
    if !Nat.beq r2 63 then r2
    else if Nat.ble 9 k then 63
    else
      let b := Nat.add deg i
      if Nat.beq k 5 then fanTri63 i a b u v
      else
        let c := Nat.add (Nat.mul 2 deg) i
        let r3 := fanTri63 i a c u v
        if !Nat.beq r3 63 then r3
        else if Nat.beq k 6 then fanTri63 i c b u v
        else
          let d := Nat.add (Nat.mul 3 deg) i
          let r4 := fanTri63 i c d u v
          if !Nat.beq r4 63 then r4
          else if Nat.beq k 7 then fanTri63 i d b u v
          else
            let e := Nat.add (Nat.mul 4 deg) i
            let r5 := fanTri63 i d e u v
            if !Nat.beq r5 63 then r5
            else fanTri63 i e b u v

def cartAdj (deg : Nat) (st : Nat) (u v : Nat) : Nat :=
  if Nat.beq u 0 then
    if Nat.ble 1 v && Nat.ble v deg then
      if Nat.beq v deg then 1 else Nat.add v 1
    else 63
  else
    let i1 := Nat.add (Nat.mod (Nat.sub u 1) deg) 1
    let w1 := cartAdjSpoke deg st i1 u v
    if !Nat.beq w1 63 then w1
    else
      let i2 := if Nat.beq i1 deg then 1 else Nat.add i1 1
      cartAdjSpoke deg st i2 u v

def checkSpokeMask (deg : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | j + 1, usedMask =>
    let w1 := Nat.add j 1
    let w2 := Nat.add deg w1
    let w3 := if Nat.beq w1 1 then Nat.mul 2 deg else Nat.sub (Nat.add deg w1) 1
    if Nat.beq (Nat.land (Nat.shiftRight usedMask w1) 1) 0 &&
       !Nat.beq (Nat.land (Nat.shiftRight usedMask w2) 1) 0 &&
       !Nat.beq (Nat.land (Nat.shiftRight usedMask w3) 1) 0 then
      false
    else
      checkSpokeMask deg j usedMask

def evalQSteps (deg : Nat) (st : Nat) (cw : Bool) : List QStep → Nat → Nat → Option (Nat × Nat)
  | [], img, usedMask => some (img, usedMask)
  | step :: rest, img, usedMask =>
    let u_img := getImgNat img step.u
    let v_img := getImgNat img step.v
    if Nat.beq u_img 63 || Nat.beq v_img 63 then none
    else
      let row := if cw then u_img else v_img
      let col := if cw then v_img else u_img
      let w := cartAdj deg st row col
      if Nat.beq w 63 then none
      else if !Nat.beq step.xi 0 && !Nat.beq step.xi (getUpp deg st w) then none
      else if !Nat.beq (Nat.land (Nat.shiftRight usedMask w) 1) 0 then none
      else
        strictNat (setImgNat img step.z w) fun img' =>
        strictNat (Nat.lor usedMask (Nat.shiftLeft 1 w)) fun usedMask' =>
        evalQSteps deg st cw rest img' usedMask'

def rootedSubConfNat (deg : Nat) (st : Nat) (fc : FastConf) (x y : Nat) (cw : Bool) : Option Nat :=
  strictNat (setImgNat (setImgNat (setImgNat emptyImgNat 0 (if cw then 1 else 0)) fc.z0 x) fc.z1 y) fun img2 =>
  strictNat (Nat.lor (Nat.shiftLeft 1 x) (Nat.shiftLeft 1 y)) fun used0 =>
  match evalQSteps deg st cw fc.qSteps img2 used0 with
  | none => none
  | some (img, usedMask) =>
    if checkSpokeMask deg deg usedMask then some img
    else none

def initIsoVerts (deg ring : Nat) (st : Nat) (img : Nat) :
    List IntVert → Nat → Nat → Option (Nat × Nat)
  | [], invMap, usedMask => some (invMap, usedMask)
  | iv :: rest, invMap, usedMask =>
    let fu := getImgNat img iv.u
    if !Nat.ble fu (Nat.mul 5 deg) then none
    else if !Nat.beq (Nat.land (Nat.shiftRight usedMask fu) 1) 0 then none
    else if !Nat.beq iv.d (getUpp deg st fu) then none
    else
      let okFan :=
        if !Nat.ble fu (Nat.mul 2 deg) then
          let i := Nat.add (Nat.mod (Nat.sub fu 1) deg) 1
          let ex := getExactDeg deg st i
          !Nat.beq ex 0 && Nat.ble (Nat.add (Nat.div (Nat.sub fu 1) deg) 4) ex
        else
          true
      if !okFan then none
      else
        strictNat (Nat.lor usedMask (Nat.shiftLeft 1 fu)) fun usedMask' =>
        strictNat (setLaneNat invMap fu (Nat.sub iv.u (Nat.add ring 1))) fun invMap' =>
        initIsoVerts deg ring st img rest invMap' usedMask'

def checkVertCyc (deg ring : Nat) (st : Nat) (img : Nat) (cw : Bool) (u : Nat) :
    List CycPair → Bool → Bool
  | [], _ => true
  | cp :: rest, worried =>
    if Nat.ble cp.v ring then
      checkVertCyc deg ring st img cw u rest true
    else
      let x := if cw then getImgNat img u else getImgNat img cp.v
      let y := if cw then getImgNat img cp.v else getImgNat img u
      if Nat.ble cp.w ring then
        if worried then false
        else checkVertCyc deg ring st img cw u rest worried
      else
        if !Nat.beq (cartAdj deg st x y) (getImgNat img cp.w) then false
        else checkVertCyc deg ring st img cw u rest false

def checkAllVertCycs (deg ring : Nat) (st : Nat) (img : Nat) (cw : Bool) : List IntVert → Bool
  | [] => true
  | iv :: rest =>
    if checkVertCyc deg ring st img cw iv.u iv.cyc iv.worried then
      checkAllVertCycs deg ring st img cw rest
    else
      false

def checkIndu (usedMask : Nat) (invMap : Nat) (adjMat : Nat) (p q : Nat) : Bool :=
  if Nat.beq (Nat.land (Nat.land (Nat.shiftRight usedMask p) (Nat.shiftRight usedMask q)) 1) 0 then
    true
  else
    let iu := getLaneNat invMap p
    let iv := getLaneNat invMap q
    let shift := Nat.add (Nat.mul iu 12) iv
    !Nat.beq (Nat.land (Nat.shiftRight adjMat shift) 1) 0

def checkAllIndu (deg : Nat) (st : Nat) (usedMask : Nat) (invMap : Nat)
    (adjMat : Nat) : Nat → Bool
  | 0 => true
  | j + 1 =>
    let i := Nat.add j 1
    let h := if Nat.beq i 1 then deg else Nat.sub i 1
    let a := Nat.add h deg
    if !checkIndu usedMask invMap adjMat 0 i then false
    else if !checkIndu usedMask invMap adjMat h i then false
    else if !checkIndu usedMask invMap adjMat h a then false
    else if !checkIndu usedMask invMap adjMat i a then false
    else
      let ex := getExactDeg deg st i
      let okSpoke :=
        if Nat.beq ex 0 then true
        else
          let b := Nat.add deg i
          if Nat.beq ex 5 then
            checkIndu usedMask invMap adjMat a b
          else
            let c := Nat.add (Nat.mul 2 deg) i
            if !checkIndu usedMask invMap adjMat a c then false
            else if !checkIndu usedMask invMap adjMat c i then false
            else if Nat.beq ex 6 then
              checkIndu usedMask invMap adjMat c b
            else
              let d := Nat.add (Nat.mul 3 deg) i
              if !checkIndu usedMask invMap adjMat c d then false
              else if !checkIndu usedMask invMap adjMat d i then false
              else if Nat.beq ex 7 then
                checkIndu usedMask invMap adjMat d b
              else if !Nat.beq ex 8 then false
              else
                let e := Nat.add (Nat.mul 4 deg) i
                checkIndu usedMask invMap adjMat e d &&
                checkIndu usedMask invMap adjMat e i &&
                checkIndu usedMask invMap adjMat e b
      if okSpoke then checkAllIndu deg st usedMask invMap adjMat j
      else false

def checkIsoNat (fc : FastConf) (deg : Nat) (st : Nat) (img : Nat) : Bool :=
  match initIsoVerts deg fc.ring st img fc.intVerts 0 0 with
  | none => false
  | some (invMap, usedMask) =>
    if !checkSpokeMask deg deg usedMask then false
    else
      let cw := !Nat.beq (getImgNat img 0) 0
      if !checkAllVertCycs deg fc.ring st img cw fc.intVerts then false
      else checkAllIndu deg st usedMask invMap fc.adjMat deg

def pushRefinements (cur : Nat) (img : Nat) : List IntVert → List Nat → List Nat
  | [], stack => stack
  | iv :: rest, stack =>
    let v := getImgNat img iv.u
    if Nat.ble 1 v then
      let m := getLaneNat cur v
      if !Nat.beq (Nat.land m (Nat.sub m 1)) 0 then
        let highBit := if Nat.ble 16 m then 16 else if Nat.ble 8 m then 8 else if Nat.ble 4 m then 4 else 2
        strictNat (setLaneNat cur v (Nat.xor m highBit)) fun nextSt =>
        pushRefinements cur img rest (nextSt :: stack)
      else
        pushRefinements cur img rest stack
    else
      pushRefinements cur img rest stack

abbrev HintStream := List Nat × List (List Nat)

def popHint : HintStream → Option (Nat × HintStream)
  | (x :: xs, chunks) => some (x, (xs, chunks))
  | ([], c :: cs) =>
    match c with
    | x :: xs => some (x, (xs, cs))
    | [] => none
  | ([], []) => none

def reduceAxleAux (deg : Nat) : Nat → List Nat → HintStream → Bool × HintStream
  | _, [], hs => (true, hs)
  | 0, _ :: _, hs => (false, hs)
  | fuel + 1, cur :: rest, hs =>
    match popHint hs with
    | none => (false, hs)
    | some (p, hs') =>
      let h := Nat.shiftRight p 13
      let x := Nat.land (Nat.shiftRight p 7) 63
      let y := Nat.land (Nat.shiftRight p 1) 63
      let cw := Nat.beq (Nat.land p 1) 1
      let fc := lookupFastConf h
      match rootedSubConfNat deg cur fc x y cw with
      | none => (false, hs')
      | some img =>
        if !checkIsoNat fc deg cur img then (false, hs')
        else
          let stack' := pushRefinements cur img fc.intVerts rest
          reduceAxleAux deg fuel stack' hs'

def filterNegOutlets (st : Nat) : Nat → List FastPosOut → List FastPosOut → Nat × List FastPosOut
  | forcedch, [], acc => (forcedch, acc)
  | forcedch, po :: rest, acc =>
    if outletForcedSWAR st po then
      let f' := if po.isPos then Nat.add forcedch 1 else Nat.sub forcedch 1
      strictNat f' fun forcedch' =>
      filterNegOutlets st forcedch' rest acc
    else if outletPermittedSWAR st po then
      filterNegOutlets st forcedch rest (po :: acc)
    else
      filterNegOutlets st forcedch rest acc

def filterRemOutlets (st : Nat) : Nat → Nat → List FastPosOut → List FastPosOut → Nat × Nat × List FastPosOut
  | forcedch, allowedch, [], acc => (forcedch, allowedch, acc.reverse)
  | forcedch, allowedch, po :: rest, acc =>
    if outletForcedSWAR st po then
      let f' := if po.isPos then Nat.add forcedch 1 else Nat.sub forcedch 1
      strictNat f' fun forcedch' =>
      filterRemOutlets st forcedch' allowedch rest acc
    else if outletPermittedSWAR st po then
      if po.isPos then
        strictNat (Nat.add allowedch 1) fun allowedch' =>
        filterRemOutlets st forcedch allowedch' rest (po :: acc)
      else
        filterRemOutlets st forcedch allowedch rest (po :: acc)
    else
      filterRemOutlets st forcedch allowedch rest acc

def noExcludedForced (st : Nat) : List FastPosOut → Bool
  | [] => true
  | ex :: rest =>
    if outletForcedSWAR st ex then false
    else noExcludedForced st rest

def checkBoundLoop (deg : Nat)
    (cb : Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (st : Nat) (forcedch allowedch : Nat) (negBefore : List FastPosOut) :
    List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream
  | [], _, _, hs => (false, hs)
  | po :: subRem, curExcluded, maxch, hs =>
    if !po.isPos then
      checkBoundLoop deg cb st forcedch allowedch (po :: negBefore) subRem curExcluded maxch hs
    else
      strictNat (narrowSWAR st po) fun st_next =>
      strictNat (Nat.add forcedch 1) fun forced_next =>
      let (okSub, hs') :=
        if noExcludedForced st_next curExcluded then
          cb st_next forced_next negBefore subRem curExcluded maxch hs
        else
          (true, hs)
      if !okSub then (false, hs')
      else
        strictNat (Nat.sub allowedch 1) fun allowedch' =>
        if Nat.ble (Nat.add allowedch' forcedch) maxch then (true, hs')
        else checkBoundLoop deg cb st forcedch allowedch' negBefore subRem (po :: curExcluded) maxch hs'

def checkBoundPure (deg : Nat) :
    Nat → Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream
  | 0, _, _, _, _, _, _, hs => (false, hs)
  | fuel + 1, st, forcedIn, negBefore, rem, excluded, maxch, hs =>
    let (forced1, nextNegBefore) := filterNegOutlets st forcedIn negBefore []
    let (forcedch, allowedch, nextRem) := filterRemOutlets st forced1 0 rem []
    if Nat.ble (Nat.add forcedch allowedch) maxch then (true, hs)
    else if Nat.ble (Nat.add maxch 1) forcedch then reduceAxleAux deg 4096 [st] hs
    else checkBoundLoop deg (checkBoundPure deg fuel) st forcedch allowedch nextNegBefore nextRem excluded maxch hs

structure SymOutlet where
  number : Nat
  nolines : Nat
  conds : List (Nat × Nat)
  deriving Repr, BEq, Inhabited

def symForced (st : Nat) (x deg : Nat) (refl : Bool) : List (Nat × Nat) → Bool
  | [] => true
  | (p0, bm) :: rest =>
    let x_shift := Nat.sub x 1
    let p :=
      if !Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg)) then
        Nat.add p0 x_shift
      else
        Nat.sub (Nat.add p0 x_shift) deg
    if refl then
      if !Nat.ble 1 p || !Nat.ble p (Nat.mul 2 deg) then false
      else
        let q :=
          if Nat.ble p deg then Nat.add (Nat.sub deg p) 1
          else if !Nat.ble (Nat.mul 2 deg) p then Nat.sub (Nat.mul 3 deg) p
          else Nat.mul 2 deg
        if !Nat.beq (Nat.land (getLaneNat st q) (Nat.xor 31 bm)) 0 then false
        else symForced st x deg refl rest
    else
      if !Nat.beq (Nat.land (getLaneNat st p) (Nat.xor 31 bm)) 0 then false
      else symForced st x deg refl rest

def findSymOutlet (line : Nat) : List SymOutlet → Option SymOutlet
  | [] => none
  | o :: rest => if Nat.beq o.number line then some o else findSymOutlet line rest

def extractConds (deg : Nat) (condV condM : Nat) :
    Nat → List (Nat × Nat) → Option (List (Nat × Nat))
  | 0, acc =>
    let n := getLaneNat condV 0
    if Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg) then
      some ((n, getLaneNat condM 0) :: acc)
    else none
  | i + 1, acc =>
    let idx := Nat.add i 1
    let n := getLaneNat condV idx
    if Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg) then
      extractConds deg condV condM i ((n, getLaneNat condM idx) :: acc)
    else none

def filterSymsLe (lev : Nat) : List SymOutlet → List SymOutlet
  | [] => []
  | o :: rest =>
    if Nat.ble (Nat.sub o.nolines 1) lev then o :: filterSymsLe lev rest
    else filterSymsLe lev rest

def filterSymsLt (lev : Nat) : List SymOutlet → List SymOutlet
  | [] => []
  | o :: rest =>
    if !Nat.ble lev (Nat.sub o.nolines 1) then o :: filterSymsLt lev rest
    else filterSymsLt lev rest

def initHubcapOutletsAcc (st : Nat) : Nat → List FastPosOut → List FastPosOut → Nat × List FastPosOut
  | forced, [], acc => (forced, acc)
  | forced, fpo :: rest, acc =>
    if outletForcedSWAR st fpo then
      let f' := if fpo.isPos then Nat.add forced 1 else Nat.sub forced 1
      strictNat f' fun forced' =>
      initHubcapOutletsAcc st forced' rest acc
    else if outletPermittedSWAR st fpo then
      initHubcapOutletsAcc st forced rest (fpo :: acc)
    else
      initHubcapOutletsAcc st forced rest acc

def verifyHubcapMembers (deg : Nat) (st : Nat) (shiftedTable : List (List FastPosOut)) :
    List (Nat × Nat × Int) → HintStream → Bool × HintStream
  | [], hs => (true, hs)
  | (x, y, v) :: rest, hs =>
    let outsX := lookupListD [] shiftedTable x
    let (forced1, acc1) := initHubcapOutletsAcc st 500 outsX []
    let (initForced, acc2) :=
      if !Nat.beq x y then
        let outsY := lookupListD [] shiftedTable y
        initHubcapOutletsAcc st forced1 outsY acc1
      else
        (forced1, acc1)
    let maxchNat := (v + 500).toNat
    strictNat maxchNat fun maxchStrict =>
    let (ok, hs') := checkBoundPure deg 256 st initForced [] acc2.reverse [] maxchStrict hs
    if !ok then (false, hs')
    else verifyHubcapMembers deg st shiftedTable rest hs'

def verifyTreePure (deg : Nat) (shiftedTable : List (List FastPosOut)) (st : Nat) :
    ProofTree → Nat → Nat → Nat → Nat → List SymOutlet → HintStream → Bool × Nat × List SymOutlet × HintStream
  | ProofTree.reduce, lineno, _lev, _condV, _condM, syms, hs =>
    let (ok, hs') := reduceAxleAux deg 4096 [st] hs
    strictNat (Nat.add lineno 1) fun lineno' =>
    (ok, lineno', syms, hs')
  | ProofTree.hubcap members, lineno, _lev, _condV, _condM, syms, hs =>
    let (ok, hs') := verifyHubcapMembers deg st shiftedTable members hs
    strictNat (Nat.add lineno 1) fun lineno' =>
    (ok, lineno', syms, hs')
  | ProofTree.sym k eps lev_in line, lineno, _lev, _condV, _condM, syms, hs =>
    let ok :=
      if !Nat.ble deg k && Nat.ble eps 1 then
        match findSymOutlet line syms with
        | some found =>
          if Nat.beq found.nolines (Nat.add lev_in 1) then
            symForced st (Nat.add k 1) deg (!Nat.beq eps 0) found.conds
          else false
        | none => false
      else false
    strictNat (Nat.add lineno 1) fun lineno' =>
    (ok, lineno', syms, hs)
  | ProofTree.cond v m trueBranch falseBranch, lineno, lev, condV, condM, syms, hs =>
    let maskTrue := condMaskNat m
    let maskFalse := Nat.xor 31 maskTrue
    let curLane := getLaneNat st v
    strictNat (setLaneNat st v (Nat.land curLane maskTrue)) fun stTrue =>
    strictNat (setLaneNat st v (Nat.land curLane maskFalse)) fun stFalse =>
    strictNat (Nat.add lev 1) fun lev1 =>
    strictNat (Nat.add lineno 1) fun lineno1 =>
    let syms' :=
      match extractConds deg condV condM lev [] with
      | some conds => { number := lineno, nolines := lev1, conds := conds } :: syms
      | none => syms
    strictNat (setLaneNat (setLaneNat condV lev v) lev1 0) fun condV' =>
    strictNat (setLaneNat (setLaneNat condM lev maskTrue) lev1 0) fun condM' =>
    let (bTrue, next_lineno, syms_after_true, hs1) :=
      verifyTreePure deg shiftedTable stTrue trueBranch lineno1 lev1 condV' condM' syms' hs
    if !bTrue then
      (false, next_lineno, syms_after_true, hs1)
    else
      let syms_popped := filterSymsLe lev syms_after_true
      let (bFalse, final_lineno, syms_after_false, hs2) :=
        verifyTreePure deg shiftedTable stFalse falseBranch next_lineno lev condV' condM' syms_popped hs1
      let syms_final := filterSymsLt lev syms_after_false
      (bFalse, final_lineno, syms_final, hs2)

def getHintsForDeg (deg : Nat) : List (List Nat) :=
  if Nat.beq deg 7 then hints_7
  else if Nat.beq deg 8 then hints_8
  else if Nat.beq deg 9 then hints_9
  else if Nat.beq deg 10 then hints_10
  else if Nat.beq deg 11 then hints_11
  else []

def getShiftedTableForDeg (deg : Nat) : List (List FastPosOut) :=
  if Nat.beq deg 7 then shiftedOutsTable_7
  else if Nat.beq deg 8 then shiftedOutsTable_8
  else if Nat.beq deg 9 then shiftedOutsTable_9
  else if Nat.beq deg 10 then shiftedOutsTable_10
  else shiftedOutsTable_11

def getInitStateForDeg (deg : Nat) : Nat :=
  if Nat.beq deg 7 then initStateNat_7
  else if Nat.beq deg 8 then initStateNat_8
  else if Nat.beq deg 9 then initStateNat_9
  else if Nat.beq deg 10 then initStateNat_10
  else initStateNat_11

noncomputable def lookupListRec {a : Type} (d : a) (l : List a) (idx : Nat) : a :=
  List.rec
    (motive := fun _ => Nat → a)
    (fun _ => d)
    (fun x _ ih n => Nat.casesOn n x (fun k => ih k))
    l idx

noncomputable def lookupFastConfRec (h : Nat) : FastConf :=
  let b0 := lookupListRec [] fastConfTable (Nat.shiftRight h 6)
  let b1 := lookupListRec [] b0 (Nat.land (Nat.shiftRight h 3) 7)
  lookupListRec default b1 (Nat.land h 7)

noncomputable def getUppStrict (deg : Nat) (st : Nat) (p : Nat) : Nat :=
  Bool.rec
    (strictNat (getLaneNat st p) fun m =>
     Bool.rec
       (Bool.rec
         (Bool.rec
           (Bool.rec 5 6 (Nat.ble 2 m))
           7 (Nat.ble 4 m))
         8 (Nat.ble 8 m))
       12 (Nat.ble 16 m))
    deg
    (Nat.beq p 0)

noncomputable def getExactDegStrict (deg : Nat) (st : Nat) (p : Nat) : Nat :=
  Bool.rec
    (strictNat (getLaneNat st p) fun m =>
     Bool.rec
       (Bool.rec
         (Bool.rec
           (Bool.rec 0 8 (Nat.beq m 8))
           7 (Nat.beq m 4))
         6 (Nat.beq m 2))
       5 (Nat.beq m 1))
    deg
    (Nat.beq p 0)

noncomputable def fanTri63Strict (x y z u v : Nat) : Nat :=
  Bool.rec
    (Bool.rec
      (Bool.rec
        63
        y
        (Nat.beq u z && Nat.beq v x))
      x
      (Nat.beq u y && Nat.beq v z))
    z
    (Nat.beq u x && Nat.beq v y)

noncomputable def cartAdjSpokeStrict (deg : Nat) (st : Nat) (i u v : Nat) : Nat :=
  strictNat (getUppStrict deg st i) fun k =>
  strictNat (Bool.rec (Nat.sub i 1) deg (Nat.beq i 1)) fun h =>
  strictNat (fanTri63Strict 0 h i u v) fun r1 =>
  Bool.rec
    (strictNat (Nat.add deg h) fun a =>
     strictNat (fanTri63Strict i h a u v) fun r2 =>
     Bool.rec
       (Bool.rec
         (strictNat (Nat.add deg i) fun b =>
          Bool.rec
            (strictNat (Nat.add (Nat.mul 2 deg) i) fun c =>
             strictNat (fanTri63Strict i a c u v) fun r3 =>
             Bool.rec
               (Bool.rec
                 (strictNat (Nat.add (Nat.mul 3 deg) i) fun d =>
                  strictNat (fanTri63Strict i c d u v) fun r4 =>
                  Bool.rec
                    (Bool.rec
                      (strictNat (Nat.add (Nat.mul 4 deg) i) fun e =>
                       strictNat (fanTri63Strict i d e u v) fun r5 =>
                       Bool.rec
                         (fanTri63Strict i e b u v)
                         r5
                         (!Nat.beq r5 63))
                      (fanTri63Strict i d b u v)
                      (Nat.beq k 7))
                    r4
                    (!Nat.beq r4 63))
                 (fanTri63Strict i c b u v)
                 (Nat.beq k 6))
               r3
               (!Nat.beq r3 63))
            (fanTri63Strict i a b u v)
            (Nat.beq k 5))
         63
         (Nat.ble 9 k))
       r2
       (!Nat.beq r2 63))
    r1
    (!Nat.beq r1 63)

noncomputable def cartAdjStrict (deg : Nat) (st : Nat) (u v : Nat) : Nat :=
  Bool.rec
    (strictNat (Nat.add (Nat.mod (Nat.sub u 1) deg) 1) fun i1 =>
     strictNat (cartAdjSpokeStrict deg st i1 u v) fun w1 =>
     Bool.rec
       (strictNat (Bool.rec (Nat.add i1 1) 1 (Nat.beq i1 deg)) fun i2 =>
        cartAdjSpokeStrict deg st i2 u v)
       w1
       (!Nat.beq w1 63))
    (Bool.rec
      63
      (Bool.rec (Nat.add v 1) 1 (Nat.beq v deg))
      (Nat.ble 1 v && Nat.ble v deg))
    (Nat.beq u 0)

noncomputable def checkSpokeMaskRec (deg : Nat) (usedMask : Nat) : Bool :=
  Nat.rec
    (motive := fun _ => Bool)
    true
    (fun j ih =>
      Bool.rec
        false
        (strictNat (Nat.add j 1) fun w1 =>
         let w2 := Nat.add deg w1
         let w3 := Bool.rec (Nat.sub (Nat.add deg w1) 1) (Nat.mul 2 deg) (Nat.beq w1 1)
         Bool.rec
           true
           false
           (Nat.beq (Nat.land (Nat.shiftRight usedMask w1) 1) 0 &&
            !Nat.beq (Nat.land (Nat.shiftRight usedMask w2) 1) 0 &&
            !Nat.beq (Nat.land (Nat.shiftRight usedMask w3) 1) 0))
        ih)
    deg

noncomputable def evalQStepsRec (deg : Nat) (st : Nat) (cw : Bool) (steps : List QStep) (img0 used0 : Nat) : Option (Nat × Nat) :=
  List.rec
    (motive := fun _ => Nat → Nat → Option (Nat × Nat))
    (fun img usedMask => some (img, usedMask))
    (fun step _ ih img usedMask =>
      match step with
      | QStep.mk su sv sz sxi =>
        strictNat (getImgNat img su) fun u_img =>
        strictNat (getImgNat img sv) fun v_img =>
        Bool.rec
          (let row := Bool.rec v_img u_img cw
           let col := Bool.rec u_img v_img cw
           strictNat (cartAdjStrict deg st row col) fun w =>
           Bool.rec
             (Bool.rec
               (Bool.rec
                 (strictNat (setImgNat img sz w) fun img' =>
                  strictNat (Nat.lor usedMask (Nat.shiftLeft 1 w)) fun usedMask' =>
                  ih img' usedMask')
                 none
                 (!Nat.beq (Nat.land (Nat.shiftRight usedMask w) 1) 0))
               none
               (!Nat.beq sxi 0 && !Nat.beq sxi (getUppStrict deg st w)))
             none
             (Nat.beq w 63))
          none
          (Nat.beq u_img 63 || Nat.beq v_img 63))
    steps img0 used0

noncomputable def rootedSubConfRec (deg : Nat) (st : Nat) (z0 z1 : Nat) (qSteps : List QStep) (x y : Nat) (cw : Bool) : Option Nat :=
  strictNat (setImgNat (setImgNat (setImgNat emptyImgNat 0 (Bool.rec 0 1 cw)) z0 x) z1 y) fun img2 =>
  strictNat (Nat.lor (Nat.shiftLeft 1 x) (Nat.shiftLeft 1 y)) fun used0 =>
  match evalQStepsRec deg st cw qSteps img2 used0 with
  | none => none
  | some (img, usedMask) =>
    Bool.rec none (some img) (checkSpokeMaskRec deg usedMask)

noncomputable def initIsoVertsRec (deg ring : Nat) (st : Nat) (img : Nat) (ivs : List IntVert) : Option (Nat × Nat) :=
  List.rec
    (motive := fun _ => Nat → Nat → Option (Nat × Nat))
    (fun invMap usedMask => some (invMap, usedMask))
    (fun iv _ ih invMap usedMask =>
      match iv with
      | IntVert.mk ivu ivd _ _ =>
        strictNat (getImgNat img ivu) fun fu =>
        Bool.rec
          none
          (Bool.rec
            (Bool.rec
              none
              (let okFan :=
                 Bool.rec
                   (let i := Nat.add (Nat.mod (Nat.sub fu 1) deg) 1
                    strictNat (getExactDegStrict deg st i) fun ex =>
                    !Nat.beq ex 0 && Nat.ble (Nat.add (Nat.div (Nat.sub fu 1) deg) 4) ex)
                   true
                   (Nat.ble fu (Nat.mul 2 deg))
               Bool.rec
                 none
                 (strictNat (Nat.lor usedMask (Nat.shiftLeft 1 fu)) fun usedMask' =>
                  strictNat (setLaneNat invMap fu (Nat.sub ivu (Nat.add ring 1))) fun invMap' =>
                  ih invMap' usedMask')
                 okFan)
              (Nat.beq ivd (getUppStrict deg st fu)))
            none
            (!Nat.beq (Nat.land (Nat.shiftRight usedMask fu) 1) 0))
          (Nat.ble fu (Nat.mul 5 deg)))
    ivs 0 0

noncomputable def checkVertCycRec (deg ring : Nat) (st : Nat) (img : Nat) (cw : Bool) (fu : Nat) (cps : List CycPair) (w0 : Bool) : Bool :=
  List.rec
    (motive := fun _ => Bool → Bool)
    (fun _ => true)
    (fun cp _ ih worried =>
      match cp with
      | CycPair.mk cpv cpw =>
        Bool.rec
          (strictNat (getImgNat img cpv) fun fv =>
           let x := Bool.rec fv fu cw
           let y := Bool.rec fu fv cw
           Bool.rec
             (Bool.rec
               false
               (ih false)
               (Nat.beq (cartAdjStrict deg st x y) (getImgNat img cpw)))
             (Bool.rec (ih worried) false worried)
             (Nat.ble cpw ring))
          (ih true)
          (Nat.ble cpv ring))
    cps w0

noncomputable def checkAllVertCycsRec (deg ring : Nat) (st : Nat) (img : Nat) (cw : Bool) (ivs : List IntVert) : Bool :=
  List.rec
    (motive := fun _ => Bool)
    true
    (fun iv _ ih =>
      match iv with
      | IntVert.mk ivu _ ivw ivcyc =>
        strictNat (getImgNat img ivu) fun fu =>
        Bool.rec false ih (checkVertCycRec deg ring st img cw fu ivcyc ivw))
    ivs

noncomputable def checkInduStrict (usedMask : Nat) (invMap : Nat) (adjMat : Nat) (p q : Nat) : Bool :=
  Bool.rec
    (let iu := getLaneNat invMap p
     let iv := getLaneNat invMap q
     let shift := Nat.add (Nat.mul iu 12) iv
     !Nat.beq (Nat.land (Nat.shiftRight adjMat shift) 1) 0)
    true
    (Nat.beq (Nat.land (Nat.land (Nat.shiftRight usedMask p) (Nat.shiftRight usedMask q)) 1) 0)

noncomputable def checkAllInduRec (deg : Nat) (st : Nat) (usedMask : Nat) (invMap : Nat) (adjMat : Nat) : Bool :=
  Nat.rec
    (motive := fun _ => Bool)
    true
    (fun j ih =>
      Bool.rec
        false
        (strictNat (Nat.add j 1) fun i =>
         strictNat (Bool.rec (Nat.sub i 1) deg (Nat.beq i 1)) fun h =>
         strictNat (Nat.add h deg) fun a =>
         Bool.rec
           false
           (strictNat (getExactDegStrict deg st i) fun ex =>
            Bool.rec
              (strictNat (Nat.add deg i) fun b =>
               Bool.rec
                 (strictNat (Nat.add (Nat.mul 2 deg) i) fun c =>
                  Bool.rec
                    false
                    (Bool.rec
                      (strictNat (Nat.add (Nat.mul 3 deg) i) fun d =>
                       Bool.rec
                         false
                         (Bool.rec
                           (Bool.rec
                             false
                             (strictNat (Nat.add (Nat.mul 4 deg) i) fun e =>
                              checkInduStrict usedMask invMap adjMat e d &&
                              checkInduStrict usedMask invMap adjMat e i &&
                              checkInduStrict usedMask invMap adjMat e b)
                             (Nat.beq ex 8))
                           (checkInduStrict usedMask invMap adjMat d b)
                           (Nat.beq ex 7))
                         (checkInduStrict usedMask invMap adjMat c d &&
                          checkInduStrict usedMask invMap adjMat d i))
                      (checkInduStrict usedMask invMap adjMat c b)
                      (Nat.beq ex 6))
                    (checkInduStrict usedMask invMap adjMat a c &&
                     checkInduStrict usedMask invMap adjMat c i))
                 (checkInduStrict usedMask invMap adjMat a b)
                 (Nat.beq ex 5))
              true
              (Nat.beq ex 0))
           (checkInduStrict usedMask invMap adjMat 0 i &&
            checkInduStrict usedMask invMap adjMat h i &&
            checkInduStrict usedMask invMap adjMat h a &&
            checkInduStrict usedMask invMap adjMat i a))
        ih)
    deg

noncomputable def checkIsoRec (ring adjMat : Nat) (intVerts : List IntVert) (deg : Nat) (st : Nat) (img : Nat) : Bool :=
  match initIsoVertsRec deg ring st img intVerts with
  | none => false
  | some (invMap, usedMask) =>
    Bool.rec
      false
      (let cw := !Nat.beq (getImgNat img 0) 0
       Bool.rec
         false
         (checkAllInduRec deg st usedMask invMap adjMat)
         (checkAllVertCycsRec deg ring st img cw intVerts))
      (checkSpokeMaskRec deg usedMask)

noncomputable def pushRefinementsRec (cur : Nat) (img : Nat) (ivs : List IntVert) (stack0 : List Nat) : List Nat :=
  List.rec
    (motive := fun _ => List Nat → List Nat)
    (fun stack => stack)
    (fun iv _ ih stack =>
      match iv with
      | IntVert.mk ivu _ _ _ =>
        strictNat (getImgNat img ivu) fun v =>
        Bool.rec
          (ih stack)
          (strictNat (getLaneNat cur v) fun m =>
           Bool.rec
             (ih stack)
             (let highBit :=
                Bool.rec
                  (Bool.rec
                    (Bool.rec 2 4 (Nat.ble 4 m))
                    8 (Nat.ble 8 m))
                  16 (Nat.ble 16 m)
              strictNat (setLaneNat cur v (Nat.xor m highBit)) fun nextSt =>
              ih (nextSt :: stack))
             (!Nat.beq (Nat.land m (Nat.sub m 1)) 0))
          (Nat.ble 1 v))
    ivs stack0

noncomputable def popHintRec (hs : HintStream) : Option (Nat × HintStream) :=
  List.casesOn hs.1
    (List.casesOn hs.2
      none
      (fun c cs =>
        List.casesOn c
          none
          (fun x xs => some (x, (xs, cs)))))
    (fun x xs => some (x, (xs, hs.2)))

noncomputable def reduceAxleRec (deg : Nat) (fuel : Nat) (stack0 : List Nat) (hs0 : HintStream) : Bool × HintStream :=
  Nat.rec
    (motive := fun _ => List Nat → HintStream → Bool × HintStream)
    (fun stack hs =>
      match stack with
      | [] => (true, hs)
      | _ :: _ => (false, hs))
    (fun _ ih stack hs =>
      match stack with
      | [] => (true, hs)
      | cur :: rest =>
        match popHintRec hs with
        | none => (false, hs)
        | some (p, hs') =>
          let h := Nat.shiftRight p 13
          strictNat (Nat.land (Nat.shiftRight p 7) 63) fun x =>
          strictNat (Nat.land (Nat.shiftRight p 1) 63) fun y =>
          let cw := Nat.beq (Nat.land p 1) 1
          match lookupFastConfRec h with
          | FastConf.mk _ ring z0 z1 adjMat qSteps intVerts =>
            match rootedSubConfRec deg cur z0 z1 qSteps x y cw with
            | none => (false, hs')
            | some img =>
              Bool.rec
                (false, hs')
                (let stack' := pushRefinementsRec cur img intVerts rest
                 ih stack' hs')
                (checkIsoRec ring adjMat intVerts deg cur img))
    fuel stack0 hs0

noncomputable def revFastPosOut (l : List FastPosOut) : List FastPosOut :=
  List.rec
    (motive := fun _ => List FastPosOut → List FastPosOut)
    (fun acc => acc)
    (fun x _ ih acc => ih (x :: acc))
    l []

noncomputable def appendFastPosOut (l1 l2 : List FastPosOut) : List FastPosOut :=
  List.rec
    (motive := fun _ => List FastPosOut)
    l2
    (fun x _ ih => x :: ih)
    l1

noncomputable def filterNegAPS (st : Nat) (negBefore : List FastPosOut) (f0 : Nat) : Nat × List FastPosOut :=
  List.rec
    (motive := fun _ => Nat → List FastPosOut → Nat × List FastPosOut)
    (fun f acc =>
      strictNat f fun f' => (f', acc))
    (fun po _ ih f acc =>
      Bool.rec
        (Bool.rec
          (ih f acc)
          (ih f (po :: acc))
          (outletPermittedSWAR st po))
        (ih (Bool.rec (Nat.sub f 1) (Nat.add f 1) po.isPos) acc)
        (outletForcedSWAR st po))
    negBefore f0 []

noncomputable def filterRemAPS (st : Nat) (rem : List FastPosOut) (f0 : Nat) : Nat × Nat × List FastPosOut :=
  List.rec
    (motive := fun _ => Nat → Nat → List FastPosOut → Nat × Nat × List FastPosOut)
    (fun f a acc =>
      strictNat f fun f' =>
      strictNat a fun a' =>
      (f', a', revFastPosOut acc))
    (fun po _ ih f a acc =>
      Bool.rec
        (Bool.rec
          (ih f a acc)
          (Bool.rec
            (ih f a (po :: acc))
            (ih f (Nat.add a 1) (po :: acc))
            po.isPos)
          (outletPermittedSWAR st po))
        (ih (Bool.rec (Nat.sub f 1) (Nat.add f 1) po.isPos) a acc)
        (outletForcedSWAR st po))
    rem f0 0 []

noncomputable def noExcludedForcedRec (st : Nat) (excluded : List FastPosOut) : Bool :=
  List.rec
    (motive := fun _ => Bool)
    true
    (fun ex _ ih => Bool.rec ih false (outletForcedSWAR st ex))
    excluded

noncomputable def checkBoundLoopRec
    (cb : Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (st : Nat) (forcedch : Nat) (maxch : Nat) (rem : List FastPosOut)
    (allowed0 : Nat) (neg0 : List FastPosOut) (excl0 : List FastPosOut) (hs0 : HintStream) : Bool × HintStream :=
  List.rec
    (motive := fun _ => Nat → List FastPosOut → List FastPosOut → HintStream → Bool × HintStream)
    (fun _ _ _ hs => (false, hs))
    (fun po subRem ih allowedch negBefore curExcluded hs =>
      Bool.rec
        (ih allowedch (po :: negBefore) curExcluded hs)
        (strictNat (narrowSWAR st po) fun st_next =>
         strictNat (Nat.add forcedch 1) fun forced_next =>
         let (okSub, hs') :=
           Bool.rec
             (true, hs)
             (cb st_next forced_next negBefore subRem curExcluded maxch hs)
             (noExcludedForcedRec st_next curExcluded)
         Bool.rec
           (false, hs')
           (strictNat (Nat.sub allowedch 1) fun allowedch' =>
            Bool.rec
              (ih allowedch' negBefore (po :: curExcluded) hs')
              (true, hs')
              (Nat.ble (Nat.add allowedch' forcedch) maxch))
           okSub)
        po.isPos)
    rem allowed0 neg0 excl0 hs0

noncomputable def checkBoundRec (deg : Nat) (fuel : Nat) :
    Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream :=
  Nat.rec
    (motive := fun _ => Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (fun _ _ _ _ _ _ hs => (false, hs))
    (fun _ ih st forcedIn negBefore rem excluded maxch hs =>
      let (forced1, nextNegBefore) := filterNegAPS st negBefore forcedIn
      let (forcedch, allowedch, nextRem) := filterRemAPS st rem forced1
      Bool.rec
        (Bool.rec
          (checkBoundLoopRec ih st forcedch maxch nextRem allowedch nextNegBefore excluded hs)
          (reduceAxleRec deg 64 [st] hs)
          (Nat.ble (Nat.add maxch 1) forcedch))
        (true, hs)
        (Nat.ble (Nat.add forcedch allowedch) maxch))
    fuel

noncomputable def verifyHubcapMembersRec (deg : Nat) (st : Nat) (shiftedTable : List (List FastPosOut))
    (members : List (Nat × Nat × Int)) (hs0 : HintStream) : Bool × HintStream :=
  List.rec
    (motive := fun _ => HintStream → Bool × HintStream)
    (fun hs => (true, hs))
    (fun m _ ih hs =>
      let (x, y, v) := m
      let outsX := lookupListRec [] shiftedTable x
      let initRem :=
        Bool.rec
          outsX
          (appendFastPosOut outsX (lookupListRec [] shiftedTable y))
          (!Nat.beq x y)
      let maxchNat := (v + 500).toNat
      strictNat maxchNat fun maxchStrict =>
      let (ok, hs') := checkBoundRec deg 20 st 500 [] initRem [] maxchStrict hs
      Bool.rec (false, hs') (ih hs') ok)
    members hs0

noncomputable def symForcedRec (st : Nat) (x deg : Nat) (refl : Bool) (conds : List (Nat × Nat)) : Bool :=
  strictNat (Nat.sub x 1) fun x_shift =>
  List.rec
    (motive := fun _ => Bool)
    true
    (fun c _ ih =>
      let (p0, bm) := c
      strictNat
        (Bool.rec
          (Nat.sub (Nat.add p0 x_shift) deg)
          (Nat.add p0 x_shift)
          (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))))
        fun p =>
      Bool.rec
        (Bool.rec
          ih
          false
          (!Nat.beq (Nat.land (getLaneNat st p) (Nat.xor 31 bm)) 0))
        (Bool.rec
          false
          (let q :=
             Bool.rec
               (Bool.rec
                 (Nat.mul 2 deg)
                 (Nat.sub (Nat.mul 3 deg) p)
                 (!Nat.ble (Nat.mul 2 deg) p))
               (Nat.add (Nat.sub deg p) 1)
               (Nat.ble p deg)
           Bool.rec
             ih
             false
             (!Nat.beq (Nat.land (getLaneNat st q) (Nat.xor 31 bm)) 0))
          (Nat.ble 1 p && Nat.ble p (Nat.mul 2 deg)))
        refl)
    conds

noncomputable def findSymOutletRec (line : Nat) (syms : List SymOutlet) : Option SymOutlet :=
  List.rec
    (motive := fun _ => Option SymOutlet)
    none
    (fun o _ ih => Bool.rec ih (some o) (Nat.beq o.number line))
    syms

noncomputable def extractCondsRec (deg : Nat) (condV condM : Nat) (lev : Nat) : Option (List (Nat × Nat)) :=
  Nat.rec
    (motive := fun _ => List (Nat × Nat) → Option (List (Nat × Nat)))
    (fun acc =>
      strictNat (getLaneNat condV 0) fun n =>
      Bool.rec
        none
        (some ((n, getLaneNat condM 0) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)))
    (fun i ih acc =>
      strictNat (Nat.add i 1) fun idx =>
      strictNat (getLaneNat condV idx) fun n =>
      Bool.rec
        none
        (ih ((n, getLaneNat condM idx) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)))
    lev []

noncomputable def verifyTreePureRec (deg : Nat) (shiftedTable : List (List FastPosOut))
    (t : ProofTree) (st0 lineno0 lev0 condV0 condM0 : Nat) (syms0 : List SymOutlet) (hs0 : HintStream) :
    Bool × Nat × HintStream :=
  ProofTree.rec
    (motive := fun _ => Nat → Nat → Nat → Nat → Nat → List SymOutlet → HintStream → Bool × Nat × HintStream)
    (fun v m _ _ ihTrue ihFalse st lineno lev condV condM syms hs =>
      strictNat (condMaskNat m) fun maskTrue =>
      strictNat (Nat.xor 31 maskTrue) fun maskFalse =>
      strictNat (getLaneNat st v) fun curLane =>
      strictNat (setLaneNat st v (Nat.land curLane maskTrue)) fun stTrue =>
      strictNat (setLaneNat st v (Nat.land curLane maskFalse)) fun stFalse =>
      strictNat (Nat.add lev 1) fun lev1 =>
      strictNat (Nat.add lineno 1) fun lineno1 =>
      let syms' :=
        match extractCondsRec deg condV condM lev with
        | none => syms
        | some conds => { number := lineno, nolines := lev1, conds := conds } :: syms
      strictNat (setLaneNat (setLaneNat condV lev v) lev1 0) fun condV' =>
      strictNat (setLaneNat (setLaneNat condM lev maskTrue) lev1 0) fun condM' =>
      let (bTrue, next_lineno, hs1) :=
        ihTrue stTrue lineno1 lev1 condV' condM' syms' hs
      Bool.rec
        (false, next_lineno, hs1)
        (ihFalse stFalse next_lineno lev condV' condM' syms' hs1)
        bTrue)
    (fun k eps lev_in line st lineno _lev _condV _condM syms hs =>
      let ok :=
        Bool.rec
          false
          (match findSymOutletRec line syms with
           | none => false
           | some found =>
             Bool.rec
               false
               (symForcedRec st (Nat.add k 1) deg (!Nat.beq eps 0) found.conds)
               (Nat.beq found.nolines (Nat.add lev_in 1)))
          (!Nat.ble deg k && Nat.ble eps 1)
      strictNat (Nat.add lineno 1) fun lineno' =>
      (ok, lineno', hs))
    (fun st lineno _lev _condV _condM _syms hs =>
      let (ok, hs') := reduceAxleRec deg 64 [st] hs
      strictNat (Nat.add lineno 1) fun lineno' =>
      (ok, lineno', hs'))
    (fun members st lineno _lev _condV _condM _syms hs =>
      let (ok, hs') := verifyHubcapMembersRec deg st shiftedTable members hs
      strictNat (Nat.add lineno 1) fun lineno' =>
      (ok, lineno', hs'))
    t st0 lineno0 lev0 condV0 condM0 syms0 hs0

noncomputable def verifyTree (_configs : List Configuration) (deg : Nat) (_A_low _A_upp : Array Nat) (t : ProofTree) (_outs : Array Outlet) : Bool :=
  (verifyTreePureRec deg (getShiftedTableForDeg deg) t (getInitStateForDeg deg) 2 0 0 0 [] ([], getHintsForDeg deg)).1

noncomputable def advanceHints (n : Nat) (hs0 : HintStream) : HintStream :=
  Nat.rec
    (motive := fun _ => HintStream → HintStream)
    (fun hs => hs)
    (fun _ ih hs =>
      match popHintRec hs with
      | none => hs
      | some (_, hs') => ih hs')
    n hs0

theorem strictNat_eq {a : Type} (n : Nat) (k : Nat → a) : strictNat n k = k n := by
  cases n <;> rfl

theorem verifyTreePureRec_cond_eq (deg : Nat) (shiftedTable : List (List FastPosOut))
    (v : Nat) (m : Int) (tTrue tFalse : ProofTree)
    (st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream) :
    verifyTreePureRec deg shiftedTable (ProofTree.cond v m tTrue tFalse) st lineno lev condV condM syms hs =
      (strictNat (condMaskNat m) fun maskTrue =>
       strictNat (Nat.xor 31 maskTrue) fun maskFalse =>
       strictNat (getLaneNat st v) fun curLane =>
       strictNat (setLaneNat st v (Nat.land curLane maskTrue)) fun stTrue =>
       strictNat (setLaneNat st v (Nat.land curLane maskFalse)) fun stFalse =>
       strictNat (Nat.add lev 1) fun lev1 =>
       strictNat (Nat.add lineno 1) fun lineno1 =>
       let syms' :=
         match extractCondsRec deg condV condM lev with
         | none => syms
         | some conds => { number := lineno, nolines := lev1, conds := conds } :: syms
       strictNat (setLaneNat (setLaneNat condV lev v) lev1 0) fun condV' =>
       strictNat (setLaneNat (setLaneNat condM lev maskTrue) lev1 0) fun condM' =>
       let (bTrue, next_lineno, hs1) :=
         verifyTreePureRec deg shiftedTable tTrue stTrue lineno1 lev1 condV' condM' syms' hs
       Bool.rec
         (false, next_lineno, hs1)
         (verifyTreePureRec deg shiftedTable tFalse stFalse next_lineno lev condV' condM' syms' hs1)
         bTrue) := rfl

theorem verifyTreePureRec_cond_split (deg : Nat) (shiftedTable : List (List FastPosOut))
    (v : Nat) (m : Int) (tTrue tFalse : ProofTree)
    (st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream)
    (stTrue stFalse lev1 lineno1 condV' condM' next_lineno final_lineno : Nat)
    (syms' : List SymOutlet) (hs1 hs2 : HintStream)
    (hStTrue : setLaneNat st v (Nat.land (getLaneNat st v) (condMaskNat m)) = stTrue)
    (hStFalse : setLaneNat st v (Nat.land (getLaneNat st v) (Nat.xor 31 (condMaskNat m))) = stFalse)
    (hLev1 : Nat.add lev 1 = lev1)
    (hLineno1 : Nat.add lineno 1 = lineno1)
    (hSyms' : (match extractCondsRec deg condV condM lev with
               | none => syms
               | some conds => { number := lineno, nolines := lev1, conds := conds } :: syms) = syms')
    (hCondV' : setLaneNat (setLaneNat condV lev v) lev1 0 = condV')
    (hCondM' : setLaneNat (setLaneNat condM lev (condMaskNat m)) lev1 0 = condM')
    (hTrue : verifyTreePureRec deg shiftedTable tTrue stTrue lineno1 lev1 condV' condM' syms' hs = (true, next_lineno, hs1))
    (hFalse : verifyTreePureRec deg shiftedTable tFalse stFalse next_lineno lev condV' condM' syms' hs1 = (true, final_lineno, hs2)) :
    verifyTreePureRec deg shiftedTable (ProofTree.cond v m tTrue tFalse) st lineno lev condV condM syms hs =
      (true, final_lineno, hs2) := by
  rw [verifyTreePureRec_cond_eq]
  simp only [strictNat_eq]
  rw [hStTrue, hStFalse, hLev1, hLineno1, hSyms', hCondV', hCondM', hTrue]
  exact hFalse

theorem verifyTree_of_pure (configs : List Configuration) (deg : Nat) (A_low A_upp : Array Nat)
    (t : ProofTree) (outs : Array Outlet) (final_lineno : Nat) (hs_final : HintStream)
    (h : verifyTreePureRec deg (getShiftedTableForDeg deg) t (getInitStateForDeg deg) 2 0 0 0 [] ([], getHintsForDeg deg) =
      (true, final_lineno, hs_final)) :
    verifyTree configs deg A_low A_upp t outs = true := by
  unfold verifyTree
  rw [h]

def ptIsCond : ProofTree → Bool
  | ProofTree.cond _ _ _ _ => true
  | _ => false

def ptCondV : ProofTree → Nat
  | ProofTree.cond v _ _ _ => v
  | _ => 0

def ptCondM : ProofTree → Int
  | ProofTree.cond _ m _ _ => m
  | _ => 0

def ptLeft : ProofTree → ProofTree
  | ProofTree.cond _ _ l _ => l
  | t => t

def ptRight : ProofTree → ProofTree
  | ProofTree.cond _ _ _ r => r
  | t => t

theorem verifyTreePureRec_split_pt (deg : Nat) (shiftedTable : List (List FastPosOut))
    (t : ProofTree)
    (st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream)
    (v : Nat) (m : Int)
    (stTrue stFalse lev1 lineno1 condV' condM' next_lineno final_lineno : Nat)
    (syms' : List SymOutlet) (hs1 hs2 : HintStream)
    (hIsCond : ptIsCond t = true)
    (hV : ptCondV t = v)
    (hM : ptCondM t = m)
    (hStTrue : setLaneNat st v (Nat.land (getLaneNat st v) (condMaskNat m)) = stTrue)
    (hStFalse : setLaneNat st v (Nat.land (getLaneNat st v) (Nat.xor 31 (condMaskNat m))) = stFalse)
    (hLev1 : Nat.add lev 1 = lev1)
    (hLineno1 : Nat.add lineno 1 = lineno1)
    (hSyms' : (match extractCondsRec deg condV condM lev with
               | none => syms
               | some conds => { number := lineno, nolines := lev1, conds := conds } :: syms) = syms')
    (hCondV' : setLaneNat (setLaneNat condV lev v) lev1 0 = condV')
    (hCondM' : setLaneNat (setLaneNat condM lev (condMaskNat m)) lev1 0 = condM')
    (hTrue : verifyTreePureRec deg shiftedTable (ptLeft t) stTrue lineno1 lev1 condV' condM' syms' hs = (true, next_lineno, hs1))
    (hFalse : verifyTreePureRec deg shiftedTable (ptRight t) stFalse next_lineno lev condV' condM' syms' hs1 = (true, final_lineno, hs2)) :
    verifyTreePureRec deg shiftedTable t st lineno lev condV condM syms hs =
      (true, final_lineno, hs2) := by
  cases t with
  | cond tv tm tTrue tFalse =>
    cases hV
    cases hM
    exact verifyTreePureRec_cond_split deg shiftedTable tv tm tTrue tFalse st lineno lev condV condM syms hs
      stTrue stFalse lev1 lineno1 condV' condM' next_lineno final_lineno syms' hs1 hs2
      hStTrue hStFalse hLev1 hLineno1 hSyms' hCondV' hCondM' hTrue hFalse
  | sym _ _ _ _ => contradiction
  | reduce => contradiction
  | hubcap _ => contradiction

def verifyTreeFull (configs : List Configuration) (deg : Nat) (A_low A_upp : Array Nat) (t : ProofTree) (outs : Array Outlet) : Bool :=
  (verifyTreeAux configs deg A_low A_upp t outs 2 0 (mkArray 16 (0, 0)) #[]).1


end Math.Discharging
