import FourColorTheorem.Math.Rules
import FourColorTheorem.Math.ProofTree
import FourColorTheorem.Math.U633Parser

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
def verifyTree (configs : List Configuration) (deg : Nat) (A_low A_upp : Array Nat) (t : ProofTree) (outs : Array Outlet) : Bool :=
  (verifyTreeAux configs deg A_low A_upp t outs 2 0 (mkArray 16 (0, 0)) #[]).1


end Math.Discharging
