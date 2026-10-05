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
    
    if r.invert then
      if let some o := doOutlet deg r.num V U z b then outs := outs.push o
      if let some o := doOutlet deg (- (r.num : Int)) V U z b then outs := outs.push o
    else
      if let some o := doOutlet deg r.num U V z b then outs := outs.push o
      if let some o := doOutlet deg (- (r.num : Int)) U V z b then outs := outs.push o

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

partial def findIso (st : IsoState) (k : Nat) : Option (Array Nat) :=
  let totalNodes := st.c.ringSize + st.c.interiorSize
  if k == totalNodes then
    if isWellPositioned st.upp[0]! st.used then some st.mapping else none
  else Id.run do
    let mut prev_neighbors : Array Nat := #[]
    for i in [0:k] do
      if st.c.adj i k then
        prev_neighbors := prev_neighbors.push i
        
    let mut candBits : UInt64 := 0xFFFFFFFFFFFFFFFF
    if prev_neighbors.isEmpty then
      candBits := ((1 : UInt64) <<< CARTVERT.toUInt64) - 1
    else
      for i in prev_neighbors do
        candBits := candBits &&& st.adjBool[st.mapping[i]!]!
        
    let mut res := none
    for w in [0 : CARTVERT] do
      if (candBits &&& ((1 : UInt64) <<< w.toUInt64)) == 0 then continue
      if w >= st.upp.size then continue
      if st.used[w]! then continue
      
      let is_interior := k >= st.c.ringSize
      let exp_deg := st.degrees[k]!
      if exp_deg > st.upp[w]! then continue
      
      let new_mapping := st.mapping.set! k w
      let new_used := st.used.set! w true
      match findIso { st with mapping := new_mapping, used := new_used } (k + 1) with
      | some m => 
        res := some m
        break
      | none => continue
    res

partial def verifyReduce (configs : List Configuration) (A_low A_upp : Array Nat) (adjmat : Array (Array Int)) (adjBool : Array UInt64) : Bool := Id.run do
  let mut found := false
  let mut mapping : Array Nat := #[]
  let mut matched_c : Configuration := default
  
  for c in configs do
    let totalNodes := c.ringSize + c.interiorSize
    let degrees := mkArray totalNodes 0 |>.mapIdx fun i _ => getDegree c i
    let st : IsoState := {
      c := c,
      adjmat := adjmat,
      adjBool := adjBool,
      low := A_low,
      upp := A_upp,
      mapping := mkArray totalNodes CARTVERT,
      used := mkArray CARTVERT false,
      degrees := degrees
    }
    match findIso st 0 with
    | some m =>
      found := true
      mapping := m
      matched_c := c
      break
    | none => continue

  if not found then return false

  let mut all_reduced := true
  for i in [matched_c.ringSize : matched_c.ringSize + matched_c.interiorSize] do
    let v := mapping[i]!
    if A_low[v]! < A_upp[v]! then
      let mut A_upp_new := A_upp
      A_upp_new := A_upp_new.set! v (A_upp[v]! - 1)
      let adjmat_new := getAdjMat A_upp_new
      let adjBool_new := getAdjBool adjmat_new
      if not (verifyReduce configs A_low A_upp_new adjmat_new adjBool_new) then
        all_reduced := false
        break
        
  return all_reduced

def isReducible (configs : List Configuration) (A_low A_upp : Array Nat) (adjmat : Array (Array Int)) (adjBool : Array UInt64) : Bool :=
  verifyReduce configs A_low A_upp adjmat adjBool

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

partial def verifyTree (configs : List Configuration) (deg : Nat) (A_low A_upp : Array Nat) (t : ProofTree) (outs : Array Outlet) : Bool :=
  match t with
  | ProofTree.reduce =>
      let res := isReducible configs A_low A_upp (getAdjMat A_upp) (getAdjBool (getAdjMat A_upp))
      if not res then
        dbg_trace s!"isReducible returned false!"
        res
      else
        res
  | ProofTree.cond v m trueBranch falseBranch => Id.run do
    let mut AA_low_true := A_low
    let mut AA_upp_true := A_upp
    let mut AA_low_false := A_low
    let mut AA_upp_false := A_upp
    
    if m > 0 then
      AA_upp_false := AA_upp_false.set! v (m.toNat - 1)
      AA_low_true := AA_low_true.set! v m.toNat
    else
      AA_low_false := AA_low_false.set! v (1 - m).toNat
      AA_upp_true := AA_upp_true.set! v (-m).toNat

    let bTrue := verifyTree configs deg AA_low_true AA_upp_true trueBranch outs
    if not bTrue then
      dbg_trace "Failure in cond"
      return false
    else return verifyTree configs deg AA_low_false AA_upp_false falseBranch outs
  
  | ProofTree.sym _ _ _ _ =>
    -- TODO: CheckSymmetry
    true
  
  | ProofTree.hubcap members => Id.run do
    let adjmat := getAdjMat A_upp
    let adjBool := getAdjBool adjmat
    for (x, y, v) in members do
      let mut posout : Array PosOut := #[]
      for o in outs do
        posout := posout.push { T := o, x := x }
      if x != y then
        for o in outs do
          posout := posout.push { T := o, x := y }
      
      let s := mkArray posout.size 0
      if not (checkBound configs deg A_low A_upp posout s v 0 adjmat adjBool) then
          dbg_trace "Failure in hubcap"
        return false
    return true

end Math.Discharging
