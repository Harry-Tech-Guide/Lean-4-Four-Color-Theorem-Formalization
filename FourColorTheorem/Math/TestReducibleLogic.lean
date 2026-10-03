import FourColorTheorem.Math.DischargingAlgo

namespace Math.Discharging

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
  upp : Array Nat
  mapping : Array Nat
  used : Array Bool
  degrees : Array Nat

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
    let prev_neighbors := (List.range k).filter (fun i => st.c.adj i k)
    let candidates := 
      if prev_neighbors.isEmpty then List.range CARTVERT
      else getNeighbors st.adjmat st.mapping[prev_neighbors.head!]!
    
    let mut res := none
    for w in candidates do
      if st.used[w]! then continue
      let is_interior := k >= st.c.ringSize
      let exp_deg := st.degrees[k]!
      if is_interior && st.upp[w]! != exp_deg then continue
      
      let edges_ok := prev_neighbors.all fun i => isAdj st.adjmat st.mapping[i]! w
      if not edges_ok then continue
      
      let new_mapping := st.mapping.set! k w
      let new_used := st.used.set! w true
      match findIso { st with mapping := new_mapping, used := new_used } (k + 1) with
      | some m => 
        res := some m
        break
      | none => continue
    res

partial def verifyReduce (A_low A_upp : Array Nat) : Bool := Id.run do
  let adjmat := getAdjMat A_upp
  let mut found := false
  let mut mapping : Array Nat := #[]
  let mut matched_c : Configuration := default
  
  for c in theUnavoidableSet do
    let totalNodes := c.ringSize + c.interiorSize
    let degrees := mkArray totalNodes 0 |>.mapIdx fun i _ => getDegree c i
    let st : IsoState := {
      c := c,
      adjmat := adjmat,
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
      if not (verifyReduce A_low A_upp_new) then
        all_reduced := false
        break
        
  return all_reduced

end Math.Discharging
