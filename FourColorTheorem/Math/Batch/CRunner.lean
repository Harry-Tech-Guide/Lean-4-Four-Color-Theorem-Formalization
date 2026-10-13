import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# Optimized C-Reducibility Batch Runner for In-Kernel Reflection

This module implements the verified C-reducibility reflection runner for RSST
configurations with non-empty contraction specifications (`contract > 0`).

A configuration is C-reducible modulo a contract `E_C` if for every proper 4-coloring
of the contracted graph `G / E_C`, its induced boundary coloring on the ring does NOT
belong to the consistent live set `live` (i.e., it extends to the uncontracted configuration).
-/

/-- Check that NO proper coloring of the contracted configuration restricts to a trace in `live`.
    Equivalently: every proper coloring of the contracted configuration extends to the original configuration! -/
partial def checkContractExact (earlier : Array (Array Nat)) (alias : Array Nat) (n r v : Nat)
    (col : Array Nat) (pow3 : Array Nat) (live : ByteArray) : Bool :=
  if v >= n then Id.run do
    let mut idx := 0
    for i in [0:r] do
      let nxt := if i + 1 == r then 0 else i + 1
      let x := col[i]! ^^^ col[nxt]!
      if x == 0 then return true
      let d_i := x - 1
      idx := idx + d_i * pow3[i]!
    if live.get! idx == 1 then
      return false
    return true
  else Id.run do
    let root_v := alias[v]!
    if root_v < v then
      let c := col[root_v]!
      for u in earlier[v]! do
        if alias[u]! != root_v && col[u]! == c then
          return true
      let col' := col.set! v c
      return checkContractExact earlier alias n r (v + 1) col' pow3 live
    else
      let mut used : Nat := 0
      for u in earlier[v]! do
        if alias[u]! != root_v then
          used := used ||| (1 <<< col[u]!)
      let mut col' := col
      for c in [0:4] do
        if (used >>> c) &&& 1 == 0 then
          col' := col'.set! v c
          if not (checkContractExact earlier alias n r (v + 1) col' pow3 live) then
            return false
      return true

/-- Test whether a configuration's contraction eliminates all remaining consistent live colorings. -/
def runContractCheck (c : RConf) (pow3 : Array Nat) (live : ByteArray) : Bool := Id.run do
  let mut alias := mkArray c.n 0
  for i in [0:c.n] do alias := alias.set! i i
  for _ in [0:c.n] do
    for (u, v) in c.contractEdges do
      let root_u := alias[u]!
      let root_v := alias[v]!
      let mn := min root_u root_v
      alias := alias.set! u mn
      alias := alias.set! v mn
      alias := alias.set! root_u mn
      alias := alias.set! root_v mn
  let col : Array Nat := mkArray c.n 0
  return checkContractExact c.earlier alias c.n c.r 1 col pow3 live

/-- Combined D-reduction fixed-point solver and C-reduction contract validator. -/
def checkCFast (c : RConf) (sms : Array SMData) (pow3 : Array Nat) : Bool := Id.run do
  let r := c.r
  let N := pow3[r]!
  let (live0, orbits0) := initialLiveFast c pow3
  let mut live := live0
  let mut orbits := orbits0
  let mut activeSM := sms
  let mut changed := true
  while changed && !orbits.isEmpty do
    let mut cover := zeros N
    let mut nextSM : Array SMData := Array.mkEmpty activeSM.size
    for sm in activeSM do
      if allFitLive sm live 0 0 then
        cover := markFitCover sm 0 0 cover
        nextSM := nextSM.push sm
    activeSM := nextSM
    let mut nextOrbits : Array Orbit6 := Array.mkEmpty orbits.size
    for orb in orbits do
      if cover.get! orb.j0 == 1 && cover.get! orb.j2 == 1 && cover.get! orb.j5 == 1 then
        nextOrbits := nextOrbits.push orb
      else
        live := live.set! orb.j0 0
        live := live.set! orb.j1 0
        live := live.set! orb.j2 0
        live := live.set! orb.j3 0
        live := live.set! orb.j4 0
        live := live.set! orb.j5 0
    changed := nextOrbits.size != orbits.size
    orbits := nextOrbits
  if orbits.isEmpty then
    return true
  else
    return runContractCheck c pow3 live

/-- Check a single configuration index for C-reducibility using the precomputed signed-matching table. -/
def checkIdxCFast (sms : Array SMData) (idx : Nat) : Bool :=
  checkCFast sharedCfgs[idx]! sms sharedPow3

/-- Evaluate C-reducibility for a batch of configurations with the same ring size. -/
def checkCRingBatch (r : Nat) (indices : List Nat) : Bool :=
  let sms := buildSMData r sharedPow3
  indices.all (checkIdxCFast sms)

/-- Soundness extraction lemma for C-reducibility batches. -/
theorem certified_of_cbatch (r : Nat) (indices : List Nat)
    (hBatch : checkCRingBatch r indices = true)
    (idx : Nat) (hMem : idx ∈ indices) :
    checkIdxCFast (buildSMData r sharedPow3) idx = true :=
  List.all_eq_true.mp hBatch idx hMem

end Batch
end Math
