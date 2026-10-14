import FourColorTheorem.Math.Batch.Runner

namespace Math
namespace Batch

open FastReducer

/-!
# Optimized Batch Verification Runner for Ring 13 & 14 In-Kernel Reflection

This module optimizes initial live-state generation for larger ring sizes (r ≥ 13)
by replacing the full-cube enumeration (3^r iterations) with `genCanonicalLive`, which
directly recurses through valid canonical colorings without division or modulo operations.
-/

/-- Efficiently generate canonical live traces and their S₃-orbits for ring size `r`.
    Returns (live, orbits, extOrbits). Seeds j0..j5 with 0 0 1 1 2 2 to match
    perms[k][0] * 3^0 at boundary position 0. -/
partial def genCanonicalLive (c : RConf) (pow3 : Array Nat) : ByteArray × Array Orbit6 × Nat := Id.run do
  let r := c.r
  let N := pow3[r]!
  let live := zeros N
  let orbits : Array Orbit6 := #[]
  let col : Array Nat := mkArray c.n 0
  
  let rec go (i : Nat) (seen1 : Bool) (x cv j0 j1 j2 j3 j4 j5 : Nat) (extCount : Nat) (col : Array Nat)
      (live : ByteArray) (orbits : Array Orbit6) : (Array Nat × ByteArray × Array Orbit6 × Nat) :=
    if i == r - 1 then
      if x >= 1 && x <= 3 then
        let last_d := x - 1
        if seen1 || last_d != 2 then
          let p_r := pow3[i]!
          let k0 := j0 + last_d * p_r
          let k1 := j1 + perms[1]![last_d]! * p_r
          let k2 := j2 + perms[2]![last_d]! * p_r
          let k3 := j3 + perms[3]![last_d]! * p_r
          let k4 := j4 + perms[4]![last_d]! * p_r
          let k5 := j5 + perms[5]![last_d]! * p_r
          let col' := col.set! i cv
          let (ok, col'') := extend c.earlier c.n r col'
          if !ok then
            let live' := (((((live.set! k0 1).set! k1 1).set! k2 1).set! k3 1).set! k4 1).set! k5 1
            let orbits' := orbits.push ⟨k0, k1, k2, k3, k4, k5⟩
            (col'', live', orbits', extCount)
          else
            (col'', live, orbits, extCount + 1)
        else (col, live, orbits, extCount)
      else (col, live, orbits, extCount)
    else
      let col' := col.set! i cv
      let p_i := pow3[i]!
      let (col1, live1, orb1, ext1) := go (i + 1) seen1 (x ^^^ 1) (cv ^^^ 1)
        j0 (j1 + perms[1]![0]! * p_i) (j2 + perms[2]![0]! * p_i) (j3 + perms[3]![0]! * p_i)
        (j4 + perms[4]![0]! * p_i) (j5 + perms[5]![0]! * p_i) extCount col' live orbits
      let (col2, live2, orb2, ext2) := go (i + 1) true (x ^^^ 2) (cv ^^^ 2)
        (j0 + p_i) (j1 + perms[1]![1]! * p_i) (j2 + perms[2]![1]! * p_i) (j3 + perms[3]![1]! * p_i)
        (j4 + perms[4]![1]! * p_i) (j5 + perms[5]![1]! * p_i) ext1 col1 live1 orb1
      if seen1 then
        go (i + 1) true (x ^^^ 3) (cv ^^^ 3)
          (j0 + 2 * p_i) (j1 + perms[1]![2]! * p_i) (j2 + perms[2]![2]! * p_i) (j3 + perms[3]![2]! * p_i)
          (j4 + perms[4]![2]! * p_i) (j5 + perms[5]![2]! * p_i) ext2 col2 live2 orb2
      else
        (col2, live2, orb2, ext2)

  let (_, liveRes, orbRes, extRes) := go 1 false 1 1 0 0 1 1 2 2 0 col live orbits
  return (liveRes, orbRes, extRes)

/-- Fast exact D-reducibility checker for ring 13 using canonical trace generation.
    Cross-verifies that extendable orbit count matches RSST metadata `c.X`. -/
def checkFast13 (c : RConf) (sms : Array SMData) (pow3 : Array Nat) : Bool := Id.run do
  let r := c.r
  let N := pow3[r]!
  let (live0, orbits0, extOrbits) := genCanonicalLive c pow3
  if extOrbits != c.X then return false
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
  return orbits.isEmpty

/-- Check a single ring-13 configuration index using the precomputed signed-matching table. -/
def checkIdxFast13 (sms : Array SMData) (idx : Nat) : Bool :=
  checkFast13 sharedCfgs[idx]! sms sharedPow3

/-- Batch checker for ring 13 configurations. -/
def checkRingBatch13 (indices : List Nat) : Bool :=
  let sms := buildSMData 13 sharedPow3
  indices.all (checkIdxFast13 sms)

/-- Soundness extraction lemma for ring-13 batches. -/
theorem certified_of_batch13 (indices : List Nat)
    (hBatch : checkRingBatch13 indices = true)
    (idx : Nat) (hMem : idx ∈ indices) :
    checkIdxFast13 (buildSMData 13 sharedPow3) idx = true :=
  List.all_eq_true.mp hBatch idx hMem

end Batch
end Math
