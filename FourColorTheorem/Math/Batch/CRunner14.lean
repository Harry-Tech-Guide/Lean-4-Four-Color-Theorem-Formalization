import FourColorTheorem.Math.Batch.CRunner
import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

/-!
# Optimized C-Reducibility Batch Runner for Ring 14 In-Kernel Reflection

This module implements the verified C-reducibility reflection runner for RSST
configurations with ring size 14 using canonical trace generation (`genCanonicalLive`).
-/

/-- Fast C-reducibility checker for Ring 14 configurations. -/
def checkCFast14 (c : RConf) (sms : Array SMData) (pow3 : Array Nat) : Bool := Id.run do
  let r := c.r
  let N := pow3[r]!
  let (live0, orbits0) := genCanonicalLive c pow3
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

/-- Check a single ring-14 configuration index using the precomputed signed-matching table. -/
def checkIdxCFast14 (sms : Array SMData) (idx : Nat) : Bool :=
  checkCFast14 sharedCfgs[idx]! sms sharedPow3

/-- Batch checker for ring 14 C-reducible configurations. -/
def checkCRingBatch14 (indices : List Nat) : Bool :=
  let sms := buildSMData 14 sharedPow3
  indices.all (checkIdxCFast14 sms)

/-- Soundness extraction lemma for ring-14 C-reducibility batches. -/
theorem certified_of_cbatch14 (indices : List Nat)
    (hBatch : checkCRingBatch14 indices = true)
    (idx : Nat) (hMem : idx ∈ indices) :
    checkIdxCFast14 (buildSMData 14 sharedPow3) idx = true :=
  List.all_eq_true.mp hBatch idx hMem

end Batch
end Math
