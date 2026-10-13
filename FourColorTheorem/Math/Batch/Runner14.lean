import FourColorTheorem.Math.Batch.Runner
import FourColorTheorem.Math.Batch.Runner13

namespace Math
namespace Batch

open FastReducer

/-!
# Optimized Batch Verification Runner for Ring 14 In-Kernel Reflection

This module provides the batch verification runner for ring size 14 (search space 3^14 ≈ 4.78M).
It uses `genCanonicalLive` from `Runner13.lean` to prune the state space by 24× and eliminates
all base-3 division/modulo operations in the trace generation loop.
-/

/-- Fast exact D-reducibility checker for ring 14 using canonical trace generation. -/
def checkFast14 (c : RConf) (sms : Array SMData) (pow3 : Array Nat) : Bool := Id.run do
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
  return orbits.isEmpty

/-- Check a single ring-14 configuration index using the precomputed signed-matching table. -/
def checkIdxFast14 (sms : Array SMData) (idx : Nat) : Bool :=
  checkFast14 sharedCfgs[idx]! sms sharedPow3

/-- Batch checker for ring 14 configurations. -/
def checkRingBatch14 (indices : List Nat) : Bool :=
  let sms := buildSMData 14 sharedPow3
  indices.all (checkIdxFast14 sms)

/-- Soundness extraction lemma for ring-14 batches. -/
theorem certified_of_batch14 (indices : List Nat)
    (hBatch : checkRingBatch14 indices = true)
    (idx : Nat) (hMem : idx ∈ indices) :
    checkIdxFast14 (buildSMData 14 sharedPow3) idx = true :=
  List.all_eq_true.mp hBatch idx hMem

end Batch
end Math
