import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# Batch Verification Runner for In-Kernel Reflection

This module provides shared helper definitions for evaluating batches of RSST
configurations inside Lean 4's kernel via `native_decide`.
-/

/-- Precomputed powers of 3 up to 3^15. -/
def sharedPow3 : Array Nat := powers3 15

/-- Precomputed parsed array of all 633 RSST configurations. -/
def sharedCfgs : Array RConf := loadAll ()

/-- Check a single configuration index `idx` using a given matching table `md`. -/
def checkIdxWithMData (md : Array MData × Nat) (idx : Nat) : Bool :=
  (check sharedCfgs[idx]! md sharedPow3).dReducible

/-- Evaluate D-reducibility for a list of configuration indices sharing the same ring size `r`.
    Precomputes the signed non-crossing matching table `md` once for the entire list. -/
def checkRingBatch (r : Nat) (indices : List Nat) : Bool :=
  let md := buildMData r sharedPow3
  indices.all (checkIdxWithMData md)

/-- Soundness extraction lemma: if `checkRingBatch r indices = true`, then every `idx ∈ indices`
    is certified D-reducible by `FastReducer.check`. -/
theorem certified_of_batch (r : Nat) (indices : List Nat)
    (hBatch : checkRingBatch r indices = true)
    (idx : Nat) (hMem : idx ∈ indices) :
    checkIdxWithMData (buildMData r sharedPow3) idx = true :=
  List.all_eq_true.mp hBatch idx hMem

end Batch
end Math
