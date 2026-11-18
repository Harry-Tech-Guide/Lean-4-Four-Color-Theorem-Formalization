module

public import FourColorTheorem.Math.KernelReducer
public import FourColorTheorem.Math.CheckerSoundness.InitialLive

@[expose] public section

namespace Math
namespace KernelSoundness

open KernelReducer
open FastReducer
open Batch
open Soundness
open CheckerSoundness

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

attribute [-simp] Nat.lor_eq Nat.land_eq Nat.xor_eq Nat.shiftLeft_eq' Nat.shiftRight_eq'

/-!
# Checkpoint K4.1: Canonical Slice Bijection, `repeatBlock` Specification, and $S_3$ Digit Swaps

This module establishes the foundational bit-level and base-3 lemmas for `KernelReducer`:
1. **`getRConf_eq_sharedCfgs`:** Connects `KernelReducer.getRConf idx` (`(getRConfBox idx).val`) to
   `Batch.sharedCfgs[idx]!` and `theUnavoidableSet[idx]!` for all `idx < 633`.
2. **`runDLiveLoop_sound` & `runCLiveLoop_sound`:** Extracts the terminal round index `k ≤ fuel`
   where `stepKempeRounds ... k L2 = 0` (for D-reducibility) or
   `Nat.land (stepKempeRounds ... k L2) contractCanon = 0` (for C-reducibility).
3. **Bit-Routing & $S_3$ Digit Swaps (`swap12Idx`, `swap01Idx`, `swap02Idx`):**
   Connects `swapDigits12`, `swapDigits01`, and `swapDigits02` to base-3 digit permutations on
   the canonical $d_{r-2} = 0$ slice `[0, 3^{r-2})`.
4. **`canonIdx` & `KernelLiveInvariant`:** Defines the canonical $d_{r-2} = 0$ slice index of any
   boundary coloring `b` and the direct bitmask elimination invariant `KernelLiveInvariant c L`.
-/

/-!
### Part 1: Connection Between `KernelReducer.getRConf` and `sharedCfgs` / `theUnavoidableSet`
-/

/-- Helper lemma for `getRConfBox.go` on an arbitrary list `L : List RConf`. -/
theorem getRConfBox_go_eq (L : List RConf) (idx : Nat) (hIdx : idx < L.length) :
    (getRConfBox.go L idx).val = L[idx]'hIdx := by
  induction L generalizing idx with
  | nil => contradiction
  | cons hd tl ih =>
    cases idx with
    | zero => rfl
    | succ i' =>
      have hi' : i' < tl.length := by
        dsimp at hIdx
        omega
      exact ih i' hi'

/-- For every `idx < 633`, `KernelReducer.getRConf idx` equals `Batch.sharedCfgs[idx]!`. -/
theorem getRConf_eq_sharedCfgs (idx : Nat) (hIdx : idx < 633) :
    KernelReducer.getRConf idx = Batch.sharedCfgs[idx]! := by
  unfold KernelReducer.getRConf KernelReducer.getRConfBox
  have hLen : idx < parsedRConfList.length := by
    rw [parsedRConfList_length]
    exact hIdx
  rw [getRConfBox_go_eq parsedRConfList idx hLen]
  let arr : Array RConf := ⟨parsedRConfList⟩
  have hSz : idx < arr.size := hLen
  change parsedRConfList[idx]'hLen = arr[idx]!
  rw [getElem!_pos arr idx hSz]
  rfl

/-- For every `idx < 633`, `configOfRConf (KernelReducer.getRConf idx)` equals `theUnavoidableSet[idx]!`. -/
theorem configOfRConf_getRConf_eq (idx : Nat) (hIdx : idx < 633) :
    configOfRConf (KernelReducer.getRConf idx) = theUnavoidableSet[idx]! := by
  rw [getRConf_eq_sharedCfgs idx hIdx, theUnavoidableSet_getElem! idx hIdx]

/-!
### Part 2: Loop Termination Witness Extraction for `runDLiveLoop` and `runCLiveLoop`
-/

/-- `KernelReducer.pow3 n` equals `3 ^ n`. -/
theorem kernel_pow3_eq (n : Nat) : KernelReducer.pow3 n = 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 3 * KernelReducer.pow3 n = 3 ^ (n + 1)
    rw [ih, Nat.pow_succ, Nat.mul_comm]

/-- If `runDLiveLoop ... fuel L2 = true`, then there exists `k ≤ fuel` such that
    `stepKempeRounds ... k L2 = 0`. -/
theorem runDLiveLoop_sound
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (fuel L2 : Nat)
    (h : runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel L2 = true) :
    ∃ k ≤ fuel,
      stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs k L2 = 0 := by
  induction fuel generalizing L2 with
  | zero =>
    change Nat.beq L2 0 = true at h
    exact ⟨0, Nat.le_refl 0, Nat.beq_eq.mp h⟩
  | succ fuel ih =>
    change selectBool (Nat.beq L2 0) true
      (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
        (runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel
          (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2))) = true at h
    rw [seqNat_eq] at h
    cases hZ : Nat.beq L2 0 with
    | true =>
      exact ⟨0, Nat.zero_le _, Nat.beq_eq.mp hZ⟩
    | false =>
      rw [hZ] at h
      dsimp at h
      rcases ih (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2) h with ⟨k, hk, hStep⟩
      refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
      change seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
        (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs k
          (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)) = 0
      rw [seqNat_eq]
      exact hStep

/-- If `runCLiveLoop ... contractCanon fuel L2 = true`, then there exists `k ≤ fuel` such that
    `Nat.land (stepKempeRounds ... k L2) contractCanon = 0`. -/
theorem runCLiveLoop_sound
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (contractCanon fuel L2 : Nat)
    (h : runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel L2 = true) :
    ∃ k ≤ fuel,
      Nat.land (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs k L2) contractCanon = 0 := by
  induction fuel generalizing L2 with
  | zero =>
    change Nat.beq (Nat.land L2 contractCanon) 0 = true at h
    exact ⟨0, Nat.le_refl 0, Nat.beq_eq.mp h⟩
  | succ fuel ih =>
    change selectBool (Nat.beq (Nat.land L2 contractCanon) 0) true
      (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
        (runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel
          (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2))) = true at h
    rw [seqNat_eq] at h
    cases hZ : Nat.beq (Nat.land L2 contractCanon) 0 with
    | true =>
      exact ⟨0, Nat.zero_le _, Nat.beq_eq.mp hZ⟩
    | false =>
      rw [hZ] at h
      dsimp at h
      rcases ih (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2) h with ⟨k, hk, hStep⟩
      refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
      change Nat.land
        (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
          (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs k
            (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)))
        contractCanon = 0
      rw [seqNat_eq]
      exact hStep

/-- Unpacking `verifyIdxD idx = true` into a `stepKempeRounds` witness `k ≤ 120`. -/
theorem verifyIdxD_steps_zero (idx : Nat) (h : KernelReducer.verifyIdxD idx = true) :
    let rc := KernelReducer.getRConf idx
    let rVal := rc.r
    let mMaxVal := rVal - 1
    let mMax1 := mMaxVal - 1
    let pTop := KernelReducer.pow3 mMax1
    let swapSteps1 := (buildSwapSteps mMax1).val
    let (packLevels, unpackRevLevels) := buildAllPackUnpackLevels mMaxVal
    let bucketSpecs := (buildAllBucketSpecs rVal mMaxVal).val
    ∃ k ≤ 120,
      stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs k (initLiveIdx idx) = 0 := by
  dsimp
  change selectBool (Nat.beq (initLiveIdx idx) 0) true
    (runEngineD (buildKempeEngine (getRConf idx).r) 120 (initLiveIdx idx)) = true at h
  cases hZ : Nat.beq (initLiveIdx idx) 0 with
  | true =>
    exact ⟨0, Nat.zero_le 120, Nat.beq_eq.mp hZ⟩
  | false =>
    rw [hZ] at h
    dsimp [buildKempeEngine, Nat.sub_eq] at h
    rcases hPack : buildAllPackUnpackLevels ((getRConf idx).r - 1) with ⟨packLevels, unpackRevLevels⟩
    rw [hPack] at h
    dsimp [runEngineD] at h
    rw [seqNat_eq] at h
    exact runDLiveLoop_sound _ _ packLevels unpackRevLevels _ 120 (initLiveIdx idx) h

/-- Unpacking `verifyIdxC idx = true` into a `stepKempeRounds` witness `k ≤ 120`. -/
theorem verifyIdxC_steps_land_zero (idx : Nat) (h : KernelReducer.verifyIdxC idx = true) :
    let rc := KernelReducer.getRConf idx
    let rVal := rc.r
    let mMaxVal := rVal - 1
    let mMax1 := mMaxVal - 1
    let pTop := KernelReducer.pow3 mMax1
    let swapSteps1 := (buildSwapSteps mMax1).val
    let (packLevels, unpackRevLevels) := buildAllPackUnpackLevels mMaxVal
    let bucketSpecs := (buildAllBucketSpecs rVal mMaxVal).val
    ∃ k ≤ 120,
      Nat.land
        (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs k (initLiveIdx idx))
        (contractCanonIdx idx) = 0 := by
  dsimp
  change selectBool (Nat.beq (Nat.land (initLiveIdx idx) (contractCanonIdx idx)) 0) true
    (runEngineC (buildKempeEngine (getRConf idx).r) (contractCanonIdx idx) 120 (initLiveIdx idx)) = true at h
  cases hZ : Nat.beq (Nat.land (initLiveIdx idx) (contractCanonIdx idx)) 0 with
  | true =>
    exact ⟨0, Nat.zero_le 120, Nat.beq_eq.mp hZ⟩
  | false =>
    rw [hZ] at h
    dsimp [buildKempeEngine, Nat.sub_eq] at h
    rcases hPack : buildAllPackUnpackLevels ((getRConf idx).r - 1) with ⟨packLevels, unpackRevLevels⟩
    rw [hPack] at h
    dsimp [runEngineC] at h
    rw [seqNat_eq] at h
    exact runCLiveLoop_sound _ _ packLevels unpackRevLevels _ (contractCanonIdx idx) 120 (initLiveIdx idx) h

/-!
### Part 3: Bitwise Routing Soundness for `SwapStep` and `swapDigits12` / `swapDigits01` / `swapDigits02`
-/

@[simp] theorem testBit_lor (a b j : Nat) :
    Nat.testBit (Nat.lor a b) j = (Nat.testBit a j || Nat.testBit b j) :=
  Nat.testBit_or a b j

@[simp] theorem testBit_land (a b j : Nat) :
    Nat.testBit (Nat.land a b) j = (Nat.testBit a j && Nat.testBit b j) :=
  Nat.testBit_and a b j

@[simp] theorem testBit_xor (a b j : Nat) :
    Nat.testBit (Nat.xor a b) j = Bool.xor (Nat.testBit a j) (Nat.testBit b j) :=
  Nat.testBit_xor a b j

@[simp] theorem testBit_shiftRight (a s j : Nat) :
    Nat.testBit (Nat.shiftRight a s) j = Nat.testBit a (s + j) :=
  Nat.testBit_shiftRight a

@[simp] theorem testBit_shiftLeft (a s j : Nat) :
    Nat.testBit (Nat.shiftLeft a s) j = (decide (j ≥ s) && Nat.testBit a (j - s)) :=
  Nat.testBit_shiftLeft a

/-- Single-step execution of `swapDigits12` on `acc`. -/
def stepSwap12 (step : SwapStep) (acc : Nat) : Nat :=
  match step with
  | SwapStep.mk P _ m0 m1 _ =>
    let g00 := Nat.land acc m0
    let g12 := Nat.shiftLeft (Nat.land acc m1) P
    let g21 := Nat.land (Nat.shiftRight acc P) m1
    Nat.lor g00 (Nat.lor g21 g12)

/-- Single-step execution of `swapDigits01` on `acc`. -/
def stepSwap01 (step : SwapStep) (acc : Nat) : Nat :=
  match step with
  | SwapStep.mk P _ m0 _ m2 =>
    let g01 := Nat.shiftLeft (Nat.land acc m0) P
    let g10 := Nat.land (Nat.shiftRight acc P) m0
    let g22 := Nat.land acc m2
    Nat.lor g22 (Nat.lor g10 g01)

/-- Single-step execution of `swapDigits02` on `acc`. -/
def stepSwap02 (step : SwapStep) (acc : Nat) : Nat :=
  match step with
  | SwapStep.mk _ P2 m0 m1 _ =>
    let g02 := Nat.shiftLeft (Nat.land acc m0) P2
    let g20 := Nat.land (Nat.shiftRight acc P2) m0
    let g11 := Nat.land acc m1
    Nat.lor g11 (Nat.lor g20 g02)

/-- Index router for one `SwapStep` of `swapDigits12`. -/
def routeSwap12Step (step : SwapStep) (j : Nat) : Nat :=
  match step with
  | SwapStep.mk P _ m0 m1 _ =>
    if Nat.testBit m0 j then j
    else if Nat.testBit m1 j then j + P
    else if P ≤ j && Nat.testBit m1 (j - P) then j - P
    else j

/-- Index router for one `SwapStep` of `swapDigits01`. -/
def routeSwap01Step (step : SwapStep) (j : Nat) : Nat :=
  match step with
  | SwapStep.mk P _ m0 _ m2 =>
    if Nat.testBit m2 j then j
    else if Nat.testBit m0 j then j + P
    else if P ≤ j && Nat.testBit m0 (j - P) then j - P
    else j

/-- Index router for one `SwapStep` of `swapDigits02`. -/
def routeSwap02Step (step : SwapStep) (j : Nat) : Nat :=
  match step with
  | SwapStep.mk _ P2 m0 m1 _ =>
    if Nat.testBit m1 j then j
    else if Nat.testBit m0 j then j + P2
    else if P2 ≤ j && Nat.testBit m0 (j - P2) then j - P2
    else j

/-- Reverse-order index routing across a list of `SwapStep`s: since `swapDigits12 steps X`
    applies the head of `steps` first and the tail later, tracing output bit `j` backwards
    routes through `rest` first and then `step`. -/
def routeSwap12List : List SwapStep → Nat → Nat
  | [], j => j
  | step :: rest, j => routeSwap12Step step (routeSwap12List rest j)

def routeSwap01List : List SwapStep → Nat → Nat
  | [], j => j
  | step :: rest, j => routeSwap01Step step (routeSwap01List rest j)

def routeSwap02List : List SwapStep → Nat → Nat
  | [], j => j
  | step :: rest, j => routeSwap02Step step (routeSwap02List rest j)

/-- Validity of `routeSwap12Step` at bit `j`: at least one of the three mask conditions holds at `j`. -/
def ValidSwap12Bit (step : SwapStep) (j : Nat) : Bool :=
  match step with
  | SwapStep.mk P _ m0 m1 _ =>
    Nat.testBit m0 j || Nat.testBit m1 j || (decide (P ≤ j) && Nat.testBit m1 (j - P))

def ValidSwap01Bit (step : SwapStep) (j : Nat) : Bool :=
  match step with
  | SwapStep.mk P _ m0 _ m2 =>
    Nat.testBit m2 j || Nat.testBit m0 j || (decide (P ≤ j) && Nat.testBit m0 (j - P))

def ValidSwap02Bit (step : SwapStep) (j : Nat) : Bool :=
  match step with
  | SwapStep.mk _ P2 m0 m1 _ =>
    Nat.testBit m1 j || Nat.testBit m0 j || (decide (P2 ≤ j) && Nat.testBit m0 (j - P2))

/-- Soundness of a single `stepSwap12` when `Nat.testBit (stepSwap12 step acc) j = false`. -/
theorem stepSwap12_false_sound (step : SwapStep) (acc j : Nat)
    (hValid : ValidSwap12Bit step j = true)
    (hFalse : Nat.testBit (stepSwap12 step acc) j = false) :
    Nat.testBit acc (routeSwap12Step step j) = false := by
  cases step with
  | mk P P2 m0 m1 m2 =>
    dsimp [stepSwap12, routeSwap12Step, ValidSwap12Bit] at hValid hFalse ⊢
    rw [testBit_lor, testBit_lor, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hFalse
    rcases hFalse with ⟨h00, h21, h12⟩
    by_cases hm0 : Nat.testBit m0 j = true
    · rw [if_pos hm0]
      rw [testBit_land, hm0, Bool.and_true] at h00
      exact h00
    · rw [if_neg hm0]
      by_cases hm1 : Nat.testBit m1 j = true
      · rw [if_pos hm1]
        rw [testBit_land, hm1, Bool.and_true, testBit_shiftRight, Nat.add_comm P j] at h21
        exact h21
      · rw [if_neg hm1]
        have hm0F : Nat.testBit m0 j = false := Bool.eq_false_iff.mpr hm0
        have hm1F : Nat.testBit m1 j = false := Bool.eq_false_iff.mpr hm1
        rw [hm0F, hm1F, Bool.false_or, Bool.false_or] at hValid
        have hCond : (P ≤ j && Nat.testBit m1 (j - P)) = true := hValid
        rw [if_pos hCond]
        rcases Bool.and_eq_true_iff.mp hValid with ⟨hLeB, hm1Sub⟩
        have hLe : j ≥ P := of_decide_eq_true hLeB
        rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and,
            testBit_land, hm1Sub, Bool.and_true] at h12
        exact h12

/-- Soundness of a single `stepSwap01` when `Nat.testBit (stepSwap01 step acc) j = false`. -/
theorem stepSwap01_false_sound (step : SwapStep) (acc j : Nat)
    (hValid : ValidSwap01Bit step j = true)
    (hFalse : Nat.testBit (stepSwap01 step acc) j = false) :
    Nat.testBit acc (routeSwap01Step step j) = false := by
  cases step with
  | mk P P2 m0 m1 m2 =>
    dsimp [stepSwap01, routeSwap01Step, ValidSwap01Bit] at hValid hFalse ⊢
    rw [testBit_lor, testBit_lor, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hFalse
    rcases hFalse with ⟨h22, h10, h01⟩
    by_cases hm2 : Nat.testBit m2 j = true
    · rw [if_pos hm2]
      rw [testBit_land, hm2, Bool.and_true] at h22
      exact h22
    · rw [if_neg hm2]
      by_cases hm0 : Nat.testBit m0 j = true
      · rw [if_pos hm0]
        rw [testBit_land, hm0, Bool.and_true, testBit_shiftRight, Nat.add_comm P j] at h10
        exact h10
      · rw [if_neg hm0]
        have hm2F : Nat.testBit m2 j = false := Bool.eq_false_iff.mpr hm2
        have hm0F : Nat.testBit m0 j = false := Bool.eq_false_iff.mpr hm0
        rw [hm2F, hm0F, Bool.false_or, Bool.false_or] at hValid
        have hCond : (P ≤ j && Nat.testBit m0 (j - P)) = true := hValid
        rw [if_pos hCond]
        rcases Bool.and_eq_true_iff.mp hValid with ⟨hLeB, hm0Sub⟩
        have hLe : j ≥ P := of_decide_eq_true hLeB
        rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and,
            testBit_land, hm0Sub, Bool.and_true] at h01
        exact h01

/-- Soundness of a single `stepSwap02` when `Nat.testBit (stepSwap02 step acc) j = false`. -/
theorem stepSwap02_false_sound (step : SwapStep) (acc j : Nat)
    (hValid : ValidSwap02Bit step j = true)
    (hFalse : Nat.testBit (stepSwap02 step acc) j = false) :
    Nat.testBit acc (routeSwap02Step step j) = false := by
  cases step with
  | mk P P2 m0 m1 m2 =>
    dsimp [stepSwap02, routeSwap02Step, ValidSwap02Bit] at hValid hFalse ⊢
    rw [testBit_lor, testBit_lor, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hFalse
    rcases hFalse with ⟨h11, h20, h02⟩
    by_cases hm1 : Nat.testBit m1 j = true
    · rw [if_pos hm1]
      rw [testBit_land, hm1, Bool.and_true] at h11
      exact h11
    · rw [if_neg hm1]
      by_cases hm0 : Nat.testBit m0 j = true
      · rw [if_pos hm0]
        rw [testBit_land, hm0, Bool.and_true, testBit_shiftRight, Nat.add_comm P2 j] at h20
        exact h20
      · rw [if_neg hm0]
        have hm1F : Nat.testBit m1 j = false := Bool.eq_false_iff.mpr hm1
        have hm0F : Nat.testBit m0 j = false := Bool.eq_false_iff.mpr hm0
        rw [hm1F, hm0F, Bool.false_or, Bool.false_or] at hValid
        have hCond : (P2 ≤ j && Nat.testBit m0 (j - P2)) = true := hValid
        rw [if_pos hCond]
        rcases Bool.and_eq_true_iff.mp hValid with ⟨hLeB, hm0Sub⟩
        have hLe : j ≥ P2 := of_decide_eq_true hLeB
        rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and,
            testBit_land, hm0Sub, Bool.and_true] at h02
        exact h02

/-- Multi-step fold for `swapDigits12`. -/
def foldSwap12 : List SwapStep → Nat → Nat
  | [], acc => acc
  | step :: rest, acc => foldSwap12 rest (stepSwap12 step acc)

/-- Multi-step fold for `swapDigits01`. -/
def foldSwap01 : List SwapStep → Nat → Nat
  | [], acc => acc
  | step :: rest, acc => foldSwap01 rest (stepSwap01 step acc)

/-- Multi-step fold for `swapDigits02`. -/
def foldSwap02 : List SwapStep → Nat → Nat
  | [], acc => acc
  | step :: rest, acc => foldSwap02 rest (stepSwap02 step acc)

theorem foldSwap12_zero (steps : List SwapStep) : foldSwap12 steps 0 = 0 := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | mk P P2 m0 m1 m2 =>
      change foldSwap12 rest (stepSwap12 (SwapStep.mk P P2 m0 m1 m2) 0) = 0
      have h0 : stepSwap12 (SwapStep.mk P P2 m0 m1 m2) 0 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        dsimp [stepSwap12]
        simp
      rw [h0]
      exact ih

theorem foldSwap01_zero (steps : List SwapStep) : foldSwap01 steps 0 = 0 := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | mk P P2 m0 m1 m2 =>
      change foldSwap01 rest (stepSwap01 (SwapStep.mk P P2 m0 m1 m2) 0) = 0
      have h0 : stepSwap01 (SwapStep.mk P P2 m0 m1 m2) 0 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        dsimp [stepSwap01]
        simp
      rw [h0]
      exact ih

theorem foldSwap02_zero (steps : List SwapStep) : foldSwap02 steps 0 = 0 := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | mk P P2 m0 m1 m2 =>
      change foldSwap02 rest (stepSwap02 (SwapStep.mk P P2 m0 m1 m2) 0) = 0
      have h0 : stepSwap02 (SwapStep.mk P P2 m0 m1 m2) 0 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        dsimp [stepSwap02]
        simp
      rw [h0]
      exact ih

/-- `swapDigits12 steps X` equals `foldSwap12 steps X` for all `X`. -/
theorem swapDigits12_eq_fold (steps : List SwapStep) (X : Nat) :
    swapDigits12 steps X = foldSwap12 steps X := by
  unfold swapDigits12
  have hRec :
      (@List.rec SwapStep (fun _ => Nat → Nat)
        (fun acc => acc)
        (fun step _ ih acc =>
          @SwapStep.rec (fun _ => Nat)
            (fun P _ m0 m1 _ =>
              let g00 := Nat.land acc m0
              let g12 := Nat.shiftLeft (Nat.land acc m1) P
              let g21 := Nat.land (Nat.shiftRight acc P) m1
              ih (Nat.lor g00 (Nat.lor g21 g12)))
            step)
        steps X) = foldSwap12 steps X := by
    induction steps generalizing X with
    | nil => rfl
    | cons step rest ih =>
      cases step with
      | mk P P2 m0 m1 m2 =>
        exact ih (stepSwap12 (SwapStep.mk P P2 m0 m1 m2) X)
  cases hZ : Nat.beq X 0 with
  | true =>
    have hX : X = 0 := Nat.beq_eq.mp hZ
    subst hX
    exact (foldSwap12_zero steps).symm
  | false =>
    exact hRec

/-- `swapDigits01 steps X` equals `foldSwap01 steps X` for all `X`. -/
theorem swapDigits01_eq_fold (steps : List SwapStep) (X : Nat) :
    swapDigits01 steps X = foldSwap01 steps X := by
  unfold swapDigits01
  have hRec :
      (@List.rec SwapStep (fun _ => Nat → Nat)
        (fun acc => acc)
        (fun step _ ih acc =>
          @SwapStep.rec (fun _ => Nat)
            (fun P _ m0 _ m2 =>
              let g01 := Nat.shiftLeft (Nat.land acc m0) P
              let g10 := Nat.land (Nat.shiftRight acc P) m0
              let g22 := Nat.land acc m2
              ih (Nat.lor g22 (Nat.lor g10 g01)))
            step)
        steps X) = foldSwap01 steps X := by
    induction steps generalizing X with
    | nil => rfl
    | cons step rest ih =>
      cases step with
      | mk P P2 m0 m1 m2 =>
        exact ih (stepSwap01 (SwapStep.mk P P2 m0 m1 m2) X)
  cases hZ : Nat.beq X 0 with
  | true =>
    have hX : X = 0 := Nat.beq_eq.mp hZ
    subst hX
    exact (foldSwap01_zero steps).symm
  | false =>
    exact hRec

/-- `swapDigits02 steps X` equals `foldSwap02 steps X` for all `X`. -/
theorem swapDigits02_eq_fold (steps : List SwapStep) (X : Nat) :
    swapDigits02 steps X = foldSwap02 steps X := by
  unfold swapDigits02
  have hRec :
      (@List.rec SwapStep (fun _ => Nat → Nat)
        (fun acc => acc)
        (fun step _ ih acc =>
          @SwapStep.rec (fun _ => Nat)
            (fun _ P2 m0 m1 _ =>
              let g02 := Nat.shiftLeft (Nat.land acc m0) P2
              let g20 := Nat.land (Nat.shiftRight acc P2) m0
              let g11 := Nat.land acc m1
              ih (Nat.lor g11 (Nat.lor g20 g02)))
            step)
        steps X) = foldSwap02 steps X := by
    induction steps generalizing X with
    | nil => rfl
    | cons step rest ih =>
      cases step with
      | mk P P2 m0 m1 m2 =>
        exact ih (stepSwap02 (SwapStep.mk P P2 m0 m1 m2) X)
  cases hZ : Nat.beq X 0 with
  | true =>
    have hX : X = 0 := Nat.beq_eq.mp hZ
    subst hX
    exact (foldSwap02_zero steps).symm
  | false =>
    exact hRec

/-- Multi-step validity of `routeSwap12List` at bit `j`. -/
def ValidSwap12List : List SwapStep → Nat → Bool
  | [], _ => true
  | step :: rest, j =>
    ValidSwap12List rest j && ValidSwap12Bit step (routeSwap12List rest j)

def ValidSwap01List : List SwapStep → Nat → Bool
  | [], _ => true
  | step :: rest, j =>
    ValidSwap01List rest j && ValidSwap01Bit step (routeSwap01List rest j)

def ValidSwap02List : List SwapStep → Nat → Bool
  | [], _ => true
  | step :: rest, j =>
    ValidSwap02List rest j && ValidSwap02Bit step (routeSwap02List rest j)

/-- Multi-step soundness of `swapDigits12`: if `ValidSwap12List steps j = true` and
    `Nat.testBit (swapDigits12 steps X) j = false`, then `Nat.testBit X (routeSwap12List steps j) = false`. -/
theorem swapDigits12_false_sound (steps : List SwapStep) (X j : Nat)
    (hValid : ValidSwap12List steps j = true)
    (hFalse : Nat.testBit (swapDigits12 steps X) j = false) :
    Nat.testBit X (routeSwap12List steps j) = false := by
  rw [swapDigits12_eq_fold] at hFalse
  induction steps generalizing X with
  | nil => exact hFalse
  | cons step rest ih =>
    dsimp [ValidSwap12List, routeSwap12List] at hValid ⊢
    rcases Bool.and_eq_true_iff.mp hValid with ⟨hRest, hStep⟩
    have hMid := ih (stepSwap12 step X) hRest hFalse
    exact stepSwap12_false_sound step X (routeSwap12List rest j) hStep hMid

/-- Multi-step soundness of `swapDigits01`. -/
theorem swapDigits01_false_sound (steps : List SwapStep) (X j : Nat)
    (hValid : ValidSwap01List steps j = true)
    (hFalse : Nat.testBit (swapDigits01 steps X) j = false) :
    Nat.testBit X (routeSwap01List steps j) = false := by
  rw [swapDigits01_eq_fold] at hFalse
  induction steps generalizing X with
  | nil => exact hFalse
  | cons step rest ih =>
    dsimp [ValidSwap01List, routeSwap01List] at hValid ⊢
    rcases Bool.and_eq_true_iff.mp hValid with ⟨hRest, hStep⟩
    have hMid := ih (stepSwap01 step X) hRest hFalse
    exact stepSwap01_false_sound step X (routeSwap01List rest j) hStep hMid

/-- Multi-step soundness of `swapDigits02`. -/
theorem swapDigits02_false_sound (steps : List SwapStep) (X j : Nat)
    (hValid : ValidSwap02List steps j = true)
    (hFalse : Nat.testBit (swapDigits02 steps X) j = false) :
    Nat.testBit X (routeSwap02List steps j) = false := by
  rw [swapDigits02_eq_fold] at hFalse
  induction steps generalizing X with
  | nil => exact hFalse
  | cons step rest ih =>
    dsimp [ValidSwap02List, routeSwap02List] at hValid ⊢
    rcases Bool.and_eq_true_iff.mp hValid with ⟨hRest, hStep⟩
    have hMid := ih (stepSwap02 step X) hRest hFalse
    exact stepSwap02_false_sound step X (routeSwap02List rest j) hStep hMid

/-!
### Part 4: Mathematical Base-3 Digit Swaps and Canonical Slice Index `canonIdx`
-/

/-- The `(01)` digit transposition swapping `0 ↔ 1` and fixing `2`. -/
def swap01Digit : Nat → Nat
  | 0 => 1
  | 1 => 0
  | d => d

/-- The `(02)` digit transposition swapping `0 ↔ 2` and fixing `1`. -/
def swap02Digit : Nat → Nat
  | 0 => 2
  | 2 => 0
  | d => d

/-- Apply digit map `f : Nat → Nat` to the first `k` base-3 digits of `j`. -/
def mapTernaryDigits (f : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, j => f (j % 3) + 3 * mapTernaryDigits f k (j / 3)

/-- Mathematical `(12)` digit swap on `[0, 3^k)`. -/
def swap12Idx (k j : Nat) : Nat :=
  mapTernaryDigits swap12Digit k j

/-- Mathematical `(01)` digit swap on `[0, 3^k)`. -/
def swap01Idx (k j : Nat) : Nat :=
  mapTernaryDigits swap01Digit k j

/-- Mathematical `(02)` digit swap on `[0, 3^k)`. -/
def swap02Idx (k j : Nat) : Nat :=
  mapTernaryDigits swap02Digit k j

theorem swap12Digit_lt_three (d : Nat) (hd : d < 3) : swap12Digit d < 3 := by
  revert d hd; decide

theorem swap01Digit_lt_three (d : Nat) (hd : d < 3) : swap01Digit d < 3 := by
  revert d hd; decide

theorem swap02Digit_lt_three (d : Nat) (hd : d < 3) : swap02Digit d < 3 := by
  revert d hd; decide

theorem swap12Digit_involutive (d : Nat) (hd : d < 3) : swap12Digit (swap12Digit d) = d := by
  revert d hd; decide

theorem swap01Digit_involutive (d : Nat) (hd : d < 3) : swap01Digit (swap01Digit d) = d := by
  revert d hd; decide

theorem swap02Digit_involutive (d : Nat) (hd : d < 3) : swap02Digit (swap02Digit d) = d := by
  revert d hd; decide

/-- `mapTernaryDigits f k j < 3 ^ k` whenever `f` maps `{0, 1, 2}` into `{0, 1, 2}`. -/
theorem mapTernaryDigits_lt (f : Nat → Nat) (hf : ∀ d < 3, f d < 3) (k j : Nat) :
    mapTernaryDigits f k j < 3 ^ k := by
  induction k generalizing j with
  | zero =>
    dsimp [mapTernaryDigits]
    decide
  | succ k ih =>
    dsimp [mapTernaryDigits]
    have hd : f (j % 3) < 3 := hf (j % 3) (Nat.mod_lt j (by decide))
    have hRest := ih (j / 3)
    rw [Nat.pow_succ]
    omega

theorem swap12Idx_lt (k j : Nat) : swap12Idx k j < 3 ^ k :=
  mapTernaryDigits_lt swap12Digit swap12Digit_lt_three k j

theorem swap01Idx_lt (k j : Nat) : swap01Idx k j < 3 ^ k :=
  mapTernaryDigits_lt swap01Digit swap01Digit_lt_three k j

theorem swap02Idx_lt (k j : Nat) : swap02Idx k j < 3 ^ k :=
  mapTernaryDigits_lt swap02Digit swap02Digit_lt_three k j

/-- Composition of `mapTernaryDigits`: if `∀ d < 3, g (f d) = h d`, then
    `mapTernaryDigits g k (mapTernaryDigits f k j) = mapTernaryDigits h k j`. -/
theorem mapTernaryDigits_comp (f g h : Nat → Nat)
    (hf : ∀ d < 3, f d < 3)
    (hComp : ∀ d < 3, g (f d) = h d) (k j : Nat) :
    mapTernaryDigits g k (mapTernaryDigits f k j) = mapTernaryDigits h k j := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    dsimp [mapTernaryDigits]
    have hd : j % 3 < 3 := Nat.mod_lt j (by decide)
    have hfd : f (j % 3) < 3 := hf (j % 3) hd
    have hMod : (f (j % 3) + 3 * mapTernaryDigits f k (j / 3)) % 3 = f (j % 3) := by omega
    have hDiv : (f (j % 3) + 3 * mapTernaryDigits f k (j / 3)) / 3 = mapTernaryDigits f k (j / 3) := by omega
    rw [hMod, hDiv, hComp (j % 3) hd, ih (j / 3)]

/-- At the identity digit map, `mapTernaryDigits` on `j < 3 ^ k` returns `j`. -/
theorem mapTernaryDigits_id (k j : Nat) (hj : j < 3 ^ k) :
    mapTernaryDigits (fun d => d) k j = j := by
  induction k generalizing j with
  | zero =>
    dsimp [mapTernaryDigits]
    have : 3 ^ 0 = 1 := rfl
    omega
  | succ k ih =>
    dsimp [mapTernaryDigits]
    rw [Nat.pow_succ] at hj
    have hDiv : j / 3 < 3 ^ k := by omega
    rw [ih (j / 3) hDiv]
    omega

/-- `swap12Idx k` is an involution on `[0, 3^k)`. -/
theorem swap12Idx_involutive (k j : Nat) (hj : j < 3 ^ k) :
    swap12Idx k (swap12Idx k j) = j := by
  unfold swap12Idx
  rw [mapTernaryDigits_comp swap12Digit swap12Digit (fun d => d)
        swap12Digit_lt_three swap12Digit_involutive k j]
  exact mapTernaryDigits_id k j hj

/-- Connection between `mapTernaryDigits` and `permTraceVal`:
    applying `mapTernaryDigits f k` to `permTraceVal p r b k i` equals `permTraceVal (fun d => f (p d)) r b k i`. -/
theorem mapTernaryDigits_permTraceVal (f p : Nat → Nat)
    (hp : ∀ d < 3, p d < 3) (r : Nat) (b : Nat → Color) (k i : Nat) :
    mapTernaryDigits f k (permTraceVal p r b k i) =
      permTraceVal (fun d => f (p d)) r b k i := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    dsimp [permTraceVal, mapTernaryDigits]
    have hd : p (edgeDigitAt r b i) < 3 := hp _ (edgeDigitAt_lt_three r b i)
    have hMod : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k (i + 1)) % 3 = p (edgeDigitAt r b i) := by omega
    have hDiv : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k (i + 1)) / 3 = permTraceVal p r b k (i + 1) := by omega
    rw [hMod, hDiv, ih (i + 1)]

/-- Canonical color pairing mapping `edgeDigitAt r b (r - 2)` to `0`:
    - `0 ↦ theta1` (`[0, 1, 2]`)
    - `1 ↦ theta2` (`[1, 0, 2]`)
    - `2 ↦ theta3` (`[2, 1, 0]`) -/
def canonPairing (r : Nat) (b : Nat → Color) : ColorPairing :=
  match edgeDigitAt r b (r - 2) with
  | 0 => theta1
  | 1 => theta2
  | _ => theta3

/-- Canonical digit permutation mapping `edgeDigitAt r b (r - 2)` to `0`. -/
def canonDigitPerm (r : Nat) (b : Nat → Color) : Nat → Nat :=
  relabelDigit (canonPairing r b)

/-- Canonical $d_{r-2} = 0$ slice index of a boundary coloring `b` in `[0, 3^{r-2})`. -/
def canonIdx (r : Nat) (b : Nat → Color) : Nat :=
  permTraceVal (canonDigitPerm r b) r b (r - 2) 0

theorem canonDigitPerm_lt_three (r : Nat) (b : Nat → Color) (d : Nat) (hd : d < 3) :
    canonDigitPerm r b d < 3 := by
  unfold canonDigitPerm canonPairing
  split <;> (revert d hd; decide)

/-- `canonIdx r b < 3 ^ (r - 2)` for every boundary coloring `b`. -/
theorem canonIdx_lt (r : Nat) (b : Nat → Color) :
    canonIdx r b < 3 ^ (r - 2) :=
  permTraceVal_lt_pow3 (canonDigitPerm r b) (canonDigitPerm_lt_three r b) r b (r - 2) 0

/-- `canonDigitPerm r b` maps the top slice digit `edgeDigitAt r b (r - 2)` to `0`. -/
theorem canonDigitPerm_top_eq_zero (r : Nat) (b : Nat → Color) :
    canonDigitPerm r b (edgeDigitAt r b (r - 2)) = 0 := by
  have hd := edgeDigitAt_lt_three r b (r - 2)
  unfold canonDigitPerm canonPairing
  revert hd
  generalize edgeDigitAt r b (r - 2) = d
  intro hd
  rcases d with _ | _ | _ | d
  · decide
  · decide
  · decide
  · omega

/-!
### Part 5: `repeatBlock` / `getRepeatMask` Bit Specification and `buildSwapSteps` Exactness
-/

/-- Recursive geometric repetition of `cell` `count` times at bit stride `stride`. -/
def geomRepeat (cell stride : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => cell + (geomRepeat cell stride count <<< stride)

theorem testBit_add_shiftLeft (cell stride G j : Nat) (hCell : cell < 2 ^ stride) :
    Nat.testBit (cell + (G <<< stride)) j =
      if j < stride then Nat.testBit cell j else Nat.testBit G (j - stride) := by
  have hShift : G <<< stride = 2 ^ stride * G := by
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
  rw [hShift]
  by_cases hj : j < stride
  · rw [if_pos hj]
    have hMod : (cell + 2 ^ stride * G) % 2 ^ stride = cell := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hCell]
    have hBit := Nat.testBit_mod_two_pow (cell + 2 ^ stride * G) stride j
    rw [hMod, decide_eq_true hj, Bool.true_and] at hBit
    exact hBit.symm
  · rw [if_neg hj]
    have hLe : stride ≤ j := by omega
    have hAdd : j = stride + (j - stride) := by omega
    rw [hAdd, ← Nat.testBit_shiftRight, Nat.shiftRight_eq_div_pow]
    have hPos : 0 < 2 ^ stride := Nat.two_pow_pos stride
    rw [Nat.add_mul_div_left cell G hPos, Nat.div_eq_of_lt hCell, Nat.zero_add]
    have hSub : stride + (j - stride) - stride = j - stride := by omega
    rw [hSub]

theorem testBit_geomRepeat (cell stride count j : Nat) (hCell : cell < 2 ^ stride) :
    Nat.testBit (geomRepeat cell stride count) j =
      (decide (j < count * stride) && Nat.testBit cell (j % stride)) := by
  induction count generalizing j with
  | zero =>
    dsimp [geomRepeat]
    simp
  | succ count ih =>
    dsimp [geomRepeat]
    rw [testBit_add_shiftLeft cell stride _ j hCell]
    by_cases hj : j < stride
    · rw [if_pos hj]
      have hLt : j < (count + 1) * stride := by
        rw [Nat.add_mul, Nat.one_mul]; omega
      rw [decide_eq_true hLt, Bool.true_and, Nat.mod_eq_of_lt hj]
    · rw [if_neg hj, ih (j - stride)]
      have hMod : (j - stride) % stride = j % stride := by
        have h1 := Nat.add_mod_right (j - stride) stride
        rw [Nat.sub_add_cancel (by omega)] at h1
        exact h1.symm
      have hDec : decide (j - stride < count * stride) = decide (j < (count + 1) * stride) := by
        rw [Nat.add_mul, Nat.one_mul]
        by_cases h1 : j - stride < count * stride
        · rw [decide_eq_true h1, decide_eq_true (by omega)]
        · rw [decide_eq_false h1, decide_eq_false (by omega)]
      rw [hMod, hDec]

theorem geomRepeat_mul_cell (cell stride count : Nat) :
    geomRepeat cell stride count = cell * geomRepeat 1 stride count := by
  induction count with
  | zero => simp [geomRepeat]
  | succ count ih =>
    dsimp [geomRepeat]
    rw [ih, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_assoc, Nat.mul_add, Nat.mul_one]

theorem geomRepeat_one_mul_sub (stride count : Nat) :
    geomRepeat 1 stride count * (2 ^ stride - 1) = 2 ^ (count * stride) - 1 := by
  induction count with
  | zero => simp [geomRepeat]
  | succ count ih =>
    dsimp [geomRepeat]
    rw [Nat.shiftLeft_eq, Nat.add_mul, Nat.one_mul]
    have hAssoc : geomRepeat 1 stride count * 2 ^ stride * (2 ^ stride - 1) =
        geomRepeat 1 stride count * (2 ^ stride - 1) * 2 ^ stride := by
      rw [Nat.mul_assoc, Nat.mul_comm (2 ^ stride) (2 ^ stride - 1), ← Nat.mul_assoc]
    rw [hAssoc, ih, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.add_mul, Nat.one_mul]
    have hGe1 : 1 ≤ 2 ^ stride := Nat.two_pow_pos stride
    have hGe2 : 2 ^ stride ≤ 2 ^ (count * stride + stride) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

theorem repeatBlock_eq_geomRepeat (cell stride count : Nat) (hStride : 0 < stride) :
    repeatBlock cell stride count = geomRepeat cell stride count := by
  unfold repeatBlock
  rcases count with _ | _ | count
  · rfl
  · cases hCell0 : Nat.beq cell 0 with
    | true =>
      have hc0 : cell = 0 := Nat.beq_eq.mp hCell0
      subst hc0
      change 0 = 0 + (0 <<< stride)
      simp
    | false =>
      change cell = cell + (0 <<< stride)
      simp
  · cases hCell0 : Nat.beq cell 0 with
    | true =>
      have hc0 : cell = 0 := Nat.beq_eq.mp hCell0
      subst hc0
      change 0 = geomRepeat 0 stride (count + 2)
      rw [geomRepeat_mul_cell, Nat.zero_mul]
    | false =>
      change cell * ((Nat.shiftLeft 1 (Nat.mul (count + 2) stride) - 1) / (Nat.shiftLeft 1 stride - 1)) =
        geomRepeat cell stride (count + 2)
      have hS1' : Nat.shiftLeft 1 (Nat.mul (count + 2) stride) = 2 ^ ((count + 2) * stride) := by
        change 1 <<< ((count + 2) * stride) = 2 ^ ((count + 2) * stride)
        rw [Nat.shiftLeft_eq, Nat.one_mul]
      have hS2 : Nat.shiftLeft 1 stride = 2 ^ stride := by
        change 1 <<< stride = 2 ^ stride
        rw [Nat.shiftLeft_eq, Nat.one_mul]
      rw [hS1', hS2, ← geomRepeat_one_mul_sub stride (count + 2)]
      have hPos : 0 < 2 ^ stride - 1 := by
        have : 2 ^ 1 ≤ 2 ^ stride := Nat.pow_le_pow_right (by decide) hStride
        omega
      rw [Nat.mul_div_cancel _ hPos, ← geomRepeat_mul_cell]

theorem testBit_repeatBlock (cell stride count j : Nat)
    (hStride : 0 < stride) (hCell : cell < 2 ^ stride) :
    Nat.testBit (repeatBlock cell stride count) j =
      (decide (j < count * stride) && Nat.testBit cell (j % stride)) := by
  rw [repeatBlock_eq_geomRepeat cell stride count hStride]
  exact testBit_geomRepeat cell stride count j hCell

theorem testBit_getRepeatMask (count stride width j : Nat)
    (hStride : 0 < stride) (hWidth : width ≤ stride) :
    Nat.testBit (getRepeatMask count stride width) j =
      (decide (j < count * stride) && decide (j % stride < width)) := by
  unfold getRepeatMask
  have hBase : Nat.sub (Nat.shiftLeft 1 width) 1 = 2 ^ width - 1 := by
    change 1 <<< width - 1 = 2 ^ width - 1
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hBase]
  have hCell : 2 ^ width - 1 < 2 ^ stride := by
    have : 2 ^ width ≤ 2 ^ stride := Nat.pow_le_pow_right (by decide) hWidth
    have : 0 < 2 ^ width := Nat.two_pow_pos width
    omega
  rw [testBit_repeatBlock _ stride count j hStride hCell, Nat.testBit_two_pow_sub_one]

theorem mod_three_mul_lt_iff (j P : Nat) (hP : 0 < P) :
    j % (3 * P) < P ↔ (j / P) % 3 = 0 := by
  have h1 : j % (3 * P) < P ↔ (j % (3 * P)) / P < 1 := by
    rw [Nat.div_lt_iff_lt_mul hP, Nat.one_mul]
  rw [h1, Nat.mod_mul_left_div_self]
  omega

theorem sub_div_self (j P : Nat) (hP : 0 < P) (hLe : P ≤ j) :
    (j - P) / P = j / P - 1 := by
  have h1 := Nat.add_mul_div_left (j - P) 1 hP
  rw [Nat.mul_one, Nat.sub_add_cancel hLe] at h1
  rw [h1]
  exact (Nat.add_sub_cancel _ 1).symm

theorem sub_two_mul_div_self (j P : Nat) (hP : 0 < P) (hLe : 2 * P ≤ j) :
    (j - 2 * P) / P = j / P - 2 := by
  have h1 := Nat.add_mul_div_left (j - 2 * P) 2 hP
  have hEq : j - 2 * P + P * 2 = j := by omega
  rw [hEq] at h1
  rw [h1]
  exact (Nat.add_sub_cancel _ 2).symm

theorem le_of_div_mod_three_pos (j P : Nat) (h : (j / P) % 3 ≥ 1) :
    P ≤ j := by
  have hDivPos : 1 ≤ j / P := by
    rcases h0 : j / P with _ | q
    · rw [h0] at h; omega
    · omega
  have := Nat.mul_le_mul_right P hDivPos
  have hLe := Nat.div_mul_le_self j P
  omega

theorem two_mul_le_of_div_mod_three_eq_two (j P : Nat) (h : (j / P) % 3 = 2) :
    2 * P ≤ j := by
  have hDivPos : 2 ≤ j / P := by
    rcases h0 : j / P with _ | _ | q
    · rw [h0] at h; omega
    · rw [h0] at h; omega
    · omega
  have := Nat.mul_le_mul_right P hDivPos
  have hLe := Nat.div_mul_le_self j P
  omega

noncomputable def mkSwapStep (nDigits e : Nat) : SwapStep :=
  let P := KernelReducer.pow3 e
  let P2 := Nat.mul 2 P
  let count := KernelReducer.pow3 (Nat.sub (Nat.sub nDigits 1) e)
  let m0 := getRepeatMask count (Nat.mul 3 P) P
  let m1 := Nat.shiftLeft m0 P
  let m2 := Nat.shiftLeft m0 P2
  SwapStep.mk P P2 m0 m1 m2

theorem pow3_pos (e : Nat) : 0 < 3 ^ e :=
  Nat.pow_pos (by decide)

theorem count_mul_stride_eq (nDigits e : Nat) (he : e < nDigits) :
    3 ^ (nDigits - 1 - e) * (3 * 3 ^ e) = 3 ^ nDigits := by
  have h1 : 3 * 3 ^ e = 3 ^ (e + 1) := Nat.pow_succ'.symm
  rw [h1, ← Nat.pow_add]
  have h2 : nDigits - 1 - e + (e + 1) = nDigits := by omega
  rw [h2]

theorem testBit_swapStep_m0 (nDigits e j : Nat) (he : e < nDigits) (hj : j < 3 ^ nDigits) :
    let P := 3 ^ e
    let count := 3 ^ (nDigits - 1 - e)
    let m0 := getRepeatMask count (3 * P) P
    Nat.testBit m0 j = decide ((j / P) % 3 = 0) := by
  dsimp
  have hP : 0 < 3 ^ e := pow3_pos e
  rw [testBit_getRepeatMask _ (3 * 3 ^ e) (3 ^ e) j (by omega) (by omega)]
  rw [count_mul_stride_eq nDigits e he, decide_eq_true hj, Bool.true_and]
  by_cases h0 : (j / 3 ^ e) % 3 = 0
  · rw [decide_eq_true h0, decide_eq_true ((mod_three_mul_lt_iff j (3 ^ e) hP).mpr h0)]
  · rw [decide_eq_false h0, decide_eq_false (mt (mod_three_mul_lt_iff j (3 ^ e) hP).mp h0)]

theorem testBit_swapStep_m1 (nDigits e j : Nat) (he : e < nDigits) (hj : j < 3 ^ nDigits) :
    let P := 3 ^ e
    let count := 3 ^ (nDigits - 1 - e)
    let m0 := getRepeatMask count (3 * P) P
    let m1 := Nat.shiftLeft m0 P
    Nat.testBit m1 j = decide ((j / P) % 3 = 1) := by
  dsimp
  have hP : 0 < 3 ^ e := pow3_pos e
  rw [testBit_shiftLeft]
  by_cases hLe : j ≥ 3 ^ e
  · rw [decide_eq_true hLe, Bool.true_and]
    rw [testBit_swapStep_m0 nDigits e (j - 3 ^ e) he (by omega)]
    rw [sub_div_self j (3 ^ e) hP hLe]
    have hd : (j / 3 ^ e) % 3 < 3 := Nat.mod_lt _ (by decide)
    have hDivPos : 1 ≤ j / 3 ^ e := (Nat.le_div_iff_mul_le hP).mpr (by omega)
    by_cases h1 : (j / 3 ^ e) % 3 = 1
    · rw [decide_eq_true h1, decide_eq_true (by omega)]
    · rw [decide_eq_false h1, decide_eq_false (by omega)]
  · rw [decide_eq_false hLe, Bool.false_and]
    have h1 : (j / 3 ^ e) % 3 ≠ 1 := by
      intro hc
      exact hLe (le_of_div_mod_three_pos j (3 ^ e) (by omega))
    rw [decide_eq_false h1]

theorem testBit_swapStep_m2 (nDigits e j : Nat) (he : e < nDigits) (hj : j < 3 ^ nDigits) :
    let P := 3 ^ e
    let count := 3 ^ (nDigits - 1 - e)
    let m0 := getRepeatMask count (3 * P) P
    let m2 := Nat.shiftLeft m0 (2 * P)
    Nat.testBit m2 j = decide ((j / P) % 3 = 2) := by
  dsimp
  have hP : 0 < 3 ^ e := pow3_pos e
  rw [testBit_shiftLeft]
  by_cases hLe : j ≥ 2 * 3 ^ e
  · rw [decide_eq_true hLe, Bool.true_and]
    rw [testBit_swapStep_m0 nDigits e (j - 2 * 3 ^ e) he (by omega)]
    rw [sub_two_mul_div_self j (3 ^ e) hP hLe]
    have hd : (j / 3 ^ e) % 3 < 3 := Nat.mod_lt _ (by decide)
    have hDivPos : 2 ≤ j / 3 ^ e := (Nat.le_div_iff_mul_le hP).mpr (by omega)
    by_cases h2 : (j / 3 ^ e) % 3 = 2
    · rw [decide_eq_true h2, decide_eq_true (by omega)]
    · rw [decide_eq_false h2, decide_eq_false (by omega)]
  · rw [decide_eq_false hLe, Bool.false_and]
    have h2 : (j / 3 ^ e) % 3 ≠ 2 := by
      intro hc
      exact hLe (two_mul_le_of_div_mod_three_eq_two j (3 ^ e) hc)
    rw [decide_eq_false h2]

/-- Update the base-3 digit of `j` at position `e` using `f`. -/
def mapDigitAt (f : Nat → Nat) (e j : Nat) : Nat :=
  let P := 3 ^ e
  let d := (j / P) % 3
  j - d * P + f d * P

theorem d_mul_le_self (j P : Nat) : ((j / P) % 3) * P ≤ j := by
  have h1 : (j / P) % 3 ≤ j / P := Nat.mod_le (j / P) 3
  have h2 := Nat.mul_le_mul_right P h1
  have h3 := Nat.div_mul_le_self j P
  omega

theorem mapDigitAt_zero (f : Nat → Nat) (j : Nat) :
    mapDigitAt f 0 j = f (j % 3) + 3 * (j / 3) := by
  dsimp [mapDigitAt]
  rw [Nat.div_one, Nat.mul_one, Nat.mul_one]
  have hDiv := Nat.div_add_mod j 3
  omega

theorem mapDigitAt_succ (f : Nat → Nat) (e j : Nat) :
    mapDigitAt f (e + 1) j = j % 3 + 3 * mapDigitAt f e (j / 3) := by
  dsimp [mapDigitAt]
  have hPow : 3 ^ (e + 1) = 3 ^ e * 3 := Nat.pow_succ 3 e
  have hDivEq : j / 3 ^ (e + 1) = (j / 3) / 3 ^ e := by
    rw [Nat.pow_succ', Nat.div_div_eq_div_mul]
  rw [hDivEq, hPow, ← Nat.mul_assoc, ← Nat.mul_assoc]
  have hLe : (((j / 3) / 3 ^ e) % 3) * 3 ^ e ≤ j / 3 := d_mul_le_self (j / 3) (3 ^ e)
  have hDiv3 := Nat.div_add_mod j 3
  omega

theorem mapDigitAt_lt (f : Nat → Nat) (hf : ∀ d < 3, f d < 3)
    (nDigits e j : Nat) (he : e < nDigits) (hj : j < 3 ^ nDigits) :
    mapDigitAt f e j < 3 ^ nDigits := by
  induction nDigits generalizing e j with
  | zero => omega
  | succ n ih =>
    rcases e with _ | e
    · rw [mapDigitAt_zero]
      have hd : f (j % 3) < 3 := hf (j % 3) (Nat.mod_lt j (by decide))
      have hPow : 3 ^ (n + 1) = 3 * 3 ^ n := Nat.pow_succ'
      have hDiv : j / 3 < 3 ^ n := by omega
      omega
    · rw [mapDigitAt_succ]
      have hPow : 3 ^ (n + 1) = 3 * 3 ^ n := Nat.pow_succ'
      have hDiv : j / 3 < 3 ^ n := by omega
      have hSub := ih e (j / 3) (by omega) hDiv
      have hMod : j % 3 < 3 := Nat.mod_lt j (by decide)
      omega

/-- Apply `mapDigitAt f` from `e = start + k - 1` down to `e = start`. -/
def mapDigitsFrom (f : Nat → Nat) (start : Nat) : Nat → Nat → Nat
  | 0, j => j
  | k + 1, j => mapDigitAt f start (mapDigitsFrom f (start + 1) k j)

theorem mapDigitsFrom_lt (f : Nat → Nat) (hf : ∀ d < 3, f d < 3)
    (nDigits start k j : Nat) (hBound : start + k ≤ nDigits) (hj : j < 3 ^ nDigits) :
    mapDigitsFrom f start k j < 3 ^ nDigits := by
  induction k generalizing start j with
  | zero => exact hj
  | succ k ih =>
    dsimp [mapDigitsFrom]
    exact mapDigitAt_lt f hf nDigits start _ (by omega) (ih (start + 1) j (by omega) hj)

theorem mapDigitsFrom_succ_start (f : Nat → Nat) (start k j : Nat) :
    mapDigitsFrom f (start + 1) k j = j % 3 + 3 * mapDigitsFrom f start k (j / 3) := by
  induction k generalizing start j with
  | zero =>
    dsimp [mapDigitsFrom]
    have := Nat.div_add_mod j 3
    omega
  | succ k ih =>
    dsimp [mapDigitsFrom]
    rw [ih (start + 1) j, mapDigitAt_succ]
    have hMod : (j % 3 + 3 * mapDigitsFrom f (start + 1) k (j / 3)) % 3 = j % 3 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt j (by decide))]
    have hDiv : (j % 3 + 3 * mapDigitsFrom f (start + 1) k (j / 3)) / 3 =
        mapDigitsFrom f (start + 1) k (j / 3) := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 3),
          Nat.div_eq_of_lt (Nat.mod_lt j (by decide)), Nat.zero_add]
    rw [hMod, hDiv]

theorem mapDigitsFrom_zero_eq_mapTernaryDigits (f : Nat → Nat) (k j : Nat) (hj : j < 3 ^ k) :
    mapDigitsFrom f 0 k j = mapTernaryDigits f k j := by
  induction k generalizing j with
  | zero =>
    dsimp [mapDigitsFrom, mapTernaryDigits]
    omega
  | succ k ih =>
    dsimp [mapDigitsFrom, mapTernaryDigits]
    rw [mapDigitsFrom_succ_start, mapDigitAt_zero]
    have hMod : (j % 3 + 3 * mapDigitsFrom f 0 k (j / 3)) % 3 = j % 3 := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Nat.mod_lt j (by decide))]
    have hDiv : (j % 3 + 3 * mapDigitsFrom f 0 k (j / 3)) / 3 =
        mapDigitsFrom f 0 k (j / 3) := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 3),
          Nat.div_eq_of_lt (Nat.mod_lt j (by decide)), Nat.zero_add]
    have hjDiv : j / 3 < 3 ^ k := by
      rw [Nat.pow_succ'] at hj; omega
    rw [hMod, hDiv, ih (j / 3) hjDiv]

theorem valid_and_routeSwap12Step_mkSwapStep (nDigits e j : Nat)
    (he : e < nDigits) (hj : j < 3 ^ nDigits) :
    ValidSwap12Bit (mkSwapStep nDigits e) j = true ∧
    routeSwap12Step (mkSwapStep nDigits e) j = mapDigitAt swap12Digit e j := by
  dsimp [mkSwapStep, ValidSwap12Bit, routeSwap12Step, mapDigitAt]
  simp only [kernel_pow3_eq]
  rw [testBit_swapStep_m0 nDigits e j he hj, testBit_swapStep_m1 nDigits e j he hj]
  have hP : 0 < 3 ^ e := pow3_pos e
  have hd : (j / 3 ^ e) % 3 < 3 := Nat.mod_lt _ (by decide)
  have hLeSelf : ((j / 3 ^ e) % 3) * 3 ^ e ≤ j := d_mul_le_self j (3 ^ e)
  rcases hd_eq : (j / 3 ^ e) % 3 with _ | _ | _ | d
  · simp [swap12Digit]
  · rw [hd_eq] at hLeSelf
    simp [swap12Digit]
    omega
  · rw [hd_eq] at hLeSelf
    have hLeP : 3 ^ e ≤ j := by omega
    have hSub1 : ((j - 3 ^ e) / 3 ^ e) % 3 = 1 := by
      rw [sub_div_self j (3 ^ e) hP hLeP]
      have hDivPos : 2 ≤ j / 3 ^ e := (Nat.le_div_iff_mul_le hP).mpr (by omega)
      omega
    rw [testBit_swapStep_m1 nDigits e (j - 3 ^ e) he (by omega), hSub1]
    simp [decide_eq_true hLeP, swap12Digit]
    omega
  · omega

theorem valid_and_routeSwap01Step_mkSwapStep (nDigits e j : Nat)
    (he : e < nDigits) (hj : j < 3 ^ nDigits) :
    ValidSwap01Bit (mkSwapStep nDigits e) j = true ∧
    routeSwap01Step (mkSwapStep nDigits e) j = mapDigitAt swap01Digit e j := by
  dsimp [mkSwapStep, ValidSwap01Bit, routeSwap01Step, mapDigitAt]
  simp only [kernel_pow3_eq]
  rw [testBit_swapStep_m0 nDigits e j he hj, testBit_swapStep_m2 nDigits e j he hj]
  have hP : 0 < 3 ^ e := pow3_pos e
  have hd : (j / 3 ^ e) % 3 < 3 := Nat.mod_lt _ (by decide)
  have hLeSelf : ((j / 3 ^ e) % 3) * 3 ^ e ≤ j := d_mul_le_self j (3 ^ e)
  rcases hd_eq : (j / 3 ^ e) % 3 with _ | _ | _ | d
  · simp [swap01Digit]
  · rw [hd_eq] at hLeSelf
    have hLeP : 3 ^ e ≤ j := by omega
    have hSub0 : ((j - 3 ^ e) / 3 ^ e) % 3 = 0 := by
      rw [sub_div_self j (3 ^ e) hP hLeP]
      have hDivPos : 1 ≤ j / 3 ^ e := (Nat.le_div_iff_mul_le hP).mpr (by omega)
      omega
    rw [testBit_swapStep_m0 nDigits e (j - 3 ^ e) he (by omega), hSub0]
    simp [decide_eq_true hLeP, swap01Digit]
  · rw [hd_eq] at hLeSelf
    simp [swap01Digit]
    omega
  · omega

theorem valid_and_routeSwap02Step_mkSwapStep (nDigits e j : Nat)
    (he : e < nDigits) (hj : j < 3 ^ nDigits) :
    ValidSwap02Bit (mkSwapStep nDigits e) j = true ∧
    routeSwap02Step (mkSwapStep nDigits e) j = mapDigitAt swap02Digit e j := by
  dsimp [mkSwapStep, ValidSwap02Bit, routeSwap02Step, mapDigitAt]
  simp only [kernel_pow3_eq]
  rw [testBit_swapStep_m0 nDigits e j he hj, testBit_swapStep_m1 nDigits e j he hj]
  have hP : 0 < 3 ^ e := pow3_pos e
  have hd : (j / 3 ^ e) % 3 < 3 := Nat.mod_lt _ (by decide)
  have hLeSelf : ((j / 3 ^ e) % 3) * 3 ^ e ≤ j := d_mul_le_self j (3 ^ e)
  rcases hd_eq : (j / 3 ^ e) % 3 with _ | _ | _ | d
  · simp [swap02Digit]
  · rw [hd_eq] at hLeSelf
    simp [swap02Digit]
    omega
  · rw [hd_eq] at hLeSelf
    have hLe2P : 2 * 3 ^ e ≤ j := by omega
    have hSub0 : ((j - 2 * 3 ^ e) / 3 ^ e) % 3 = 0 := by
      rw [sub_two_mul_div_self j (3 ^ e) hP hLe2P]
      have hDivPos : 2 ≤ j / 3 ^ e := (Nat.le_div_iff_mul_le hP).mpr (by omega)
      omega
    rw [testBit_swapStep_m0 nDigits e (j - 2 * 3 ^ e) he (by omega), hSub0]
    simp [decide_eq_true hLe2P, swap02Digit]
  · omega

noncomputable def buildSwapStepsList (nDigits start : Nat) : Nat → List SwapStep
  | 0 => []
  | m + 1 => mkSwapStep nDigits start :: buildSwapStepsList nDigits (start + 1) m

theorem buildSwapSteps_eq_list (nDigits : Nat) :
    (buildSwapSteps nDigits).val = buildSwapStepsList nDigits 0 nDigits := by
  unfold buildSwapSteps
  have hLoop : ∀ (k m : Nat),
      (@Nat.rec (fun _ => List SwapStep → StrictBox (List SwapStep))
        (fun acc => StrictBox.mk acc)
        (fun e ih acc =>
          let P := KernelReducer.pow3 e
          let P2 := Nat.mul 2 P
          let count := KernelReducer.pow3 (Nat.sub (Nat.sub nDigits 1) e)
          let m0 := getRepeatMask count (Nat.mul 3 P) P
          let m1 := Nat.shiftLeft m0 P
          let m2 := Nat.shiftLeft m0 P2
          ih (SwapStep.mk P P2 m0 m1 m2 :: acc))
        k (buildSwapStepsList nDigits k m)).val =
      buildSwapStepsList nDigits 0 (k + m) := by
    intro k
    induction k with
    | zero =>
      intro m
      rw [Nat.zero_add]
      rfl
    | succ k ih =>
      intro m
      change _ = buildSwapStepsList nDigits 0 (k + 1 + m)
      have hAdd : k + 1 + m = k + (m + 1) := by omega
      rw [hAdd]
      exact ih (m + 1)
  have h0 := hLoop nDigits 0
  rw [Nat.add_zero] at h0
  exact h0

theorem valid_and_routeSwap12List_buildSwapStepsList (nDigits start m j : Nat)
    (hBound : start + m ≤ nDigits) (hj : j < 3 ^ nDigits) :
    ValidSwap12List (buildSwapStepsList nDigits start m) j = true ∧
    routeSwap12List (buildSwapStepsList nDigits start m) j = mapDigitsFrom swap12Digit start m j := by
  induction m generalizing start j with
  | zero =>
    dsimp [buildSwapStepsList, ValidSwap12List, routeSwap12List, mapDigitsFrom]
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    dsimp [buildSwapStepsList, ValidSwap12List, routeSwap12List, mapDigitsFrom]
    rcases ih (start + 1) j (by omega) hj with ⟨hVRest, hRRest⟩
    rw [hVRest, hRRest, Bool.true_and]
    have hLtRest : mapDigitsFrom swap12Digit (start + 1) m j < 3 ^ nDigits :=
      mapDigitsFrom_lt swap12Digit swap12Digit_lt_three nDigits (start + 1) m j (by omega) hj
    exact valid_and_routeSwap12Step_mkSwapStep nDigits start _ (by omega) hLtRest

theorem valid_and_routeSwap01List_buildSwapStepsList (nDigits start m j : Nat)
    (hBound : start + m ≤ nDigits) (hj : j < 3 ^ nDigits) :
    ValidSwap01List (buildSwapStepsList nDigits start m) j = true ∧
    routeSwap01List (buildSwapStepsList nDigits start m) j = mapDigitsFrom swap01Digit start m j := by
  induction m generalizing start j with
  | zero =>
    dsimp [buildSwapStepsList, ValidSwap01List, routeSwap01List, mapDigitsFrom]
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    dsimp [buildSwapStepsList, ValidSwap01List, routeSwap01List, mapDigitsFrom]
    rcases ih (start + 1) j (by omega) hj with ⟨hVRest, hRRest⟩
    rw [hVRest, hRRest, Bool.true_and]
    have hLtRest : mapDigitsFrom swap01Digit (start + 1) m j < 3 ^ nDigits :=
      mapDigitsFrom_lt swap01Digit swap01Digit_lt_three nDigits (start + 1) m j (by omega) hj
    exact valid_and_routeSwap01Step_mkSwapStep nDigits start _ (by omega) hLtRest

theorem valid_and_routeSwap02List_buildSwapStepsList (nDigits start m j : Nat)
    (hBound : start + m ≤ nDigits) (hj : j < 3 ^ nDigits) :
    ValidSwap02List (buildSwapStepsList nDigits start m) j = true ∧
    routeSwap02List (buildSwapStepsList nDigits start m) j = mapDigitsFrom swap02Digit start m j := by
  induction m generalizing start j with
  | zero =>
    dsimp [buildSwapStepsList, ValidSwap02List, routeSwap02List, mapDigitsFrom]
    exact ⟨rfl, rfl⟩
  | succ m ih =>
    dsimp [buildSwapStepsList, ValidSwap02List, routeSwap02List, mapDigitsFrom]
    rcases ih (start + 1) j (by omega) hj with ⟨hVRest, hRRest⟩
    rw [hVRest, hRRest, Bool.true_and]
    have hLtRest : mapDigitsFrom swap02Digit (start + 1) m j < 3 ^ nDigits :=
      mapDigitsFrom_lt swap02Digit swap02Digit_lt_three nDigits (start + 1) m j (by omega) hj
    exact valid_and_routeSwap02Step_mkSwapStep nDigits start _ (by omega) hLtRest

/-- Soundness of `swapDigits12 (buildSwapSteps nDigits).val` at any bit `j < 3 ^ nDigits`. -/
theorem swapDigits12_buildSwapSteps_false_sound (nDigits X j : Nat)
    (hj : j < 3 ^ nDigits)
    (hFalse : Nat.testBit (swapDigits12 (buildSwapSteps nDigits).val X) j = false) :
    Nat.testBit X (swap12Idx nDigits j) = false := by
  rw [buildSwapSteps_eq_list] at hFalse
  rcases valid_and_routeSwap12List_buildSwapStepsList nDigits 0 nDigits j (by omega) hj with ⟨hV, hR⟩
  have hSound := swapDigits12_false_sound (buildSwapStepsList nDigits 0 nDigits) X j hV hFalse
  rw [hR, mapDigitsFrom_zero_eq_mapTernaryDigits swap12Digit nDigits j hj] at hSound
  exact hSound

/-- Soundness of `swapDigits01 (buildSwapSteps nDigits).val` at any bit `j < 3 ^ nDigits`. -/
theorem swapDigits01_buildSwapSteps_false_sound (nDigits X j : Nat)
    (hj : j < 3 ^ nDigits)
    (hFalse : Nat.testBit (swapDigits01 (buildSwapSteps nDigits).val X) j = false) :
    Nat.testBit X (swap01Idx nDigits j) = false := by
  rw [buildSwapSteps_eq_list] at hFalse
  rcases valid_and_routeSwap01List_buildSwapStepsList nDigits 0 nDigits j (by omega) hj with ⟨hV, hR⟩
  have hSound := swapDigits01_false_sound (buildSwapStepsList nDigits 0 nDigits) X j hV hFalse
  rw [hR, mapDigitsFrom_zero_eq_mapTernaryDigits swap01Digit nDigits j hj] at hSound
  exact hSound

/-- Soundness of `swapDigits02 (buildSwapSteps nDigits).val` at any bit `j < 3 ^ nDigits`. -/
theorem swapDigits02_buildSwapSteps_false_sound (nDigits X j : Nat)
    (hj : j < 3 ^ nDigits)
    (hFalse : Nat.testBit (swapDigits02 (buildSwapSteps nDigits).val X) j = false) :
    Nat.testBit X (swap02Idx nDigits j) = false := by
  rw [buildSwapSteps_eq_list] at hFalse
  rcases valid_and_routeSwap02List_buildSwapStepsList nDigits 0 nDigits j (by omega) hj with ⟨hV, hR⟩
  have hSound := swapDigits02_false_sound (buildSwapStepsList nDigits 0 nDigits) X j hV hFalse
  rw [hR, mapDigitsFrom_zero_eq_mapTernaryDigits swap02Digit nDigits j hj] at hSound
  exact hSound

/-- Direct Bitmask Elimination Invariant on `KernelReducer`'s $3^{r-2}$-bit canonical slice `L`:
    Every valid boundary coloring `b` for which at least one of its two canonical $d_{r-2} = 0$
    slice bits (`canonIdx c.ringSize b` or `swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)`)
    is `false` in `L` is mathematically `Eliminated c b`. -/
def KernelLiveInvariant (c : Configuration) (L : Nat) : Prop :=
  ∀ b : BoundaryColoring c, IsValidBoundaryColoring c b →
    (Nat.testBit L (canonIdx c.ringSize b) = false ∨
     Nat.testBit L (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)) = false) →
    Eliminated c b

/-- If `KernelLiveInvariant c 0` holds, then `c` is D-reducible (`IsDReducible c`). -/
theorem isDReducible_of_kernelLiveInvariant_zero (c : Configuration)
    (hInv : KernelLiveInvariant c 0) : IsDReducible c := by
  intro b hb
  exact hInv b hb (Or.inl (Nat.zero_testBit (canonIdx c.ringSize b)))

/-- If `KernelLiveInvariant c L` holds, `Nat.land L contractCanon = 0`, and every valid boundary
    coloring extending to the contracted graph has bit `true` in `contractCanon` at one of its
    two canonical slice indices (or is already `Eliminated c b`), then `c` is C-reducible (`IsCReducible c`). -/
theorem isCReducible_of_kernelLiveInvariant_land_zero (c : Configuration)
    (L contractCanon : Nat)
    (hNe : c.contractEdges ≠ [])
    (hInv : KernelLiveInvariant c L)
    (hContract : ∀ b : BoundaryColoring c, IsValidBoundaryColoring c b →
      extendsToContracted c b →
      Nat.testBit contractCanon (canonIdx c.ringSize b) = true ∨
      Nat.testBit contractCanon (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)) = true ∨
      Eliminated c b)
    (hLand : Nat.land L contractCanon = 0) :
    IsCReducible c := by
  refine ⟨hNe, ?_⟩
  intro b hb hExtC
  rcases hContract b hb hExtC with hBitC0 | hBitC1 | hElim
  · apply hInv b hb
    left
    have hZeroBit : Nat.testBit (Nat.land L contractCanon) (canonIdx c.ringSize b) = false := by
      rw [hLand]
      exact Nat.zero_testBit _
    rw [testBit_land, hBitC0, Bool.and_true] at hZeroBit
    exact hZeroBit
  · apply hInv b hb
    right
    have hZeroBit :
        Nat.testBit (Nat.land L contractCanon) (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)) = false := by
      rw [hLand]
      exact Nat.zero_testBit _
    rw [testBit_land, hBitC1, Bool.and_true] at hZeroBit
    exact hZeroBit
  · exact hElim

end KernelSoundness
end Math
