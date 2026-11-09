import FourColorTheorem.Math.KernelSoundness.KernelInitialSoundness
import FourColorTheorem.Math.KernelSoundness.KernelKempeSoundness

namespace Math
namespace KernelSoundness

open KernelReducer
open FastReducer
open Batch
open Soundness
open CheckerSoundness

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-!
# Checkpoint K4.4: `KernelReducer` End-to-End Soundness (`verifyIdxD_sound` & `verifyIdxC_sound`)

This module combines:
1. **Initial Slice Soundness (`KernelInitialSoundness`):**
   - `initLiveIdx_sound`: `KernelLiveInvariant (theUnavoidableSet[idx]!) (initLiveIdx idx)`
   - `contractCanonIdx_sound`: every valid boundary coloring extending to the contracted configuration
     has bit `true` in `contractCanonIdx idx` at one of its two canonical slice indices (or is `Eliminated`).
2. **Pascal-Catalan Kempe Round Soundness (`KernelKempeSoundness`):**
   - `stepKempeRounds_preserves_invariant`: every round of `kempeRound` preserves `KernelLiveInvariant`.
3. **Loop Termination Extraction (`KernelSlice`):**
   - `verifyIdxD_steps_zero` and `verifyIdxC_steps_land_zero`.

Together, these yield the unconditional soundness of `KernelReducer.verifyIdxD` and `KernelReducer.verifyIdxC`
for all 633 configurations in `theUnavoidableSet`.
-/

/-- Executable check that every configuration in a list has ring size `r ≤ 14`. -/
def checkRConfListR14 : List FastReducer.RConf → Bool
  | [] => true
  | rc :: rest => Nat.ble rc.r 14 && checkRConfListR14 rest

theorem checkRConfListR14_sound (L : List FastReducer.RConf) (k : Nat)
    (hk : k < L.length) (h : checkRConfListR14 L = true) :
    (L[k]'hk).r ≤ 14 := by
  induction L generalizing k with
  | nil => contradiction
  | cons hd tl ih =>
    dsimp [checkRConfListR14] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h_hd, h_tl⟩
    cases k with
    | zero => exact Nat.le_of_ble_eq_true h_hd
    | succ k' =>
      have hk' : k' < tl.length := by dsimp at hk; omega
      exact ih k' hk' h_tl

set_option maxRecDepth 100000 in
theorem parsedRConfList_r_le_14 : checkRConfListR14 parsedRConfList = true := by
  rfl

theorem sharedCfgs_r_le_14 (idx : Nat) (hIdx : idx < 633) :
    Batch.sharedCfgs[idx]!.r ≤ 14 := by
  have h_len : idx < parsedRConfList.length := by
    rw [parsedRConfList_length]; exact hIdx
  have h_arr : Batch.sharedCfgs[idx]! = parsedRConfList[idx]'h_len := by
    let arr : Array FastReducer.RConf := ⟨parsedRConfList⟩
    have h_sz : idx < arr.size := h_len
    change arr[idx]! = parsedRConfList[idx]'h_len
    rw [getElem!_pos arr idx h_sz]
    rfl
  rw [h_arr]
  exact checkRConfListR14_sound parsedRConfList idx h_len parsedRConfList_r_le_14

theorem configOfRConf_ringSize (rc : FastReducer.RConf) :
    (configOfRConf rc).ringSize = rc.r := rfl

theorem getRConf_ring_bounds (idx : Nat) (hIdx : idx < 633) :
    (theUnavoidableSet[idx]!).ringSize = (KernelReducer.getRConf idx).r ∧
    3 ≤ (KernelReducer.getRConf idx).r ∧
    (KernelReducer.getRConf idx).r ≤ 14 := by
  rw [getRConf_eq_sharedCfgs idx hIdx]
  have hR : (theUnavoidableSet[idx]!).ringSize = Batch.sharedCfgs[idx]!.r := by
    rw [theUnavoidableSet_getElem! idx hIdx]
    exact configOfRConf_ringSize _
  have h_extra := sharedCfgs_kernelExtra_verified idx hIdx
  dsimp [checkRConfKernelExtra] at h_extra
  rcases Bool.and_eq_true_iff.mp h_extra with ⟨h3Len, _⟩
  rcases Bool.and_eq_true_iff.mp h3Len with ⟨h3B, _⟩
  exact ⟨hR, Nat.le_of_ble_eq_true h3B, sharedCfgs_r_le_14 idx hIdx⟩

/-- **End-to-End D-Reducibility Soundness of `KernelReducer.verifyIdxD`:**
    For every configuration index `idx < 633`, if `KernelReducer.verifyIdxD idx = true`,
    then `theUnavoidableSet[idx]!` is mathematically D-reducible (`IsDReducible`). -/
theorem verifyIdxD_sound (idx : Nat) (hIdx : idx < 633)
    (hCert : KernelReducer.verifyIdxD idx = true) :
    IsDReducible (theUnavoidableSet[idx]!) := by
  have hSteps := verifyIdxD_steps_zero idx hCert
  dsimp only [] at hSteps
  rcases hSteps with ⟨k, _, hZero⟩
  rcases getRConf_ring_bounds idx hIdx with ⟨hRingEq, hR_lo, hR_hi⟩
  let c := theUnavoidableSet[idx]!
  let rc := KernelReducer.getRConf idx
  let mMax := rc.r - 1
  have hr : c.ringSize = mMax + 1 := by
    dsimp [c, rc, mMax]; omega
  have hmMax_lo : 1 ≤ mMax := by
    dsimp [rc, mMax]; omega
  have hmMax_hi : mMax ≤ 13 := by
    dsimp [rc, mMax]; omega
  have h_ring : IsRingCycle c := unavoidable_is_ring_cycle idx hIdx
  have hInv0 : KernelLiveInvariant c (initLiveIdx idx) := initLiveIdx_sound idx hIdx
  have hInvK := stepKempeRounds_preserves_invariant c mMax k (initLiveIdx idx)
    hr hmMax_lo hmMax_hi h_ring hInv0
  dsimp [c, rc, mMax] at hInvK
  rw [hRingEq, hZero] at hInvK
  exact isDReducible_of_kernelLiveInvariant_zero (theUnavoidableSet[idx]!) hInvK

/-- **End-to-End C-Reducibility Soundness of `KernelReducer.verifyIdxC`:**
    For every configuration index `idx < 633` with non-empty `contractEdges`,
    if `KernelReducer.verifyIdxC idx = true`, then `theUnavoidableSet[idx]!` is
    mathematically C-reducible (`IsCReducible`). -/
theorem verifyIdxC_sound (idx : Nat) (hIdx : idx < 633)
    (hNe : (theUnavoidableSet[idx]!).contractEdges ≠ [])
    (hCert : KernelReducer.verifyIdxC idx = true) :
    IsCReducible (theUnavoidableSet[idx]!) := by
  have hSteps := verifyIdxC_steps_land_zero idx hCert
  dsimp only [] at hSteps
  rcases hSteps with ⟨k, _, hLand⟩
  rcases getRConf_ring_bounds idx hIdx with ⟨hRingEq, hR_lo, hR_hi⟩
  let c := theUnavoidableSet[idx]!
  let rc := KernelReducer.getRConf idx
  let mMax := rc.r - 1
  have hr : c.ringSize = mMax + 1 := by
    dsimp [c, rc, mMax]; omega
  have hmMax_lo : 1 ≤ mMax := by
    dsimp [rc, mMax]; omega
  have hmMax_hi : mMax ≤ 13 := by
    dsimp [rc, mMax]; omega
  have h_ring : IsRingCycle c := unavoidable_is_ring_cycle idx hIdx
  have hInv0 : KernelLiveInvariant c (initLiveIdx idx) := initLiveIdx_sound idx hIdx
  have hInvK := stepKempeRounds_preserves_invariant c mMax k (initLiveIdx idx)
    hr hmMax_lo hmMax_hi h_ring hInv0
  dsimp [c, rc, mMax] at hInvK
  rw [hRingEq] at hInvK
  exact isCReducible_of_kernelLiveInvariant_land_zero (theUnavoidableSet[idx]!)
    _ (contractCanonIdx idx) hNe hInvK (contractCanonIdx_sound idx hIdx) hLand

end KernelSoundness
end Math
