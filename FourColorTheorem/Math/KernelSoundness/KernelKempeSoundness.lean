import FourColorTheorem.Math.KernelSoundness.KernelInitialSoundness
import FourColorTheorem.Math.CheckerSoundness.BuildSMDataSoundness

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
# Checkpoint K4.3: Soundness of `PackStep`, `ChordOp`, `CatalanTrie`, and `kempeRound`

This module establishes the bit-level specifications of `KernelReducer`'s Pascal-Catalan Kempe
reduction engine:
1. **`stepPack`, `stepUnpack`, `runPackSteps`, `runUnpack`:**
   Bit-routing soundness for the logarithmic SWAR butterfly pack and unpack steps.
2. **`evalChordOp` & `evalCatalanTrie` Algebraic Reduction (`evalCatalanTrie_mkCatalanNode`):**
   Collapses all 5 constructors of `CatalanTrie` (`leaf`, `nil`, `leafOp`, `only`, `branch`) and
   short-circuiting `mBase == 0` checks into the clean recursive specification:
   `evalCatalanTrie (mkCatalanNode op child sib) B = Nat.lor (evalCatalanTrie child (evalChordOp op B)) (evalCatalanTrie sib B)`.
3. **Single-Chord Flip Soundness (`evalChordOp_last_false_sound`, `evalChordOp_pair_false_sound`):**
   Whenever `Nat.testBit (evalChordOp op B) j = false`, at least one of the two chord-mate states
   (`j` or `j_swap`, differing by flipping the two chord endpoints `lo` and `kIdx`) has bit `false` in `B`.
4. **`kempeRound_swap12_symm`:**
   Proves that `kempeRound` unconditionally preserves the `(12)` digit symmetry conjunct of
   `KernelLiveInvariant` whenever `ExactSwap12List` holds.
-/

/-!
### Part 1: Bitwise Routing Soundness for `PackStep`, `runPackSteps`, and `runUnpack`
-/

/-- Single-step execution of `runPackSteps` on `acc`. -/
def stepPack (step : PackStep) (acc : Nat) : Nat :=
  match step with
  | PackStep.mk shiftDiff m0 m1 =>
    let g0 := Nat.land acc m0
    let s1 := Nat.land (Nat.shiftRight acc shiftDiff) m1
    Nat.lor g0 s1

/-- Single-step execution of `runUnpack` on `acc`. -/
def stepUnpack (step : PackStep) (acc : Nat) : Nat :=
  match step with
  | PackStep.mk shiftDiff m0 m1 =>
    let g0 := Nat.land acc m0
    let s1 := Nat.shiftLeft (Nat.land acc m1) shiftDiff
    Nat.lor g0 s1

/-- Index router for one `PackStep` of `runPackSteps`. -/
def routePackStep (step : PackStep) (j : Nat) : Nat :=
  match step with
  | PackStep.mk shiftDiff m0 m1 =>
    if Nat.testBit m0 j then j
    else if Nat.testBit m1 j then j + shiftDiff
    else j

/-- Index router for one `PackStep` of `runUnpack`. -/
def routeUnpackStep (step : PackStep) (j : Nat) : Nat :=
  match step with
  | PackStep.mk shiftDiff m0 m1 =>
    if Nat.testBit m0 j then j
    else if shiftDiff ≤ j && Nat.testBit m1 (j - shiftDiff) then j - shiftDiff
    else j

def ValidPackBit (step : PackStep) (j : Nat) : Bool :=
  match step with
  | PackStep.mk _ m0 m1 =>
    Nat.testBit m0 j || Nat.testBit m1 j

def ValidUnpackBit (step : PackStep) (j : Nat) : Bool :=
  match step with
  | PackStep.mk shiftDiff m0 m1 =>
    Nat.testBit m0 j || (decide (shiftDiff ≤ j) && Nat.testBit m1 (j - shiftDiff))

/-- Soundness of a single `stepPack` when `Nat.testBit (stepPack step acc) j = false`. -/
theorem stepPack_false_sound (step : PackStep) (acc j : Nat)
    (hValid : ValidPackBit step j = true)
    (hFalse : Nat.testBit (stepPack step acc) j = false) :
    Nat.testBit acc (routePackStep step j) = false := by
  cases step with
  | mk shiftDiff m0 m1 =>
    dsimp [stepPack, routePackStep, ValidPackBit] at hValid hFalse ⊢
    rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
    rcases hFalse with ⟨hg0, hs1⟩
    by_cases hm0 : Nat.testBit m0 j = true
    · rw [if_pos hm0]
      rw [testBit_land, hm0, Bool.and_true] at hg0
      exact hg0
    · rw [if_neg hm0]
      have hm0F : Nat.testBit m0 j = false := Bool.eq_false_iff.mpr hm0
      rw [hm0F, Bool.false_or] at hValid
      rw [if_pos hValid]
      rw [testBit_land, hValid, Bool.and_true, testBit_shiftRight, Nat.add_comm shiftDiff j] at hs1
      exact hs1

/-- Soundness of a single `stepUnpack` when `Nat.testBit (stepUnpack step acc) j = false`. -/
theorem stepUnpack_false_sound (step : PackStep) (acc j : Nat)
    (hValid : ValidUnpackBit step j = true)
    (hFalse : Nat.testBit (stepUnpack step acc) j = false) :
    Nat.testBit acc (routeUnpackStep step j) = false := by
  cases step with
  | mk shiftDiff m0 m1 =>
    dsimp [stepUnpack, routeUnpackStep, ValidUnpackBit] at hValid hFalse ⊢
    rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
    rcases hFalse with ⟨hg0, hs1⟩
    by_cases hm0 : Nat.testBit m0 j = true
    · rw [if_pos hm0]
      rw [testBit_land, hm0, Bool.and_true] at hg0
      exact hg0
    · rw [if_neg hm0]
      have hm0F : Nat.testBit m0 j = false := Bool.eq_false_iff.mpr hm0
      rw [hm0F, Bool.false_or] at hValid
      have hCond : (shiftDiff ≤ j && Nat.testBit m1 (j - shiftDiff)) = true := hValid
      rw [if_pos hCond]
      rcases Bool.and_eq_true_iff.mp hValid with ⟨hLeB, hm1Sub⟩
      have hLe : j ≥ shiftDiff := of_decide_eq_true hLeB
      rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and,
          testBit_land, hm1Sub, Bool.and_true] at hs1
      exact hs1

/-- Multi-step fold for `runPackSteps`. -/
def foldPack : List PackStep → Nat → Nat
  | [], acc => acc
  | step :: rest, acc => foldPack rest (stepPack step acc)

/-- Multi-step fold for `runUnpack`. -/
def foldUnpack : List PackStep → Nat → Nat
  | [], acc => acc
  | step :: rest, acc => foldUnpack rest (stepUnpack step acc)

theorem foldPack_zero (steps : List PackStep) : foldPack steps 0 = 0 := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | mk shiftDiff m0 m1 =>
      change foldPack rest (stepPack (PackStep.mk shiftDiff m0 m1) 0) = 0
      have h0 : stepPack (PackStep.mk shiftDiff m0 m1) 0 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        dsimp [stepPack]
        simp
      rw [h0]
      exact ih

theorem foldUnpack_zero (steps : List PackStep) : foldUnpack steps 0 = 0 := by
  induction steps with
  | nil => rfl
  | cons step rest ih =>
    cases step with
    | mk shiftDiff m0 m1 =>
      change foldUnpack rest (stepUnpack (PackStep.mk shiftDiff m0 m1) 0) = 0
      have h0 : stepUnpack (PackStep.mk shiftDiff m0 m1) 0 = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        dsimp [stepUnpack]
        simp
      rw [h0]
      exact ih

theorem runPackSteps_eq_fold (steps : List PackStep) (X : Nat) :
    runPackSteps steps X = foldPack steps X := by
  unfold runPackSteps
  have hRec :
      (@List.rec PackStep (fun _ => Nat → Nat)
        (fun acc => acc)
        (fun step _ ih acc =>
          @PackStep.rec (fun _ => Nat)
            (fun shiftDiff m0 m1 =>
              let g0 := Nat.land acc m0
              let s1 := Nat.land (Nat.shiftRight acc shiftDiff) m1
              ih (Nat.lor g0 s1))
            step)
        steps X) = foldPack steps X := by
    induction steps generalizing X with
    | nil => rfl
    | cons step rest ih =>
      cases step with
      | mk shiftDiff m0 m1 =>
        exact ih (stepPack (PackStep.mk shiftDiff m0 m1) X)
  cases hZ : Nat.beq X 0 with
  | true =>
    have hX : X = 0 := Nat.beq_eq.mp hZ
    subst hX
    exact (foldPack_zero steps).symm
  | false =>
    exact hRec

theorem runUnpack_eq_fold (X : Nat) (revSteps : List PackStep) :
    runUnpack X revSteps = foldUnpack revSteps X := by
  unfold runUnpack
  have hRec :
      (@List.rec PackStep (fun _ => Nat → Nat)
        (fun acc => acc)
        (fun step _ ih acc =>
          @PackStep.rec (fun _ => Nat)
            (fun shiftDiff m0 m1 =>
              let g0 := Nat.land acc m0
              let s1 := Nat.shiftLeft (Nat.land acc m1) shiftDiff
              ih (Nat.lor g0 s1))
            step)
        revSteps X) = foldUnpack revSteps X := by
    induction revSteps generalizing X with
    | nil => rfl
    | cons step rest ih =>
      cases step with
      | mk shiftDiff m0 m1 =>
        exact ih (stepUnpack (PackStep.mk shiftDiff m0 m1) X)
  cases hZ : Nat.beq X 0 with
  | true =>
    have hX : X = 0 := Nat.beq_eq.mp hZ
    subst hX
    exact (foldUnpack_zero revSteps).symm
  | false =>
    exact hRec

def routePackList : List PackStep → Nat → Nat
  | [], j => j
  | step :: rest, j => routePackStep step (routePackList rest j)

def routeUnpackList : List PackStep → Nat → Nat
  | [], j => j
  | step :: rest, j => routeUnpackStep step (routeUnpackList rest j)

def ValidPackList : List PackStep → Nat → Bool
  | [], _ => true
  | step :: rest, j =>
    ValidPackList rest j && ValidPackBit step (routePackList rest j)

def ValidUnpackList : List PackStep → Nat → Bool
  | [], _ => true
  | step :: rest, j =>
    ValidUnpackList rest j && ValidUnpackBit step (routeUnpackList rest j)

theorem runPackSteps_false_sound (steps : List PackStep) (X j : Nat)
    (hValid : ValidPackList steps j = true)
    (hFalse : Nat.testBit (runPackSteps steps X) j = false) :
    Nat.testBit X (routePackList steps j) = false := by
  rw [runPackSteps_eq_fold] at hFalse
  induction steps generalizing X with
  | nil => exact hFalse
  | cons step rest ih =>
    dsimp [ValidPackList, routePackList] at hValid ⊢
    rcases Bool.and_eq_true_iff.mp hValid with ⟨hRest, hStep⟩
    have hMid := ih (stepPack step X) hRest hFalse
    exact stepPack_false_sound step X (routePackList rest j) hStep hMid

theorem runUnpack_false_sound (revSteps : List PackStep) (X j : Nat)
    (hValid : ValidUnpackList revSteps j = true)
    (hFalse : Nat.testBit (runUnpack X revSteps) j = false) :
    Nat.testBit X (routeUnpackList revSteps j) = false := by
  rw [runUnpack_eq_fold] at hFalse
  induction revSteps generalizing X with
  | nil => exact hFalse
  | cons step rest ih =>
    dsimp [ValidUnpackList, routeUnpackList] at hValid ⊢
    rcases Bool.and_eq_true_iff.mp hValid with ⟨hRest, hStep⟩
    have hMid := ih (stepUnpack step X) hRest hFalse
    exact stepUnpack_false_sound step X (routeUnpackList rest j) hStep hMid

/-!
### Part 2: Algebraic Reduction of `ChordOp` and `evalCatalanTrie`
-/

@[simp] theorem lor_zero_left (a : Nat) : Nat.lor 0 a = a :=
  Nat.zero_or a

@[simp] theorem lor_zero_right (a : Nat) : Nat.lor a 0 = a :=
  Nat.or_zero a

/-- Function wrapper around `applyChordOp op B`. -/
noncomputable def evalChordOp (op : ChordOp) (B : Nat) : Nat :=
  applyChordOp op B

/-- Without the `selectBool (Nat.beq mBase 0) 0` guard, `evalChordOp` computes the exact same `Nat`. -/
theorem evalChordOp_eq_raw (op : ChordOp) (B : Nat) :
    evalChordOp op B =
      match op with
      | ChordOp.pair dPlus dMinus mask00 mask10 =>
        let mPlus := Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00
        let mMinus := Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10
        let mBase := Nat.lor mPlus mMinus
        Nat.lor mBase (Nat.lor (Nat.shiftLeft mPlus dPlus) (Nat.shiftLeft mMinus dMinus))
      | ChordOp.last dShift mask0 =>
        let m := Nat.land (Nat.land B (Nat.shiftRight B dShift)) mask0
        Nat.lor m (Nat.shiftLeft m dShift) := by
  cases op with
  | pair dPlus dMinus mask00 mask10 =>
    dsimp [evalChordOp]
    cases hZ : Nat.beq (Nat.lor (Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00)
                                (Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10)) 0 with
    | false => rfl
    | true =>
      dsimp
      have hmBase : Nat.lor (Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00)
                            (Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10) = 0 :=
        Nat.beq_eq.mp hZ
      apply Nat.eq_of_testBit_eq; intro i
      have hBit : ∀ k, Nat.testBit (Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00) k = false ∧
                       Nat.testBit (Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10) k = false := by
        intro k
        have hk : Nat.testBit (Nat.lor (Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00)
                                       (Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10)) k = false := by
          rw [hmBase]; exact Nat.zero_testBit k
        rw [testBit_lor, Bool.or_eq_false_iff] at hk
        exact hk
      rw [Nat.zero_testBit, testBit_lor, testBit_lor, testBit_lor,
          testBit_shiftLeft, testBit_shiftLeft,
          (hBit i).1, (hBit i).2, (hBit (i - dPlus)).1, (hBit (i - dMinus)).2]
      simp
  | last dShift mask0 =>
    dsimp [evalChordOp]
    cases hZ : Nat.beq (Nat.land (Nat.land B (Nat.shiftRight B dShift)) mask0) 0 with
    | false => rfl
    | true =>
      dsimp
      have hm : Nat.land (Nat.land B (Nat.shiftRight B dShift)) mask0 = 0 := Nat.beq_eq.mp hZ
      rw [hm]
      apply Nat.eq_of_testBit_eq; intro i; simp

/-- `evalChordOp op 0 = 0` for every `op : ChordOp`. -/
theorem evalChordOp_zero (op : ChordOp) : evalChordOp op 0 = 0 := by
  rw [evalChordOp_eq_raw]
  cases op with
  | pair dPlus dMinus mask00 mask10 =>
    apply Nat.eq_of_testBit_eq; intro i; dsimp; simp
  | last dShift mask0 =>
    apply Nat.eq_of_testBit_eq; intro i; dsimp; simp

/-- `evalCatalanTrie trie 0 = 0` for every `trie : CatalanTrie`. -/
theorem evalCatalanTrie_zero (trie : CatalanTrie) : evalCatalanTrie trie 0 = 0 := by
  induction trie with
  | leaf => rfl
  | nil => rfl
  | leafOp op => exact evalChordOp_zero op
  | only op child _ihChild =>
    cases op with
    | pair dPlus dMinus mask00 mask10 =>
      change (let mPlus := Nat.land (Nat.land 0 (Nat.shiftRight 0 dPlus)) mask00
              let mMinus := Nat.land (Nat.land 0 (Nat.shiftRight 0 dMinus)) mask10
              let mBase := Nat.lor mPlus mMinus
              selectBool (Nat.beq mBase 0) 0
                (evalCatalanTrie child (Nat.lor mBase (Nat.lor (Nat.shiftLeft mPlus dPlus) (Nat.shiftLeft mMinus dMinus))))) = 0
      have h0 : Nat.lor (Nat.land (Nat.land 0 (Nat.shiftRight 0 dPlus)) mask00)
                  (Nat.land (Nat.land 0 (Nat.shiftRight 0 dMinus)) mask10) = 0 := by
        apply Nat.eq_of_testBit_eq; intro i; simp
      dsimp
      rw [h0]
      rfl
    | last dShift mask0 =>
      change (let m := Nat.land (Nat.land 0 (Nat.shiftRight 0 dShift)) mask0
              selectBool (Nat.beq m 0) 0
                (evalCatalanTrie child (Nat.lor m (Nat.shiftLeft m dShift)))) = 0
      have h0 : Nat.land (Nat.land 0 (Nat.shiftRight 0 dShift)) mask0 = 0 := by
        apply Nat.eq_of_testBit_eq; intro i; simp
      dsimp
      rw [h0]
      rfl
  | branch op child sib _ihChild ihSib =>
    cases op with
    | pair dPlus dMinus mask00 mask10 =>
      change (let sibCov := evalCatalanTrie sib 0
              let mPlus := Nat.land (Nat.land 0 (Nat.shiftRight 0 dPlus)) mask00
              let mMinus := Nat.land (Nat.land 0 (Nat.shiftRight 0 dMinus)) mask10
              let mBase := Nat.lor mPlus mMinus
              selectBool (Nat.beq mBase 0) sibCov
                (Nat.lor (evalCatalanTrie child (Nat.lor mBase (Nat.lor (Nat.shiftLeft mPlus dPlus) (Nat.shiftLeft mMinus dMinus)))) sibCov)) = 0
      have h0 : Nat.lor (Nat.land (Nat.land 0 (Nat.shiftRight 0 dPlus)) mask00)
                  (Nat.land (Nat.land 0 (Nat.shiftRight 0 dMinus)) mask10) = 0 := by
        apply Nat.eq_of_testBit_eq; intro i; simp
      dsimp
      rw [h0, ihSib]
      rfl
    | last dShift mask0 =>
      change (let sibCov := evalCatalanTrie sib 0
              let m := Nat.land (Nat.land 0 (Nat.shiftRight 0 dShift)) mask0
              selectBool (Nat.beq m 0) sibCov
                (Nat.lor (evalCatalanTrie child (Nat.lor m (Nat.shiftLeft m dShift))) sibCov)) = 0
      have h0 : Nat.land (Nat.land 0 (Nat.shiftRight 0 dShift)) mask0 = 0 := by
        apply Nat.eq_of_testBit_eq; intro i; simp
      dsimp
      rw [h0, ihSib]
      rfl

/-- `evalCatalanTrie (CatalanTrie.only op child) B` equals `evalCatalanTrie child (evalChordOp op B)`. -/
theorem evalCatalanTrie_only (op : ChordOp) (child : CatalanTrie) (B : Nat) :
    evalCatalanTrie (CatalanTrie.only op child) B =
      evalCatalanTrie child (evalChordOp op B) := by
  cases op with
  | pair dPlus dMinus mask00 mask10 =>
    change (let mPlus := Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00
            let mMinus := Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10
            let mBase := Nat.lor mPlus mMinus
            selectBool (Nat.beq mBase 0) 0
              (evalCatalanTrie child (Nat.lor mBase (Nat.lor (Nat.shiftLeft mPlus dPlus) (Nat.shiftLeft mMinus dMinus))))) =
      evalCatalanTrie child (evalChordOp (ChordOp.pair dPlus dMinus mask00 mask10) B)
    dsimp [evalChordOp]
    cases Nat.beq (Nat.lor (Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00)
                           (Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10)) 0 with
    | false => rfl
    | true => exact (evalCatalanTrie_zero child).symm
  | last dShift mask0 =>
    change (let m := Nat.land (Nat.land B (Nat.shiftRight B dShift)) mask0
            selectBool (Nat.beq m 0) 0
              (evalCatalanTrie child (Nat.lor m (Nat.shiftLeft m dShift)))) =
      evalCatalanTrie child (evalChordOp (ChordOp.last dShift mask0) B)
    dsimp [evalChordOp]
    cases Nat.beq (Nat.land (Nat.land B (Nat.shiftRight B dShift)) mask0) 0 with
    | false => rfl
    | true => exact (evalCatalanTrie_zero child).symm

/-- `evalCatalanTrie (CatalanTrie.branch op child sib) B` equals
    `Nat.lor (evalCatalanTrie child (evalChordOp op B)) (evalCatalanTrie sib B)`. -/
theorem evalCatalanTrie_branch (op : ChordOp) (child sib : CatalanTrie) (B : Nat) :
    evalCatalanTrie (CatalanTrie.branch op child sib) B =
      Nat.lor (evalCatalanTrie child (evalChordOp op B)) (evalCatalanTrie sib B) := by
  cases op with
  | pair dPlus dMinus mask00 mask10 =>
    change (let sibCov := evalCatalanTrie sib B
            let mPlus := Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00
            let mMinus := Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10
            let mBase := Nat.lor mPlus mMinus
            selectBool (Nat.beq mBase 0) sibCov
              (Nat.lor (evalCatalanTrie child (Nat.lor mBase (Nat.lor (Nat.shiftLeft mPlus dPlus) (Nat.shiftLeft mMinus dMinus)))) sibCov)) =
      Nat.lor (evalCatalanTrie child (evalChordOp (ChordOp.pair dPlus dMinus mask00 mask10) B)) (evalCatalanTrie sib B)
    dsimp [evalChordOp]
    cases Nat.beq (Nat.lor (Nat.land (Nat.land B (Nat.shiftRight B dPlus)) mask00)
                           (Nat.land (Nat.land B (Nat.shiftRight B dMinus)) mask10)) 0 with
    | false => rfl
    | true =>
      dsimp
      rw [evalCatalanTrie_zero child, lor_zero_left]
  | last dShift mask0 =>
    change (let sibCov := evalCatalanTrie sib B
            let m := Nat.land (Nat.land B (Nat.shiftRight B dShift)) mask0
            selectBool (Nat.beq m 0) sibCov
              (Nat.lor (evalCatalanTrie child (Nat.lor m (Nat.shiftLeft m dShift))) sibCov)) =
      Nat.lor (evalCatalanTrie child (evalChordOp (ChordOp.last dShift mask0) B)) (evalCatalanTrie sib B)
    dsimp [evalChordOp]
    cases Nat.beq (Nat.land (Nat.land B (Nat.shiftRight B dShift)) mask0) 0 with
    | false => rfl
    | true =>
      dsimp
      rw [evalCatalanTrie_zero child, lor_zero_left]

/-- **Universal Algebraic Reduction of `mkCatalanNode` (`evalCatalanTrie_mkCatalanNode`):**
    For all `op`, `child`, `sib`, and `B`:
    `evalCatalanTrie (mkCatalanNode op child sib) B = Nat.lor (evalCatalanTrie child (evalChordOp op B)) (evalCatalanTrie sib B)`. -/
theorem evalCatalanTrie_mkCatalanNode (op : ChordOp) (child sib : CatalanTrie) (B : Nat) :
    evalCatalanTrie (mkCatalanNode op child sib) B =
      Nat.lor (evalCatalanTrie child (evalChordOp op B)) (evalCatalanTrie sib B) := by
  unfold mkCatalanNode
  cases sib with
  | nil =>
    have hNil : evalCatalanTrie CatalanTrie.nil (evalChordOp op B) = 0 := rfl
    have hNilB : evalCatalanTrie CatalanTrie.nil B = 0 := rfl
    cases child with
    | leaf =>
      change evalChordOp op B = Nat.lor (evalChordOp op B) 0
      rw [lor_zero_right]
    | nil =>
      change evalCatalanTrie (CatalanTrie.only op CatalanTrie.nil) B =
        Nat.lor (evalCatalanTrie CatalanTrie.nil (evalChordOp op B)) 0
      rw [evalCatalanTrie_only, lor_zero_right]
    | leafOp op' =>
      change evalCatalanTrie (CatalanTrie.only op (CatalanTrie.leafOp op')) B =
        Nat.lor (evalCatalanTrie (CatalanTrie.leafOp op') (evalChordOp op B)) 0
      rw [evalCatalanTrie_only, lor_zero_right]
    | only op' c' =>
      change evalCatalanTrie (CatalanTrie.only op (CatalanTrie.only op' c')) B =
        Nat.lor (evalCatalanTrie (CatalanTrie.only op' c') (evalChordOp op B)) 0
      rw [evalCatalanTrie_only, lor_zero_right]
    | branch op' c' s' =>
      change evalCatalanTrie (CatalanTrie.only op (CatalanTrie.branch op' c' s')) B =
        Nat.lor (evalCatalanTrie (CatalanTrie.branch op' c' s') (evalChordOp op B)) 0
      rw [evalCatalanTrie_only, lor_zero_right]
  | leaf =>
    exact evalCatalanTrie_branch op child CatalanTrie.leaf B
  | leafOp op' =>
    exact evalCatalanTrie_branch op child (CatalanTrie.leafOp op') B
  | only op' c' =>
    exact evalCatalanTrie_branch op child (CatalanTrie.only op' c') B
  | branch op' c' s' =>
    exact evalCatalanTrie_branch op child (CatalanTrie.branch op' c' s') B

/-!
### Part 3: Single-Chord Flip Soundness (`evalChordOp_last_false_sound`, `evalChordOp_pair_false_sound`)
-/

/-- Mate index for `ChordOp.last dShift mask0` at bit `j`:
    if `Nat.testBit mask0 j = true`, flips upward to `j + dShift`;
    otherwise flips downward to `j - dShift`. -/
def mateLastIdx (dShift mask0 j : Nat) : Nat :=
  if Nat.testBit mask0 j then j + dShift else j - dShift

/-- Mate index for `ChordOp.pair dPlus dMinus mask00 mask10` at bit `j`:
    - `00` (`Nat.testBit mask00 j`): `j + dPlus`
    - `11` (`dPlus ≤ j ∧ Nat.testBit mask00 (j - dPlus)`): `j - dPlus`
    - `10` (`Nat.testBit mask10 j`): `j + dMinus`
    - `01` (`dMinus ≤ j ∧ Nat.testBit mask10 (j - dMinus)`): `j - dMinus` -/
def matePairIdx (dPlus dMinus mask00 mask10 j : Nat) : Nat :=
  if Nat.testBit mask00 j then j + dPlus
  else if dPlus ≤ j && Nat.testBit mask00 (j - dPlus) then j - dPlus
  else if Nat.testBit mask10 j then j + dMinus
  else j - dMinus

def ValidLastBit (dShift mask0 j : Nat) : Bool :=
  Nat.testBit mask0 j || (decide (dShift ≤ j) && Nat.testBit mask0 (j - dShift))

def ValidPairBit (dPlus dMinus mask00 mask10 j : Nat) : Bool :=
  Nat.testBit mask00 j ||
  (decide (dPlus ≤ j) && Nat.testBit mask00 (j - dPlus)) ||
  Nat.testBit mask10 j ||
  (decide (dMinus ≤ j) && Nat.testBit mask10 (j - dMinus))

/-- **Soundness of `ChordOp.last` when `Nat.testBit (evalChordOp (ChordOp.last dShift mask0) B) j = false`:**
    At least one of `j` or `mateLastIdx dShift mask0 j` has bit `false` in `B`. -/
theorem evalChordOp_last_false_sound (dShift mask0 B j : Nat)
    (hValid : ValidLastBit dShift mask0 j = true)
    (hFalse : Nat.testBit (evalChordOp (ChordOp.last dShift mask0) B) j = false) :
    Nat.testBit B j = false ∨ Nat.testBit B (mateLastIdx dShift mask0 j) = false := by
  rw [evalChordOp_eq_raw] at hFalse
  dsimp at hFalse
  rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
  rcases hFalse with ⟨hm0, hm1⟩
  dsimp [ValidLastBit, mateLastIdx] at hValid ⊢
  by_cases hMask : Nat.testBit mask0 j = true
  · rw [if_pos hMask]
    rw [testBit_land, hMask, Bool.and_true, testBit_land, testBit_shiftRight,
        Nat.add_comm dShift j, Bool.and_eq_false_imp] at hm0
    by_cases hBj : Nat.testBit B j = true
    · exact Or.inr (hm0 hBj)
    · exact Or.inl (Bool.eq_false_iff.mpr hBj)
  · rw [if_neg hMask]
    have hMaskF : Nat.testBit mask0 j = false := Bool.eq_false_iff.mpr hMask
    rw [hMaskF, Bool.false_or] at hValid
    rcases Bool.and_eq_true_iff.mp hValid with ⟨hLeB, hMaskSub⟩
    have hLe : j ≥ dShift := of_decide_eq_true hLeB
    rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and,
        testBit_land, hMaskSub, Bool.and_true, testBit_land,
        testBit_shiftRight, Nat.add_comm dShift (j - dShift),
        Nat.sub_add_cancel hLe, Bool.and_eq_false_imp] at hm1
    by_cases hBsub : Nat.testBit B (j - dShift) = true
    · exact Or.inl (hm1 hBsub)
    · exact Or.inr (Bool.eq_false_iff.mpr hBsub)

/-- **Soundness of `ChordOp.pair` when `Nat.testBit (evalChordOp (ChordOp.pair dPlus dMinus mask00 mask10) B) j = false`:**
    At least one of `j` or `matePairIdx dPlus dMinus mask00 mask10 j` has bit `false` in `B`. -/
theorem evalChordOp_pair_false_sound (dPlus dMinus mask00 mask10 B j : Nat)
    (hValid : ValidPairBit dPlus dMinus mask00 mask10 j = true)
    (hFalse : Nat.testBit (evalChordOp (ChordOp.pair dPlus dMinus mask00 mask10) B) j = false) :
    Nat.testBit B j = false ∨ Nat.testBit B (matePairIdx dPlus dMinus mask00 mask10 j) = false := by
  rw [evalChordOp_eq_raw] at hFalse
  dsimp at hFalse
  rw [testBit_lor, testBit_lor, testBit_lor,
      Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hFalse
  rcases hFalse with ⟨⟨hPlus0, hMinus0⟩, hPlus1, hMinus1⟩
  dsimp [ValidPairBit, matePairIdx] at hValid ⊢
  by_cases hm00 : Nat.testBit mask00 j = true
  · rw [if_pos hm00]
    rw [testBit_land, hm00, Bool.and_true, testBit_land, testBit_shiftRight,
        Nat.add_comm dPlus j, Bool.and_eq_false_imp] at hPlus0
    by_cases hBj : Nat.testBit B j = true
    · exact Or.inr (hPlus0 hBj)
    · exact Or.inl (Bool.eq_false_iff.mpr hBj)
  · rw [if_neg hm00]
    have hm00F : Nat.testBit mask00 j = false := Bool.eq_false_iff.mpr hm00
    rw [hm00F, Bool.false_or] at hValid
    by_cases hm11 : (dPlus ≤ j && Nat.testBit mask00 (j - dPlus)) = true
    · rw [if_pos hm11]
      rcases Bool.and_eq_true_iff.mp hm11 with ⟨hLeB, hm00Sub⟩
      have hLe : j ≥ dPlus := of_decide_eq_true hLeB
      rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and,
          testBit_land, hm00Sub, Bool.and_true, testBit_land,
          testBit_shiftRight, Nat.add_comm dPlus (j - dPlus),
          Nat.sub_add_cancel hLe, Bool.and_eq_false_imp] at hPlus1
      by_cases hBsub : Nat.testBit B (j - dPlus) = true
      · exact Or.inl (hPlus1 hBsub)
      · exact Or.inr (Bool.eq_false_iff.mpr hBsub)
    · rw [if_neg hm11]
      have hm11F : (decide (dPlus ≤ j) && Nat.testBit mask00 (j - dPlus)) = false :=
        Bool.eq_false_iff.mpr hm11
      rw [hm11F, Bool.false_or] at hValid
      by_cases hm10 : Nat.testBit mask10 j = true
      · rw [if_pos hm10]
        rw [testBit_land, hm10, Bool.and_true, testBit_land, testBit_shiftRight,
            Nat.add_comm dMinus j, Bool.and_eq_false_imp] at hMinus0
        by_cases hBj : Nat.testBit B j = true
        · exact Or.inr (hMinus0 hBj)
        · exact Or.inl (Bool.eq_false_iff.mpr hBj)
      · rw [if_neg hm10]
        have hm10F : Nat.testBit mask10 j = false := Bool.eq_false_iff.mpr hm10
        rw [hm10F, Bool.false_or] at hValid
        rcases Bool.and_eq_true_iff.mp hValid with ⟨hLeB, hm10Sub⟩
        have hLe : j ≥ dMinus := of_decide_eq_true hLeB
        rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and,
            testBit_land, hm10Sub, Bool.and_true, testBit_land,
            testBit_shiftRight, Nat.add_comm dMinus (j - dMinus),
            Nat.sub_add_cancel hLe, Bool.and_eq_false_imp] at hMinus1
        by_cases hBsub : Nat.testBit B (j - dMinus) = true
        · exact Or.inl (hMinus1 hBsub)
        · exact Or.inr (Bool.eq_false_iff.mpr hBsub)

/-- If `Nat.testBit (evalCatalanTrie (mkCatalanNode op child sib) B) j = false`, then
    both the child subtree (evaluated on `evalChordOp op B`) and the sibling subtree
    (evaluated on `B`) have bit `j = false`. -/
theorem evalCatalanTrie_mkCatalanNode_false_sound
    (op : ChordOp) (child sib : CatalanTrie) (B j : Nat)
    (hFalse : Nat.testBit (evalCatalanTrie (mkCatalanNode op child sib) B) j = false) :
    Nat.testBit (evalCatalanTrie child (evalChordOp op B)) j = false ∧
    Nat.testBit (evalCatalanTrie sib B) j = false := by
  rw [evalCatalanTrie_mkCatalanNode, testBit_lor, Bool.or_eq_false_iff] at hFalse
  exact hFalse

/-- Function wrapper around `evalBucketCatalan bSpec B`. -/
noncomputable def evalBucketSpec (bSpec : BucketCatalanSpec) (B : Nat) : Nat :=
  evalBucketCatalan bSpec B

/-- Odd-bucket soundness of `evalBucketSpec`: when `kBucket > 0` and `isEven = false`,
    `Nat.testBit (evalBucketSpec bSpec B) j = false` implies `Nat.testBit (evalCatalanTrie trie B) j = false`. -/
theorem evalBucketSpec_odd_false_sound
    (kBucket halfShift evenHalfMask evenParityMask : Nat) (trie : CatalanTrie) (B j : Nat)
    (hk : Nat.beq kBucket 0 = false)
    (hFalse : Nat.testBit
      (evalBucketSpec (BucketCatalanSpec.mk kBucket false halfShift evenHalfMask evenParityMask trie) B) j = false) :
    Nat.testBit (evalCatalanTrie trie B) j = false := by
  unfold evalBucketSpec at hFalse
  dsimp at hFalse
  rw [hk] at hFalse
  dsimp at hFalse
  cases hB : Nat.beq B 0 with
  | true =>
    have hB0 : B = 0 := Nat.beq_eq.mp hB
    subst hB0
    rw [evalCatalanTrie_zero, Nat.zero_testBit]
  | false =>
    rw [hB] at hFalse
    dsimp at hFalse
    exact hFalse

/-- Even-bucket soundness of `evalBucketSpec`: when `kBucket > 0`, `isEven = true`, and
    `Nat.testBit evenParityMask j = true`, `Nat.testBit (evalBucketSpec bSpec B) j = false` implies
    `Nat.testBit (evalCatalanTrie trie workB) j = false` (and if `halfShift ≤ j`,
    `Nat.testBit (evalCatalanTrie trie workB) (j - halfShift) = false`). -/
theorem evalBucketSpec_even_false_sound
    (kBucket halfShift evenHalfMask evenParityMask : Nat) (trie : CatalanTrie) (B j : Nat)
    (hk : Nat.beq kBucket 0 = false)
    (hPar : Nat.testBit evenParityMask j = true)
    (hFalse : Nat.testBit
      (evalBucketSpec (BucketCatalanSpec.mk kBucket true halfShift evenHalfMask evenParityMask trie) B) j = false) :
    let workB := Nat.lor (Nat.land B evenHalfMask)
                         (Nat.land (Nat.shiftRight B halfShift) evenHalfMask)
    Nat.testBit (evalCatalanTrie trie workB) j = false ∧
    (halfShift ≤ j → Nat.testBit (evalCatalanTrie trie workB) (j - halfShift) = false) := by
  dsimp
  unfold evalBucketSpec at hFalse
  dsimp at hFalse
  rw [hk] at hFalse
  dsimp at hFalse
  let workB := Nat.lor (Nat.land B evenHalfMask) (Nat.land (Nat.shiftRight B halfShift) evenHalfMask)
  change Nat.testBit (evalCatalanTrie trie workB) j = false ∧
    (halfShift ≤ j → Nat.testBit (evalCatalanTrie trie workB) (j - halfShift) = false)
  cases hB : Nat.beq B 0 with
  | true =>
    have hB0 : B = 0 := Nat.beq_eq.mp hB
    have hW0 : workB = 0 := by
      dsimp [workB]; rw [hB0]; apply Nat.eq_of_testBit_eq; intro i; simp
    rw [hW0, evalCatalanTrie_zero]
    exact ⟨Nat.zero_testBit j, fun _ => Nat.zero_testBit (j - halfShift)⟩
  | false =>
    rw [hB] at hFalse
    dsimp at hFalse
    cases hW : Nat.beq workB 0 with
    | true =>
      have hW0 : workB = 0 := Nat.beq_eq.mp hW
      rw [hW0, evalCatalanTrie_zero]
      exact ⟨Nat.zero_testBit j, fun _ => Nat.zero_testBit (j - halfShift)⟩
    | false =>
      change Nat.testBit
        (selectBool (Nat.beq workB 0) 0
          (let cov := evalCatalanTrie trie workB
           Nat.land (Nat.lor cov (Nat.shiftLeft cov halfShift)) evenParityMask)) j = false at hFalse
      rw [hW] at hFalse
      dsimp at hFalse
      rw [testBit_land, hPar, Bool.and_true, testBit_lor, Bool.or_eq_false_iff] at hFalse
      refine ⟨hFalse.1, ?_⟩
      intro hLe
      have hShift := hFalse.2
      rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and] at hShift
      exact hShift

/-!
### Part 4: Symbolic Bit-Routing Soundness of `withPackSteps`, `packToBuckets`, and `withUnpackFromBucketsPair`
-/

theorem stepPack_false_0 (shiftDiff m0 m1 acc j : Nat)
    (hm0 : Nat.testBit m0 j = true)
    (hFalse : Nat.testBit (stepPack (PackStep.mk shiftDiff m0 m1) acc) j = false) :
    Nat.testBit acc j = false := by
  dsimp [stepPack] at hFalse
  rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
  have hg0 := hFalse.1
  rw [testBit_land, hm0, Bool.and_true] at hg0
  exact hg0

theorem stepPack_false_1 (shiftDiff m0 m1 acc j : Nat)
    (hm1 : Nat.testBit m1 j = true)
    (hFalse : Nat.testBit (stepPack (PackStep.mk shiftDiff m0 m1) acc) j = false) :
    Nat.testBit acc (j + shiftDiff) = false := by
  dsimp [stepPack] at hFalse
  rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
  have hs1 := hFalse.2
  rw [testBit_land, hm1, Bool.and_true, testBit_shiftRight, Nat.add_comm shiftDiff j] at hs1
  exact hs1

theorem stepUnpack_false_0 (shiftDiff m0 m1 acc j : Nat)
    (hm0 : Nat.testBit m0 j = true)
    (hFalse : Nat.testBit (stepUnpack (PackStep.mk shiftDiff m0 m1) acc) j = false) :
    Nat.testBit acc j = false := by
  dsimp [stepUnpack] at hFalse
  rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
  have hg0 := hFalse.1
  rw [testBit_land, hm0, Bool.and_true] at hg0
  exact hg0

theorem stepUnpack_false_1 (shiftDiff m0 m1 acc j : Nat)
    (hLe : shiftDiff ≤ j)
    (hm1 : Nat.testBit m1 (j - shiftDiff) = true)
    (hFalse : Nat.testBit (stepUnpack (PackStep.mk shiftDiff m0 m1) acc) j = false) :
    Nat.testBit acc (j - shiftDiff) = false := by
  dsimp [stepUnpack] at hFalse
  rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
  have hs1 := hFalse.2
  rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and, testBit_land, hm1, Bool.and_true] at hs1
  exact hs1

theorem testBit_getRepeatMask_of_decompose (count stride width q r : Nat)
    (hq : q < count) (hr : r < width) (hws : width ≤ stride) :
    Nat.testBit (getRepeatMask count stride width) (q * stride + r) = true := by
  have hs : 0 < stride := by omega
  rw [testBit_getRepeatMask count stride width (q * stride + r) hs hws]
  have hlt : q * stride + r < count * stride := by
    have h1 : (q + 1) * stride ≤ count * stride := Nat.mul_le_mul_right stride hq
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  have hhr : r < stride := Nat.lt_of_lt_of_le hr hws
  have hmod : (q * stride + r) % stride = r := by
    rw [Nat.add_comm (q * stride) r, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hhr]
  rw [decide_eq_true hlt, hmod, decide_eq_true hr, Bool.and_self]

theorem testBit_two_pow_sub_two_pow (hi lo j : Nat) (hLo : lo ≤ j) (hHi : j < hi) :
    Nat.testBit (Nat.sub (Nat.shiftLeft 1 hi) (Nat.shiftLeft 1 lo)) j = true := by
  have hle : lo ≤ hi := by omega
  have hEq : Nat.sub (Nat.shiftLeft 1 hi) (Nat.shiftLeft 1 lo) =
      Nat.shiftLeft ((1 <<< (hi - lo)) - 1) lo := by
    change (1 <<< hi) - (1 <<< lo) = ((1 <<< (hi - lo)) - 1) <<< lo
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
        Nat.one_mul, Nat.one_mul, Nat.one_mul, Nat.sub_mul, ← Nat.pow_add,
        Nat.sub_add_cancel hle, Nat.one_mul]
  rw [hEq, testBit_shiftLeft, decide_eq_true hLo, Bool.true_and,
      Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true (by omega)

noncomputable def mkPackStepAt (N W S b : Nat) : PackStep :=
  let pow2b := Nat.shiftLeft 1 b
  let nextB := Nat.succ b
  let pow2b1 := Nat.shiftLeft 1 nextB
  let curW := Nat.mul pow2b W
  let oldStep := Nat.mul pow2b S
  let shiftDiff := Nat.sub oldStep curW
  let numPairs := Nat.shiftRight (Nat.add N (Nat.sub pow2b1 1)) nextB
  let m0 := getRepeatMask numPairs (Nat.mul 2 oldStep) curW
  let m1 :=
    selectBool (Nat.ble N pow2b1)
      (Nat.sub (Nat.shiftLeft 1 (Nat.mul N W)) (Nat.shiftLeft 1 curW))
      (Nat.shiftLeft m0 curW)
  PackStep.mk shiftDiff m0 m1

noncomputable def buildPackStepsFwd (fuel N W S b : Nat) : List PackStep :=
  match fuel with
  | 0 => []
  | fuel' + 1 =>
    if Nat.blt (Nat.shiftLeft 1 b) N then
      mkPackStepAt N W S b :: buildPackStepsFwd fuel' N W S (b + 1)
    else []

def packPos (W S b c rem : Nat) : Nat :=
  (c / (1 <<< b)) * ((1 <<< b) * S) + (c % (1 <<< b)) * W + rem

theorem shiftLeft_one_succ (b : Nat) : (1 <<< (b + 1)) = 2 * (1 <<< b) := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_comm]

theorem shiftLeft_one_pos (b : Nat) : 0 < (1 <<< b) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.two_pow_pos b

theorem shiftRight_eq_div_shiftLeft_one (x k : Nat) :
    Nat.shiftRight x k = x / (1 <<< k) := by
  change x >>> k = x / (1 <<< k)
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.one_mul]

theorem div_mod_two_mul (K c : Nat) (hK : 0 < K) :
    c / (2 * K) = (c / K) / 2 ∧ c % (2 * K) = ((c / K) % 2) * K + c % K := by
  have hDiv : c / (2 * K) = (c / K) / 2 := by
    rw [Nat.mul_comm 2 K, ← Nat.div_div_eq_div_mul]
  refine ⟨hDiv, ?_⟩
  have h1 : c = K * (c / K) + c % K := (Nat.div_add_mod c K).symm
  have h2 : c / K = 2 * ((c / K) / 2) + (c / K) % 2 := (Nat.div_add_mod (c / K) 2).symm
  have h3 : c = (2 * K) * (c / (2 * K)) + c % (2 * K) := (Nat.div_add_mod c (2 * K)).symm
  rw [hDiv] at h3
  have h4 : K * (c / K) = (2 * K) * ((c / K) / 2) + ((c / K) % 2) * K := by
    calc K * (c / K)
      _ = K * (2 * ((c / K) / 2) + (c / K) % 2) := by rw [← h2]
      _ = K * (2 * ((c / K) / 2)) + K * ((c / K) % 2) := Nat.mul_add _ _ _
      _ = (2 * K) * ((c / K) / 2) + ((c / K) % 2) * K := by
        rw [← Nat.mul_assoc K 2, Nat.mul_comm K 2, Nat.mul_comm K ((c / K) % 2)]
  omega

theorem div_lt_ceil_div (N M c : Nat) (hM : 0 < M) (hc : c < N) :
    c / M < (N + (M - 1)) / M := by
  have h1 : c = M * (c / M) + c % M := (Nat.div_add_mod c M).symm
  have h2 : (c / M + 1) * M ≤ N + (M - 1) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (c / M) M]
    omega
  exact (Nat.le_div_iff_mul_le hM).mpr h2

theorem mul_add_lt_mul (r K W rem : Nat) (hr : r < K) (hrem : rem < W) :
    r * W + rem < K * W := by
  have h1 : (r + 1) * W ≤ K * W := Nat.mul_le_mul_right W hr
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

theorem mkPackStepAt_props (N W S b c rem : Nat)
    (hc : c < N) (hrem : rem < W) (hws : W ≤ S) :
    let K := 1 <<< b
    let curW := K * W
    let oldStep := K * S
    let shiftDiff := oldStep - curW
    let numPairs := (N + (2 * K - 1)) / (2 * K)
    let m0 := getRepeatMask numPairs (2 * oldStep) curW
    let m1 :=
      if Nat.ble N (2 * K) then
        Nat.sub (Nat.shiftLeft 1 (N * W)) (Nat.shiftLeft 1 curW)
      else
        Nat.shiftLeft m0 curW
    ((c / K) % 2 = 0 →
      packPos W S (b + 1) c rem = packPos W S b c rem ∧
      Nat.testBit m0 (packPos W S (b + 1) c rem) = true) ∧
    ((c / K) % 2 ≠ 0 →
      packPos W S b c rem = packPos W S (b + 1) c rem + shiftDiff ∧
      Nat.testBit m1 (packPos W S (b + 1) c rem) = true) := by
  dsimp
  have hK : 0 < (1 <<< b) := shiftLeft_one_pos b
  rcases div_mod_two_mul (1 <<< b) c hK with ⟨hDiv2, hMod2⟩
  have hSucc : (1 <<< (b + 1)) = 2 * (1 <<< b) := shiftLeft_one_succ b
  have hr0 : c % (1 <<< b) < (1 <<< b) := Nat.mod_lt c hK
  have hRemW : (c % (1 <<< b)) * W + rem < (1 <<< b) * W :=
    mul_add_lt_mul (c % (1 <<< b)) (1 <<< b) W rem hr0 hrem
  have hKW_le : (1 <<< b) * W ≤ (1 <<< b) * S := Nat.mul_le_mul_left (1 <<< b) hws
  have hKW_le2 : (1 <<< b) * W ≤ 2 * ((1 <<< b) * S) := by omega
  have hq1_lt : (c / (1 <<< b)) / 2 < (N + (2 * (1 <<< b) - 1)) / (2 * (1 <<< b)) := by
    rw [← hDiv2]
    exact div_lt_ceil_div N (2 * (1 <<< b)) c (by omega) hc
  have hb0_lt : (c / (1 <<< b)) % 2 < 2 := Nat.mod_lt (c / (1 <<< b)) (by decide)
  constructor
  · intro hb0
    have hPos1 : packPos W S (b + 1) c rem =
        ((c / (1 <<< b)) / 2) * (2 * ((1 <<< b) * S)) + ((c % (1 <<< b)) * W + rem) := by
      unfold packPos
      rw [hSucc, hDiv2, hMod2, hb0, Nat.zero_mul, Nat.zero_add,
          Nat.mul_assoc 2 (1 <<< b) S, Nat.add_assoc]
    have hPos0 : packPos W S b c rem =
        ((c / (1 <<< b)) / 2) * (2 * ((1 <<< b) * S)) + ((c % (1 <<< b)) * W + rem) := by
      unfold packPos
      have hDivK : c / (1 <<< b) = 2 * ((c / (1 <<< b)) / 2) := by
        have := (Nat.div_add_mod (c / (1 <<< b)) 2).symm
        omega
      have hMul : (c / (1 <<< b)) * ((1 <<< b) * S) =
          ((c / (1 <<< b)) / 2) * (2 * ((1 <<< b) * S)) := by
        rw [ ← Nat.mul_assoc ((c / (1 <<< b)) / 2) 2,
             Nat.mul_comm ((c / (1 <<< b)) / 2) 2, ← hDivK ]
      rw [hMul, Nat.add_assoc]
    refine ⟨hPos1.trans hPos0.symm, ?_⟩
    rw [hPos1]
    exact testBit_getRepeatMask_of_decompose _ _ _ _ _ hq1_lt hRemW hKW_le2
  · intro hb0
    have hb1 : (c / (1 <<< b)) % 2 = 1 := by omega
    have hPos1 : packPos W S (b + 1) c rem =
        ((c / (1 <<< b)) / 2) * (2 * ((1 <<< b) * S)) + (1 <<< b) * W + ((c % (1 <<< b)) * W + rem) := by
      unfold packPos
      rw [hSucc, hDiv2, hMod2, hb1, Nat.one_mul, Nat.add_mul,
          Nat.mul_assoc 2 (1 <<< b) S]
      omega
    have hPos0 : packPos W S b c rem =
        ((c / (1 <<< b)) / 2) * (2 * ((1 <<< b) * S)) + (1 <<< b) * S + ((c % (1 <<< b)) * W + rem) := by
      unfold packPos
      have hDivK : c / (1 <<< b) = 2 * ((c / (1 <<< b)) / 2) + 1 := by
        have := (Nat.div_add_mod (c / (1 <<< b)) 2).symm
        omega
      have hMul : (c / (1 <<< b)) * ((1 <<< b) * S) =
          ((c / (1 <<< b)) / 2) * (2 * ((1 <<< b) * S)) + (1 <<< b) * S := by
        calc (c / (1 <<< b)) * ((1 <<< b) * S)
          _ = (2 * ((c / (1 <<< b)) / 2) + 1) * ((1 <<< b) * S) := by
            congr 1
          _ = (2 * ((c / (1 <<< b)) / 2)) * ((1 <<< b) * S) + 1 * ((1 <<< b) * S) :=
            Nat.add_mul _ _ _
          _ = ((c / (1 <<< b)) / 2) * (2 * ((1 <<< b) * S)) + (1 <<< b) * S := by
            rw [Nat.mul_comm 2 ((c / (1 <<< b)) / 2), Nat.mul_assoc, Nat.one_mul]
      rw [hMul, Nat.add_assoc]
    refine ⟨by omega, ?_⟩
    cases hBle : Nat.ble N (2 * (1 <<< b)) with
    | true =>
      rw [if_pos rfl]
      have hNle : N ≤ 2 * (1 <<< b) := Nat.ble_eq.mp hBle
      have hc2 : c < 2 * (1 <<< b) := Nat.lt_of_lt_of_le hc hNle
      have hq1_0 : (c / (1 <<< b)) / 2 = 0 := by
        rw [← hDiv2]
        exact Nat.div_eq_of_lt hc2
      have hKr0 : (1 <<< b) + c % (1 <<< b) = c := by
        have h := Nat.mod_eq_of_lt hc2
        rw [hMod2, hb1, Nat.one_mul] at h
        exact h
      have hPos1_eq : packPos W S (b + 1) c rem = c * W + rem := by
        unfold packPos
        rw [hSucc, hDiv2, hq1_0, Nat.zero_mul, Nat.zero_add, hMod2, hb1, Nat.one_mul, hKr0]
      rw [hPos1_eq]
      have hLo : (1 <<< b) * W ≤ c * W + rem := by
        have hKc : (1 <<< b) ≤ c := by omega
        have := Nat.mul_le_mul_right W hKc
        omega
      have hHi : c * W + rem < N * W := mul_add_lt_mul c N W rem hc hrem
      exact testBit_two_pow_sub_two_pow (N * W) ((1 <<< b) * W) (c * W + rem) hLo hHi
    | false =>
      rw [if_neg (by decide)]
      have hGe : (1 <<< b) * W ≤ packPos W S (b + 1) c rem := by omega
      have hSub : packPos W S (b + 1) c rem - (1 <<< b) * W =
          ((c / (1 <<< b)) / 2) * (2 * ((1 <<< b) * S)) + ((c % (1 <<< b)) * W + rem) := by omega
      rw [testBit_shiftLeft, decide_eq_true hGe, Bool.true_and, hSub]
      exact testBit_getRepeatMask_of_decompose _ _ _ _ _ hq1_lt hRemW hKW_le2

theorem mkPackStepAt_eq (N W S b : Nat) :
    mkPackStepAt N W S b =
      let K := 1 <<< b
      let curW := K * W
      let oldStep := K * S
      let shiftDiff := oldStep - curW
      let numPairs := (N + (2 * K - 1)) / (2 * K)
      let m0 := getRepeatMask numPairs (2 * oldStep) curW
      let m1 :=
        if Nat.ble N (2 * K) then
          Nat.sub (Nat.shiftLeft 1 (N * W)) (Nat.shiftLeft 1 curW)
        else
          Nat.shiftLeft m0 curW
      PackStep.mk shiftDiff m0 m1 := by
  unfold mkPackStepAt
  dsimp
  have h1 : Nat.shiftLeft 1 b = (1 <<< b) := rfl
  have h2 : Nat.shiftLeft 1 (b + 1) = 2 * (1 <<< b) := shiftLeft_one_succ b
  have h3 : (N + (Nat.shiftLeft 1 (b + 1) - 1)).shiftRight (b + 1) =
      (N + (2 * (1 <<< b) - 1)) / (2 * (1 <<< b)) := by
    rw [shiftRight_eq_div_shiftLeft_one, h2, ← shiftLeft_one_succ]
  rw [h3, h1, h2]
  cases Nat.ble N (2 * (1 <<< b)) <;> rfl

theorem mkPackStepAt_pack_false_sound (N W S b c rem acc : Nat)
    (hc : c < N) (hrem : rem < W) (hws : W ≤ S)
    (hFalse : Nat.testBit (stepPack (mkPackStepAt N W S b) acc) (packPos W S (b + 1) c rem) = false) :
    Nat.testBit acc (packPos W S b c rem) = false := by
  rw [mkPackStepAt_eq] at hFalse
  rcases mkPackStepAt_props N W S b c rem hc hrem hws with ⟨hEven, hOdd⟩
  by_cases hb0 : (c / (1 <<< b)) % 2 = 0
  · rcases hEven hb0 with ⟨hPosEq, hm0⟩
    rw [← hPosEq]
    exact stepPack_false_0 _ _ _ acc _ hm0 hFalse
  · rcases hOdd hb0 with ⟨hPosEq, hm1⟩
    rw [hPosEq]
    exact stepPack_false_1 _ _ _ acc _ hm1 hFalse

theorem mkPackStepAt_unpack_false_sound (N W S b c rem acc : Nat)
    (hc : c < N) (hrem : rem < W) (hws : W ≤ S)
    (hFalse : Nat.testBit (stepUnpack (mkPackStepAt N W S b) acc) (packPos W S b c rem) = false) :
    Nat.testBit acc (packPos W S (b + 1) c rem) = false := by
  rw [mkPackStepAt_eq] at hFalse
  rcases mkPackStepAt_props N W S b c rem hc hrem hws with ⟨hEven, hOdd⟩
  by_cases hb0 : (c / (1 <<< b)) % 2 = 0
  · rcases hEven hb0 with ⟨hPosEq, hm0⟩
    rw [hPosEq]
    rw [hPosEq] at hm0
    exact stepUnpack_false_0 _ _ _ acc _ hm0 hFalse
  · rcases hOdd hb0 with ⟨hPosEq, hm1⟩
    have hLe : (1 <<< b) * S - (1 <<< b) * W ≤ packPos W S b c rem := by omega
    have hSub : packPos W S b c rem - ((1 <<< b) * S - (1 <<< b) * W) = packPos W S (b + 1) c rem := by omega
    rw [← hSub]
    rw [← hSub] at hm1
    exact stepUnpack_false_1 _ _ _ acc _ hLe hm1 hFalse

theorem packPos_zero (W S c rem : Nat) :
    packPos W S 0 c rem = c * S + rem := by
  unfold packPos
  change (c / 1) * (1 * S) + (c % 1) * W + rem = c * S + rem
  rw [Nat.div_one, Nat.one_mul, Nat.mod_one, Nat.zero_mul, Nat.add_zero]

theorem packPos_of_lt (W S b c rem : Nat) (hc : c < (1 <<< b)) :
    packPos W S b c rem = c * W + rem := by
  unfold packPos
  rw [Nat.div_eq_of_lt hc, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hc]

theorem foldUnpack_append (xs ys : List PackStep) (acc : Nat) :
    foldUnpack (xs ++ ys) acc = foldUnpack ys (foldUnpack xs acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih => exact ih (stepUnpack x acc)

theorem buildPackStepsFwd_pack_false_sound :
    ∀ (fuel N W S b c rem acc : Nat),
      c < N → rem < W → W ≤ S → N ≤ (1 <<< (b + fuel)) →
      Nat.testBit (foldPack (buildPackStepsFwd fuel N W S b) acc) (c * W + rem) = false →
      Nat.testBit acc (packPos W S b c rem) = false
  | 0, N, W, S, b, c, rem, acc, hc, _, _, hN, hFalse => by
    rw [Nat.add_zero] at hN
    have hcB : c < (1 <<< b) := Nat.lt_of_lt_of_le hc hN
    rw [packPos_of_lt W S b c rem hcB]
    exact hFalse
  | fuel' + 1, N, W, S, b, c, rem, acc, hc, hrem, hws, hN, hFalse => by
    unfold buildPackStepsFwd at hFalse
    cases hBlt : Nat.blt (Nat.shiftLeft 1 b) N with
    | false =>
      rw [if_neg (by simp [hBlt])] at hFalse
      have hGe : N ≤ (1 <<< b) := by
        have hNotLt : ¬ (1 <<< b) < N := by
          intro hLt
          have : Nat.blt (Nat.shiftLeft 1 b) N = true := Nat.blt_eq.mpr hLt
          rw [hBlt] at this
          contradiction
        omega
      have hcB : c < (1 <<< b) := Nat.lt_of_lt_of_le hc hGe
      rw [packPos_of_lt W S b c rem hcB]
      exact hFalse
    | true =>
      rw [if_pos hBlt] at hFalse
      dsimp [foldPack] at hFalse
      have hN' : N ≤ (1 <<< ((b + 1) + fuel')) := by
        rw [Nat.add_right_comm b 1 fuel']
        exact hN
      have hMid := buildPackStepsFwd_pack_false_sound fuel' N W S (b + 1) c rem
        (stepPack (mkPackStepAt N W S b) acc) hc hrem hws hN' hFalse
      exact mkPackStepAt_pack_false_sound N W S b c rem acc hc hrem hws hMid

theorem buildPackStepsFwd_unpack_false_sound :
    ∀ (fuel N W S b c rem acc : Nat),
      c < N → rem < W → W ≤ S → N ≤ (1 <<< (b + fuel)) →
      Nat.testBit (foldUnpack (buildPackStepsFwd fuel N W S b).reverse acc) (packPos W S b c rem) = false →
      Nat.testBit acc (c * W + rem) = false
  | 0, N, W, S, b, c, rem, acc, hc, _, _, hN, hFalse => by
    rw [Nat.add_zero] at hN
    have hcB : c < (1 <<< b) := Nat.lt_of_lt_of_le hc hN
    rw [packPos_of_lt W S b c rem hcB] at hFalse
    exact hFalse
  | fuel' + 1, N, W, S, b, c, rem, acc, hc, hrem, hws, hN, hFalse => by
    unfold buildPackStepsFwd at hFalse
    cases hBlt : Nat.blt (Nat.shiftLeft 1 b) N with
    | false =>
      rw [if_neg (by simp [hBlt])] at hFalse
      have hGe : N ≤ (1 <<< b) := by
        have hNotLt : ¬ (1 <<< b) < N := by
          intro hLt
          have : Nat.blt (Nat.shiftLeft 1 b) N = true := Nat.blt_eq.mpr hLt
          rw [hBlt] at this
          contradiction
        omega
      have hcB : c < (1 <<< b) := Nat.lt_of_lt_of_le hc hGe
      rw [packPos_of_lt W S b c rem hcB] at hFalse
      exact hFalse
    | true =>
      rw [if_pos hBlt, List.reverse_cons, foldUnpack_append] at hFalse
      dsimp [foldUnpack] at hFalse
      have hMid := mkPackStepAt_unpack_false_sound N W S b c rem
        (foldUnpack (buildPackStepsFwd fuel' N W S (b + 1)).reverse acc) hc hrem hws hFalse
      have hN' : N ≤ (1 <<< ((b + 1) + fuel')) := by
        rw [Nat.add_right_comm b 1 fuel']
        exact hN
      exact buildPackStepsFwd_unpack_false_sound fuel' N W S (b + 1) c rem acc hc hrem hws hN' hMid

theorem buildPackStepsRevAux_eq_fwd (fuel N W S b : Nat) (acc : List PackStep) :
    (buildPackStepsRevAux fuel N W S b acc).val = (buildPackStepsFwd fuel N W S b).reverse ++ acc := by
  induction fuel generalizing b acc with
  | zero =>
    rfl
  | succ fuel' ih =>
    unfold buildPackStepsFwd
    change (selectBool (Nat.blt (Nat.shiftLeft 1 b) N)
      (buildPackStepsRevAux fuel' N W S (b + 1) (mkPackStepAt N W S b :: acc))
      (StrictBox.mk acc)).val = _
    cases hBlt : Nat.blt (Nat.shiftLeft 1 b) N with
    | false =>
      rw [if_neg (by decide)]
      rfl
    | true =>
      rw [if_pos rfl]
      change (buildPackStepsRevAux fuel' N W S (b + 1) (mkPackStepAt N W S b :: acc)).val = _
      rw [ih (b + 1) (mkPackStepAt N W S b :: acc), List.reverse_cons, List.append_assoc,
          List.singleton_append]

theorem revList_eq_reverse {α : Type} (xs : List α) :
    revList xs = xs.reverse := by
  unfold revList
  have hAux : ∀ (ys acc : List α),
      (@List.rec α (fun _ => List α → List α)
        (fun acc => acc)
        (fun h _ ih acc => ih (h :: acc))
        ys acc) = ys.reverse ++ acc := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons h rest ih =>
      intro acc
      change _ = (h :: rest).reverse ++ acc
      rw [ih (h :: acc), List.reverse_cons, List.append_assoc, List.singleton_append]
  rw [hAux xs [], List.append_nil]

theorem revListBox_eq_reverse {α : Type} (xs : List α) :
    (revListBox xs).val = xs.reverse := by
  unfold revListBox
  have hAux : ∀ (ys acc : List α),
      (@List.rec α (fun _ => List α → StrictBox (List α))
        (fun acc => StrictBox.mk acc)
        (fun h _ ih acc => ih (h :: acc))
        ys acc).val = ys.reverse ++ acc := by
    intro ys
    induction ys with
    | nil => intro acc; rfl
    | cons h rest ih =>
      intro acc
      change _ = (h :: rest).reverse ++ acc
      rw [ih (h :: acc), List.reverse_cons, List.append_assoc, List.singleton_append]
  rw [hAux xs [], List.append_nil]

theorem withPackSteps_pack_false_sound (N W S : Nat) (maskWhenOne : Bool) (c rem X : Nat)
    (hc : c < N) (hrem : rem < W) (hws : W ≤ S) (hN : N ≤ (1 <<< 20))
    (hFalse : Nat.testBit (runPackSteps (withPackSteps N W S maskWhenOne).1 X) (c * W + rem) = false) :
    Nat.testBit X (c * S + rem) = false := by
  rw [runPackSteps_eq_fold] at hFalse
  unfold withPackSteps at hFalse
  cases hBle : Nat.ble N 1 with
  | true =>
    have hN1 : N ≤ 1 := Nat.ble_eq.mp hBle
    have hc0 : c = 0 := by omega
    subst hc0
    rw [Nat.zero_mul, Nat.zero_add] at hFalse ⊢
    rw [hBle] at hFalse
    cases maskWhenOne with
    | false => exact hFalse
    | true =>
      dsimp [foldPack] at hFalse
      have hm0 : Nat.testBit (Nat.sub (Nat.shiftLeft 1 W) 1) rem = true := by
        change Nat.testBit ((1 <<< W) - 1) rem = true
        rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hrem
      exact stepPack_false_0 0 _ 0 X rem hm0 hFalse
  | false =>
    rw [hBle] at hFalse
    dsimp at hFalse
    rw [revListBox_eq_reverse, buildPackStepsRevAux_eq_fwd, List.append_nil,
        List.reverse_reverse] at hFalse
    have hN' : N ≤ (1 <<< (0 + 20)) := by rw [Nat.zero_add]; exact hN
    have hRes := buildPackStepsFwd_pack_false_sound 20 N W S 0 c rem X hc hrem hws hN' hFalse
    rwa [packPos_zero] at hRes

theorem withPackSteps_unpack_false_sound (N W S : Nat) (maskWhenOne : Bool) (c rem X : Nat)
    (hc : c < N) (hrem : rem < W) (hws : W ≤ S) (hN : N ≤ (1 <<< 20))
    (hFalse : Nat.testBit (runUnpack X (withPackSteps N W S maskWhenOne).2) (c * S + rem) = false) :
    Nat.testBit X (c * W + rem) = false := by
  rw [runUnpack_eq_fold] at hFalse
  unfold withPackSteps at hFalse
  cases hBle : Nat.ble N 1 with
  | true =>
    have hN1 : N ≤ 1 := Nat.ble_eq.mp hBle
    have hc0 : c = 0 := by omega
    subst hc0
    rw [Nat.zero_mul, Nat.zero_add] at hFalse ⊢
    rw [hBle] at hFalse
    cases maskWhenOne <;> exact hFalse
  | false =>
    rw [hBle] at hFalse
    dsimp at hFalse
    rw [buildPackStepsRevAux_eq_fwd, List.append_nil] at hFalse
    rw [← packPos_zero W S c rem] at hFalse
    have hN' : N ≤ (1 <<< (0 + 20)) := by rw [Nat.zero_add]; exact hN
    exact buildPackStepsFwd_unpack_false_sound 20 N W S 0 c rem X hc hrem hws hN' hFalse

/-!
### Recursive Coordinate Mapping (`wordK`, `wordCell`, `wordSign`, `wordBlock`)
-/

def wordK : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, q => if q % 3 = 0 then wordK m (q / 3) else wordK m (q / 3) + 1

noncomputable def wordCell : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, q =>
    if q % 3 = 0 then wordCell m (q / 3)
    else binom m (wordK m (q / 3) + 1) + wordCell m (q / 3)

def wordSign : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, q =>
    if q % 3 = 0 then wordSign m (q / 3)
    else 2 * wordSign m (q / 3) + (q % 3 - 1)

noncomputable def wordBlock (m q : Nat) : Nat :=
  wordCell m q * (1 <<< wordK m q) + wordSign m q

theorem wordK_le (m q : Nat) : wordK m q ≤ m := by
  induction m generalizing q with
  | zero => exact Nat.le_refl 0
  | succ m' ih =>
    dsimp [wordK]
    have := ih (q / 3)
    split <;> omega

theorem wordSign_lt (m q : Nat) : wordSign m q < (1 <<< wordK m q) := by
  induction m generalizing q with
  | zero =>
    dsimp [wordSign, wordK]
    decide
  | succ m' ih =>
    dsimp [wordSign, wordK]
    have hSub := ih (q / 3)
    have hMod : q % 3 < 3 := Nat.mod_lt q (by decide)
    split
    · exact hSub
    · rw [shiftLeft_one_succ]
      omega

theorem binom_zero_right (m : Nat) : binom m 0 = 1 := by
  unfold binom
  have h : Nat.blt m 0 = false := by
    cases hBlt : Nat.blt m 0 with
    | false => rfl
    | true =>
      have := Nat.blt_eq.mp hBlt
      omega
  rw [h]
  rfl

theorem binom_gt_zero (m k : Nat) (h : m < k) : binom m k = 0 := by
  unfold binom
  have hBlt : Nat.blt m k = true := Nat.blt_eq.mpr h
  rw [hBlt]

private theorem binom_pascal_check :
    (List.range 14).all (fun m =>
      (List.range 14).all (fun k =>
        binom (m + 1) (k + 1) == binom m (k + 1) + binom m k)) = true := by rfl

theorem binom_pascal_small (m k : Nat) (hm : m ≤ 13) (hk : k ≤ 13) :
    binom (m + 1) (k + 1) = binom m (k + 1) + binom m k := by
  have h1 := List.all_eq_true.mp binom_pascal_check m (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 k (List.mem_range.mpr (by omega))
  exact beq_iff_eq.mp h2

private theorem binom_mul_pow2_check :
    (List.range 14).all (fun m =>
      (List.range 14).all (fun k =>
        decide (binom m k * (1 <<< k) ≤ (1 <<< 20)))) = true := by rfl

theorem binom_mul_pow2_le (m k : Nat) (hm : m ≤ 13) (hk : k ≤ 13) :
    binom m k * (1 <<< k) ≤ (1 <<< 20) := by
  have h1 := List.all_eq_true.mp binom_mul_pow2_check m (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 k (List.mem_range.mpr (by omega))
  exact of_decide_eq_true h2

theorem wordCell_lt (m q : Nat) (hm : m ≤ 13) : wordCell m q < binom m (wordK m q) := by
  induction m generalizing q with
  | zero =>
    dsimp [wordCell, wordK]
    rw [binom_zero_right]
    decide
  | succ m' ih =>
    dsimp [wordCell, wordK]
    have hm' : m' ≤ 13 := by omega
    have hSub := ih (q / 3) hm'
    have hk' : wordK m' (q / 3) ≤ 13 := Nat.le_trans (wordK_le m' (q / 3)) hm'
    split
    · cases hk0 : wordK m' (q / 3) with
      | zero =>
        rw [hk0] at hSub
        rw [binom_zero_right] at hSub ⊢
        exact hSub
      | succ k0 =>
        rw [hk0] at hSub
        rw [binom_pascal_small m' k0 hm' (by omega)]
        omega
    · rw [binom_pascal_small m' (wordK m' (q / 3)) hm' hk']
      omega

theorem wordBlock_lt (m q : Nat) (hm : m ≤ 13) :
    wordBlock m q < binom m (wordK m q) * (1 <<< wordK m q) := by
  unfold wordBlock
  exact mul_add_lt_mul (wordCell m q) (binom m (wordK m q)) (1 <<< wordK m q) (wordSign m q)
    (wordCell_lt m q hm) (wordSign_lt m q)

theorem wordBlock_succ (m q : Nat) :
    wordBlock (m + 1) q =
      let k' := wordK m (q / 3)
      let c' := wordBlock m (q / 3)
      if q % 3 = 0 then c'
      else binom m (k' + 1) * (1 <<< (k' + 1)) + 2 * c' + (q % 3 - 1) := by
  unfold wordBlock
  dsimp [wordCell, wordSign, wordK]
  split
  · rfl
  · rw [Nat.add_mul, shiftLeft_one_succ (wordK m (q / 3))]
    have hMul : wordCell m (q / 3) * (2 * (1 <<< wordK m (q / 3))) =
        2 * (wordCell m (q / 3) * (1 <<< wordK m (q / 3))) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (wordCell m (q / 3)) 2, Nat.mul_assoc]
    omega

/-- Inductive relation stating that `X` and `X'` differ only at ternary digit `e`,
    where one has digit `1` and the other has digit `2`. -/
def FlipDigitAt : Nat → Nat → Nat → Prop
  | 0, X, X' => X / 3 = X' / 3 ∧ ((X % 3 = 1 ∧ X' % 3 = 2) ∨ (X % 3 = 2 ∧ X' % 3 = 1))
  | e + 1, X, X' => X % 3 = X' % 3 ∧ FlipDigitAt e (X / 3) (X' / 3)

theorem flipDigitAt_symm (e X X' : Nat) (h : FlipDigitAt e X X') : FlipDigitAt e X' X := by
  induction e generalizing X X' with
  | zero =>
    rcases h with ⟨hDiv, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨hDiv.symm, Or.inr ⟨h2, h1⟩⟩
    · exact ⟨hDiv.symm, Or.inl ⟨h2, h1⟩⟩
  | succ e' ih =>
    exact ⟨h.1.symm, ih (X / 3) (X' / 3) h.2⟩

theorem wordK_eq_of_flipDigitAt (m e X X' : Nat) (h : FlipDigitAt e X X') :
    wordK m X = wordK m X' := by
  induction m generalizing e X X' with
  | zero => rfl
  | succ m' ih =>
    dsimp [wordK]
    cases e with
    | zero =>
      rcases h with ⟨hDiv, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> simp [hDiv, h1, h2]
    | succ e' =>
      rcases h with ⟨hMod, hSub⟩
      rw [hMod, ih e' (X / 3) (X' / 3) hSub]

theorem wordCell_eq_of_flipDigitAt (m e X X' : Nat) (h : FlipDigitAt e X X') :
    wordCell m X = wordCell m X' := by
  induction m generalizing e X X' with
  | zero => rfl
  | succ m' ih =>
    dsimp [wordCell]
    cases e with
    | zero =>
      rcases h with ⟨hDiv, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> simp [hDiv, h1, h2]
    | succ e' =>
      rcases h with ⟨hMod, hSub⟩
      rw [hMod, ih e' (X / 3) (X' / 3) hSub, wordK_eq_of_flipDigitAt m' e' (X / 3) (X' / 3) hSub]

theorem testBit_two_mul_add_zero (s a : Nat) :
    Nat.testBit (2 * s) a = (if a = 0 then false else Nat.testBit s (a - 1)) := by
  cases a with
  | zero => simp [Nat.testBit_zero]
  | succ a' =>
    change Nat.testBit (s <<< 1) (a' + 1) = if a' + 1 = 0 then false else Nat.testBit s a'
    rw [if_neg (by omega), Nat.testBit_shiftLeft]
    simp

theorem testBit_two_mul_add_one (s a : Nat) :
    Nat.testBit (2 * s + 1) a = (if a = 0 then true else Nat.testBit s (a - 1)) := by
  cases a with
  | zero =>
    simp [Nat.testBit_zero]
  | succ a' =>
    rw [if_neg (by omega), Nat.testBit_succ]
    have hDiv : (2 * s + 1) / 2 = s := by omega
    rw [hDiv, Nat.add_sub_cancel]

theorem wordSign_of_flipDigitAt :
    ∀ (e m X X' : Nat), e < m → FlipDigitAt e X X' →
      let a := wordK e X
      (Nat.testBit (wordSign m X) a = false ∧
       Nat.testBit (wordSign m X') a = true ∧
       wordSign m X' = wordSign m X + (1 <<< a)) ∨
      (Nat.testBit (wordSign m X) a = true ∧
       Nat.testBit (wordSign m X') a = false ∧
       wordSign m X = wordSign m X' + (1 <<< a))
  | 0, m' + 1, X, X', _, h => by
    dsimp [wordK, wordSign]
    change (Nat.testBit (if X % 3 = 0 then wordSign m' (X / 3) else 2 * wordSign m' (X / 3) + (X % 3 - 1)) 0 = false ∧
            Nat.testBit (if X' % 3 = 0 then wordSign m' (X' / 3) else 2 * wordSign m' (X' / 3) + (X' % 3 - 1)) 0 = true ∧
            (if X' % 3 = 0 then wordSign m' (X' / 3) else 2 * wordSign m' (X' / 3) + (X' % 3 - 1)) =
              (if X % 3 = 0 then wordSign m' (X / 3) else 2 * wordSign m' (X / 3) + (X % 3 - 1)) + 1) ∨
           (Nat.testBit (if X % 3 = 0 then wordSign m' (X / 3) else 2 * wordSign m' (X / 3) + (X % 3 - 1)) 0 = true ∧
            Nat.testBit (if X' % 3 = 0 then wordSign m' (X' / 3) else 2 * wordSign m' (X' / 3) + (X' % 3 - 1)) 0 = false ∧
            (if X % 3 = 0 then wordSign m' (X / 3) else 2 * wordSign m' (X / 3) + (X % 3 - 1)) =
              (if X' % 3 = 0 then wordSign m' (X' / 3) else 2 * wordSign m' (X' / 3) + (X' % 3 - 1)) + 1)
    rcases h with ⟨hDiv, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · left
      rw [h1, h2, hDiv]
      simp [testBit_two_mul_add_one]
    · right
      rw [h1, h2, hDiv]
      simp [testBit_two_mul_add_one]
  | e' + 1, m' + 1, X, X', hlt, h => by
    rcases h with ⟨hMod, hSub⟩
    have hlt' : e' < m' := by omega
    have ih := wordSign_of_flipDigitAt e' m' (X / 3) (X' / 3) hlt' hSub
    dsimp [wordK, wordSign] at ih ⊢
    rw [hMod]
    by_cases h0 : X' % 3 = 0
    · rw [if_pos h0, if_pos h0, if_pos h0]
      exact ih
    · rw [if_neg h0, if_neg h0, if_neg h0]
      have hModLt : X' % 3 < 3 := Nat.mod_lt X' (by decide)
      have hSub01 : X' % 3 - 1 = 0 ∨ X' % 3 - 1 = 1 := by omega
      have hShift : (1 <<< (wordK e' (X / 3) + 1)) = 2 * (1 <<< wordK e' (X / 3)) :=
        shiftLeft_one_succ (wordK e' (X / 3))
      rcases ih with ⟨hbX, hbX', hEq⟩ | ⟨hbX, hbX', hEq⟩
      · left
        rcases hSub01 with hd | hd <;>
        · rw [hd]
          simp [testBit_two_mul_add_zero, testBit_two_mul_add_one, hbX, hbX']
          omega
      · right
        rcases hSub01 with hd | hd <;>
        · rw [hd]
          simp [testBit_two_mul_add_zero, testBit_two_mul_add_one, hbX, hbX']
          omega

theorem testBit_wordSign_ne_of_flipDigitAt :
    ∀ (e m X X' a : Nat), e < m → FlipDigitAt e X X' → a ≠ wordK e X →
      Nat.testBit (wordSign m X') a = Nat.testBit (wordSign m X) a
  | 0, m' + 1, X, X', a, _, h, hne => by
    dsimp [wordK] at hne
    dsimp [wordSign]
    rcases h with ⟨hDiv, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · rw [h1, h2, hDiv, if_neg (by decide), if_neg (by decide)]
      simp [testBit_two_mul_add_zero, testBit_two_mul_add_one, hne]
    · rw [h1, h2, hDiv, if_neg (by decide), if_neg (by decide)]
      simp [testBit_two_mul_add_zero, testBit_two_mul_add_one, hne]
  | e' + 1, m' + 1, X, X', a, hlt, h, hne => by
    rcases h with ⟨hMod, hSub⟩
    have hlt' : e' < m' := by omega
    dsimp [wordK] at hne
    dsimp [wordSign]
    rw [hMod] at hne ⊢
    by_cases h0 : X' % 3 = 0
    · rw [if_pos h0] at hne
      rw [if_pos h0, if_pos h0]
      exact testBit_wordSign_ne_of_flipDigitAt e' m' (X / 3) (X' / 3) a hlt' hSub hne
    · rw [if_neg h0] at hne
      rw [if_neg h0, if_neg h0]
      have hModLt : X' % 3 < 3 := Nat.mod_lt X' (by decide)
      have hSub01 : X' % 3 - 1 = 0 ∨ X' % 3 - 1 = 1 := by omega
      cases a with
      | zero =>
        rcases hSub01 with hd | hd <;>
        · rw [hd]
          simp [testBit_two_mul_add_one]
      | succ a' =>
        have hne' : a' ≠ wordK e' (X / 3) := by omega
        have ih := testBit_wordSign_ne_of_flipDigitAt e' m' (X / 3) (X' / 3) a' hlt' hSub hne'
        rcases hSub01 with hd | hd <;>
        · rw [hd]
          simp [testBit_two_mul_add_zero, testBit_two_mul_add_one, ih]

theorem wordK_succ_right (e q : Nat) :
    wordK (e + 1) q = wordK e q + (if (q / 3 ^ e) % 3 = 0 then 0 else 1) := by
  induction e generalizing q with
  | zero =>
    dsimp [wordK]
    rw [Nat.div_one]
    split <;> omega
  | succ e' ih =>
    change (if q % 3 = 0 then wordK (e' + 1) (q / 3) else wordK (e' + 1) (q / 3) + 1) =
      (if q % 3 = 0 then wordK e' (q / 3) else wordK e' (q / 3) + 1) +
        (if (q / 3 ^ (e' + 1)) % 3 = 0 then 0 else 1)
    rw [ih (q / 3), Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    split <;> split <;> omega

theorem wordK_mono {e1 e2 : Nat} (h : e1 ≤ e2) (q : Nat) :
    wordK e1 q ≤ wordK e2 q := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    rw [wordK_succ_right]
    omega

theorem wordK_strict_mono_of_active {e1 e2 : Nat} (q : Nat)
    (h1 : (q / 3 ^ e1) % 3 ≠ 0) (hlt : e1 < e2) :
    wordK e1 q < wordK e2 q := by
  have hSucc : wordK (e1 + 1) q = wordK e1 q + 1 := by
    rw [wordK_succ_right, if_neg h1]
  have hLe : wordK (e1 + 1) q ≤ wordK e2 q := wordK_mono hlt q
  omega

theorem testBit_cell_mul_pow2_add_sign :
    ∀ (a k cell sign : Nat), a < k →
      Nat.testBit (cell * (1 <<< k) + sign) a = Nat.testBit sign a
  | 0, k' + 1, cell, sign, _ => by
    rw [shiftLeft_one_succ, Nat.testBit_zero, Nat.testBit_zero]
    have hMul : cell * (2 * (1 <<< k')) = (cell * (1 <<< k')) * 2 := by
      rw [← Nat.mul_assoc, Nat.mul_comm cell 2, Nat.mul_assoc, Nat.mul_comm 2]
    have hMod : (cell * (2 * (1 <<< k')) + sign) % 2 = sign % 2 := by
      rw [hMul, Nat.add_comm, Nat.add_mul_mod_self_right]
    rw [hMod]
  | a' + 1, k' + 1, cell, sign, ha => by
    rw [shiftLeft_one_succ, Nat.testBit_succ, Nat.testBit_succ]
    have hMul : cell * (2 * (1 <<< k')) = (cell * (1 <<< k')) * 2 := by
      rw [← Nat.mul_assoc, Nat.mul_comm cell 2, Nat.mul_assoc, Nat.mul_comm 2]
    have hDiv : (cell * (2 * (1 <<< k')) + sign) / 2 = cell * (1 <<< k') + sign / 2 := by
      rw [hMul, Nat.add_comm, Nat.add_mul_div_right _ _ (by decide), Nat.add_comm]
    rw [hDiv]
    exact testBit_cell_mul_pow2_add_sign a' k' cell (sign / 2) (by omega)

theorem testBit_wordBlock_eq_wordSign (m X a : Nat) (ha : a < wordK m X) :
    Nat.testBit (wordBlock m X) a = Nat.testBit (wordSign m X) a :=
  testBit_cell_mul_pow2_add_sign a (wordK m X) (wordCell m X) (wordSign m X) ha

theorem active_of_flipDigitAt (e X X' : Nat) (h : FlipDigitAt e X X') :
    (X / 3 ^ e) % 3 ≠ 0 := by
  induction e generalizing X X' with
  | zero =>
    rw [Nat.pow_zero, Nat.div_one]
    rcases h with ⟨_, ⟨h1, _⟩ | ⟨h1, _⟩⟩ <;> omega
  | succ e' ih =>
    rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    exact ih (X / 3) (X' / 3) h.2

theorem wordBlock_of_flipDigitAt (e m X X' : Nat) (hlt : e < m) (h : FlipDigitAt e X X') :
    let a := wordK e X
    let j := wordBlock m X
    let j' := wordBlock m X'
    (Nat.testBit j a = false ∧ Nat.testBit j' a = true ∧ j' = j + (1 <<< a)) ∨
    (Nat.testBit j a = true ∧ Nat.testBit j' a = false ∧ j = j' + (1 <<< a)) := by
  dsimp
  have hK := wordK_eq_of_flipDigitAt m e X X' h
  have hC := wordCell_eq_of_flipDigitAt m e X X' h
  have ha_lt : wordK e X < wordK m X :=
    wordK_strict_mono_of_active X (active_of_flipDigitAt e X X' h) hlt
  have ha_lt' : wordK e X < wordK m X' := by rw [← hK]; exact ha_lt
  rw [testBit_wordBlock_eq_wordSign m X (wordK e X) ha_lt,
      testBit_wordBlock_eq_wordSign m X' (wordK e X) ha_lt']
  unfold wordBlock
  rw [← hC, ← hK]
  rcases wordSign_of_flipDigitAt e m X X' hlt h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · left; refine ⟨h1, h2, by omega⟩
  · right; refine ⟨h1, h2, by omega⟩

theorem testBit_wordBlock_ne_of_flipDigitAt (e m X X' a : Nat)
    (hlt : e < m) (h : FlipDigitAt e X X') (ha : a < wordK m X) (hne : a ≠ wordK e X) :
    Nat.testBit (wordBlock m X') a = Nat.testBit (wordBlock m X) a := by
  have hK := wordK_eq_of_flipDigitAt m e X X' h
  have ha' : a < wordK m X' := by rw [← hK]; exact ha
  rw [testBit_wordBlock_eq_wordSign m X' a ha',
      testBit_wordBlock_eq_wordSign m X a ha]
  exact testBit_wordSign_ne_of_flipDigitAt e m X X' a hlt h hne

/-!
### Level-`m` Zipper Soundness (`packLevelRev` and `unpackLevelRev`)
-/

instance : Inhabited PackCellSpec where
  default := PackCellSpec.mk 0 0 [] []

instance : Inhabited UnpackCellSpec where
  default := UnpackCellSpec.mk 0 0 [] []

noncomputable def packLevelFwd : List PackCellSpec → List Nat → Nat → List Nat
  | [], _, prevS12 => [prevS12]
  | PackCellSpec.mk P lowBits steps0 steps12 :: restSpecs, [], prevS12 =>
    [prevS12]
  | PackCellSpec.mk P lowBits steps0 steps12 :: restSpecs, dk :: restD, prevS12 =>
    let s0_k := runPackSteps steps0 dk
    let s12_k := runPackSteps steps12 (Nat.shiftRight dk P)
    let nextDk := Nat.lor s0_k (Nat.shiftLeft prevS12 lowBits)
    nextDk :: packLevelFwd restSpecs restD s12_k

noncomputable def unpackLevelFwd : List UnpackCellSpec → Nat → List Nat → List Nat
  | [], _, _ => []
  | UnpackCellSpec.mk P nextLowBits revSteps0 revSteps12 :: restSpecs, dk, [] =>
    [runUnpack dk revSteps0]
  | UnpackCellSpec.mk P nextLowBits revSteps0 revSteps12 :: restSpecs, dk, dkNext :: restD' =>
    let s0_k := runUnpack dk revSteps0
    let s12_k := runUnpack (Nat.shiftRight dkNext nextLowBits) revSteps12
    let prevDk := Nat.lor s0_k (Nat.shiftLeft s12_k P)
    prevDk :: unpackLevelFwd restSpecs dkNext restD'

theorem revList_packLevelRev (specs : List PackCellSpec) (D : List Nat) (prevS12 : Nat) (acc : List Nat) :
    revList (packLevelRev specs D prevS12 acc) = acc.reverse ++ packLevelFwd specs D prevS12 := by
  rw [revList_eq_reverse]
  induction specs generalizing D prevS12 acc with
  | nil =>
    change (prevS12 :: acc).reverse = acc.reverse ++ [prevS12]
    exact List.reverse_cons
  | cons spec restSpecs ih =>
    cases spec with
    | mk P lowBits steps0 steps12 =>
      cases D with
      | nil =>
        change (prevS12 :: acc).reverse = acc.reverse ++ [prevS12]
        exact List.reverse_cons
      | cons dk restD =>
        dsimp [packLevelFwd]
        change (packLevelRev restSpecs restD (runPackSteps steps12 (Nat.shiftRight dk P))
          (Nat.lor (runPackSteps steps0 dk) (Nat.shiftLeft prevS12 lowBits) :: acc)).reverse = _
        rw [ih restD _ _, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem revList_unpackLevelRev (specs : List UnpackCellSpec) (dk : Nat) (restD acc : List Nat) :
    revList (unpackLevelRev specs dk restD acc) = acc.reverse ++ unpackLevelFwd specs dk restD := by
  rw [revList_eq_reverse]
  induction specs generalizing dk restD acc with
  | nil =>
    change acc.reverse = acc.reverse ++ []
    rw [List.append_nil]
  | cons spec restSpecs ih =>
    cases spec with
    | mk P nextLowBits revSteps0 revSteps12 =>
      cases restD with
      | nil =>
        change (runUnpack dk revSteps0 :: acc).reverse = acc.reverse ++ [runUnpack dk revSteps0]
        exact List.reverse_cons
      | cons dkNext restD' =>
        dsimp [unpackLevelFwd]
        change (unpackLevelRev restSpecs dkNext restD'
          (Nat.lor (runUnpack dk revSteps0)
            (Nat.shiftLeft (runUnpack (Nat.shiftRight dkNext nextLowBits) revSteps12) P) :: acc)).reverse = _
        rw [ih dkNext restD' _, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem packLevelFwd_length (specs : List PackCellSpec) (D : List Nat) (prevS12 : Nat)
    (hLen : specs.length ≤ D.length) :
    (packLevelFwd specs D prevS12).length = specs.length + 1 := by
  induction specs generalizing D prevS12 with
  | nil => rfl
  | cons spec restSpecs ih =>
    cases spec with
    | mk P lowBits steps0 steps12 =>
      cases D with
      | nil =>
        dsimp at hLen
        omega
      | cons dk restD =>
        dsimp [packLevelFwd]
        rw [ih restD _ (by dsimp at hLen; omega)]

theorem unpackLevelFwd_length (specs : List UnpackCellSpec) (dk : Nat) (restD : List Nat)
    (hLen : specs.length ≤ restD.length + 1) :
    (unpackLevelFwd specs dk restD).length = specs.length := by
  induction specs generalizing dk restD with
  | nil => rfl
  | cons spec restSpecs ih =>
    cases spec with
    | mk P nextLowBits revSteps0 revSteps12 =>
      cases restD with
      | nil =>
        cases restSpecs with
        | nil => rfl
        | cons _ _ =>
          dsimp at hLen
          omega
      | cons dkNext restD' =>
        dsimp [unpackLevelFwd]
        rw [ih dkNext restD' (by dsimp at hLen; omega)]

theorem list_getD_zero {α : Type} (x : α) (xs : List α) (d : α) :
    (x :: xs).getD 0 d = x := rfl

theorem list_getD_succ {α : Type} (x : α) (xs : List α) (k : Nat) (d : α) :
    (x :: xs).getD (k + 1) d = xs.getD k d := rfl

theorem packLevelFwd_getD_s0 :
    ∀ (specs : List PackCellSpec) (D : List Nat) (prevS12 k P lowBits : Nat) (steps0 steps12 : List PackStep) (j : Nat),
      k < specs.length → specs.length ≤ D.length →
      specs.getD k default = PackCellSpec.mk P lowBits steps0 steps12 →
      Nat.testBit ((packLevelFwd specs D prevS12).getD k 0) j = false →
      Nat.testBit (runPackSteps steps0 (D.getD k 0)) j = false
  | PackCellSpec.mk P' lb' st0' st12' :: restSpecs, dk :: restD, prevS12, 0, P, lowBits, steps0, steps12, j, _, _, hSpec, hFalse => by
    rw [list_getD_zero] at hSpec
    injection hSpec with hP hLb hSt0 hSt12
    subst hP; subst hLb; subst hSt0; subst hSt12
    dsimp [packLevelFwd] at hFalse
    rw [list_getD_zero] at hFalse ⊢
    rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
    exact hFalse.1
  | PackCellSpec.mk P' lb' st0' st12' :: restSpecs, dk :: restD, prevS12, k' + 1, P, lowBits, steps0, steps12, j, hk, hLen, hSpec, hFalse => by
    dsimp [packLevelFwd] at hFalse
    rw [list_getD_succ] at hSpec hFalse ⊢
    exact packLevelFwd_getD_s0 restSpecs restD _ k' P lowBits steps0 steps12 j
      (by dsimp at hk; omega) (by dsimp at hLen; omega) hSpec hFalse

def specLowBits (s : PackCellSpec) : Nat :=
  match s with
  | PackCellSpec.mk _ lb _ _ => lb

theorem packLevelFwd_getD_zero_prev (specs : List PackCellSpec) (D : List Nat) (prevS12 j : Nat)
    (hLen : specs.length ≤ D.length)
    (nextLow : Nat)
    (hNextLow : nextLow = if 0 < specs.length then specLowBits (specs.getD 0 default) else 0)
    (hLe : nextLow ≤ j)
    (hFalse : Nat.testBit ((packLevelFwd specs D prevS12).getD 0 0) j = false) :
    Nat.testBit prevS12 (j - nextLow) = false := by
  subst hNextLow
  cases specs with
  | nil =>
    dsimp [packLevelFwd] at hFalse ⊢
    rw [list_getD_zero] at hFalse
    exact hFalse
  | cons spec restSpecs =>
    cases spec with
    | mk P lb st0 st12 =>
      cases D with
      | nil => dsimp at hLen; omega
      | cons dk restD =>
        dsimp [packLevelFwd, specLowBits] at hLe hFalse ⊢
        rw [list_getD_zero] at hLe hFalse ⊢
        dsimp [specLowBits] at hLe ⊢
        rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
        have hShift := hFalse.2
        rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and] at hShift
        exact hShift

theorem packLevelFwd_getD_s12 :
    ∀ (specs : List PackCellSpec) (D : List Nat) (prevS12 k P lowBits nextLow : Nat) (steps0 steps12 : List PackStep) (j : Nat),
      k < specs.length → specs.length ≤ D.length →
      specs.getD k default = PackCellSpec.mk P lowBits steps0 steps12 →
      nextLow = (if k + 1 < specs.length then specLowBits (specs.getD (k + 1) default) else 0) →
      nextLow ≤ j →
      Nat.testBit ((packLevelFwd specs D prevS12).getD (k + 1) 0) j = false →
      Nat.testBit (runPackSteps steps12 (Nat.shiftRight (D.getD k 0) P)) (j - nextLow) = false
  | PackCellSpec.mk P' lb' st0' st12' :: restSpecs, dk :: restD, prevS12, 0, P, lowBits, nextLow, steps0, steps12, j, hk, hLen, hSpec, hNext, hLe, hFalse => by
    rw [list_getD_zero] at hSpec
    injection hSpec with hP hLb hSt0 hSt12
    subst hP; subst hLb; subst hSt0; subst hSt12
    dsimp [packLevelFwd] at hFalse
    rw [list_getD_succ] at hFalse
    rw [list_getD_zero]
    have hNext' : nextLow = if 0 < restSpecs.length then specLowBits (restSpecs.getD 0 default) else 0 := by
      rw [hNext, list_getD_succ]
      by_cases h0 : 0 < restSpecs.length
      · rw [if_pos (by dsimp; omega), if_pos h0]
      · rw [if_neg (by dsimp; omega), if_neg h0]
    exact packLevelFwd_getD_zero_prev restSpecs restD
      (runPackSteps st12' (Nat.shiftRight dk P')) j (by dsimp at hLen; omega) nextLow hNext' hLe hFalse
  | PackCellSpec.mk P' lb' st0' st12' :: restSpecs, dk :: restD, prevS12, k' + 1, P, lowBits, nextLow, steps0, steps12, j, hk, hLen, hSpec, hNext, hLe, hFalse => by
    dsimp [packLevelFwd] at hFalse
    rw [list_getD_succ] at hSpec hFalse ⊢
    have hNext' : nextLow = if k' + 1 < restSpecs.length then specLowBits (restSpecs.getD (k' + 1) default) else 0 := by
      rw [hNext, list_getD_succ]
      by_cases h0 : k' + 1 < restSpecs.length
      · rw [if_pos (by dsimp; omega), if_pos h0]
      · rw [if_neg (by dsimp; omega), if_neg h0]
    exact packLevelFwd_getD_s12 restSpecs restD _ k' P lowBits nextLow steps0 steps12 j
      (by dsimp at hk; omega) (by dsimp at hLen; omega) hSpec hNext' hLe hFalse

theorem unpackLevelFwd_getD_s0 :
    ∀ (specs : List UnpackCellSpec) (d0 : Nat) (restD : List Nat) (k P nextLowBits : Nat) (revSteps0 revSteps12 : List PackStep) (j : Nat),
      k < specs.length → specs.length ≤ restD.length + 1 →
      specs.getD k default = UnpackCellSpec.mk P nextLowBits revSteps0 revSteps12 →
      Nat.testBit ((unpackLevelFwd specs d0 restD).getD k 0) j = false →
      Nat.testBit (runUnpack ((d0 :: restD).getD k 0) revSteps0) j = false
  | UnpackCellSpec.mk P' nlb' rev0' rev12' :: restSpecs, d0, restD, 0, P, nextLowBits, revSteps0, revSteps12, j, _, _, hSpec, hFalse => by
    rw [list_getD_zero] at hSpec
    injection hSpec with hP hNlb hRev0 hRev12
    subst hP; subst hNlb; subst hRev0; subst hRev12
    rw [list_getD_zero]
    cases restD with
    | nil =>
      dsimp [unpackLevelFwd] at hFalse
      rw [list_getD_zero] at hFalse
      exact hFalse
    | cons dkNext restD' =>
      dsimp [unpackLevelFwd] at hFalse
      rw [list_getD_zero, testBit_lor, Bool.or_eq_false_iff] at hFalse
      exact hFalse.1
  | UnpackCellSpec.mk P' nlb' rev0' rev12' :: restSpecs, d0, [], k' + 1, P, nextLowBits, revSteps0, revSteps12, j, hk, hLen, _, _ => by
    dsimp at hk hLen
    omega
  | UnpackCellSpec.mk P' nlb' rev0' rev12' :: restSpecs, d0, dkNext :: restD', k' + 1, P, nextLowBits, revSteps0, revSteps12, j, hk, hLen, hSpec, hFalse => by
    dsimp [unpackLevelFwd] at hFalse
    rw [list_getD_succ] at hSpec hFalse ⊢
    exact unpackLevelFwd_getD_s0 restSpecs dkNext restD' k' P nextLowBits revSteps0 revSteps12 j
      (by dsimp at hk; omega) (by dsimp at hLen; omega) hSpec hFalse

theorem unpackLevelFwd_getD_s12 :
    ∀ (specs : List UnpackCellSpec) (d0 : Nat) (restD : List Nat) (k P nextLowBits : Nat) (revSteps0 revSteps12 : List PackStep) (j : Nat),
      k < specs.length → k < restD.length →
      specs.getD k default = UnpackCellSpec.mk P nextLowBits revSteps0 revSteps12 →
      P ≤ j →
      Nat.testBit ((unpackLevelFwd specs d0 restD).getD k 0) j = false →
      Nat.testBit (runUnpack (Nat.shiftRight ((d0 :: restD).getD (k + 1) 0) nextLowBits) revSteps12) (j - P) = false
  | UnpackCellSpec.mk P' nlb' rev0' rev12' :: restSpecs, d0, dkNext :: restD', 0, P, nextLowBits, revSteps0, revSteps12, j, _, _, hSpec, hLe, hFalse => by
    rw [list_getD_zero] at hSpec
    injection hSpec with hP hNlb hRev0 hRev12
    subst hP; subst hNlb; subst hRev0; subst hRev12
    dsimp [unpackLevelFwd] at hFalse
    rw [list_getD_zero, testBit_lor, Bool.or_eq_false_iff] at hFalse
    rw [list_getD_succ, list_getD_zero]
    have hShift := hFalse.2
    rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and] at hShift
    exact hShift
  | UnpackCellSpec.mk P' nlb' rev0' rev12' :: restSpecs, d0, dkNext :: restD', k' + 1, P, nextLowBits, revSteps0, revSteps12, j, hk, hkD, hSpec, hLe, hFalse => by
    dsimp [unpackLevelFwd] at hFalse
    rw [list_getD_succ] at hSpec hFalse ⊢
    exact unpackLevelFwd_getD_s12 restSpecs dkNext restD' k' P nextLowBits revSteps0 revSteps12 j
      (by dsimp at hk; omega) (by dsimp at hkD; omega) hSpec hLe hFalse

noncomputable def mkPackCellSpecAt (m P k : Nat) : PackCellSpec :=
  let N := Nat.mul (binom m k) (Nat.shiftLeft 1 k)
  let lowBits := Nat.mul N P
  let st0 := (withPackSteps N P (Nat.mul 3 P) true).1
  let st12 := (withPackSteps N (Nat.mul 2 P) (Nat.mul 3 P) false).1
  PackCellSpec.mk P lowBits st0 st12

noncomputable def mkUnpackCellSpecAt (m P k : Nat) : UnpackCellSpec :=
  let N := Nat.mul (binom m k) (Nat.shiftLeft 1 k)
  let nextLowBits :=
    selectBool (Nat.ble (Nat.succ k) m)
      (Nat.mul (Nat.mul (binom m (Nat.succ k)) (Nat.shiftLeft 1 (Nat.succ k))) P)
      0
  let revSt0 := (withPackSteps N P (Nat.mul 3 P) true).2
  let revSt12 := (withPackSteps N (Nat.mul 2 P) (Nat.mul 3 P) false).2
  let isM1K1 := and (Nat.beq m 1) (Nat.beq k 1)
  let rev0 :=
    selectBool isM1K1 [PackStep.mk 0 (Nat.sub (Nat.shiftLeft 1 P) 1) 0] revSt0
  let rev12 :=
    selectBool isM1K1 [PackStep.mk 0 (Nat.sub (Nat.shiftLeft 1 (Nat.mul 2 P)) 1) 0] revSt12
  UnpackCellSpec.mk P nextLowBits rev0 rev12

noncomputable def packSpecsPrefix (m P : Nat) : Nat → List PackCellSpec
  | 0 => []
  | c + 1 => packSpecsPrefix m P c ++ [mkPackCellSpecAt m P c]

noncomputable def unpackSpecsPrefix (m P : Nat) : Nat → List UnpackCellSpec
  | 0 => []
  | c + 1 => unpackSpecsPrefix m P c ++ [mkUnpackCellSpecAt m P c]

theorem list_getD_append_left {α : Type} (xs ys : List α) (k : Nat) (d : α) (hk : k < xs.length) :
    (xs ++ ys).getD k d = xs.getD k d := by
  induction xs generalizing k with
  | nil => dsimp at hk; omega
  | cons x rest ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      dsimp [List.getD]
      exact ih k' (by dsimp at hk; omega)

theorem list_getD_append_singleton_self {α : Type} (xs : List α) (y d : α) :
    (xs ++ [y]).getD xs.length d = y := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    dsimp [List.getD]
    exact ih

theorem packSpecsPrefix_length (m P c : Nat) :
    (packSpecsPrefix m P c).length = c := by
  induction c with
  | zero => rfl
  | succ c' ih =>
    dsimp [packSpecsPrefix]
    rw [List.length_append, ih]
    rfl

theorem unpackSpecsPrefix_length (m P c : Nat) :
    (unpackSpecsPrefix m P c).length = c := by
  induction c with
  | zero => rfl
  | succ c' ih =>
    dsimp [unpackSpecsPrefix]
    rw [List.length_append, ih]
    rfl

theorem packSpecsPrefix_getD (m P c k : Nat) (hk : k < c) :
    (packSpecsPrefix m P c).getD k default = mkPackCellSpecAt m P k := by
  induction c with
  | zero => omega
  | succ c' ih =>
    dsimp [packSpecsPrefix]
    by_cases hlt : k < c'
    · rw [list_getD_append_left _ _ k default (by rw [packSpecsPrefix_length]; exact hlt)]
      exact ih hlt
    · have hEq : k = c' := by omega
      subst hEq
      have h := list_getD_append_singleton_self (packSpecsPrefix m P k) (mkPackCellSpecAt m P k) default
      rwa [packSpecsPrefix_length] at h

theorem unpackSpecsPrefix_getD (m P c k : Nat) (hk : k < c) :
    (unpackSpecsPrefix m P c).getD k default = mkUnpackCellSpecAt m P k := by
  induction c with
  | zero => omega
  | succ c' ih =>
    dsimp [unpackSpecsPrefix]
    by_cases hlt : k < c'
    · rw [list_getD_append_left _ _ k default (by rw [unpackSpecsPrefix_length]; exact hlt)]
      exact ih hlt
    · have hEq : k = c' := by omega
      subst hEq
      have h := list_getD_append_singleton_self (unpackSpecsPrefix m P k) (mkUnpackCellSpecAt m P k) default
      rwa [unpackSpecsPrefix_length] at h

theorem buildLevelSpecs_eq (m P : Nat) :
    buildLevelSpecs m P = (packSpecsPrefix m P (m + 1), unpackSpecsPrefix m P (m + 1)) := by
  unfold buildLevelSpecs
  have hAux : ∀ (c : Nat) (pAcc : List PackCellSpec) (uAcc : List UnpackCellSpec),
      (@Nat.rec (fun _ => List PackCellSpec → List UnpackCellSpec → List PackCellSpec × List UnpackCellSpec)
        (fun pAcc uAcc => (pAcc, uAcc))
        (fun kIdx ih pAcc uAcc =>
          let N := Nat.mul (binom m kIdx) (Nat.shiftLeft 1 kIdx)
          let lowBits := Nat.mul N P
          let nextLowBits :=
            selectBool (Nat.ble (Nat.succ kIdx) m)
              (Nat.mul (Nat.mul (binom m (Nat.succ kIdx)) (Nat.shiftLeft 1 (Nat.succ kIdx))) P)
              0
          @Prod.rec _ _ (fun _ => _)
            (fun st0 revSt0 =>
              @Prod.rec _ _ (fun _ => _)
                (fun st12 revSt12 =>
                  let isM1K1 := and (Nat.beq m 1) (Nat.beq kIdx 1)
                  let rev0 :=
                    selectBool isM1K1
                      (let m0 := Nat.sub (Nat.shiftLeft 1 P) 1
                       [PackStep.mk 0 m0 0])
                      revSt0
                  let rev12 :=
                    selectBool isM1K1
                      (let m12 := Nat.sub (Nat.shiftLeft 1 (Nat.mul 2 P)) 1
                       [PackStep.mk 0 m12 0])
                      revSt12
                  ih (PackCellSpec.mk P lowBits st0 st12 :: pAcc)
                     (UnpackCellSpec.mk P nextLowBits rev0 rev12 :: uAcc))
                (withPackSteps N (Nat.mul 2 P) (Nat.mul 3 P) false))
            (withPackSteps N P (Nat.mul 3 P) true))
        c pAcc uAcc) =
      (packSpecsPrefix m P c ++ pAcc, unpackSpecsPrefix m P c ++ uAcc) := by
    intro c
    induction c with
    | zero => intro pAcc uAcc; rfl
    | succ c' ih =>
      intro pAcc uAcc
      change _ = (packSpecsPrefix m P c' ++ [mkPackCellSpecAt m P c'] ++ pAcc,
                  unpackSpecsPrefix m P c' ++ [mkUnpackCellSpecAt m P c'] ++ uAcc)
      rw [List.append_assoc, List.singleton_append,
          List.append_assoc, List.singleton_append]
      exact ih (mkPackCellSpecAt m P c' :: pAcc) (mkUnpackCellSpecAt m P c' :: uAcc)
  rw [hAux (m + 1) [] [], List.append_nil, List.append_nil]

theorem nextLow_eq_binom (m P k' : Nat) (hk' : k' ≤ m) :
    (if k' + 1 < (packSpecsPrefix m P (m + 1)).length then
      specLowBits ((packSpecsPrefix m P (m + 1)).getD (k' + 1) default)
     else 0) =
    binom m (k' + 1) * (1 <<< (k' + 1)) * P := by
  rw [packSpecsPrefix_length]
  by_cases hlt : k' + 1 < m + 1
  · rw [if_pos hlt, packSpecsPrefix_getD m P (m + 1) (k' + 1) hlt]
    rfl
  · rw [if_neg hlt]
    have hEq : k' = m := by omega
    subst hEq
    rw [binom_gt_zero k' (k' + 1) (by omega), Nat.zero_mul, Nat.zero_mul]

theorem unpack_nextLowBits_eq_binom (m P k' : Nat) (hk' : k' ≤ m) :
    selectBool (Nat.ble (Nat.succ k') m)
      (Nat.mul (Nat.mul (binom m (Nat.succ k')) (Nat.shiftLeft 1 (Nat.succ k'))) P)
      0 =
    binom m (k' + 1) * (1 <<< (k' + 1)) * P := by
  cases hBle : Nat.ble (k' + 1) m with
  | true => rfl
  | false =>
    have hGt : ¬ (k' + 1 ≤ m) := by
      intro hLe
      have : Nat.ble (k' + 1) m = true := Nat.ble_eq.mpr hLe
      rw [hBle] at this
      contradiction
    have hEq : k' = m := by omega
    subst hEq
    change 0 = binom k' (k' + 1) * (1 <<< (k' + 1)) * P
    rw [binom_gt_zero k' (k' + 1) (by omega), Nat.zero_mul, Nat.zero_mul]

theorem packLevel_false_sound (m P q rem : Nat) (D : List Nat)
    (hm : m ≤ 13) (hrem : rem < P) (hLen : m + 1 ≤ D.length)
    (hFalse : Nat.testBit
      ((revList (packLevelRev (buildLevelSpecs m P).1 D 0 [])).getD (wordK (m + 1) q) 0)
      (wordBlock (m + 1) q * P + rem) = false) :
    Nat.testBit (D.getD (wordK m (q / 3)) 0)
      (wordBlock m (q / 3) * (3 * P) + ((q % 3) * P + rem)) = false := by
  rw [buildLevelSpecs_eq, revList_packLevelRev, List.reverse_nil, List.nil_append] at hFalse
  let k' := wordK m (q / 3)
  let c' := wordBlock m (q / 3)
  have hk' : k' ≤ m := wordK_le m (q / 3)
  have hk'_lt : k' < (packSpecsPrefix m P (m + 1)).length := by
    rw [packSpecsPrefix_length]; omega
  have hSpecLen : (packSpecsPrefix m P (m + 1)).length ≤ D.length := by
    rw [packSpecsPrefix_length]; exact hLen
  have hSpec := packSpecsPrefix_getD m P (m + 1) k' (by omega)
  have hc' : c' < binom m k' * (1 <<< k') := wordBlock_lt m (q / 3) hm
  have hN20 : binom m k' * (1 <<< k') ≤ (1 <<< 20) :=
    binom_mul_pow2_le m k' hm (by omega)
  rw [wordBlock_succ] at hFalse
  dsimp [wordK] at hFalse
  by_cases h0 : q % 3 = 0
  · rw [if_pos h0, if_pos h0] at hFalse
    rw [h0, Nat.zero_mul, Nat.zero_add]
    have hMid := packLevelFwd_getD_s0 (packSpecsPrefix m P (m + 1)) D 0 k'
      P (binom m k' * (1 <<< k') * P)
      (withPackSteps (binom m k' * (1 <<< k')) P (3 * P) true).1
      (withPackSteps (binom m k' * (1 <<< k')) (2 * P) (3 * P) false).1
      (c' * P + rem) hk'_lt hSpecLen hSpec hFalse
    exact withPackSteps_pack_false_sound (binom m k' * (1 <<< k')) P (3 * P) true c' rem
      (D.getD k' 0) hc' hrem (by omega) hN20 hMid
  · rw [if_neg h0, if_neg h0] at hFalse
    have hMod3 : q % 3 < 3 := Nat.mod_lt q (by decide)
    have hRem12 : (q % 3 - 1) * P + rem < 2 * P :=
      mul_add_lt_mul (q % 3 - 1) 2 P rem (by omega) hrem
    let nextLow := binom m (k' + 1) * (1 <<< (k' + 1)) * P
    have hNextEq := (nextLow_eq_binom m P k' hk').symm
    have h2c : 2 * c' * P = c' * (2 * P) := by
      rw [Nat.mul_comm 2 c', Nat.mul_assoc c' 2 P]
    have hJ : (binom m (k' + 1) * (1 <<< (k' + 1)) + 2 * c' + (q % 3 - 1)) * P + rem =
        nextLow + (c' * (2 * P) + ((q % 3 - 1) * P + rem)) := by
      dsimp [nextLow]
      rw [Nat.add_mul, Nat.add_mul, h2c]
      omega
    have hLe : nextLow ≤ (binom m (k' + 1) * (1 <<< (k' + 1)) + 2 * c' + (q % 3 - 1)) * P + rem := by omega
    have hSub : ((binom m (k' + 1) * (1 <<< (k' + 1)) + 2 * c' + (q % 3 - 1)) * P + rem) - nextLow =
        c' * (2 * P) + ((q % 3 - 1) * P + rem) := by omega
    have hMid := packLevelFwd_getD_s12 (packSpecsPrefix m P (m + 1)) D 0 k'
      P (binom m k' * (1 <<< k') * P) nextLow
      (withPackSteps (binom m k' * (1 <<< k')) P (3 * P) true).1
      (withPackSteps (binom m k' * (1 <<< k')) (2 * P) (3 * P) false).1
      ((binom m (k' + 1) * (1 <<< (k' + 1)) + 2 * c' + (q % 3 - 1)) * P + rem)
      hk'_lt hSpecLen hSpec hNextEq hLe hFalse
    rw [hSub] at hMid
    have hMid2 := withPackSteps_pack_false_sound (binom m k' * (1 <<< k')) (2 * P) (3 * P) false
      c' ((q % 3 - 1) * P + rem) (Nat.shiftRight (D.getD k' 0) P) hc' hRem12 (by omega) hN20 hMid
    rw [testBit_shiftRight] at hMid2
    have hIdx : P + (c' * (3 * P) + ((q % 3 - 1) * P + rem)) =
        c' * (3 * P) + ((q % 3) * P + rem) := by
      have hq_eq : (q % 3 - 1) + 1 = q % 3 := by omega
      calc P + (c' * (3 * P) + ((q % 3 - 1) * P + rem))
        _ = c' * (3 * P) + (((q % 3 - 1) + 1) * P + rem) := by
          rw [Nat.add_mul, Nat.one_mul]; omega
        _ = c' * (3 * P) + ((q % 3) * P + rem) := by rw [hq_eq]
    rwa [hIdx] at hMid2

theorem unpackLevel_false_sound (m P q rem d0 : Nat) (restD : List Nat)
    (hm : m ≤ 13) (hrem : rem < P) (hLen : m + 1 ≤ restD.length)
    (hm1 : m = 1 ∧ wordK m (q / 3) = 1 → wordBlock m (q / 3) = 0)
    (hFalse : Nat.testBit
      ((revList (unpackLevelRev (buildLevelSpecs m P).2 d0 restD [])).getD (wordK m (q / 3)) 0)
      (wordBlock m (q / 3) * (3 * P) + ((q % 3) * P + rem)) = false) :
    Nat.testBit ((d0 :: restD).getD (wordK (m + 1) q) 0)
      (wordBlock (m + 1) q * P + rem) = false := by
  rw [buildLevelSpecs_eq, revList_unpackLevelRev, List.reverse_nil, List.nil_append] at hFalse
  let k' := wordK m (q / 3)
  let c' := wordBlock m (q / 3)
  have hk' : k' ≤ m := wordK_le m (q / 3)
  have hk'_lt : k' < (unpackSpecsPrefix m P (m + 1)).length := by
    rw [unpackSpecsPrefix_length]; omega
  have hSpecLen : (unpackSpecsPrefix m P (m + 1)).length ≤ restD.length + 1 := by
    rw [unpackSpecsPrefix_length]; omega
  have hSpec := unpackSpecsPrefix_getD m P (m + 1) k' (by omega)
  have hc' : c' < binom m k' * (1 <<< k') := wordBlock_lt m (q / 3) hm
  have hN20 : binom m k' * (1 <<< k') ≤ (1 <<< 20) :=
    binom_mul_pow2_le m k' hm (by omega)
  rw [wordBlock_succ]
  dsimp [wordK]
  by_cases h0 : q % 3 = 0
  · rw [if_pos h0, if_pos h0]
    rw [h0, Nat.zero_mul, Nat.zero_add] at hFalse
    have hMid := unpackLevelFwd_getD_s0 (unpackSpecsPrefix m P (m + 1)) d0 restD k'
      P _ _ _ (c' * (3 * P) + rem) hk'_lt hSpecLen hSpec hFalse
    dsimp [mkUnpackCellSpecAt] at hMid
    cases hM1K1 : and (Nat.beq m 1) (Nat.beq k' 1) with
    | false =>
      rw [hM1K1] at hMid
      dsimp at hMid
      exact withPackSteps_unpack_false_sound (binom m k' * (1 <<< k')) P (3 * P) true
        c' rem ((d0 :: restD).getD k' 0) hc' hrem (by omega) hN20 hMid
    | true =>
      rw [hM1K1] at hMid
      dsimp at hMid
      rcases Bool.and_eq_true_iff.mp hM1K1 with ⟨hm1_b, hk1_b⟩
      have hc0 : wordBlock m (q / 3) = 0 := hm1 ⟨Nat.beq_eq.mp hm1_b, Nat.beq_eq.mp hk1_b⟩
      change wordBlock m (q / 3) = 0 at hc0
      have hc'0 : c' = 0 := hc0
      rw [hc'0, Nat.zero_mul, Nat.zero_add] at hMid
      rw [hc0, Nat.zero_mul, Nat.zero_add]
      rw [runUnpack_eq_fold] at hMid
      dsimp [foldUnpack] at hMid
      have hm0 : Nat.testBit (Nat.sub (Nat.shiftLeft 1 P) 1) rem = true := by
        change Nat.testBit ((1 <<< P) - 1) rem = true
        rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hrem
      exact stepUnpack_false_0 0 _ 0 ((d0 :: restD).getD k' 0) rem hm0 hMid
  · rw [if_neg h0, if_neg h0]
    have hMod3 : q % 3 < 3 := Nat.mod_lt q (by decide)
    have hRem12 : (q % 3 - 1) * P + rem < 2 * P :=
      mul_add_lt_mul (q % 3 - 1) 2 P rem (by omega) hrem
    have hGeP : P ≤ c' * (3 * P) + ((q % 3) * P + rem) := by
      have : 1 * P ≤ (q % 3) * P := Nat.mul_le_mul_right P (by omega)
      omega
    have hSubP : (c' * (3 * P) + ((q % 3) * P + rem)) - P =
        c' * (3 * P) + ((q % 3 - 1) * P + rem) := by
      have h1 : (q % 3) * P = (q % 3 - 1) * P + P := by
        rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with hq | hq <;> (rw [hq]; omega)
      omega
    have hk'D : k' < restD.length := by omega
    have hMid := unpackLevelFwd_getD_s12 (unpackSpecsPrefix m P (m + 1)) d0 restD k'
      P _ _ _ (c' * (3 * P) + ((q % 3) * P + rem)) hk'_lt hk'D hSpec hGeP hFalse
    rw [hSubP, unpack_nextLowBits_eq_binom m P k' hk'] at hMid
    dsimp [mkUnpackCellSpecAt] at hMid
    let nextLow := binom m (k' + 1) * (1 <<< (k' + 1)) * P
    have hMid2 : Nat.testBit (Nat.shiftRight ((d0 :: restD).getD (k' + 1) 0) nextLow)
        (c' * (2 * P) + ((q % 3 - 1) * P + rem)) = false := by
      cases hM1K1 : and (Nat.beq m 1) (Nat.beq k' 1) with
      | false =>
        rw [hM1K1] at hMid
        dsimp at hMid
        exact withPackSteps_unpack_false_sound (binom m k' * (1 <<< k')) (2 * P) (3 * P) false
          c' ((q % 3 - 1) * P + rem) (Nat.shiftRight ((d0 :: restD).getD (k' + 1) 0) nextLow)
          hc' hRem12 (by omega) hN20 hMid
      | true =>
        rw [hM1K1] at hMid
        dsimp at hMid
        rcases Bool.and_eq_true_iff.mp hM1K1 with ⟨hm1_b, hk1_b⟩
        have hc0 : c' = 0 := hm1 ⟨Nat.beq_eq.mp hm1_b, Nat.beq_eq.mp hk1_b⟩
        rw [hc0, Nat.zero_mul, Nat.zero_add] at hMid ⊢
        rw [runUnpack_eq_fold] at hMid
        dsimp [foldUnpack] at hMid
        have hm0 : Nat.testBit (Nat.sub (Nat.shiftLeft 1 (2 * P)) 1) ((q % 3 - 1) * P + rem) = true := by
          change Nat.testBit ((1 <<< (2 * P)) - 1) ((q % 3 - 1) * P + rem) = true
          rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow_sub_one]
          exact decide_eq_true hRem12
        exact stepUnpack_false_0 0 _ 0 (Nat.shiftRight ((d0 :: restD).getD (k' + 1) 0) nextLow)
          ((q % 3 - 1) * P + rem) hm0 hMid
    rw [testBit_shiftRight] at hMid2
    have h2c : 2 * c' * P = c' * (2 * P) := by
      rw [Nat.mul_comm 2 c', Nat.mul_assoc c' 2 P]
    have hIdx : nextLow + (c' * (2 * P) + ((q % 3 - 1) * P + rem)) =
        (binom m (k' + 1) * (1 <<< (k' + 1)) + 2 * c' + (q % 3 - 1)) * P + rem := by
      dsimp [nextLow]
      rw [Nat.add_mul, Nat.add_mul, h2c]
      omega
    rwa [hIdx] at hMid2

/-!
### Multi-Level Soundness of `packToBuckets` and `withUnpackFromBucketsPair`
-/

noncomputable def packLevelsPrefix (mMax : Nat) : Nat → List (List PackCellSpec)
  | 0 => []
  | c + 1 =>
    let m := c + 1
    let P := pow3 (mMax - 1 - m)
    packLevelsPrefix mMax c ++ [(buildLevelSpecs m P).1]

noncomputable def unpackLevelsPrefix (mMax : Nat) : Nat → List (List UnpackCellSpec)
  | 0 => []
  | c + 1 =>
    let m := c + 1
    let P := pow3 (mMax - 1 - m)
    unpackLevelsPrefix mMax c ++ [(buildLevelSpecs m P).2]

theorem buildAllPackUnpackLevels_eq (mMax : Nat) :
    buildAllPackUnpackLevels mMax =
      (packLevelsPrefix mMax (mMax - 1), (unpackLevelsPrefix mMax (mMax - 1)).reverse) := by
  unfold buildAllPackUnpackLevels
  have hRev : ∀ (pOut : List (List PackCellSpec)) (xs acc : List (List UnpackCellSpec)),
      (@List.rec (List UnpackCellSpec)
        (fun _ => List (List UnpackCellSpec) → List (List PackCellSpec) × List (List UnpackCellSpec))
        (fun uRev => (pOut, uRev))
        (fun h _ ihRev uRev => ihRev (h :: uRev))
        xs acc) =
      (pOut, xs.reverse ++ acc) := by
    intro pOut xs
    induction xs with
    | nil => intro acc; rfl
    | cons h rest ih =>
      intro acc
      change _ = (pOut, (h :: rest).reverse ++ acc)
      rw [ih (h :: acc), List.reverse_cons, List.append_assoc, List.singleton_append]
  have hAux : ∀ (c : Nat) (pAcc : List (List PackCellSpec)) (uAcc : List (List UnpackCellSpec)),
      (@Nat.rec (fun _ =>
        List (List PackCellSpec) → List (List UnpackCellSpec) →
        List (List PackCellSpec) × List (List UnpackCellSpec))
        (fun pAcc uAcc =>
          @List.rec (List UnpackCellSpec)
            (fun _ => List (List UnpackCellSpec) → List (List PackCellSpec) × List (List UnpackCellSpec))
            (fun uRev => (pAcc, uRev))
            (fun h _ ihRev uRev => ihRev (h :: uRev))
            uAcc [])
        (fun mIdx ih pAcc uAcc =>
          let m := Nat.succ mIdx
          let e := Nat.sub (Nat.sub mMax 1) m
          let P := pow3 e
          @Prod.rec _ _ (fun _ => _)
            (fun pLvl uLvl => ih (pLvl :: pAcc) (uLvl :: uAcc))
            (buildLevelSpecs m P))
        c pAcc uAcc) =
      (packLevelsPrefix mMax c ++ pAcc, (unpackLevelsPrefix mMax c ++ uAcc).reverse) := by
    intro c
    induction c with
    | zero =>
      intro pAcc uAcc
      have h0 := hRev pAcc uAcc []
      rw [List.append_nil] at h0
      exact h0
    | succ c' ih =>
      intro pAcc uAcc
      let m := c' + 1
      let P := pow3 (mMax - 1 - m)
      change _ = (packLevelsPrefix mMax c' ++ [(buildLevelSpecs m P).1] ++ pAcc,
                  (unpackLevelsPrefix mMax c' ++ [(buildLevelSpecs m P).2] ++ uAcc).reverse)
      rw [List.append_assoc, List.singleton_append,
          List.append_assoc, List.singleton_append]
      exact ih ((buildLevelSpecs m P).1 :: pAcc) ((buildLevelSpecs m P).2 :: uAcc)
  have hMain := hAux (mMax - 1) [] []
  rw [List.append_nil, List.append_nil] at hMain
  exact hMain

theorem packToBuckets_append (ls1 ls2 : List (List PackCellSpec)) (D : List Nat) :
    packToBuckets (ls1 ++ ls2) D = packToBuckets ls2 (packToBuckets ls1 D) := by
  induction ls1 generalizing D with
  | nil => rfl
  | cons l rest ih =>
    exact ih (revList (packLevelRev l D 0 []))

theorem packLevelsPrefix_length_out (mMax c : Nat) (initD : List Nat) (hInit : 2 ≤ initD.length) :
    c + 2 ≤ (packToBuckets (packLevelsPrefix mMax c) initD).length := by
  induction c with
  | zero => exact hInit
  | succ c' ih =>
    dsimp [packLevelsPrefix]
    rw [packToBuckets_append]
    change c' + 1 + 2 ≤ (revList (packLevelRev (buildLevelSpecs (c' + 1) _).1
      (packToBuckets (packLevelsPrefix mMax c') initD) 0 [])).length
    rw [buildLevelSpecs_eq, revList_packLevelRev, List.reverse_nil, List.nil_append,
        packLevelFwd_length]
    · rw [packSpecsPrefix_length]; omega
    · rw [packSpecsPrefix_length]; omega

theorem packLevelsPrefix_false_sound (mMax c X : Nat) (initD : List Nat)
    (hmMax : mMax ≤ 13) (hc : c ≤ mMax - 1) (hInit : 2 ≤ initD.length)
    (hFalse :
      let P_c := 3 ^ (mMax - 1 - c)
      Nat.testBit ((packToBuckets (packLevelsPrefix mMax c) initD).getD (wordK (c + 1) (X / P_c)) 0)
        (wordBlock (c + 1) (X / P_c) * P_c + (X % P_c)) = false) :
    let P_0 := 3 ^ (mMax - 1)
    Nat.testBit (initD.getD (wordK 1 (X / P_0)) 0)
      (wordBlock 1 (X / P_0) * P_0 + (X % P_0)) = false := by
  induction c with
  | zero =>
    dsimp at hFalse ⊢
    exact hFalse
  | succ c' ih =>
    dsimp at hFalse
    let m := c' + 1
    let P := 3 ^ (mMax - 1 - m)
    have hP_eq : pow3 (mMax - 1 - m) = P := kernel_pow3_eq (mMax - 1 - m)
    have hP_pos : 0 < P := Nat.pow_pos (by decide)
    have hPc' : 3 ^ (mMax - 1 - c') = 3 * P := by
      have hSub : mMax - 1 - c' = (mMax - 1 - m) + 1 := by omega
      rw [hSub, Nat.pow_succ']
    dsimp [packLevelsPrefix] at hFalse
    rw [packToBuckets_append, hP_eq] at hFalse
    change Nat.testBit
      ((revList (packLevelRev (buildLevelSpecs m P).1 (packToBuckets (packLevelsPrefix mMax c') initD) 0 [])).getD
        (wordK (m + 1) (X / P)) 0)
      (wordBlock (m + 1) (X / P) * P + (X % P)) = false at hFalse
    have hLen := packLevelsPrefix_length_out mMax c' initD hInit
    have hStep := packLevel_false_sound m P (X / P) (X % P)
      (packToBuckets (packLevelsPrefix mMax c') initD)
      (by omega) (Nat.mod_lt X hP_pos) hLen hFalse
    have hDiv3 : (X / P) / 3 = X / (3 ^ (mMax - 1 - c')) := by
      rw [hPc', Nat.div_div_eq_div_mul, Nat.mul_comm P 3]
    have hMod3 : ((X / P) % 3) * P + (X % P) = X % (3 ^ (mMax - 1 - c')) := by
      rw [hPc']
      have h1 : X = P * (X / P) + X % P := (Nat.div_add_mod X P).symm
      have h2 : X / P = 3 * ((X / P) / 3) + (X / P) % 3 := (Nat.div_add_mod (X / P) 3).symm
      have h3 : X = (3 * P) * ((X / P) / 3) + X % (3 * P) := by
        have h3' := (Nat.div_add_mod X (3 * P)).symm
        rwa [Nat.mul_comm 3 P, ← Nat.div_div_eq_div_mul, Nat.mul_comm P 3] at h3'
      have h4 : P * (X / P) = (3 * P) * ((X / P) / 3) + ((X / P) % 3) * P := by
        calc P * (X / P)
          _ = P * (3 * ((X / P) / 3) + (X / P) % 3) := by rw [← h2]
          _ = P * (3 * ((X / P) / 3)) + P * ((X / P) % 3) := Nat.mul_add _ _ _
          _ = (3 * P) * ((X / P) / 3) + ((X / P) % 3) * P := by
            rw [← Nat.mul_assoc P 3, Nat.mul_comm P 3, Nat.mul_comm P ((X / P) % 3)]
      omega
    rw [hDiv3, ← hPc', hMod3] at hStep
    exact ih (by omega) hStep

theorem packToBuckets_false_sound (mMax X L2 d0_1 : Nat)
    (hmMax_lo : 1 ≤ mMax) (hmMax_hi : mMax ≤ 13)
    (hFalse : Nat.testBit
      ((packToBuckets (buildAllPackUnpackLevels mMax).1 [L2, d0_1]).getD (wordK mMax X) 0)
      (wordBlock mMax X) = false) :
    let P_0 := 3 ^ (mMax - 1)
    Nat.testBit ([L2, d0_1].getD (wordK 1 (X / P_0)) 0)
      (wordBlock 1 (X / P_0) * P_0 + (X % P_0)) = false := by
  rw [buildAllPackUnpackLevels_eq] at hFalse
  have h1 : mMax - 1 + 1 = mMax := by omega
  have h2 : mMax - 1 - (mMax - 1) = 0 := by omega
  have hFalse' :
      let P_c := 3 ^ (mMax - 1 - (mMax - 1))
      Nat.testBit ((packToBuckets (packLevelsPrefix mMax (mMax - 1)) [L2, d0_1]).getD
        (wordK (mMax - 1 + 1) (X / P_c)) 0)
        (wordBlock (mMax - 1 + 1) (X / P_c) * P_c + (X % P_c)) = false := by
    dsimp
    rw [h1, h2, Nat.pow_zero, Nat.div_one, Nat.mul_one, Nat.mod_one, Nat.add_zero]
    exact hFalse
  exact packLevelsPrefix_false_sound mMax (mMax - 1) X [L2, d0_1]
    hmMax_hi (Nat.le_refl _) (Nat.le_refl 2) hFalse'

theorem wordK_one_of_lt_two (q : Nat) (hq : q < 2) :
    wordK 1 q = q := by
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> rfl

theorem wordBlock_one_of_lt_two (q : Nat) (hq : q < 2) :
    wordBlock 1 q = 0 := by
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl <;> rfl

theorem packToBuckets_false_sound_lt (mMax X L2 d0_1 : Nat)
    (hmMax_lo : 1 ≤ mMax) (hmMax_hi : mMax ≤ 13)
    (hX : X < 2 * 3 ^ (mMax - 1))
    (hFalse : Nat.testBit
      ((packToBuckets (buildAllPackUnpackLevels mMax).1 [L2, d0_1]).getD (wordK mMax X) 0)
      (wordBlock mMax X) = false) :
    let P_0 := 3 ^ (mMax - 1)
    Nat.testBit ([L2, d0_1].getD (X / P_0) 0) (X % P_0) = false := by
  have hBase := packToBuckets_false_sound mMax X L2 d0_1 hmMax_lo hmMax_hi hFalse
  dsimp at hBase ⊢
  have hP0_pos : 0 < 3 ^ (mMax - 1) := Nat.pow_pos (by decide)
  have hq : X / 3 ^ (mMax - 1) < 2 := Nat.div_lt_of_lt_mul (by omega)
  rw [wordK_one_of_lt_two _ hq, wordBlock_one_of_lt_two _ hq, Nat.zero_mul, Nat.zero_add] at hBase
  exact hBase

noncomputable def unpackFromBucketsAux (revLevels : List (List UnpackCellSpec)) (buckets : List Nat) : List Nat :=
  @List.rec (List UnpackCellSpec) (fun _ => List Nat → List Nat)
    (fun D => D)
    (fun lvlSpecs _ ih D =>
      @List.rec Nat (fun _ => List Nat)
        []
        (fun d0 restD _ =>
          let prevD := revList (unpackLevelRev lvlSpecs d0 restD [])
          ih prevD)
        D)
    revLevels buckets

theorem unpackFromBucketsAux_cons (lvlSpecs : List UnpackCellSpec)
    (restLevels : List (List UnpackCellSpec)) (d0 : Nat) (restD : List Nat) :
    unpackFromBucketsAux (lvlSpecs :: restLevels) (d0 :: restD) =
      unpackFromBucketsAux restLevels (revList (unpackLevelRev lvlSpecs d0 restD [])) := rfl

theorem unpackLevelsPrefix_reverse_succ (mMax c' : Nat) :
    (unpackLevelsPrefix mMax (c' + 1)).reverse =
      (buildLevelSpecs (c' + 1) (pow3 (mMax - 1 - (c' + 1)))).2 ::
        (unpackLevelsPrefix mMax c').reverse := by
  dsimp [unpackLevelsPrefix]
  rw [List.reverse_append]
  rfl

theorem unpackLevelsPrefix_length_out (mMax c : Nat) (D : List Nat) (hLen : c + 2 ≤ D.length) :
    2 ≤ (unpackFromBucketsAux (unpackLevelsPrefix mMax c).reverse D).length := by
  induction c generalizing D with
  | zero => exact hLen
  | succ c' ih =>
    rcases D with _ | ⟨d0, restD⟩
    · simp at hLen
    · rw [unpackLevelsPrefix_reverse_succ, unpackFromBucketsAux_cons]
      apply ih
      rw [buildLevelSpecs_eq, revList_unpackLevelRev, List.reverse_nil, List.nil_append,
          unpackLevelFwd_length]
      · rw [unpackSpecsPrefix_length]; omega
      · rw [unpackSpecsPrefix_length]
        have : (d0 :: restD).length = restD.length + 1 := rfl
        omega

theorem withUnpackFromBucketsPair_eq {α : Type} (revLevels : List (List UnpackCellSpec))
    (buckets : List Nat) (k : Nat → Nat → α) (defVal : α)
    (hLen : 2 ≤ (unpackFromBucketsAux revLevels buckets).length) :
    withUnpackFromBucketsPair revLevels buckets k defVal =
      k ((unpackFromBucketsAux revLevels buckets).getD 0 0)
        ((unpackFromBucketsAux revLevels buckets).getD 1 0) := by
  unfold withUnpackFromBucketsPair
  change @List.rec Nat (fun _ => α) defVal
    (fun u0 restD _ => @List.rec Nat (fun _ => α) (k u0 0) (fun u12 _ _ => k u0 u12) restD)
    (unpackFromBucketsAux revLevels buckets) = _
  rcases hL : unpackFromBucketsAux revLevels buckets with _ | ⟨u0, _ | ⟨u12, rest⟩⟩
  · rw [hL] at hLen; contradiction
  · rw [hL] at hLen; contradiction
  · rfl

theorem unpackLevelsPrefix_false_sound (mMax c X : Nat) (D : List Nat)
    (hmMax : mMax ≤ 13) (hc : c ≤ mMax - 1) (hLen : c + 2 ≤ D.length)
    (hX : X < 2 * 3 ^ (mMax - 1))
    (hFalse :
      let P_0 := 3 ^ (mMax - 1)
      let finalD := unpackFromBucketsAux (unpackLevelsPrefix mMax c).reverse D
      Nat.testBit (finalD.getD (wordK 1 (X / P_0)) 0)
        (wordBlock 1 (X / P_0) * P_0 + (X % P_0)) = false) :
    let P_c := 3 ^ (mMax - 1 - c)
    Nat.testBit (D.getD (wordK (c + 1) (X / P_c)) 0)
      (wordBlock (c + 1) (X / P_c) * P_c + (X % P_c)) = false := by
  induction c generalizing D with
  | zero =>
    dsimp [unpackLevelsPrefix, unpackFromBucketsAux] at hFalse ⊢
    exact hFalse
  | succ c' ih =>
    rcases D with _ | ⟨d0, restD⟩
    · simp at hLen
    · dsimp at hFalse
      let m := c' + 1
      let P := 3 ^ (mMax - 1 - m)
      have hP_eq : pow3 (mMax - 1 - m) = P := kernel_pow3_eq (mMax - 1 - m)
      have hP_pos : 0 < P := Nat.pow_pos (by decide)
      have hPc' : 3 ^ (mMax - 1 - c') = 3 * P := by
        have hSub : mMax - 1 - c' = (mMax - 1 - m) + 1 := by omega
        rw [hSub, Nat.pow_succ']
      rw [unpackLevelsPrefix_reverse_succ, unpackFromBucketsAux_cons, hP_eq] at hFalse
      let prevD := revList (unpackLevelRev (buildLevelSpecs m P).2 d0 restD [])
      have hRestLen : m + 1 ≤ restD.length := by
        change c' + 1 + 2 ≤ restD.length + 1 at hLen
        omega
      have hPrevLen : c' + 2 ≤ prevD.length := by
        dsimp [prevD]
        rw [buildLevelSpecs_eq, revList_unpackLevelRev, List.reverse_nil, List.nil_append,
            unpackLevelFwd_length]
        · rw [unpackSpecsPrefix_length]; omega
        · rw [unpackSpecsPrefix_length]; omega
      have hMid := ih prevD (by omega) hPrevLen hFalse
      dsimp at hMid
      have hDiv3 : (X / P) / 3 = X / (3 ^ (mMax - 1 - c')) := by
        rw [hPc', Nat.div_div_eq_div_mul, Nat.mul_comm P 3]
      have hMod3 : ((X / P) % 3) * P + (X % P) = X % (3 ^ (mMax - 1 - c')) := by
        rw [hPc']
        have h1 : X = P * (X / P) + X % P := (Nat.div_add_mod X P).symm
        have h2 : X / P = 3 * ((X / P) / 3) + (X / P) % 3 := (Nat.div_add_mod (X / P) 3).symm
        have h3 : X = (3 * P) * ((X / P) / 3) + X % (3 * P) := by
          have h3' := (Nat.div_add_mod X (3 * P)).symm
          rwa [Nat.mul_comm 3 P, ← Nat.div_div_eq_div_mul, Nat.mul_comm P 3] at h3'
        have h4 : P * (X / P) = (3 * P) * ((X / P) / 3) + ((X / P) % 3) * P := by
          calc P * (X / P)
            _ = P * (3 * ((X / P) / 3) + (X / P) % 3) := by rw [← h2]
            _ = P * (3 * ((X / P) / 3)) + P * ((X / P) % 3) := Nat.mul_add _ _ _
            _ = (3 * P) * ((X / P) / 3) + ((X / P) % 3) * P := by
              rw [← Nat.mul_assoc P 3, Nat.mul_comm P 3, Nat.mul_comm P ((X / P) % 3)]
        omega
      rw [← hDiv3, ← hMod3, hPc'] at hMid
      have hm1 : m = 1 ∧ wordK m ((X / P) / 3) = 1 → wordBlock m ((X / P) / 3) = 0 := by
        rintro ⟨hm_eq, _⟩
        have hc'0 : c' = 0 := by omega
        rw [hm_eq, hDiv3, hc'0, Nat.sub_zero]
        have hP0_pos : 0 < 3 ^ (mMax - 1) := Nat.pow_pos (by decide)
        have hq : X / 3 ^ (mMax - 1) < 2 := Nat.div_lt_of_lt_mul (by omega)
        exact wordBlock_one_of_lt_two _ hq
      exact unpackLevel_false_sound m P (X / P) (X % P) d0 restD
        (by omega) (Nat.mod_lt X hP_pos) hRestLen hm1 hMid

theorem unpackFromBuckets_false_sound_lt (mMax X : Nat) (buckets : List Nat)
    (hmMax_lo : 1 ≤ mMax) (hmMax_hi : mMax ≤ 13)
    (hLen : mMax + 1 ≤ buckets.length)
    (hX : X < 2 * 3 ^ (mMax - 1))
    (hFalse :
      let P_0 := 3 ^ (mMax - 1)
      let finalD := unpackFromBucketsAux (buildAllPackUnpackLevels mMax).2 buckets
      Nat.testBit (finalD.getD (X / P_0) 0) (X % P_0) = false) :
    Nat.testBit (buckets.getD (wordK mMax X) 0) (wordBlock mMax X) = false := by
  rw [buildAllPackUnpackLevels_eq] at hFalse
  have hP0_pos : 0 < 3 ^ (mMax - 1) := Nat.pow_pos (by decide)
  have hq : X / 3 ^ (mMax - 1) < 2 := Nat.div_lt_of_lt_mul (by omega)
  have hFalse' :
      let P_0 := 3 ^ (mMax - 1)
      let finalD := unpackFromBucketsAux (unpackLevelsPrefix mMax (mMax - 1)).reverse buckets
      Nat.testBit (finalD.getD (wordK 1 (X / P_0)) 0)
        (wordBlock 1 (X / P_0) * P_0 + (X % P_0)) = false := by
    dsimp
    rw [wordK_one_of_lt_two _ hq, wordBlock_one_of_lt_two _ hq, Nat.zero_mul, Nat.zero_add]
    exact hFalse
  have hRes := unpackLevelsPrefix_false_sound mMax (mMax - 1) X buckets
    hmMax_hi (Nat.le_refl _) (by omega) hX hFalse'
  dsimp at hRes
  have h1 : mMax - 1 + 1 = mMax := by omega
  have h2 : mMax - 1 - (mMax - 1) = 0 := by omega
  rw [h1, h2, Nat.pow_zero, Nat.div_one, Nat.mul_one, Nat.mod_one, Nat.add_zero] at hRes
  exact hRes

/-!
### Part 5: `makeSingleBitMask0`, `buildThueMorseParityAux`, and `buildCatalanTrieAux` Soundness
-/

theorem geomRepeat_lt (cell stride count : Nat) (hCell : cell < 2 ^ stride) :
    geomRepeat cell stride count < 2 ^ (count * stride) := by
  induction count with
  | zero => simp [geomRepeat]
  | succ count ih =>
    dsimp [geomRepeat]
    rw [Nat.shiftLeft_eq, Nat.add_mul, Nat.one_mul, Nat.pow_add]
    have h1 : (geomRepeat cell stride count + 1) * 2 ^ stride ≤ 2 ^ (count * stride) * 2 ^ stride :=
      Nat.mul_le_mul_right (2 ^ stride) ih
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

theorem repeatBlock_lt (cell stride count : Nat) (hStride : 0 < stride) (hCell : cell < 2 ^ stride) :
    repeatBlock cell stride count < 2 ^ (count * stride) := by
  rw [repeatBlock_eq_geomRepeat cell stride count hStride]
  exact geomRepeat_lt cell stride count hCell

theorem getRepeatMask_lt (count stride width : Nat) (hStride : 0 < stride) (hWidth : width ≤ stride) :
    getRepeatMask count stride width < 2 ^ (count * stride) := by
  unfold getRepeatMask
  have hBase : Nat.sub (Nat.shiftLeft 1 width) 1 = 2 ^ width - 1 := by
    change 1 <<< width - 1 = 2 ^ width - 1
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [hBase]
  have hCell : 2 ^ width - 1 < 2 ^ stride := by
    have : 2 ^ width ≤ 2 ^ stride := Nat.pow_le_pow_right (by decide) hWidth
    have : 0 < 2 ^ width := Nat.two_pow_pos width
    omega
  exact repeatBlock_lt (2 ^ width - 1) stride count hStride hCell

theorem mod_two_mul_lt_iff (j P : Nat) (hP : 0 < P) :
    j % (2 * P) < P ↔ (j / P) % 2 = 0 := by
  have h1 : j % (2 * P) < P ↔ (j % (2 * P)) / P < 1 := by
    rw [Nat.div_lt_iff_lt_mul hP, Nat.one_mul]
  rw [h1, Nat.mod_mul_left_div_self]
  omega

theorem testBit_false_iff_div_mod_two (sign a : Nat) :
    Nat.testBit sign a = false ↔ (sign / 2 ^ a) % 2 = 0 := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  change (1 &&& (sign / 2 ^ a) != 0) = false ↔ (sign / 2 ^ a) % 2 = 0
  rw [Nat.and_comm 1, Nat.and_one_is_mod, bne_eq_false_iff_eq]

theorem testBit_makeSingleBitMask0_of_bit_false (kBucket numBits M a c sign : Nat)
    (hNum : numBits ≤ kBucket) (ha : a < numBits) (hc : c < M)
    (hSign : sign < (1 <<< numBits))
    (hBit : Nat.testBit sign a = false) :
    Nat.testBit (makeSingleBitMask0 kBucket numBits M a) (c * (1 <<< kBucket) + sign) = true := by
  unfold makeSingleBitMask0
  let countInCell := 1 <<< (numBits - 1 - a)
  let width := 1 <<< a
  let stride := 1 <<< (a + 1)
  have hWidth_eq : width = 2 ^ a := by
    change 1 <<< a = 2 ^ a; rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hStride_eq : stride = 2 * 2 ^ a := by
    change 1 <<< (a + 1) = 2 * 2 ^ a
    rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ']
  have hCount_eq : countInCell * stride = 1 <<< numBits := by
    change (1 <<< (numBits - 1 - a)) * (1 <<< (a + 1)) = 1 <<< numBits
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq,
        Nat.one_mul, Nat.one_mul, Nat.one_mul, ← Nat.pow_add]
    have : numBits - 1 - a + (a + 1) = numBits := by omega
    rw [this]
  have hStride_pos : 0 < stride := by
    rw [hStride_eq]; have := Nat.two_pow_pos a; omega
  have hWidth_le : width ≤ stride := by
    rw [hWidth_eq, hStride_eq]; omega
  have hCell_lt : getRepeatMask countInCell stride width < 2 ^ (1 <<< kBucket) := by
    have h1 := getRepeatMask_lt countInCell stride width hStride_pos hWidth_le
    rw [hCount_eq] at h1
    have h2 : (1 <<< numBits) ≤ (1 <<< kBucket) := by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul]
      exact Nat.pow_le_pow_right (by decide) hNum
    exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)
  have hOuter_pos : 0 < (1 <<< kBucket) := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.two_pow_pos kBucket
  have hSign_lt_k : sign < (1 <<< kBucket) := by
    have h2 : (1 <<< numBits) ≤ (1 <<< kBucket) := by
      rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul]
      exact Nat.pow_le_pow_right (by decide) hNum
    omega
  change Nat.testBit (repeatBlock (getRepeatMask countInCell stride width) (1 <<< kBucket) M)
    (c * (1 <<< kBucket) + sign) = true
  rw [testBit_repeatBlock _ (1 <<< kBucket) M _ hOuter_pos hCell_lt]
  have hIdx_lt : c * (1 <<< kBucket) + sign < M * (1 <<< kBucket) :=
    mul_add_lt_mul c M (1 <<< kBucket) sign hc hSign_lt_k
  have hIdx_mod : (c * (1 <<< kBucket) + sign) % (1 <<< kBucket) = sign := by
    rw [Nat.add_comm (c * (1 <<< kBucket)) sign, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt hSign_lt_k]
  rw [decide_eq_true hIdx_lt, Bool.true_and, hIdx_mod]
  rw [testBit_getRepeatMask countInCell stride width sign hStride_pos hWidth_le]
  rw [hCount_eq, decide_eq_true hSign, Bool.true_and, hStride_eq, hWidth_eq]
  rw [decide_eq_true_iff, mod_two_mul_lt_iff sign (2 ^ a) (Nat.two_pow_pos a)]
  exact (testBit_false_iff_div_mod_two sign a).mp hBit

theorem lookupM0_buildM0List (kBucket numBits M a : Nat) (ha : a < numBits) :
    lookupM0 a (buildM0List kBucket numBits M).val = makeSingleBitMask0 kBucket numBits M a := by
  unfold buildM0List
  have hAux : ∀ (c : Nat) (acc : List (Nat × Nat)),
      (∀ p ∈ acc, c ≤ p.1) →
      (∀ x < c, lookupM0 x
        (@Nat.rec (fun _ => List (Nat × Nat) → StrictBox (List (Nat × Nat)))
          (fun acc => StrictBox.mk acc)
          (fun a ih acc => ih ((a, makeSingleBitMask0 kBucket numBits M a) :: acc))
          c acc).val = makeSingleBitMask0 kBucket numBits M x) ∧
      (∀ x ≥ c, lookupM0 x
        (@Nat.rec (fun _ => List (Nat × Nat) → StrictBox (List (Nat × Nat)))
          (fun acc => StrictBox.mk acc)
          (fun a ih acc => ih ((a, makeSingleBitMask0 kBucket numBits M a) :: acc))
          c acc).val = lookupM0 x acc) := by
    intro c
    induction c with
    | zero =>
      intro acc _
      refine ⟨fun x hx => by omega, fun x _ => rfl⟩
    | succ c' ih =>
      intro acc hAcc
      have hAcc' : ∀ p ∈ ((c', makeSingleBitMask0 kBucket numBits M c') :: acc), c' ≤ p.1 := by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact Nat.le_refl c'
        · exact Nat.le_of_succ_le (hAcc p hp')
      rcases ih ((c', makeSingleBitMask0 kBucket numBits M c') :: acc) hAcc' with ⟨ihLt, ihGe⟩
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · by_cases hEq : x = c'
        · subst hEq
          change lookupM0 x _ = _
          rw [ihGe x (Nat.le_refl x)]
          change selectBool (Nat.beq x x) (makeSingleBitMask0 kBucket numBits M x) (lookupM0 x acc) = _
          have hSelf : Nat.beq x x = true := Nat.beq_eq.mpr rfl
          rw [hSelf]
        · exact ihLt x (by omega)
      · change lookupM0 x _ = _
        rw [ihGe x (by omega)]
        change selectBool (Nat.beq c' x) (makeSingleBitMask0 kBucket numBits M c') (lookupM0 x acc) = _
        have hNe : Nat.beq c' x = false := by
          cases hB : Nat.beq c' x with
          | false => rfl
          | true => have := Nat.beq_eq.mp hB; omega
        rw [hNe]
  exact (hAux numBits [] (fun _ h => nomatch h)).1 a ha

theorem add_two_pow_lt_of_testBit_false (sign lo numBits : Nat)
    (hSign : sign < (1 <<< numBits)) (hLo : lo < numBits)
    (hBit : Nat.testBit sign lo = false) :
    sign + (1 <<< lo) < (1 <<< numBits) := by
  have h1 : 1 <<< lo = 2 ^ lo := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  have h2 : 1 <<< numBits = 2 ^ numBits := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h1]
  rw [h2] at hSign ⊢
  have hMod : sign % (2 * 2 ^ lo) < 2 ^ lo := by
    rw [mod_two_mul_lt_iff sign (2 ^ lo) (Nat.two_pow_pos lo)]
    exact (testBit_false_iff_div_mod_two sign lo).mp hBit
  let S := 2 * 2 ^ lo
  have hS_pos : 0 < S := by dsimp [S]; have := Nat.two_pow_pos lo; omega
  have hPowSplit : 2 ^ numBits = 2 ^ (numBits - (lo + 1)) * S := by
    dsimp [S]
    rw [← Nat.pow_succ', ← Nat.pow_add]
    have : numBits - (lo + 1) + (lo + 1) = numBits := by omega
    rw [this]
  have hDivLt : sign / S < 2 ^ (numBits - (lo + 1)) := by
    rw [Nat.div_lt_iff_lt_mul hS_pos, ← hPowSplit]
    exact hSign
  have hDecomp : sign = S * (sign / S) + sign % S := (Nat.div_add_mod sign S).symm
  have hLe : (sign / S + 1) * S ≤ 2 ^ (numBits - (lo + 1)) * S :=
    Nat.mul_le_mul_right S hDivLt
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (sign / S) S, ← hPowSplit] at hLe
  dsimp [S] at hDecomp hLe hMod
  omega

theorem wordSign_lt_of_flipDigitAt (e m X X' numBits : Nat)
    (he : e < m) (hFlip : FlipDigitAt e X X')
    (hLo : wordK e X < numBits) (hSign : wordSign m X < (1 <<< numBits)) :
    wordSign m X' < (1 <<< numBits) := by
  rcases wordSign_of_flipDigitAt e m X X' he hFlip with ⟨hF, _, hEq⟩ | ⟨_, _, hEq⟩
  · rw [hEq]
    exact add_two_pow_lt_of_testBit_false (wordSign m X) (wordK e X) numBits hSign hLo hF
  · rw [hEq] at hSign
    exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSign

theorem testBit_lookupM0_wordBlock (mMax numBits X x : Nat)
    (hmMax : mMax ≤ 13)
    (hNum : numBits ≤ wordK mMax X)
    (hSign : wordSign mMax X < (1 <<< numBits))
    (ha : wordK x X < numBits)
    (hBit : Nat.testBit (wordBlock mMax X) (wordK x X) = false) :
    let kBucket := wordK mMax X
    let M := binom mMax kBucket
    let m0List := (buildM0List kBucket numBits M).val
    Nat.testBit (lookupM0 (wordK x X) m0List) (wordBlock mMax X) = true := by
  dsimp
  rw [lookupM0_buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X)) (wordK x X) ha]
  have hBitSign : Nat.testBit (wordSign mMax X) (wordK x X) = false := by
    rw [← testBit_wordBlock_eq_wordSign mMax X (wordK x X) (by omega)]
    exact hBit
  exact testBit_makeSingleBitMask0_of_bit_false (wordK mMax X) numBits
    (binom mMax (wordK mMax X)) (wordK x X) (wordCell mMax X) (wordSign mMax X)
    hNum ha (wordCell_lt mMax X hmMax) hSign hBitSign

theorem evalChordOp_last_flip_false_sound (mMax numBits X X' x B : Nat)
    (hmMax : mMax ≤ 13) (hx : x < mMax)
    (hFlip : FlipDigitAt x X X')
    (hNum : numBits ≤ wordK mMax X)
    (hSign : wordSign mMax X < (1 <<< numBits))
    (hLo : wordK x X < numBits)
    (hFalse :
      let kBucket := wordK mMax X
      let M := binom mMax kBucket
      let m0List := (buildM0List kBucket numBits M).val
      let lo := wordK x X
      let bitLo := Nat.shiftLeft 1 lo
      let m0Lo := lookupM0 lo m0List
      Nat.testBit (evalChordOp (ChordOp.last bitLo m0Lo) B) (wordBlock mMax X) = false) :
    Nat.testBit B (wordBlock mMax X) = false ∧ wordSign mMax X < (1 <<< numBits) ∨
    Nat.testBit B (wordBlock mMax X') = false ∧ wordSign mMax X' < (1 <<< numBits) := by
  dsimp at hFalse
  rw [evalChordOp_eq_raw] at hFalse
  dsimp at hFalse
  rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
  rcases hFalse with ⟨hm0, hm1⟩
  have hSign' : wordSign mMax X' < (1 <<< numBits) :=
    wordSign_lt_of_flipDigitAt x mMax X X' numBits hx hFlip hLo hSign
  rcases wordBlock_of_flipDigitAt x mMax X X' hx hFlip with ⟨hBit0, _, hEq'⟩ | ⟨_, hBit0', hEq⟩
  · have hm0Lo : Nat.testBit (lookupM0 (wordK x X) (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val)
        (wordBlock mMax X) = true :=
      testBit_lookupM0_wordBlock mMax numBits X x hmMax hNum hSign hLo hBit0
    rw [testBit_land, hm0Lo, Bool.and_true, testBit_land, testBit_shiftRight,
        Nat.add_comm (Nat.shiftLeft 1 (wordK x X)) (wordBlock mMax X)] at hm0
    change (Nat.testBit B (wordBlock mMax X) && Nat.testBit B (wordBlock mMax X + (1 <<< wordK x X))) = false at hm0
    rw [← hEq'] at hm0
    cases hBX : Nat.testBit B (wordBlock mMax X) with
    | false => exact Or.inl ⟨rfl, hSign⟩
    | true =>
      rw [hBX, Bool.true_and] at hm0
      exact Or.inr ⟨hm0, hSign'⟩
  · have hK_x : wordK x X = wordK x X' := wordK_eq_of_flipDigitAt x x X X' hFlip
    have hK_m : wordK mMax X = wordK mMax X' := wordK_eq_of_flipDigitAt mMax x X X' hFlip
    have hm0Lo' : Nat.testBit (lookupM0 (wordK x X) (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val)
        (wordBlock mMax X') = true := by
      rw [hK_x, hK_m]
      apply testBit_lookupM0_wordBlock mMax numBits X' x hmMax
      · rw [← hK_m]; exact hNum
      · exact hSign'
      · rw [← hK_x]; exact hLo
      · rw [← hK_x]; exact hBit0'
    have hLe : Nat.shiftLeft 1 (wordK x X) ≤ wordBlock mMax X := by
      change (1 <<< wordK x X) ≤ wordBlock mMax X
      rw [hEq]; exact Nat.le_add_left _ _
    have hSub : wordBlock mMax X - Nat.shiftLeft 1 (wordK x X) = wordBlock mMax X' := by
      change wordBlock mMax X - (1 <<< wordK x X) = wordBlock mMax X'
      rw [hEq]; exact Nat.add_sub_cancel _ _
    rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and, hSub,
        testBit_land, hm0Lo', Bool.and_true, testBit_land, testBit_shiftRight,
        Nat.add_comm (Nat.shiftLeft 1 (wordK x X)) (wordBlock mMax X')] at hm1
    change (Nat.testBit B (wordBlock mMax X') && Nat.testBit B (wordBlock mMax X' + (1 <<< wordK x X))) = false at hm1
    rw [← hEq] at hm1
    cases hBX' : Nat.testBit B (wordBlock mMax X') with
    | false => exact Or.inr ⟨rfl, hSign'⟩
    | true =>
      rw [hBX', Bool.true_and] at hm1
      exact Or.inl ⟨hm1, hSign⟩

theorem flipDigitAt_comm (x y X X_mid X' : Nat) (hxy : x < y)
    (hx : FlipDigitAt x X X_mid) (hy : FlipDigitAt y X_mid X') :
    ∃ X_mid2, FlipDigitAt y X X_mid2 ∧ FlipDigitAt x X_mid2 X' := by
  induction x generalizing y X X_mid X' with
  | zero =>
    rcases y with _ | y'
    · omega
    · dsimp [FlipDigitAt] at hx hy
      rcases hx with ⟨hDivX, hModX⟩
      rcases hy with ⟨hModY, hFlipY⟩
      refine ⟨3 * (X' / 3) + X % 3, ?_, ?_⟩
      · dsimp [FlipDigitAt]
        have hLt : X % 3 < 3 := Nat.mod_lt X (by decide)
        have hMod : (3 * (X' / 3) + X % 3) % 3 = X % 3 := by omega
        have hDiv : (3 * (X' / 3) + X % 3) / 3 = X' / 3 := by omega
        rw [hMod, hDiv, hDivX]
        exact ⟨rfl, hFlipY⟩
      · dsimp [FlipDigitAt]
        have hLt : X % 3 < 3 := Nat.mod_lt X (by decide)
        have hMod : (3 * (X' / 3) + X % 3) % 3 = X % 3 := by omega
        have hDiv : (3 * (X' / 3) + X % 3) / 3 = X' / 3 := by omega
        rw [hMod, hDiv, ← hModY]
        exact ⟨rfl, hModX⟩
  | succ x' ih =>
    rcases y with _ | y'
    · omega
    · dsimp [FlipDigitAt] at hx hy
      rcases hx with ⟨hModX, hFlipX⟩
      rcases hy with ⟨hModY, hFlipY⟩
      rcases ih y' (X / 3) (X_mid / 3) (X' / 3) (by omega) hFlipX hFlipY with ⟨Q_mid2, hQY, hQX⟩
      refine ⟨3 * Q_mid2 + X % 3, ?_, ?_⟩
      · dsimp [FlipDigitAt]
        have hLt : X % 3 < 3 := Nat.mod_lt X (by decide)
        have hMod : (3 * Q_mid2 + X % 3) % 3 = X % 3 := by omega
        have hDiv : (3 * Q_mid2 + X % 3) / 3 = Q_mid2 := by omega
        rw [hMod, hDiv]
        exact ⟨rfl, hQY⟩
      · dsimp [FlipDigitAt]
        have hLt : X % 3 < 3 := Nat.mod_lt X (by decide)
        have hMod : (3 * Q_mid2 + X % 3) % 3 = X % 3 := by omega
        have hDiv : (3 * Q_mid2 + X % 3) / 3 = Q_mid2 := by omega
        rw [hMod, hDiv, hModX, hModY]
        exact ⟨rfl, hQX⟩

theorem evalChordOp_pair_flip_false_sound (mMax numBits X X_mid X' x y B : Nat)
    (hmMax : mMax ≤ 13) (hxy : x < y) (hy : y < mMax)
    (hFlipX : FlipDigitAt x X X_mid)
    (hFlipY : FlipDigitAt y X_mid X')
    (hNum : numBits ≤ wordK mMax X)
    (hSign : wordSign mMax X < (1 <<< numBits))
    (hK : wordK y X < numBits)
    (hFalse :
      let kBucket := wordK mMax X
      let M := binom mMax kBucket
      let m0List := (buildM0List kBucket numBits M).val
      let lo := wordK x X
      let kIdx := wordK y X
      let bitLo := Nat.shiftLeft 1 lo
      let bitK := Nat.shiftLeft 1 kIdx
      let m0Lo := lookupM0 lo m0List
      let m0K := lookupM0 kIdx m0List
      let m00 := Nat.land m0Lo m0K
      let m10 := Nat.shiftLeft m00 bitLo
      let dPlus := Nat.add bitK bitLo
      let dMinus := Nat.sub bitK bitLo
      Nat.testBit (evalChordOp (ChordOp.pair dPlus dMinus m00 m10) B) (wordBlock mMax X) = false) :
    Nat.testBit B (wordBlock mMax X) = false ∧ wordSign mMax X < (1 <<< numBits) ∨
    Nat.testBit B (wordBlock mMax X') = false ∧ wordSign mMax X' < (1 <<< numBits) := by
  dsimp at hFalse
  rw [evalChordOp_eq_raw] at hFalse
  dsimp at hFalse
  rw [testBit_lor, testBit_lor, testBit_lor,
      Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hFalse
  rcases hFalse with ⟨⟨hPlus0, hMinus0⟩, hPlus1, hMinus1⟩
  rcases flipDigitAt_comm x y X X_mid X' hxy hFlipX hFlipY with ⟨X_mid2, hFlipY2, hFlipX2⟩
  have hx : x < mMax := by omega
  have hActX : (X / 3 ^ x) % 3 ≠ 0 := active_of_flipDigitAt x X X_mid hFlipX
  have hLo_lt_K : wordK x X < wordK y X := wordK_strict_mono_of_active X hActX hxy
  have hLo : wordK x X < numBits := by omega
  let bitLo := Nat.shiftLeft 1 (wordK x X)
  let bitK := Nat.shiftLeft 1 (wordK y X)
  let dPlus := bitK + bitLo
  let dMinus := bitK - bitLo
  have hBitLo_eq : (1 <<< wordK x X) = bitLo := rfl
  have hBitK_eq : (1 <<< wordK y X) = bitK := rfl
  have hBitLo_pos : 0 < bitLo := by
    change 0 < 1 <<< wordK x X
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.two_pow_pos _
  have hBitLo_lt_BitK : bitLo < bitK := by
    change (1 <<< wordK x X) < (1 <<< wordK y X)
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by decide) hLo_lt_K
  have hKx_mid : wordK x X_mid = wordK x X := (wordK_eq_of_flipDigitAt x x X X_mid hFlipX).symm
  have hKy_mid : wordK y X_mid = wordK y X := (wordK_eq_of_flipDigitAt y x X X_mid hFlipX).symm
  have hKm_mid : wordK mMax X_mid = wordK mMax X := (wordK_eq_of_flipDigitAt mMax x X X_mid hFlipX).symm
  have hKx' : wordK x X' = wordK x X := by
    rw [← wordK_eq_of_flipDigitAt x y X_mid X' hFlipY, hKx_mid]
  have hKy' : wordK y X' = wordK y X := by
    rw [← wordK_eq_of_flipDigitAt y y X_mid X' hFlipY, hKy_mid]
  have hKm' : wordK mMax X' = wordK mMax X := by
    rw [← wordK_eq_of_flipDigitAt mMax y X_mid X' hFlipY, hKm_mid]
  have hKx_mid2 : wordK x X_mid2 = wordK x X := (wordK_eq_of_flipDigitAt x y X X_mid2 hFlipY2).symm
  have hKy_mid2 : wordK y X_mid2 = wordK y X := (wordK_eq_of_flipDigitAt y y X X_mid2 hFlipY2).symm
  have hKm_mid2 : wordK mMax X_mid2 = wordK mMax X := (wordK_eq_of_flipDigitAt mMax y X X_mid2 hFlipY2).symm
  have hSign_mid : wordSign mMax X_mid < (1 <<< numBits) :=
    wordSign_lt_of_flipDigitAt x mMax X X_mid numBits hx hFlipX hLo hSign
  have hSign' : wordSign mMax X' < (1 <<< numBits) :=
    wordSign_lt_of_flipDigitAt y mMax X_mid X' numBits hy hFlipY (by rw [hKy_mid]; exact hK) hSign_mid
  have hSign_mid2 : wordSign mMax X_mid2 < (1 <<< numBits) :=
    wordSign_lt_of_flipDigitAt y mMax X X_mid2 numBits hy hFlipY2 hK hSign
  have hm00_of : ∀ (W : Nat),
      wordK x W = wordK x X →
      wordK y W = wordK y X →
      wordK mMax W = wordK mMax X →
      wordSign mMax W < (1 <<< numBits) →
      Nat.testBit (wordBlock mMax W) (wordK x X) = false →
      Nat.testBit (wordBlock mMax W) (wordK y X) = false →
      Nat.testBit
        (Nat.land
          (lookupM0 (wordK x X) (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val)
          (lookupM0 (wordK y X) (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val))
        (wordBlock mMax W) = true := by
    intro W hWx hWy hWm hWSign hBx hBy
    rw [testBit_land, ← hWx, ← hWy, ← hWm]
    have h1 : Nat.testBit (lookupM0 (wordK x W) (buildM0List (wordK mMax W) numBits (binom mMax (wordK mMax W))).val)
        (wordBlock mMax W) = true := by
      apply testBit_lookupM0_wordBlock mMax numBits W x hmMax
      · rw [hWm]; exact hNum
      · exact hWSign
      · rw [hWx]; exact hLo
      · rw [hWx]; exact hBx
    have h2 : Nat.testBit (lookupM0 (wordK y W) (buildM0List (wordK mMax W) numBits (binom mMax (wordK mMax W))).val)
        (wordBlock mMax W) = true := by
      apply testBit_lookupM0_wordBlock mMax numBits W y hmMax
      · rw [hWm]; exact hNum
      · exact hWSign
      · rw [hWy]; exact hK
      · rw [hWy]; exact hBy
    rw [h1, h2]; rfl
  rcases wordBlock_of_flipDigitAt x mMax X X_mid hx hFlipX with ⟨hBx0, _, hEqX1⟩ | ⟨_, hBmid_x0, hEqX2⟩ <;>
  rcases wordBlock_of_flipDigitAt y mMax X_mid X' hy hFlipY with ⟨hBmid_y0, _, hEqY1⟩ | ⟨_, hBx'_y0, hEqY2⟩
  · -- Case 1A: X -> X_mid (+ bitLo), X_mid -> X' (+ bitK)
    rw [hKy_mid] at hBmid_y0 hEqY1
    rw [hBitLo_eq] at hEqX1
    rw [hBitK_eq] at hEqY1
    rcases wordBlock_of_flipDigitAt y mMax X X_mid2 hy hFlipY2 with ⟨hBy0, _, hEqY2_1⟩ | ⟨_, _, hEqY2_2⟩
    · have hm00 := hm00_of X rfl rfl rfl hSign hBx0 hBy0
      have hAdd : dPlus + wordBlock mMax X = wordBlock mMax X' := by
        dsimp [dPlus]; omega
      rw [testBit_land, hm00, Bool.and_true, testBit_land, testBit_shiftRight] at hPlus0
      change (Nat.testBit B (wordBlock mMax X) && Nat.testBit B (dPlus + wordBlock mMax X)) = false at hPlus0
      rw [hAdd] at hPlus0
      cases hBX : Nat.testBit B (wordBlock mMax X) with
      | false => exact Or.inl ⟨rfl, hSign⟩
      | true => rw [hBX, Bool.true_and] at hPlus0; exact Or.inr ⟨hPlus0, hSign'⟩
    · rw [hBitK_eq] at hEqY2_2
      rcases wordBlock_of_flipDigitAt x mMax X_mid2 X' hx hFlipX2 with ⟨_, _, hEqX2_1⟩ | ⟨_, _, hEqX2_2⟩
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_1; omega
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_2; omega
  · -- Case 1B: X -> X_mid (+ bitLo), X_mid -> X' (- bitK)
    rw [hKy_mid] at hBx'_y0 hEqY2
    rw [hBitLo_eq] at hEqX1
    rw [hBitK_eq] at hEqY2
    rcases wordBlock_of_flipDigitAt y mMax X X_mid2 hy hFlipY2 with ⟨_, _, hEqY2_1⟩ | ⟨_, hBmid2_y0, hEqY2_2⟩
    · rw [hBitK_eq] at hEqY2_1
      rcases wordBlock_of_flipDigitAt x mMax X_mid2 X' hx hFlipX2 with ⟨_, _, hEqX2_1⟩ | ⟨_, _, hEqX2_2⟩
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_1; omega
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_2; omega
    · rw [hBitK_eq] at hEqY2_2
      rcases wordBlock_of_flipDigitAt x mMax X_mid2 X' hx hFlipX2 with ⟨hBmid2_x0, _, hEqX2_1⟩ | ⟨_, _, hEqX2_2⟩
      · rw [hKx_mid2] at hBmid2_x0
        rw [hKx_mid2, hBitLo_eq] at hEqX2_1
        have hm00 := hm00_of X_mid2 hKx_mid2 hKy_mid2 hKm_mid2 hSign_mid2 hBmid2_x0 hBmid2_y0
        have hLeMinus : dMinus ≤ wordBlock mMax X := by dsimp [dMinus]; omega
        have hSubMinus : wordBlock mMax X - dMinus = wordBlock mMax X' := by dsimp [dMinus]; omega
        have hLeLo : bitLo ≤ wordBlock mMax X' := by omega
        have hSubLo : wordBlock mMax X' - bitLo = wordBlock mMax X_mid2 := by omega
        have hAddMinus : dMinus + wordBlock mMax X' = wordBlock mMax X := by dsimp [dMinus]; omega
        rw [testBit_shiftLeft, decide_eq_true hLeMinus, Bool.true_and, hSubMinus,
            testBit_land, testBit_shiftLeft, decide_eq_true hLeLo, Bool.true_and, hSubLo,
            hm00, Bool.and_true, testBit_land, testBit_shiftRight, hAddMinus] at hMinus1
        cases hBX' : Nat.testBit B (wordBlock mMax X') with
        | false => exact Or.inr ⟨rfl, hSign'⟩
        | true => rw [hBX', Bool.true_and] at hMinus1; exact Or.inl ⟨hMinus1, hSign⟩
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_2; omega
  · -- Case 2A: X -> X_mid (- bitLo), X_mid -> X' (+ bitK)
    rw [hKy_mid] at hBmid_y0 hEqY1
    rw [hBitLo_eq] at hEqX2
    rw [hBitK_eq] at hEqY1
    have hm00 := hm00_of X_mid hKx_mid hKy_mid hKm_mid hSign_mid hBmid_x0 hBmid_y0
    have hLeLo : bitLo ≤ wordBlock mMax X := by omega
    have hSubLo : wordBlock mMax X - bitLo = wordBlock mMax X_mid := by omega
    have hAddMinus : dMinus + wordBlock mMax X = wordBlock mMax X' := by dsimp [dMinus]; omega
    rw [testBit_land, testBit_shiftLeft, decide_eq_true hLeLo, Bool.true_and, hSubLo,
        hm00, Bool.and_true, testBit_land, testBit_shiftRight, hAddMinus] at hMinus0
    cases hBX : Nat.testBit B (wordBlock mMax X) with
    | false => exact Or.inl ⟨rfl, hSign⟩
    | true => rw [hBX, Bool.true_and] at hMinus0; exact Or.inr ⟨hMinus0, hSign'⟩
  · -- Case 2B: X -> X_mid (- bitLo), X_mid -> X' (- bitK)
    rw [hKy_mid] at hBx'_y0 hEqY2
    rw [hBitLo_eq] at hEqX2
    rw [hBitK_eq] at hEqY2
    rcases wordBlock_of_flipDigitAt x mMax X_mid2 X' hx hFlipX2 with ⟨_, _, hEqX2_1⟩ | ⟨_, hBx'_x0, hEqX2_2⟩
    · rw [hKx_mid2, hBitLo_eq] at hEqX2_1
      rcases wordBlock_of_flipDigitAt y mMax X X_mid2 hy hFlipY2 with ⟨_, _, hEqY2_1⟩ | ⟨_, _, hEqY2_2⟩
      · rw [hBitK_eq] at hEqY2_1; omega
      · rw [hBitK_eq] at hEqY2_2; omega
    · rw [hKx_mid2] at hBx'_x0
      rw [hKx_mid2, hBitLo_eq] at hEqX2_2
      have hm00 := hm00_of X' hKx' hKy' hKm' hSign' hBx'_x0 hBx'_y0
      have hLePlus : dPlus ≤ wordBlock mMax X := by dsimp [dPlus]; omega
      have hSubPlus : wordBlock mMax X - dPlus = wordBlock mMax X' := by dsimp [dPlus]; omega
      have hAddPlus : dPlus + wordBlock mMax X' = wordBlock mMax X := by dsimp [dPlus]; omega
      rw [testBit_shiftLeft, decide_eq_true hLePlus, Bool.true_and, hSubPlus,
          testBit_land, hm00, Bool.and_true, testBit_land, testBit_shiftRight, hAddPlus] at hPlus1
      cases hBX' : Nat.testBit B (wordBlock mMax X') with
      | false => exact Or.inr ⟨rfl, hSign'⟩
      | true => rw [hBX', Bool.true_and] at hPlus1; exact Or.inl ⟨hPlus1, hSign⟩

/-!
### Connecting `singleArcSwap` (`boundaryKempeSwap`) to `FlipDigitAt` on `permTraceVal`
-/

theorem permTraceVal_congr_coloring (p : Nat → Nat) (r : Nat) (b b' : Nat → Color) (k i : Nat)
    (hEq : ∀ j, i ≤ j → j < i + k → edgeDigitAt r b j = edgeDigitAt r b' j) :
    permTraceVal p r b k i = permTraceVal p r b' k i := by
  induction k generalizing i with
  | zero => rfl
  | succ k' ih =>
    dsimp [permTraceVal]
    rw [hEq i (Nat.le_refl i) (by omega),
        ih (i + 1) (fun j hj1 hj2 => hEq j (by omega) (by omega))]

theorem flipDigitAt_permTraceVal (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)))
    (r : Nat) (b b' : Nat → Color) (k i e : Nat)
    (he_lo : i ≤ e) (he_hi : e < i + k)
    (hOther : ∀ j, i ≤ j → j < i + k → j ≠ e → edgeDigitAt r b j = edgeDigitAt r b' j)
    (hFlipE : (edgeDigitAt r b e = 1 ∧ edgeDigitAt r b' e = 2) ∨
              (edgeDigitAt r b e = 2 ∧ edgeDigitAt r b' e = 1)) :
    FlipDigitAt (e - i) (permTraceVal p r b k i) (permTraceVal p r b' k i) := by
  induction k generalizing i with
  | zero => omega
  | succ k' ih =>
    dsimp [permTraceVal]
    have hd1 : p (edgeDigitAt r b i) < 3 := hp3 _ (edgeDigitAt_lt_three r b i)
    have hd2 : p (edgeDigitAt r b' i) < 3 := hp3 _ (edgeDigitAt_lt_three r b' i)
    have hMod1 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k' (i + 1)) % 3 =
        p (edgeDigitAt r b i) := by omega
    have hDiv1 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k' (i + 1)) / 3 =
        permTraceVal p r b k' (i + 1) := by omega
    have hMod2 : (p (edgeDigitAt r b' i) + 3 * permTraceVal p r b' k' (i + 1)) % 3 =
        p (edgeDigitAt r b' i) := by omega
    have hDiv2 : (p (edgeDigitAt r b' i) + 3 * permTraceVal p r b' k' (i + 1)) / 3 =
        permTraceVal p r b' k' (i + 1) := by omega
    by_cases hEq : e = i
    · subst hEq
      rw [Nat.sub_self]
      dsimp [FlipDigitAt]
      rw [hDiv1, hDiv2, hMod1, hMod2]
      refine ⟨permTraceVal_congr_coloring p r b b' k' (e + 1)
        (fun j hj1 hj2 => hOther j (by omega) (by omega) (by omega)), ?_⟩
      exact hp12 _ _ hFlipE
    · have hSub : e - i = (e - (i + 1)) + 1 := by omega
      rw [hSub]
      dsimp [FlipDigitAt]
      rw [hMod1, hMod2, hDiv1, hDiv2, hOther i (Nat.le_refl i) (by omega) (Ne.symm hEq)]
      exact ⟨rfl, ih (i + 1) (by omega) (by omega) (fun j hj1 hj2 hjNe => hOther j (by omega) (by omega) hjNe)⟩

theorem exists_mid_permTraceVal (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)))
    (r : Nat) (b b' : Nat → Color) (k i x y : Nat)
    (hx_lo : i ≤ x) (hxy : x < y) (hy_hi : y < i + k)
    (hOther : ∀ j, i ≤ j → j < i + k → j ≠ x → j ≠ y → edgeDigitAt r b j = edgeDigitAt r b' j)
    (hFlipX : (edgeDigitAt r b x = 1 ∧ edgeDigitAt r b' x = 2) ∨
              (edgeDigitAt r b x = 2 ∧ edgeDigitAt r b' x = 1))
    (hFlipY : (edgeDigitAt r b y = 1 ∧ edgeDigitAt r b' y = 2) ∨
              (edgeDigitAt r b y = 2 ∧ edgeDigitAt r b' y = 1)) :
    ∃ X_mid,
      FlipDigitAt (x - i) (permTraceVal p r b k i) X_mid ∧
      FlipDigitAt (y - i) X_mid (permTraceVal p r b' k i) := by
  induction k generalizing i with
  | zero => omega
  | succ k' ih =>
    dsimp [permTraceVal]
    have hd1 : p (edgeDigitAt r b i) < 3 := hp3 _ (edgeDigitAt_lt_three r b i)
    have hd2 : p (edgeDigitAt r b' i) < 3 := hp3 _ (edgeDigitAt_lt_three r b' i)
    have hMod1 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k' (i + 1)) % 3 =
        p (edgeDigitAt r b i) := by omega
    have hDiv1 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k' (i + 1)) / 3 =
        permTraceVal p r b k' (i + 1) := by omega
    have hMod2 : (p (edgeDigitAt r b' i) + 3 * permTraceVal p r b' k' (i + 1)) % 3 =
        p (edgeDigitAt r b' i) := by omega
    have hDiv2 : (p (edgeDigitAt r b' i) + 3 * permTraceVal p r b' k' (i + 1)) / 3 =
        permTraceVal p r b' k' (i + 1) := by omega
    by_cases hEq : x = i
    · subst hEq
      refine ⟨p (edgeDigitAt r b' x) + 3 * permTraceVal p r b k' (x + 1), ?_, ?_⟩
      · rw [Nat.sub_self]
        dsimp [FlipDigitAt]
        have hModM : (p (edgeDigitAt r b' x) + 3 * permTraceVal p r b k' (x + 1)) % 3 =
            p (edgeDigitAt r b' x) := by omega
        have hDivM : (p (edgeDigitAt r b' x) + 3 * permTraceVal p r b k' (x + 1)) / 3 =
            permTraceVal p r b k' (x + 1) := by omega
        rw [hDiv1, hDivM, hMod1, hModM]
        exact ⟨rfl, hp12 _ _ hFlipX⟩
      · have hSubY : y - x = (y - (x + 1)) + 1 := by omega
        rw [hSubY]
        dsimp [FlipDigitAt]
        have hModM : (p (edgeDigitAt r b' x) + 3 * permTraceVal p r b k' (x + 1)) % 3 =
            p (edgeDigitAt r b' x) := by omega
        have hDivM : (p (edgeDigitAt r b' x) + 3 * permTraceVal p r b k' (x + 1)) / 3 =
            permTraceVal p r b k' (x + 1) := by omega
        rw [hModM, hMod2, hDivM, hDiv2]
        refine ⟨rfl, flipDigitAt_permTraceVal p hp3 hp12 r b b' k' (x + 1) y (by omega) (by omega) ?_ hFlipY⟩
        intro j hj1 hj2 hjNeY
        exact hOther j (by omega) (by omega) (by omega) hjNeY
    · rcases ih (i + 1) (by omega) (by omega)
        (fun j hj1 hj2 hxNe hyNe => hOther j (by omega) (by omega) hxNe hyNe) with ⟨Q_mid, hQX, hQY⟩
      refine ⟨p (edgeDigitAt r b i) + 3 * Q_mid, ?_, ?_⟩
      · have hSubX : x - i = (x - (i + 1)) + 1 := by omega
        rw [hSubX]
        dsimp [FlipDigitAt]
        have hModM : (p (edgeDigitAt r b i) + 3 * Q_mid) % 3 = p (edgeDigitAt r b i) := by omega
        have hDivM : (p (edgeDigitAt r b i) + 3 * Q_mid) / 3 = Q_mid := by omega
        rw [hMod1, hModM, hDiv1, hDivM]
        exact ⟨rfl, hQX⟩
      · have hSubY : y - i = (y - (i + 1)) + 1 := by omega
        rw [hSubY]
        dsimp [FlipDigitAt]
        have hModM : (p (edgeDigitAt r b i) + 3 * Q_mid) % 3 = p (edgeDigitAt r b i) := by omega
        have hDivM : (p (edgeDigitAt r b i) + 3 * Q_mid) / 3 = Q_mid := by omega
        rw [hModM, hMod2, hDivM, hDiv2, hOther i (Nat.le_refl i) (by omega) (Ne.symm hEq) (by omega)]
        exact ⟨rfl, hQY⟩

def singleArcSwap (x y v : Nat) : Bool :=
  decide (x < v ∧ v ≤ y)

theorem singleArcSwap_valid (c : Configuration) (b : BoundaryColoring c)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (x y : Nat)
    (hxy : x < y) (hy : y < c.ringSize)
    (hClosed : ∀ u < c.ringSize, ∀ w < c.ringSize,
      partEquiv equiv_ab equiv_cd u w → ((x < u ∧ u ≤ y) ↔ (x < w ∧ w ≤ y))) :
    IsValidSwapChoice c b theta1 equiv_ab equiv_cd (singleArcSwap x y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    dsimp [singleArcSwap] at hi
    have := of_decide_eq_true hi
    omega
  · intro i hi j hj hab
    dsimp [singleArcSwap]
    have h_iff := hClosed i hi j hj (Or.inl hab)
    cases h1 : decide (x < i ∧ i ≤ y) <;> cases h2 : decide (x < j ∧ j ≤ y)
    · rfl
    · exfalso; exact of_decide_eq_false h1 (h_iff.mpr (of_decide_eq_true h2))
    · exfalso; exact of_decide_eq_false h2 (h_iff.mp (of_decide_eq_true h1))
    · rfl
  · intro i hi j hj hcd
    dsimp [singleArcSwap]
    have h_iff := hClosed i hi j hj (Or.inr hcd)
    cases h1 : decide (x < i ∧ i ≤ y) <;> cases h2 : decide (x < j ∧ j ≤ y)
    · rfl
    · exfalso; exact of_decide_eq_false h1 (h_iff.mpr (of_decide_eq_true h2))
    · exfalso; exact of_decide_eq_false h2 (h_iff.mp (of_decide_eq_true h1))
    · rfl

private theorem color_swap_digit_flip (c1 c2 : Color) (s1 s2 : Bool)
    (hXor : Bool.xor s1 s2 = true)
    (hDig : (let diff := c1.toNat ^^^ c2.toNat; if diff > 0 then diff - 1 else 0) = 1 ∨
            (let diff := c1.toNat ^^^ c2.toNat; if diff > 0 then diff - 1 else 0) = 2) :
    let d := let diff := c1.toNat ^^^ c2.toNat; if diff > 0 then diff - 1 else 0
    let c1' := if s1 then theta1.swap c1 else c1
    let c2' := if s2 then theta1.swap c2 else c2
    let d' := let diff := c1'.toNat ^^^ c2'.toNat; if diff > 0 then diff - 1 else 0
    (d = 1 ∧ d' = 2) ∨ (d = 2 ∧ d' = 1) := by
  revert hXor hDig
  cases c1 <;> cases c2 <;> cases s1 <;> cases s2 <;> decide

theorem edgeDigitAt_boundaryKempeSwap_of_edgeXor_true
    (c : Configuration) (b : BoundaryColoring c) (S : Nat → Bool) (e : Nat)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (he : e < c.ringSize)
    (hDiff : theta1Pair b (e % c.ringSize) ≠ theta1Pair b ((e + 1) % c.ringSize))
    (hXor : edgeXor c.ringSize S e = true) :
    (edgeDigitAt c.ringSize b e = 1 ∧
      edgeDigitAt c.ringSize (boundaryKempeSwap c b theta1 S) e = 2) ∨
    (edgeDigitAt c.ringSize b e = 2 ∧
      edgeDigitAt c.ringSize (boundaryKempeSwap c b theta1 S) e = 1) := by
  have hDig := transition_edgeDigit_one_or_two c b h_ring hb e he hDiff
  exact color_swap_digit_flip (b e) (b ((e + 1) % c.ringSize)) (S e) (S ((e + 1) % c.ringSize)) hXor hDig

theorem edgeDigitAt_singleArcSwap_other (c : Configuration) (b : BoundaryColoring c)
    (x y j : Nat) (hxy : x < y) (hy : y < c.ringSize) (hj : j < c.ringSize)
    (hneX : j ≠ x) (hneY : j ≠ y) :
    edgeDigitAt c.ringSize b j =
      edgeDigitAt c.ringSize (boundaryKempeSwap c b theta1 (singleArcSwap x y)) j := by
  symm
  apply edgeDigitAt_boundaryKempeSwap_of_edgeXor_false
  dsimp [edgeXor, singleArcSwap]
  rw [inArc_edgeXor c.ringSize x y j hxy hy hj]
  exact decide_eq_false (by rintro (rfl | rfl); exact hneX rfl; exact hneY rfl)

theorem edgeDigitAt_singleArcSwap_left (c : Configuration) (b : BoundaryColoring c)
    (x y : Nat) (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (hxy : x < y) (hy : y < c.ringSize)
    (hDiffX : theta1Pair b (x % c.ringSize) ≠ theta1Pair b ((x + 1) % c.ringSize)) :
    (edgeDigitAt c.ringSize b x = 1 ∧
      edgeDigitAt c.ringSize (boundaryKempeSwap c b theta1 (singleArcSwap x y)) x = 2) ∨
    (edgeDigitAt c.ringSize b x = 2 ∧
      edgeDigitAt c.ringSize (boundaryKempeSwap c b theta1 (singleArcSwap x y)) x = 1) := by
  apply edgeDigitAt_boundaryKempeSwap_of_edgeXor_true c b (singleArcSwap x y) x h_ring hb (by omega) hDiffX
  dsimp [edgeXor, singleArcSwap]
  rw [inArc_edgeXor c.ringSize x y x hxy hy (by omega)]
  exact decide_eq_true (Or.inl rfl)

theorem edgeDigitAt_singleArcSwap_right (c : Configuration) (b : BoundaryColoring c)
    (x y : Nat) (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (hxy : x < y) (hy : y < c.ringSize)
    (hDiffY : theta1Pair b (y % c.ringSize) ≠ theta1Pair b ((y + 1) % c.ringSize)) :
    (edgeDigitAt c.ringSize b y = 1 ∧
      edgeDigitAt c.ringSize (boundaryKempeSwap c b theta1 (singleArcSwap x y)) y = 2) ∨
    (edgeDigitAt c.ringSize b y = 2 ∧
      edgeDigitAt c.ringSize (boundaryKempeSwap c b theta1 (singleArcSwap x y)) y = 1) := by
  apply edgeDigitAt_boundaryKempeSwap_of_edgeXor_true c b (singleArcSwap x y) y h_ring hb hy hDiffY
  dsimp [edgeXor, singleArcSwap]
  rw [inArc_edgeXor c.ringSize x y y hxy hy hy]
  exact decide_eq_true (Or.inr rfl)

/-!
### Projected Bucket Index `wordProj` for Unified Odd/Even `CatalanTrie` Evaluation
-/

noncomputable def wordProj (m numBits q : Nat) : Nat :=
  wordCell m q * (1 <<< wordK m q) + wordSign m q % (1 <<< numBits)

theorem wordSign_mod_lt (m numBits q : Nat) :
    wordSign m q % (1 <<< numBits) < (1 <<< numBits) := by
  apply Nat.mod_lt
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.two_pow_pos numBits

theorem testBit_mod_shiftLeft_one (s numBits a : Nat) (ha : a < numBits) :
    Nat.testBit (s % (1 <<< numBits)) a = Nat.testBit s a := by
  have h1 : 1 <<< numBits = 2 ^ numBits := by rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [h1, Nat.testBit_mod_two_pow, decide_eq_true ha, Bool.true_and]

theorem testBit_wordProj_eq_wordSign (m numBits q a : Nat)
    (hNum : numBits ≤ wordK m q) (ha : a < numBits) :
    Nat.testBit (wordProj m numBits q) a = Nat.testBit (wordSign m q) a := by
  dsimp [wordProj]
  rw [testBit_cell_mul_pow2_add_sign a (wordK m q) (wordCell m q)
        (wordSign m q % (1 <<< numBits)) (by omega),
      testBit_mod_shiftLeft_one (wordSign m q) numBits a ha]

theorem testBit_lookupM0_wordProj (mMax numBits X x : Nat)
    (hmMax : mMax ≤ 13)
    (hNum : numBits ≤ wordK mMax X)
    (ha : wordK x X < numBits)
    (hBit : Nat.testBit (wordProj mMax numBits X) (wordK x X) = false) :
    let kBucket := wordK mMax X
    let M := binom mMax kBucket
    let m0List := (buildM0List kBucket numBits M).val
    Nat.testBit (lookupM0 (wordK x X) m0List) (wordProj mMax numBits X) = true := by
  dsimp
  rw [lookupM0_buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X)) (wordK x X) ha]
  have hBitMod : Nat.testBit (wordSign mMax X % (1 <<< numBits)) (wordK x X) = false := by
    rw [testBit_mod_shiftLeft_one _ numBits _ ha, ← testBit_wordProj_eq_wordSign mMax numBits X _ hNum ha]
    exact hBit
  exact testBit_makeSingleBitMask0_of_bit_false (wordK mMax X) numBits
    (binom mMax (wordK mMax X)) (wordK x X) (wordCell mMax X) (wordSign mMax X % (1 <<< numBits))
    hNum ha (wordCell_lt mMax X hmMax) (wordSign_mod_lt mMax numBits X) hBitMod

theorem wordProj_of_flipDigitAt_eq (e m numBits X X' : Nat)
    (he : e < m) (hFlip : FlipDigitAt e X X') (hEqK : wordK e X = numBits) :
    wordProj m numBits X' = wordProj m numBits X := by
  dsimp [wordProj]
  rw [← wordCell_eq_of_flipDigitAt m e X X' hFlip,
      ← wordK_eq_of_flipDigitAt m e X X' hFlip]
  rcases wordSign_of_flipDigitAt e m X X' he hFlip with ⟨_, _, hEq⟩ | ⟨_, _, hEq⟩
  · rw [hEq, hEqK, Nat.add_mod_right]
  · rw [hEq, hEqK, Nat.add_mod_right]

theorem mod_add_eq_of_lt (s d N : Nat) (hLt : s % N + d < N) :
    (s + d) % N = s % N + d := by
  have hN : 0 < N := by omega
  have h1 : s + d = (s % N + d) + N * (s / N) := by
    have := (Nat.div_add_mod s N).symm
    omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hLt]

theorem wordProj_of_flipDigitAt_lt (e m numBits X X' : Nat)
    (he : e < m) (hFlip : FlipDigitAt e X X')
    (hNum : numBits ≤ wordK m X) (ha : wordK e X < numBits) :
    let a := wordK e X
    (Nat.testBit (wordProj m numBits X) a = false ∧
     Nat.testBit (wordProj m numBits X') a = true ∧
     wordProj m numBits X' = wordProj m numBits X + (1 <<< a)) ∨
    (Nat.testBit (wordProj m numBits X) a = true ∧
     Nat.testBit (wordProj m numBits X') a = false ∧
     wordProj m numBits X = wordProj m numBits X' + (1 <<< a)) := by
  have hCell := wordCell_eq_of_flipDigitAt m e X X' hFlip
  have hKm := wordK_eq_of_flipDigitAt m e X X' hFlip
  have hKe := wordK_eq_of_flipDigitAt e e X X' hFlip
  have hNum' : numBits ≤ wordK m X' := by rw [← hKm]; exact hNum
  rcases wordSign_of_flipDigitAt e m X X' he hFlip with ⟨hS0, hS1, hEq⟩ | ⟨hS1, hS0, hEq⟩
  · left
    have hP0 : Nat.testBit (wordProj m numBits X) (wordK e X) = false := by
      rw [testBit_wordProj_eq_wordSign m numBits X _ hNum ha]; exact hS0
    have hP1 : Nat.testBit (wordProj m numBits X') (wordK e X) = true := by
      rw [testBit_wordProj_eq_wordSign m numBits X' _ hNum' ha]; exact hS1
    have hModBit : Nat.testBit (wordSign m X % (1 <<< numBits)) (wordK e X) = false := by
      rw [testBit_mod_shiftLeft_one _ numBits _ ha]; exact hS0
    have hAddLt := add_two_pow_lt_of_testBit_false (wordSign m X % (1 <<< numBits)) (wordK e X) numBits
      (wordSign_mod_lt m numBits X) ha hModBit
    have hModEq : wordSign m X' % (1 <<< numBits) = wordSign m X % (1 <<< numBits) + (1 <<< wordK e X) := by
      rw [hEq]
      exact mod_add_eq_of_lt (wordSign m X) (1 <<< wordK e X) (1 <<< numBits) hAddLt
    refine ⟨hP0, hP1, ?_⟩
    dsimp [wordProj]
    rw [← hCell, ← hKm, hModEq, Nat.add_assoc]
  · right
    have hP1 : Nat.testBit (wordProj m numBits X) (wordK e X) = true := by
      rw [testBit_wordProj_eq_wordSign m numBits X _ hNum ha]; exact hS1
    have hP0 : Nat.testBit (wordProj m numBits X') (wordK e X) = false := by
      rw [testBit_wordProj_eq_wordSign m numBits X' _ hNum' ha]; exact hS0
    have hModBit : Nat.testBit (wordSign m X' % (1 <<< numBits)) (wordK e X) = false := by
      rw [testBit_mod_shiftLeft_one _ numBits _ ha]; exact hS0
    have hAddLt := add_two_pow_lt_of_testBit_false (wordSign m X' % (1 <<< numBits)) (wordK e X) numBits
      (wordSign_mod_lt m numBits X') ha hModBit
    have hModEq : wordSign m X % (1 <<< numBits) = wordSign m X' % (1 <<< numBits) + (1 <<< wordK e X) := by
      rw [hEq]
      exact mod_add_eq_of_lt (wordSign m X') (1 <<< wordK e X) (1 <<< numBits) hAddLt
    refine ⟨hP1, hP0, ?_⟩
    dsimp [wordProj]
    rw [← hCell, ← hKm, hModEq, Nat.add_assoc]

theorem evalChordOp_last_proj_false_sound (mMax numBits X X' x B : Nat)
    (hmMax : mMax ≤ 13) (hx : x < mMax)
    (hFlip : FlipDigitAt x X X')
    (hNum : numBits ≤ wordK mMax X)
    (hLo : wordK x X < numBits)
    (hFalse :
      let kBucket := wordK mMax X
      let M := binom mMax kBucket
      let m0List := (buildM0List kBucket numBits M).val
      let lo := wordK x X
      let bitLo := Nat.shiftLeft 1 lo
      let m0Lo := lookupM0 lo m0List
      Nat.testBit (evalChordOp (ChordOp.last bitLo m0Lo) B) (wordProj mMax numBits X) = false) :
    Nat.testBit B (wordProj mMax numBits X) = false ∨
    Nat.testBit B (wordProj mMax numBits X') = false := by
  dsimp at hFalse
  rw [evalChordOp_eq_raw] at hFalse
  dsimp at hFalse
  rw [testBit_lor, Bool.or_eq_false_iff] at hFalse
  rcases hFalse with ⟨hm0, hm1⟩
  rcases wordProj_of_flipDigitAt_lt x mMax numBits X X' hx hFlip hNum hLo with
    ⟨hBit0, _, hEq'⟩ | ⟨_, hBit0', hEq⟩
  · have hm0Lo : Nat.testBit (lookupM0 (wordK x X) (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val)
        (wordProj mMax numBits X) = true :=
      testBit_lookupM0_wordProj mMax numBits X x hmMax hNum hLo hBit0
    rw [testBit_land, hm0Lo, Bool.and_true, testBit_land, testBit_shiftRight,
        Nat.add_comm (Nat.shiftLeft 1 (wordK x X)) (wordProj mMax numBits X)] at hm0
    change (Nat.testBit B (wordProj mMax numBits X) &&
      Nat.testBit B (wordProj mMax numBits X + (1 <<< wordK x X))) = false at hm0
    rw [← hEq'] at hm0
    cases hBX : Nat.testBit B (wordProj mMax numBits X) with
    | false => exact Or.inl rfl
    | true => rw [hBX, Bool.true_and] at hm0; exact Or.inr hm0
  · have hK_x : wordK x X = wordK x X' := wordK_eq_of_flipDigitAt x x X X' hFlip
    have hK_m : wordK mMax X = wordK mMax X' := wordK_eq_of_flipDigitAt mMax x X X' hFlip
    have hm0Lo' : Nat.testBit (lookupM0 (wordK x X) (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val)
        (wordProj mMax numBits X') = true := by
      rw [hK_x, hK_m]
      apply testBit_lookupM0_wordProj mMax numBits X' x hmMax
      · rw [← hK_m]; exact hNum
      · rw [← hK_x]; exact hLo
      · rw [← hK_x]; exact hBit0'
    have hLe : Nat.shiftLeft 1 (wordK x X) ≤ wordProj mMax numBits X := by
      change (1 <<< wordK x X) ≤ wordProj mMax numBits X
      rw [hEq]; exact Nat.le_add_left _ _
    have hSub : wordProj mMax numBits X - Nat.shiftLeft 1 (wordK x X) = wordProj mMax numBits X' := by
      change wordProj mMax numBits X - (1 <<< wordK x X) = wordProj mMax numBits X'
      rw [hEq]; exact Nat.add_sub_cancel _ _
    rw [testBit_shiftLeft, decide_eq_true hLe, Bool.true_and, hSub,
        testBit_land, hm0Lo', Bool.and_true, testBit_land, testBit_shiftRight,
        Nat.add_comm (Nat.shiftLeft 1 (wordK x X)) (wordProj mMax numBits X')] at hm1
    change (Nat.testBit B (wordProj mMax numBits X') &&
      Nat.testBit B (wordProj mMax numBits X' + (1 <<< wordK x X))) = false at hm1
    rw [← hEq] at hm1
    cases hBX' : Nat.testBit B (wordProj mMax numBits X') with
    | false => exact Or.inr rfl
    | true => rw [hBX', Bool.true_and] at hm1; exact Or.inl hm1

theorem evalChordOp_pair_proj_false_sound (mMax numBits X X_mid X' x y B : Nat)
    (hmMax : mMax ≤ 13) (hxy : x < y) (hy : y < mMax)
    (hFlipX : FlipDigitAt x X X_mid)
    (hFlipY : FlipDigitAt y X_mid X')
    (hNum : numBits ≤ wordK mMax X)
    (hK : wordK y X < numBits)
    (hFalse :
      let kBucket := wordK mMax X
      let M := binom mMax kBucket
      let m0List := (buildM0List kBucket numBits M).val
      let lo := wordK x X
      let kIdx := wordK y X
      let bitLo := Nat.shiftLeft 1 lo
      let bitK := Nat.shiftLeft 1 kIdx
      let m0Lo := lookupM0 lo m0List
      let m0K := lookupM0 kIdx m0List
      let m00 := Nat.land m0Lo m0K
      let m10 := Nat.shiftLeft m00 bitLo
      let dPlus := Nat.add bitK bitLo
      let dMinus := Nat.sub bitK bitLo
      Nat.testBit (evalChordOp (ChordOp.pair dPlus dMinus m00 m10) B) (wordProj mMax numBits X) = false) :
    Nat.testBit B (wordProj mMax numBits X) = false ∨
    Nat.testBit B (wordProj mMax numBits X') = false := by
  dsimp at hFalse
  rw [evalChordOp_eq_raw] at hFalse
  dsimp at hFalse
  rw [testBit_lor, testBit_lor, testBit_lor,
      Bool.or_eq_false_iff, Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hFalse
  rcases hFalse with ⟨⟨hPlus0, hMinus0⟩, hPlus1, hMinus1⟩
  rcases flipDigitAt_comm x y X X_mid X' hxy hFlipX hFlipY with ⟨X_mid2, hFlipY2, hFlipX2⟩
  have hx : x < mMax := by omega
  have hActX : (X / 3 ^ x) % 3 ≠ 0 := active_of_flipDigitAt x X X_mid hFlipX
  have hLo_lt_K : wordK x X < wordK y X := wordK_strict_mono_of_active X hActX hxy
  have hLo : wordK x X < numBits := by omega
  let bitLo := Nat.shiftLeft 1 (wordK x X)
  let bitK := Nat.shiftLeft 1 (wordK y X)
  let dPlus := bitK + bitLo
  let dMinus := bitK - bitLo
  have hBitLo_eq : (1 <<< wordK x X) = bitLo := rfl
  have hBitK_eq : (1 <<< wordK y X) = bitK := rfl
  have hBitLo_pos : 0 < bitLo := by
    change 0 < 1 <<< wordK x X
    rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.two_pow_pos _
  have hBitLo_lt_BitK : bitLo < bitK := by
    change (1 <<< wordK x X) < (1 <<< wordK y X)
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by decide) hLo_lt_K
  have hKx_mid : wordK x X_mid = wordK x X := (wordK_eq_of_flipDigitAt x x X X_mid hFlipX).symm
  have hKy_mid : wordK y X_mid = wordK y X := (wordK_eq_of_flipDigitAt y x X X_mid hFlipX).symm
  have hKm_mid : wordK mMax X_mid = wordK mMax X := (wordK_eq_of_flipDigitAt mMax x X X_mid hFlipX).symm
  have hKx' : wordK x X' = wordK x X := by
    rw [← wordK_eq_of_flipDigitAt x y X_mid X' hFlipY, hKx_mid]
  have hKy' : wordK y X' = wordK y X := by
    rw [← wordK_eq_of_flipDigitAt y y X_mid X' hFlipY, hKy_mid]
  have hKm' : wordK mMax X' = wordK mMax X := by
    rw [← wordK_eq_of_flipDigitAt mMax y X_mid X' hFlipY, hKm_mid]
  have hKx_mid2 : wordK x X_mid2 = wordK x X := (wordK_eq_of_flipDigitAt x y X X_mid2 hFlipY2).symm
  have hKy_mid2 : wordK y X_mid2 = wordK y X := (wordK_eq_of_flipDigitAt y y X X_mid2 hFlipY2).symm
  have hKm_mid2 : wordK mMax X_mid2 = wordK mMax X := (wordK_eq_of_flipDigitAt mMax y X X_mid2 hFlipY2).symm
  have hm00_of : ∀ (W : Nat),
      wordK x W = wordK x X →
      wordK y W = wordK y X →
      wordK mMax W = wordK mMax X →
      Nat.testBit (wordProj mMax numBits W) (wordK x X) = false →
      Nat.testBit (wordProj mMax numBits W) (wordK y X) = false →
      Nat.testBit
        (Nat.land
          (lookupM0 (wordK x X) (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val)
          (lookupM0 (wordK y X) (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val))
        (wordProj mMax numBits W) = true := by
    intro W hWx hWy hWm hBx hBy
    rw [testBit_land, ← hWx, ← hWy, ← hWm]
    have h1 : Nat.testBit (lookupM0 (wordK x W) (buildM0List (wordK mMax W) numBits (binom mMax (wordK mMax W))).val)
        (wordProj mMax numBits W) = true := by
      apply testBit_lookupM0_wordProj mMax numBits W x hmMax
      · rw [hWm]; exact hNum
      · rw [hWx]; exact hLo
      · rw [hWx]; exact hBx
    have h2 : Nat.testBit (lookupM0 (wordK y W) (buildM0List (wordK mMax W) numBits (binom mMax (wordK mMax W))).val)
        (wordProj mMax numBits W) = true := by
      apply testBit_lookupM0_wordProj mMax numBits W y hmMax
      · rw [hWm]; exact hNum
      · rw [hWy]; exact hK
      · rw [hWy]; exact hBy
    rw [h1, h2]; rfl
  have hNum_mid : numBits ≤ wordK mMax X_mid := by rw [hKm_mid]; exact hNum
  have hNum_mid2 : numBits ≤ wordK mMax X_mid2 := by rw [hKm_mid2]; exact hNum
  have hK_mid : wordK y X_mid < numBits := by rw [hKy_mid]; exact hK
  have hLo_mid2 : wordK x X_mid2 < numBits := by rw [hKx_mid2]; exact hLo
  rcases wordProj_of_flipDigitAt_lt x mMax numBits X X_mid hx hFlipX hNum hLo with
    ⟨hBx0, _, hEqX1⟩ | ⟨_, hBmid_x0, hEqX2⟩ <;>
  rcases wordProj_of_flipDigitAt_lt y mMax numBits X_mid X' hy hFlipY hNum_mid hK_mid with
    ⟨hBmid_y0, _, hEqY1⟩ | ⟨_, hBx'_y0, hEqY2⟩
  · rw [hKy_mid] at hBmid_y0 hEqY1
    rw [hBitLo_eq] at hEqX1
    rw [hBitK_eq] at hEqY1
    rcases wordProj_of_flipDigitAt_lt y mMax numBits X X_mid2 hy hFlipY2 hNum hK with
      ⟨hBy0, _, hEqY2_1⟩ | ⟨_, _, hEqY2_2⟩
    · have hm00 := hm00_of X rfl rfl rfl hBx0 hBy0
      have hAdd : dPlus + wordProj mMax numBits X = wordProj mMax numBits X' := by
        dsimp [dPlus]; omega
      rw [testBit_land, hm00, Bool.and_true, testBit_land, testBit_shiftRight] at hPlus0
      change (Nat.testBit B (wordProj mMax numBits X) &&
        Nat.testBit B (dPlus + wordProj mMax numBits X)) = false at hPlus0
      rw [hAdd] at hPlus0
      cases hBX : Nat.testBit B (wordProj mMax numBits X) with
      | false => exact Or.inl rfl
      | true => rw [hBX, Bool.true_and] at hPlus0; exact Or.inr hPlus0
    · rw [hBitK_eq] at hEqY2_2
      rcases wordProj_of_flipDigitAt_lt x mMax numBits X_mid2 X' hx hFlipX2 hNum_mid2 hLo_mid2 with
        ⟨_, _, hEqX2_1⟩ | ⟨_, _, hEqX2_2⟩
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_1; omega
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_2; omega
  · rw [hKy_mid] at hBx'_y0 hEqY2
    rw [hBitLo_eq] at hEqX1
    rw [hBitK_eq] at hEqY2
    rcases wordProj_of_flipDigitAt_lt y mMax numBits X X_mid2 hy hFlipY2 hNum hK with
      ⟨_, _, hEqY2_1⟩ | ⟨_, hBmid2_y0, hEqY2_2⟩
    · rw [hBitK_eq] at hEqY2_1
      rcases wordProj_of_flipDigitAt_lt x mMax numBits X_mid2 X' hx hFlipX2 hNum_mid2 hLo_mid2 with
        ⟨_, _, hEqX2_1⟩ | ⟨_, _, hEqX2_2⟩
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_1; omega
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_2; omega
    · rw [hBitK_eq] at hEqY2_2
      rcases wordProj_of_flipDigitAt_lt x mMax numBits X_mid2 X' hx hFlipX2 hNum_mid2 hLo_mid2 with
        ⟨hBmid2_x0, _, hEqX2_1⟩ | ⟨_, _, hEqX2_2⟩
      · rw [hKx_mid2] at hBmid2_x0
        rw [hKx_mid2, hBitLo_eq] at hEqX2_1
        have hm00 := hm00_of X_mid2 hKx_mid2 hKy_mid2 hKm_mid2 hBmid2_x0 hBmid2_y0
        have hLeMinus : dMinus ≤ wordProj mMax numBits X := by dsimp [dMinus]; omega
        have hSubMinus : wordProj mMax numBits X - dMinus = wordProj mMax numBits X' := by dsimp [dMinus]; omega
        have hLeLo : bitLo ≤ wordProj mMax numBits X' := by omega
        have hSubLo : wordProj mMax numBits X' - bitLo = wordProj mMax numBits X_mid2 := by omega
        have hAddMinus : dMinus + wordProj mMax numBits X' = wordProj mMax numBits X := by dsimp [dMinus]; omega
        rw [testBit_shiftLeft, decide_eq_true hLeMinus, Bool.true_and, hSubMinus,
            testBit_land, testBit_shiftLeft, decide_eq_true hLeLo, Bool.true_and, hSubLo,
            hm00, Bool.and_true, testBit_land, testBit_shiftRight, hAddMinus] at hMinus1
        cases hBX' : Nat.testBit B (wordProj mMax numBits X') with
        | false => exact Or.inr rfl
        | true => rw [hBX', Bool.true_and] at hMinus1; exact Or.inl hMinus1
      · rw [hKx_mid2, hBitLo_eq] at hEqX2_2; omega
  · rw [hKy_mid] at hBmid_y0 hEqY1
    rw [hBitLo_eq] at hEqX2
    rw [hBitK_eq] at hEqY1
    have hm00 := hm00_of X_mid hKx_mid hKy_mid hKm_mid hBmid_x0 hBmid_y0
    have hLeLo : bitLo ≤ wordProj mMax numBits X := by omega
    have hSubLo : wordProj mMax numBits X - bitLo = wordProj mMax numBits X_mid := by omega
    have hAddMinus : dMinus + wordProj mMax numBits X = wordProj mMax numBits X' := by dsimp [dMinus]; omega
    rw [testBit_land, testBit_shiftLeft, decide_eq_true hLeLo, Bool.true_and, hSubLo,
        hm00, Bool.and_true, testBit_land, testBit_shiftRight, hAddMinus] at hMinus0
    cases hBX : Nat.testBit B (wordProj mMax numBits X) with
    | false => exact Or.inl rfl
    | true => rw [hBX, Bool.true_and] at hMinus0; exact Or.inr hMinus0
  · rw [hKy_mid] at hBx'_y0 hEqY2
    rw [hBitLo_eq] at hEqX2
    rw [hBitK_eq] at hEqY2
    rcases wordProj_of_flipDigitAt_lt x mMax numBits X_mid2 X' hx hFlipX2 hNum_mid2 hLo_mid2 with
      ⟨_, _, hEqX2_1⟩ | ⟨_, hBx'_x0, hEqX2_2⟩
    · rw [hKx_mid2, hBitLo_eq] at hEqX2_1
      rcases wordProj_of_flipDigitAt_lt y mMax numBits X X_mid2 hy hFlipY2 hNum hK with
        ⟨_, _, hEqY2_1⟩ | ⟨_, _, hEqY2_2⟩
      · rw [hBitK_eq] at hEqY2_1; omega
      · rw [hBitK_eq] at hEqY2_2; omega
    · rw [hKx_mid2] at hBx'_x0
      rw [hKx_mid2, hBitLo_eq] at hEqX2_2
      have hm00 := hm00_of X' hKx' hKy' hKm' hBx'_x0 hBx'_y0
      have hLePlus : dPlus ≤ wordProj mMax numBits X := by dsimp [dPlus]; omega
      have hSubPlus : wordProj mMax numBits X - dPlus = wordProj mMax numBits X' := by dsimp [dPlus]; omega
      have hAddPlus : dPlus + wordProj mMax numBits X' = wordProj mMax numBits X := by dsimp [dPlus]; omega
      rw [testBit_shiftLeft, decide_eq_true hLePlus, Bool.true_and, hSubPlus,
          testBit_land, hm00, Bool.and_true, testBit_land, testBit_shiftRight, hAddPlus] at hPlus1
      cases hBX' : Nat.testBit B (wordProj mMax numBits X') with
      | false => exact Or.inr rfl
      | true => rw [hBX', Bool.true_and] at hPlus1; exact Or.inl hPlus1

/-!
### Partition Preservation & Active-Edge Counting on `IsExtractedMatching`
-/

theorem boundaryKempeSwap_preserves_partition (c : Configuration) (b : BoundaryColoring c)
    (θ : ColorPairing) (equiv_ab equiv_cd : Nat → Nat → Prop) (S : Nat → Bool)
    (hPart : IsJointPlanarRingPartition c b θ equiv_ab equiv_cd) :
    IsJointPlanarRingPartition c (boundaryKempeSwap c b θ S) θ equiv_ab equiv_cd where
  ab_refl := fun i hi h => hPart.ab_refl i hi ((boundaryKempeSwap_ab_mem c b θ S i).mp h)
  ab_symm := hPart.ab_symm
  ab_trans := hPart.ab_trans
  ab_color := fun i hi j hj h => (boundaryKempeSwap_ab_mem c b θ S i).mpr (hPart.ab_color i hi j hj h)
  cd_refl := fun i hi h => hPart.cd_refl i hi ((boundaryKempeSwap_cd_mem c b θ S i).mp h)
  cd_symm := hPart.cd_symm
  cd_trans := hPart.cd_trans
  cd_color := fun i hi j hj h => (boundaryKempeSwap_cd_mem c b θ S i).mpr (hPart.cd_color i hi j hj h)
  ab_adj := fun i hi j hj hadj hi_ab hj_ab =>
    hPart.ab_adj i hi j hj hadj
      ((boundaryKempeSwap_ab_mem c b θ S i).mp hi_ab)
      ((boundaryKempeSwap_ab_mem c b θ S j).mp hj_ab)
  cd_adj := fun i hi j hj hadj hi_cd hj_cd =>
    hPart.cd_adj i hi j hj hadj
      ((boundaryKempeSwap_cd_mem c b θ S i).mp hi_cd)
      ((boundaryKempeSwap_cd_mem c b θ S j).mp hj_cd)
  ab_noncross := hPart.ab_noncross
  cd_noncross := hPart.cd_noncross
  cross_ab_cd := hPart.cross_ab_cd
  cross_cd_ab := hPart.cross_cd_ab

theorem theta1Pair_boundaryKempeSwap (c : Configuration) (b : BoundaryColoring c) (S : Nat → Bool) :
    theta1Pair (boundaryKempeSwap c b theta1 S) = theta1Pair b := by
  funext i
  dsimp [theta1Pair, boundaryKempeSwap]
  cases S i <;> cases b i <;> rfl

theorem permTraceVal_div_pow3_mod_three (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3) (r : Nat) (b : Nat → Color) (k i e : Nat) (he : e < k) :
    (permTraceVal p r b k i / 3 ^ e) % 3 = p (edgeDigitAt r b (i + e)) := by
  induction e generalizing k i with
  | zero =>
    rcases k with _ | k'
    · omega
    · dsimp [permTraceVal]
      rw [Nat.div_one, Nat.add_zero]
      have hd : p (edgeDigitAt r b i) < 3 := hp3 _ (edgeDigitAt_lt_three r b i)
      omega
  | succ e' ih =>
    rcases k with _ | k'
    · omega
    · dsimp [permTraceVal]
      have hd : p (edgeDigitAt r b i) < 3 := hp3 _ (edgeDigitAt_lt_three r b i)
      have hDiv : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k' (i + 1)) / 3 =
          permTraceVal p r b k' (i + 1) := by omega
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul, hDiv, ih k' (i + 1) (by omega)]
      have hAdd : i + 1 + e' = i + (e' + 1) := by omega
      rw [hAdd]

theorem wordK_permTraceVal_eq_of_le (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3) (r : Nat) (b : Nat → Color) (e k1 k2 i : Nat)
    (he1 : e ≤ k1) (he2 : e ≤ k2) :
    wordK e (permTraceVal p r b k1 i) = wordK e (permTraceVal p r b k2 i) := by
  induction e generalizing k1 k2 i with
  | zero => rfl
  | succ e' ih =>
    rcases k1 with _ | k1'
    · omega
    · rcases k2 with _ | k2'
      · omega
      · dsimp [permTraceVal, wordK]
        have hd : p (edgeDigitAt r b i) < 3 := hp3 _ (edgeDigitAt_lt_three r b i)
        have hMod1 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k1' (i + 1)) % 3 =
            p (edgeDigitAt r b i) := by omega
        have hDiv1 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k1' (i + 1)) / 3 =
            permTraceVal p r b k1' (i + 1) := by omega
        have hMod2 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k2' (i + 1)) % 3 =
            p (edgeDigitAt r b i) := by omega
        have hDiv2 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k2' (i + 1)) / 3 =
            permTraceVal p r b k2' (i + 1) := by omega
        rw [hMod1, hDiv1, hMod2, hDiv2, ih k1' k2' (i + 1) (by omega) (by omega)]

theorem wordK_extractedMatching_eq (c : Configuration) (b : BoundaryColoring c)
    (E : Nat → Nat → Prop) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp0 : ∀ d < 3, p d = 0 ↔ d = 0)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    {lo hi : Nat} {m : List (Nat × Nat)}
    (hExt : IsExtractedMatching c.ringSize (theta1Pair b) E lo hi m) :
    let X_full := permTraceVal p c.ringSize b c.ringSize 0
    wordK hi X_full = wordK lo X_full + 2 * m.length := by
  intro X_full
  induction hExt with
  | nil lo _ => simp
  | skip lo hi m h_lt h_hi h_same _ ih =>
    have hlo_r : lo < c.ringSize := Nat.lt_of_lt_of_le h_lt h_hi
    rw [Nat.mod_eq_of_lt hlo_r] at h_same
    have hd0 : edgeDigitAt c.ringSize b lo = 0 :=
      (edgeDigitAt_eq_zero_iff_same_pair c b h_ring hb lo hlo_r).mpr h_same
    have hp_lo : (X_full / 3 ^ lo) % 3 = 0 := by
      dsimp [X_full]
      rw [permTraceVal_div_pow3_mod_three p hp3 c.ringSize b c.ringSize 0 lo hlo_r,
          Nat.zero_add, (hp0 _ (edgeDigitAt_lt_three c.ringSize b lo)).mpr hd0]
    have hStep : wordK (lo + 1) X_full = wordK lo X_full := by
      rw [wordK_succ_right, if_pos hp_lo, Nat.add_zero]
    omega
  | pair lo k₀ hi m1 m2 hk_ge hk_lt h_hi h_diff_lo h_diff_k0 _ _ _ ih1 ih2 =>
    have hk0_r : k₀ < c.ringSize := Nat.lt_of_lt_of_le hk_lt h_hi
    have hlo_r : lo < c.ringSize := by omega
    have hd_lo := transition_edgeDigit_one_or_two c b h_ring hb lo hlo_r h_diff_lo
    have hd_k0 := transition_edgeDigit_one_or_two c b h_ring hb k₀ hk0_r h_diff_k0
    have hp_lo : (X_full / 3 ^ lo) % 3 ≠ 0 := by
      dsimp [X_full]
      rw [permTraceVal_div_pow3_mod_three p hp3 c.ringSize b c.ringSize 0 lo hlo_r,
          Nat.zero_add]
      intro h0
      have := (hp0 _ (edgeDigitAt_lt_three c.ringSize b lo)).mp h0
      omega
    have hp_k0 : (X_full / 3 ^ k₀) % 3 ≠ 0 := by
      dsimp [X_full]
      rw [permTraceVal_div_pow3_mod_three p hp3 c.ringSize b c.ringSize 0 k₀ hk0_r,
          Nat.zero_add]
      intro h0
      have := (hp0 _ (edgeDigitAt_lt_three c.ringSize b k₀)).mp h0
      omega
    have hStepLo : wordK (lo + 1) X_full = wordK lo X_full + 1 := by
      rw [wordK_succ_right, if_neg hp_lo]
    have hStepK0 : wordK (k₀ + 1) X_full = wordK k₀ X_full + 1 := by
      rw [wordK_succ_right, if_neg hp_k0]
    simp only [List.length_cons, List.length_append]
    omega

noncomputable def mkNodeOp (twoP : Nat) (m0List : List (Nat × Nat)) (lo kIdx : Nat) : ChordOp :=
  let bitLo := Nat.shiftLeft 1 lo
  let m0Lo := lookupM0 lo m0List
  selectBool (Nat.beq kIdx (Nat.sub twoP 1))
    (ChordOp.last bitLo m0Lo)
    (let m0K := lookupM0 kIdx m0List
     let m00 := Nat.land m0Lo m0K
     let m10 := Nat.shiftLeft m00 bitLo
     let bitK := Nat.shiftLeft 1 kIdx
     let dPlus := Nat.add bitK bitLo
     let dMinus := Nat.sub bitK bitLo
     ChordOp.pair dPlus dMinus m00 m10)

theorem boundaryKempeSwap_false_id (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing) :
    boundaryKempeSwap c b θ (fun _ => false) = b := rfl

theorem boundaryKempeSwap_comp (c : Configuration) (b : BoundaryColoring c)
    (θ : ColorPairing) (S1 S2 : Nat → Bool) :
    boundaryKempeSwap c (boundaryKempeSwap c b θ S1) θ S2 =
      boundaryKempeSwap c b θ (fun v => Bool.xor (S1 v) (S2 v)) := by
  funext i
  dsimp [boundaryKempeSwap]
  cases S1 i <;> cases S2 i <;> simp [θ.swap_inv]

theorem validSwapChoice_xor (c : Configuration) (b b1 b2 : BoundaryColoring c)
    (θ : ColorPairing) (equiv_ab equiv_cd : Nat → Nat → Prop) (S1 S2 : Nat → Bool)
    (h1 : IsValidSwapChoice c b1 θ equiv_ab equiv_cd S1)
    (h2 : IsValidSwapChoice c b2 θ equiv_ab equiv_cd S2) :
    IsValidSwapChoice c b θ equiv_ab equiv_cd (fun v => Bool.xor (S1 v) (S2 v)) where
  ring_only := fun i hi => by
    cases hS1 : S1 i <;> cases hS2 : S2 i
    · rw [hS1, hS2] at hi; contradiction
    · exact h2.ring_only i hS2
    · exact h1.ring_only i hS1
    · exact h1.ring_only i hS1
  respects_ab := fun i hi j hj hab => by
    rw [h1.respects_ab i hi j hj hab, h2.respects_ab i hi j hj hab]
  respects_cd := fun i hi j hj hcd => by
    rw [h1.respects_cd i hi j hj hcd, h2.respects_cd i hi j hj hcd]

def SameActiveClass (c : Configuration) (p : Nat → Nat)
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (b b' : BoundaryColoring c) : Prop :=
  (∃ S, IsValidSwapChoice c b theta1 equiv_ab equiv_cd S ∧
        b' = boundaryKempeSwap c b theta1 S) ∧
  (∀ e,
    wordK e (permTraceVal p c.ringSize b' c.ringSize 0) =
    wordK e (permTraceVal p c.ringSize b c.ringSize 0))

theorem sameActiveClass_refl (c : Configuration) (p : Nat → Nat)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (b : BoundaryColoring c) :
    SameActiveClass c p equiv_ab equiv_cd b b :=
  ⟨⟨fun _ => false, empty_swap_is_valid c b theta1 equiv_ab equiv_cd, rfl⟩,
   fun _ => rfl⟩

theorem sameActiveClass_trans (c : Configuration) (p : Nat → Nat)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (b b1 b2 : BoundaryColoring c)
    (h1 : SameActiveClass c p equiv_ab equiv_cd b b1)
    (h2 : SameActiveClass c p equiv_ab equiv_cd b1 b2) :
    SameActiveClass c p equiv_ab equiv_cd b b2 := by
  rcases h1 with ⟨⟨S1, hS1, rfl⟩, hK1⟩
  rcases h2 with ⟨⟨S2, hS2, rfl⟩, hK2⟩
  refine ⟨⟨fun v => Bool.xor (S1 v) (S2 v),
    validSwapChoice_xor c b b (boundaryKempeSwap c b theta1 S1) theta1 equiv_ab equiv_cd S1 S2 hS1 hS2,
    boundaryKempeSwap_comp c b theta1 S1 S2⟩,
    fun e => (hK2 e).trans (hK1 e)⟩

theorem mkNodeOp_coloring_false_sound (c : Configuration) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)))
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (b : BoundaryColoring c)
    (mMax numBits twoP x y B : Nat)
    (hr : c.ringSize = mMax + 1) (hmMax : mMax ≤ 13)
    (h_ring : IsRingCycle c)
    (hb : IsValidBoundaryColoring c b)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd)
    (hxy : x < y) (hy : y < c.ringSize)
    (hDiffX : theta1Pair b (x % c.ringSize) ≠ theta1Pair b ((x + 1) % c.ringSize))
    (hDiffY : theta1Pair b (y % c.ringSize) ≠ theta1Pair b ((y + 1) % c.ringSize))
    (hClosed : ∀ u < c.ringSize, ∀ w < c.ringSize,
      partEquiv equiv_ab equiv_cd u w → ((x < u ∧ u ≤ y) ↔ (x < w ∧ w ≤ y)))
    (hNum : numBits ≤ wordK mMax (permTraceVal p c.ringSize b mMax 0))
    (hTwoP : twoP - 1 = numBits)
    (hK_le : wordK y (permTraceVal p c.ringSize b c.ringSize 0) ≤ numBits)
    (hFalse :
      let X := permTraceVal p c.ringSize b mMax 0
      let X_full := permTraceVal p c.ringSize b c.ringSize 0
      let kBucket := wordK mMax X
      let m0List := (buildM0List kBucket numBits (binom mMax kBucket)).val
      let lo := wordK x X_full
      let kIdx := wordK y X_full
      Nat.testBit (evalChordOp (mkNodeOp twoP m0List lo kIdx) B) (wordProj mMax numBits X) = false) :
    ∃ b',
      SameActiveClass c p equiv_ab equiv_cd b b' ∧
      Nat.testBit B (wordProj mMax numBits (permTraceVal p c.ringSize b' mMax 0)) = false := by
  let b_swap := boundaryKempeSwap c b theta1 (singleArcSwap x y)
  let X := permTraceVal p c.ringSize b mMax 0
  let X' := permTraceVal p c.ringSize b_swap mMax 0
  let X_full := permTraceVal p c.ringSize b c.ringSize 0
  let X'_full := permTraceVal p c.ringSize b_swap c.ringSize 0
  change wordK y X_full ≤ numBits at hK_le
  have hValidSwap : IsValidSwapChoice c b theta1 equiv_ab equiv_cd (singleArcSwap x y) :=
    singleArcSwap_valid c b equiv_ab equiv_cd x y hxy hy hClosed
  have hOther : ∀ j, 0 ≤ j → j < 0 + c.ringSize → j ≠ x → j ≠ y →
      edgeDigitAt c.ringSize b j = edgeDigitAt c.ringSize b_swap j := by
    intro j _ hj hxNe hyNe
    exact edgeDigitAt_singleArcSwap_other c b x y j hxy hy (by omega) hxNe hyNe
  have hFlipEdgeX := edgeDigitAt_singleArcSwap_left c b x y h_ring hb hxy hy hDiffX
  have hFlipEdgeY := edgeDigitAt_singleArcSwap_right c b x y h_ring hb hxy hy hDiffY
  rcases exists_mid_permTraceVal p hp3 hp12 c.ringSize b b_swap c.ringSize 0 x y
    (Nat.zero_le x) hxy (by omega) hOther hFlipEdgeX hFlipEdgeY with ⟨Q_mid, hFlipFullX, hFlipFullY⟩
  rw [Nat.sub_zero] at hFlipFullX hFlipFullY
  have hSameSwap : SameActiveClass c p equiv_ab equiv_cd b b_swap := by
    refine ⟨⟨singleArcSwap x y, hValidSwap, rfl⟩, fun e => ?_⟩
    change wordK e X'_full = wordK e X_full
    rw [← wordK_eq_of_flipDigitAt e y Q_mid X'_full hFlipFullY,
        ← wordK_eq_of_flipDigitAt e x X_full Q_mid hFlipFullX]
  have hx_lt_mMax : x < mMax := by omega
  have hKx_eq : wordK x X_full = wordK x X :=
    (wordK_permTraceVal_eq_of_le p hp3 c.ringSize b x mMax c.ringSize 0 (by omega) (by omega)).symm
  have hKm_eq : wordK mMax X_full = wordK mMax X :=
    (wordK_permTraceVal_eq_of_le p hp3 c.ringSize b mMax mMax c.ringSize 0 (by omega) (by omega)).symm
  have hActX_full : (X_full / 3 ^ x) % 3 ≠ 0 := active_of_flipDigitAt x X_full Q_mid hFlipFullX
  have hLo_lt_K : wordK x X_full < wordK y X_full := wordK_strict_mono_of_active X_full hActX_full hxy
  have hLo_lt_num : wordK x X < numBits := by omega
  change Nat.testBit (evalChordOp (mkNodeOp twoP
    (buildM0List (wordK mMax X) numBits (binom mMax (wordK mMax X))).val
    (wordK x X_full) (wordK y X_full)) B) (wordProj mMax numBits X) = false at hFalse
  unfold mkNodeOp at hFalse
  cases hBeq : Nat.beq (wordK y X_full) (Nat.sub twoP 1) with
  | true =>
    rw [hBeq] at hFalse
    dsimp at hFalse
    rw [hKx_eq] at hFalse
    have hK_eq_num : wordK y X_full = numBits := by
      have := Nat.beq_eq.mp hBeq
      change wordK y X_full = twoP - 1 at this
      omega
    by_cases hy_mMax : y = mMax
    · have hFlipX_mMax : FlipDigitAt x X X' := by
        have hF := flipDigitAt_permTraceVal p hp3 hp12 c.ringSize b b_swap mMax 0 x
          (Nat.zero_le x) (by omega)
          (fun j _ hj hxNe => hOther j (Nat.zero_le j) (by omega) hxNe (by omega))
          hFlipEdgeX
        rwa [Nat.sub_zero] at hF
      rcases evalChordOp_last_proj_false_sound mMax numBits X X' x B hmMax hx_lt_mMax
        hFlipX_mMax hNum hLo_lt_num hFalse with h0 | h1
      · exact ⟨b, sameActiveClass_refl c p equiv_ab equiv_cd b, h0⟩
      · exact ⟨b_swap, hSameSwap, h1⟩
    · have hy_lt_mMax : y < mMax := by omega
      have hKy_eq : wordK y X_full = wordK y X :=
        (wordK_permTraceVal_eq_of_le p hp3 c.ringSize b y mMax c.ringSize 0 (by omega) (by omega)).symm
      rcases exists_mid_permTraceVal p hp3 hp12 c.ringSize b b_swap mMax 0 x y
        (Nat.zero_le x) hxy (by omega)
        (fun j _ hj hxNe hyNe => hOther j (Nat.zero_le j) (by omega) hxNe hyNe)
        hFlipEdgeX hFlipEdgeY with ⟨X_mid, hFlipX_m, hFlipY_m⟩
      rw [Nat.sub_zero] at hFlipX_m hFlipY_m
      have hKy_mid : wordK y X_mid = numBits := by
        rw [← wordK_eq_of_flipDigitAt y x X X_mid hFlipX_m, ← hKy_eq, hK_eq_num]
      have hProjEq : wordProj mMax numBits X' = wordProj mMax numBits X_mid :=
        wordProj_of_flipDigitAt_eq y mMax numBits X_mid X' hy_lt_mMax hFlipY_m hKy_mid
      rcases evalChordOp_last_proj_false_sound mMax numBits X X_mid x B hmMax hx_lt_mMax
        hFlipX_m hNum hLo_lt_num hFalse with h0 | h1
      · exact ⟨b, sameActiveClass_refl c p equiv_ab equiv_cd b, h0⟩
      · rw [← hProjEq] at h1
        exact ⟨b_swap, hSameSwap, h1⟩
  | false =>
    rw [hBeq] at hFalse
    dsimp at hFalse
    have hK_ne_num : wordK y X_full ≠ numBits := by
      intro hEq
      have h1 : wordK y X_full = Nat.sub twoP 1 := by
        change wordK y X_full = twoP - 1; omega
      have h2 : Nat.beq (wordK y X_full) (Nat.sub twoP 1) = true := Nat.beq_eq.mpr h1
      rw [hBeq] at h2; contradiction
    have hK_lt_num : wordK y X_full < numBits := by omega
    rcases (by omega : y < mMax ∨ y = mMax) with hy_lt_mMax | hy_eq
    · have hKy_eq : wordK y X_full = wordK y X :=
        (wordK_permTraceVal_eq_of_le p hp3 c.ringSize b y mMax c.ringSize 0 (by omega) (by omega)).symm
      rw [hKx_eq, hKy_eq] at hFalse
      rcases exists_mid_permTraceVal p hp3 hp12 c.ringSize b b_swap mMax 0 x y
        (Nat.zero_le x) hxy (by omega)
        (fun j _ hj hxNe hyNe => hOther j (Nat.zero_le j) (by omega) hxNe hyNe)
        hFlipEdgeX hFlipEdgeY with ⟨X_mid, hFlipX_m, hFlipY_m⟩
      rw [Nat.sub_zero] at hFlipX_m hFlipY_m
      rcases evalChordOp_pair_proj_false_sound mMax numBits X X_mid X' x y B hmMax hxy hy_lt_mMax
        hFlipX_m hFlipY_m hNum (by rw [← hKy_eq]; exact hK_lt_num) hFalse with h0 | h1
      · exact ⟨b, sameActiveClass_refl c p equiv_ab equiv_cd b, h0⟩
      · exact ⟨b_swap, hSameSwap, h1⟩
    · exfalso
      rw [hy_eq, hKm_eq] at hK_lt_num
      change numBits ≤ wordK mMax X at hNum
      omega

theorem mkNodeOp_sameActiveClass_step (c : Configuration) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)))
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (b b_child : BoundaryColoring c)
    (mMax numBits twoP x y B : Nat)
    (hr : c.ringSize = mMax + 1) (hmMax : mMax ≤ 13)
    (h_ring : IsRingCycle c)
    (hb : IsValidBoundaryColoring c b)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd)
    (hSameChild : SameActiveClass c p equiv_ab equiv_cd b b_child)
    (hxy : x < y) (hy : y < c.ringSize)
    (hDiffX : theta1Pair b (x % c.ringSize) ≠ theta1Pair b ((x + 1) % c.ringSize))
    (hDiffY : theta1Pair b (y % c.ringSize) ≠ theta1Pair b ((y + 1) % c.ringSize))
    (hClosed : ∀ u < c.ringSize, ∀ w < c.ringSize,
      partEquiv equiv_ab equiv_cd u w → ((x < u ∧ u ≤ y) ↔ (x < w ∧ w ≤ y)))
    (hNum : numBits ≤ wordK mMax (permTraceVal p c.ringSize b mMax 0))
    (hTwoP : twoP - 1 = numBits)
    (hK_le : wordK y (permTraceVal p c.ringSize b c.ringSize 0) ≤ numBits)
    (hFalse :
      let X := permTraceVal p c.ringSize b mMax 0
      let X_full := permTraceVal p c.ringSize b c.ringSize 0
      let X_child := permTraceVal p c.ringSize b_child mMax 0
      let kBucket := wordK mMax X
      let m0List := (buildM0List kBucket numBits (binom mMax kBucket)).val
      let lo := wordK x X_full
      let kIdx := wordK y X_full
      Nat.testBit (evalChordOp (mkNodeOp twoP m0List lo kIdx) B) (wordProj mMax numBits X_child) = false) :
    ∃ b',
      SameActiveClass c p equiv_ab equiv_cd b b' ∧
      Nat.testBit B (wordProj mMax numBits (permTraceVal p c.ringSize b' mMax 0)) = false := by
  rcases hSameChild with ⟨⟨S1, hS1, hEqChild⟩, hKChild⟩
  have hb_child : IsValidBoundaryColoring c b_child := by
    rw [hEqChild]; exact swap_preserves_valid c b theta1 equiv_ab equiv_cd S1 hb hPart hS1
  have hPart_child : IsJointPlanarRingPartition c b_child theta1 equiv_ab equiv_cd := by
    rw [hEqChild]; exact boundaryKempeSwap_preserves_partition c b theta1 equiv_ab equiv_cd S1 hPart
  have hPair_child : theta1Pair b_child = theta1Pair b := by
    rw [hEqChild]; exact theta1Pair_boundaryKempeSwap c b S1
  have hDiffX_child : theta1Pair b_child (x % c.ringSize) ≠ theta1Pair b_child ((x + 1) % c.ringSize) := by
    rw [hPair_child]; exact hDiffX
  have hDiffY_child : theta1Pair b_child (y % c.ringSize) ≠ theta1Pair b_child ((y + 1) % c.ringSize) := by
    rw [hPair_child]; exact hDiffY
  have hKm_child : wordK mMax (permTraceVal p c.ringSize b_child mMax 0) =
      wordK mMax (permTraceVal p c.ringSize b mMax 0) := by
    rw [wordK_permTraceVal_eq_of_le p hp3 c.ringSize b_child mMax mMax c.ringSize 0 (by omega) (by omega),
        hKChild mMax,
        ← wordK_permTraceVal_eq_of_le p hp3 c.ringSize b mMax mMax c.ringSize 0 (by omega) (by omega)]
  have hFalse_child :
      let X_c := permTraceVal p c.ringSize b_child mMax 0
      let X_c_full := permTraceVal p c.ringSize b_child c.ringSize 0
      let kBucket := wordK mMax X_c
      let m0List := (buildM0List kBucket numBits (binom mMax kBucket)).val
      let lo := wordK x X_c_full
      let kIdx := wordK y X_c_full
      Nat.testBit (evalChordOp (mkNodeOp twoP m0List lo kIdx) B) (wordProj mMax numBits X_c) = false := by
    dsimp at hFalse ⊢
    rw [hKm_child, hKChild x, hKChild y]
    exact hFalse
  rcases mkNodeOp_coloring_false_sound c p hp3 hp12 equiv_ab equiv_cd b_child
    mMax numBits twoP x y B hr hmMax h_ring hb_child hPart_child hxy hy
    hDiffX_child hDiffY_child hClosed
    (by rw [hKm_child]; exact hNum) hTwoP (by rw [hKChild y]; exact hK_le) hFalse_child with ⟨b', hSame', hB'⟩
  exact ⟨b', sameActiveClass_trans c p equiv_ab equiv_cd b b_child b' ⟨⟨S1, hS1, hEqChild⟩, hKChild⟩ hSame', hB'⟩

/-!
### Structural Induction on `IsExtractedMatching` and `buildCatalanTrieAux`
-/

theorem extractedMatching_uncons_pair (c : Configuration) (b : BoundaryColoring c)
    (E : Nat → Nat → Prop) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp0 : ∀ d < 3, p d = 0 ↔ d = 0)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    {a b_hi : Nat} {m : List (Nat × Nat)}
    (hExt : IsExtractedMatching c.ringSize (theta1Pair b) E a b_hi m)
    (hm : 0 < m.length) :
    let X_full := permTraceVal p c.ringSize b c.ringSize 0
    ∃ x y m1 m2,
      a ≤ x ∧ x + 1 ≤ y ∧ y < b_hi ∧ b_hi ≤ c.ringSize ∧
      m = (x, y) :: (m1 ++ m2) ∧
      wordK x X_full = wordK a X_full ∧
      wordK (x + 1) X_full = wordK x X_full + 1 ∧
      wordK y X_full = (wordK x X_full + 1) + 2 * m1.length ∧
      wordK (y + 1) X_full = wordK y X_full + 1 ∧
      wordK b_hi X_full = (wordK y X_full + 1) + 2 * m2.length ∧
      theta1Pair b (x % c.ringSize) ≠ theta1Pair b ((x + 1) % c.ringSize) ∧
      theta1Pair b (y % c.ringSize) ≠ theta1Pair b ((y + 1) % c.ringSize) ∧
      (∀ u < c.ringSize, ∀ w < c.ringSize, E u w → ((x < u ∧ u ≤ y) ↔ (x < w ∧ w ≤ y))) ∧
      IsExtractedMatching c.ringSize (theta1Pair b) E (x + 1) y m1 ∧
      IsExtractedMatching c.ringSize (theta1Pair b) E (y + 1) b_hi m2 := by
  intro X_full
  induction hExt with
  | nil lo _ => simp at hm
  | skip lo hi m h_lt h_hi h_same _ ih =>
    have hlo_r : lo < c.ringSize := Nat.lt_of_lt_of_le h_lt h_hi
    rw [Nat.mod_eq_of_lt hlo_r] at h_same
    have hd0 : edgeDigitAt c.ringSize b lo = 0 :=
      (edgeDigitAt_eq_zero_iff_same_pair c b h_ring hb lo hlo_r).mpr h_same
    have hp_lo : (X_full / 3 ^ lo) % 3 = 0 := by
      dsimp [X_full]
      rw [permTraceVal_div_pow3_mod_three p hp3 c.ringSize b c.ringSize 0 lo hlo_r,
          Nat.zero_add, (hp0 _ (edgeDigitAt_lt_three c.ringSize b lo)).mpr hd0]
    have hStep : wordK (lo + 1) X_full = wordK lo X_full := by
      rw [wordK_succ_right, if_pos hp_lo, Nat.add_zero]
    rcases ih hm with ⟨x, y, m1, m2, hx, hxy, hy, hhi, hm_eq, hKx, hKx1, hKy, hKy1, hKhi,
      hDiffX, hDiffY, hCl, hLeft, hRight⟩
    exact ⟨x, y, m1, m2, by omega, hxy, hy, hhi, hm_eq, by omega, hKx1, hKy, hKy1, hKhi,
      hDiffX, hDiffY, hCl, hLeft, hRight⟩
  | pair lo k₀ hi m1 m2 hk_ge hk_lt h_hi h_diff_lo h_diff_k0 h_closed h_left h_right =>
    have hk0_r : k₀ < c.ringSize := Nat.lt_of_lt_of_le hk_lt h_hi
    have hlo_r : lo < c.ringSize := by omega
    have hd_lo := transition_edgeDigit_one_or_two c b h_ring hb lo hlo_r h_diff_lo
    have hd_k0 := transition_edgeDigit_one_or_two c b h_ring hb k₀ hk0_r h_diff_k0
    have hp_lo : (X_full / 3 ^ lo) % 3 ≠ 0 := by
      dsimp [X_full]
      rw [permTraceVal_div_pow3_mod_three p hp3 c.ringSize b c.ringSize 0 lo hlo_r, Nat.zero_add]
      intro h0
      have := (hp0 _ (edgeDigitAt_lt_three c.ringSize b lo)).mp h0
      omega
    have hp_k0 : (X_full / 3 ^ k₀) % 3 ≠ 0 := by
      dsimp [X_full]
      rw [permTraceVal_div_pow3_mod_three p hp3 c.ringSize b c.ringSize 0 k₀ hk0_r, Nat.zero_add]
      intro h0
      have := (hp0 _ (edgeDigitAt_lt_three c.ringSize b k₀)).mp h0
      omega
    have hStepLo : wordK (lo + 1) X_full = wordK lo X_full + 1 := by
      rw [wordK_succ_right, if_neg hp_lo]
    have hStepK0 : wordK (k₀ + 1) X_full = wordK k₀ X_full + 1 := by
      rw [wordK_succ_right, if_neg hp_k0]
    have hLeftDiff := wordK_extractedMatching_eq c b E p hp3 hp0 h_ring hb h_left
    have hRightDiff := wordK_extractedMatching_eq c b E p hp3 hp0 h_ring hb h_right
    change wordK k₀ X_full = wordK (lo + 1) X_full + 2 * m1.length at hLeftDiff
    change wordK hi X_full = wordK (k₀ + 1) X_full + 2 * m2.length at hRightDiff
    exact ⟨lo, k₀, m1, m2, Nat.le_refl lo, hk_ge, hk_lt, h_hi, rfl, rfl,
      hStepLo, by omega, hStepK0, by omega, h_diff_lo, h_diff_k0, h_closed, h_left, h_right⟩

inductive ValidIntervalStack (r : Nat) (pair : Nat → Bool) (E : Nat → Nat → Prop) (X_full twoP : Nat) :
    List (Nat × Nat) → Nat → Prop where
  | nil : ValidIntervalStack r pair E X_full twoP [] 0
  | cons (a b_hi nRest : Nat) (m : List (Nat × Nat)) (rest : List (Nat × Nat))
      (hExt : IsExtractedMatching r pair E a b_hi m)
      (hm : 0 < m.length)
      (hHi : wordK b_hi X_full ≤ twoP)
      (hRest : ValidIntervalStack r pair E X_full twoP rest nRest) :
      ValidIntervalStack r pair E X_full twoP ((wordK a X_full, wordK b_hi X_full) :: rest) (m.length + nRest)

theorem validIntervalStack_push_opt (c : Configuration) (b : BoundaryColoring c)
    (E : Nat → Nat → Prop) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp0 : ∀ d < 3, p d = 0 ↔ d = 0)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (twoP a b_hi nRest : Nat) (m : List (Nat × Nat)) (rest : List (Nat × Nat))
    (hExt : IsExtractedMatching c.ringSize (theta1Pair b) E a b_hi m)
    (hHi : wordK b_hi (permTraceVal p c.ringSize b c.ringSize 0) ≤ twoP)
    (hRest : ValidIntervalStack c.ringSize (theta1Pair b) E (permTraceVal p c.ringSize b c.ringSize 0) twoP rest nRest) :
    let X_full := permTraceVal p c.ringSize b c.ringSize 0
    let lo_act := wordK a X_full
    let hi_act := wordK b_hi X_full
    ValidIntervalStack c.ringSize (theta1Pair b) E X_full twoP
      (selectBool (Nat.blt lo_act hi_act) ((lo_act, hi_act) :: rest) rest)
      (m.length + nRest) := by
  intro X_full lo_act hi_act
  have hDiff := wordK_extractedMatching_eq c b E p hp3 hp0 h_ring hb hExt
  change hi_act = lo_act + 2 * m.length at hDiff
  cases hBlt : Nat.blt lo_act hi_act with
  | true =>
    have hLt : lo_act < hi_act := Nat.blt_eq.mp hBlt
    have hm : 0 < m.length := by omega
    exact ValidIntervalStack.cons a b_hi nRest m rest hExt hm hHi hRest
  | false =>
    have hGe : ¬ (lo_act < hi_act) := by
      intro hLt
      have : Nat.blt lo_act hi_act = true := Nat.blt_eq.mpr hLt
      rw [hBlt] at this; contradiction
    have hm0 : m.length = 0 := by omega
    rw [hm0, Nat.zero_add]
    exact hRest

noncomputable def catalanSibLoop (twoP : Nat) (m0List : List (Nat × Nat))
    (ihFuel : List (Nat × Nat) → StrictBox CatalanTrie)
    (lo hi : Nat) (rest : List (Nat × Nat)) (steps : Nat) (sibAcc : CatalanTrie) : StrictBox CatalanTrie :=
  let bitLo := Nat.shiftLeft 1 lo
  let m0Lo := lookupM0 lo m0List
  let loPlus1 := Nat.add lo 1
  @Nat.rec (fun _ => CatalanTrie → StrictBox CatalanTrie)
    (fun sibAcc => StrictBox.mk sibAcc)
    (fun idx ihSib sibAcc =>
      let kIdx := Nat.add loPlus1 (Nat.mul 2 idx)
      let kPlus1 := Nat.add kIdx 1
      let rest1 := selectBool (Nat.blt kPlus1 hi) ((kPlus1, hi) :: rest) rest
      let rest2 := selectBool (Nat.blt loPlus1 kIdx) ((loPlus1, kIdx) :: rest1) rest1
      let childTrie := (ihFuel rest2).val
      selectBool (Nat.beq kIdx (Nat.sub twoP 1))
        (ihSib (mkCatalanNode (ChordOp.last bitLo m0Lo) childTrie sibAcc))
        (let m0K := lookupM0 kIdx m0List
         let m00 := Nat.land m0Lo m0K
         let m10 := Nat.shiftLeft m00 bitLo
         let bitK := Nat.shiftLeft 1 kIdx
         let dPlus := Nat.add bitK bitLo
         let dMinus := Nat.sub bitK bitLo
         ihSib (mkCatalanNode (ChordOp.pair dPlus dMinus m00 m10) childTrie sibAcc)))
    steps sibAcc

theorem catalanSibLoop_succ (twoP : Nat) (m0List : List (Nat × Nat))
    (ihFuel : List (Nat × Nat) → StrictBox CatalanTrie)
    (lo hi : Nat) (rest : List (Nat × Nat)) (steps : Nat) (sibAcc : CatalanTrie) :
    catalanSibLoop twoP m0List ihFuel lo hi rest (steps + 1) sibAcc =
      let loPlus1 := lo + 1
      let kIdx := loPlus1 + 2 * steps
      let kPlus1 := kIdx + 1
      let rest1 := selectBool (Nat.blt kPlus1 hi) ((kPlus1, hi) :: rest) rest
      let rest2 := selectBool (Nat.blt loPlus1 kIdx) ((loPlus1, kIdx) :: rest1) rest1
      let childTrie := (ihFuel rest2).val
      let op := mkNodeOp twoP m0List lo kIdx
      catalanSibLoop twoP m0List ihFuel lo hi rest steps (mkCatalanNode op childTrie sibAcc) := by
  dsimp [catalanSibLoop, mkNodeOp]
  cases Nat.beq (Nat.add (Nat.add lo 1) (Nat.mul 2 steps)) (Nat.sub twoP 1) <;> rfl

theorem evalCatalanTrie_catalanSibLoop_false_sound
    (twoP : Nat) (m0List : List (Nat × Nat))
    (ihFuel : List (Nat × Nat) → StrictBox CatalanTrie)
    (lo hi : Nat) (rest : List (Nat × Nat))
    (steps : Nat) (sibAcc : CatalanTrie) (B q : Nat)
    (hFalse : Nat.testBit (evalCatalanTrie (catalanSibLoop twoP m0List ihFuel lo hi rest steps sibAcc).val B) q = false) :
    Nat.testBit (evalCatalanTrie sibAcc B) q = false ∧
    ∀ idx < steps,
      let loPlus1 := lo + 1
      let kIdx := loPlus1 + 2 * idx
      let kPlus1 := kIdx + 1
      let rest1 := selectBool (Nat.blt kPlus1 hi) ((kPlus1, hi) :: rest) rest
      let rest2 := selectBool (Nat.blt loPlus1 kIdx) ((loPlus1, kIdx) :: rest1) rest1
      let childTrie := (ihFuel rest2).val
      let op := mkNodeOp twoP m0List lo kIdx
      Nat.testBit (evalCatalanTrie childTrie (evalChordOp op B)) q = false := by
  induction steps generalizing sibAcc with
  | zero =>
    refine ⟨hFalse, ?_⟩
    intro idx hLt
    omega
  | succ steps ih =>
    rw [catalanSibLoop_succ] at hFalse
    rcases ih _ hFalse with ⟨hNode, hPrev⟩
    rcases evalCatalanTrie_mkCatalanNode_false_sound _ _ _ B q hNode with ⟨hChild, hSib⟩
    refine ⟨hSib, ?_⟩
    intro idx hIdx
    by_cases hEq : idx = steps
    · subst hEq
      exact hChild
    · exact hPrev idx (by omega)

theorem evalCatalanTrie_buildCatalanTrieAux_false_sound
    (c : Configuration) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp0 : ∀ d < 3, p d = 0 ↔ d = 0)
    (hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)))
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (b : BoundaryColoring c)
    (mMax numBits twoP fuel nChords : Nat)
    (intervals : List (Nat × Nat))
    (hr : c.ringSize = mMax + 1) (hmMax : mMax ≤ 13)
    (h_ring : IsRingCycle c)
    (hb : IsValidBoundaryColoring c b)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd)
    (hNum : numBits ≤ wordK mMax (permTraceVal p c.ringSize b mMax 0))
    (hTwoP : twoP - 1 = numBits)
    (hStack : ValidIntervalStack c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd)
      (permTraceVal p c.ringSize b c.ringSize 0) twoP intervals nChords)
    (hFuel : nChords ≤ fuel)
    (B : Nat)
    (hFalse :
      let X := permTraceVal p c.ringSize b mMax 0
      let kBucket := wordK mMax X
      let m0List := (buildM0List kBucket numBits (binom mMax kBucket)).val
      let trie := (buildCatalanTrieAux twoP m0List fuel intervals).val
      Nat.testBit (evalCatalanTrie trie B) (wordProj mMax numBits X) = false) :
    ∃ b',
      SameActiveClass c p equiv_ab equiv_cd b b' ∧
      Nat.testBit B (wordProj mMax numBits (permTraceVal p c.ringSize b' mMax 0)) = false := by
  induction fuel generalizing intervals nChords B with
  | zero =>
    exact ⟨b, sameActiveClass_refl c p equiv_ab equiv_cd b, hFalse⟩
  | succ fuel ihFuel =>
    cases hStack with
    | nil =>
      exact ⟨b, sameActiveClass_refl c p equiv_ab equiv_cd b, hFalse⟩
    | cons a b_hi nRest m rest hExt hm hHi hRest =>
      let X_full := permTraceVal p c.ringSize b c.ringSize 0
      let X := permTraceVal p c.ringSize b mMax 0
      let kBucket := wordK mMax X
      let m0List := (buildM0List kBucket numBits (binom mMax kBucket)).val
      rcases extractedMatching_uncons_pair c b (partEquiv equiv_ab equiv_cd) p hp3 hp0 h_ring hb hExt hm with
        ⟨x, y, m1, m2, hax, hxy_le, hy_b, hb_r, hm_eq, hKx_a, hKx1, hKy, hKy1, hKhi,
         hDiffX, hDiffY, hCl, hLeft, hRight⟩
      change wordK x X_full = wordK a X_full at hKx_a
      change wordK (x + 1) X_full = wordK x X_full + 1 at hKx1
      change wordK y X_full = (wordK x X_full + 1) + 2 * m1.length at hKy
      change wordK (y + 1) X_full = wordK y X_full + 1 at hKy1
      change wordK b_hi X_full = (wordK y X_full + 1) + 2 * m2.length at hKhi
      change wordK b_hi X_full ≤ twoP at hHi
      have hm_len : m.length = 1 + m1.length + m2.length := by
        rw [hm_eq, List.length_cons, List.length_append]; omega
      let lo := wordK a X_full
      let hi := wordK b_hi X_full
      have hHi_eq : hi = lo + 2 * m.length := by
        change wordK b_hi X_full = wordK a X_full + 2 * m.length
        omega
      have hSteps : Nat.shiftRight (Nat.sub hi lo) 1 = m.length := by
        change (hi - lo) >>> 1 = m.length
        rw [Nat.shiftRight_eq_div_pow]
        change (hi - lo) / 2 = m.length
        omega
      have hIdxLt : m1.length < Nat.shiftRight (Nat.sub hi lo) 1 := by omega
      have hSibLoop :
          (buildCatalanTrieAux twoP m0List (fuel + 1) ((lo, hi) :: rest)).val =
          (catalanSibLoop twoP m0List (buildCatalanTrieAux twoP m0List fuel) lo hi rest
            (Nat.shiftRight (Nat.sub hi lo) 1) CatalanTrie.nil).val := rfl
      dsimp at hFalse
      rw [hSibLoop] at hFalse
      have hChildFalse := (evalCatalanTrie_catalanSibLoop_false_sound
        twoP m0List (buildCatalanTrieAux twoP m0List fuel) lo hi rest
        (Nat.shiftRight (Nat.sub hi lo) 1) CatalanTrie.nil B (wordProj mMax numBits X) hFalse).2
        m1.length hIdxLt
      dsimp at hChildFalse
      let loPlus1 := lo + 1
      let kIdx := loPlus1 + 2 * m1.length
      let kPlus1 := kIdx + 1
      let rest1 := selectBool (Nat.blt kPlus1 hi) ((kPlus1, hi) :: rest) rest
      let rest2 := selectBool (Nat.blt loPlus1 kIdx) ((loPlus1, kIdx) :: rest1) rest1
      have hLoPlus1_eq : loPlus1 = wordK (x + 1) X_full := by
        change wordK a X_full + 1 = wordK (x + 1) X_full; omega
      have hKIdx_eq : kIdx = wordK y X_full := by
        change (wordK a X_full + 1) + 2 * m1.length = wordK y X_full; omega
      have hKPlus1_eq : kPlus1 = wordK (y + 1) X_full := by
        change ((wordK a X_full + 1) + 2 * m1.length) + 1 = wordK (y + 1) X_full; omega
      have hStack1 : ValidIntervalStack c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd)
          X_full twoP rest1 (m2.length + nRest) := by
        dsimp [rest1]
        rw [hKPlus1_eq]
        exact validIntervalStack_push_opt c b (partEquiv equiv_ab equiv_cd) p hp3 hp0 h_ring hb
          twoP (y + 1) b_hi nRest m2 rest hRight hHi hRest
      have hKy_le_twoP : wordK y X_full ≤ twoP := by omega
      have hStack2 : ValidIntervalStack c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd)
          X_full twoP rest2 (m1.length + (m2.length + nRest)) := by
        dsimp [rest2]
        rw [hLoPlus1_eq, hKIdx_eq]
        exact validIntervalStack_push_opt c b (partEquiv equiv_ab equiv_cd) p hp3 hp0 h_ring hb
          twoP (x + 1) y (m2.length + nRest) m1 rest1 hLeft hKy_le_twoP hStack1
      have hFuel2 : m1.length + (m2.length + nRest) ≤ fuel := by omega
      rcases ihFuel (m1.length + (m2.length + nRest)) rest2 hStack2 hFuel2
        (evalChordOp (mkNodeOp twoP m0List lo kIdx) B) hChildFalse with ⟨b_child, hSameChild, hB_child⟩
      have hLo_eq : lo = wordK x X_full := by
        change wordK a X_full = wordK x X_full; omega
      rw [hLo_eq, hKIdx_eq] at hB_child
      have hKy_le_num : wordK y X_full ≤ numBits := by omega
      exact mkNodeOp_sameActiveClass_step c p hp3 hp12 equiv_ab equiv_cd b b_child
        mMax numBits twoP x y B hr hmMax h_ring hb hPart hSameChild
        (by omega) (by omega) hDiffX hDiffY hCl hNum hTwoP hKy_le_num hB_child

/-!
### Thue-Morse Sign Parity and `evalBucketSpec` / `evalAllBuckets` Soundness
-/

def popcountK : Nat → Nat → Nat
  | 0, _ => 0
  | c + 1, q => (q % 2) + popcountK c (q / 2)

theorem lor_shiftLeft_lt_two_pow (a b W : Nat) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    Nat.lor a (Nat.shiftLeft b W) < 2 ^ (Nat.shiftLeft W 1) := by
  have hW2 : Nat.shiftLeft W 1 = W + W := by
    change W <<< 1 = W + W
    rw [Nat.shiftLeft_eq, Nat.pow_one]
    omega
  rw [hW2]
  have ha' : a < 2 ^ (W + W) :=
    Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))
  apply Nat.or_lt_two_pow ha'
  change b <<< W < 2 ^ (W + W)
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos W)

theorem buildThueMorseParityAux_lt (rMod2 c W evenM oddM : Nat)
    (hEven : evenM < 2 ^ W) (hOdd : oddM < 2 ^ W) :
    buildThueMorseParityAux rMod2 c W evenM oddM < 2 ^ (W * (1 <<< c)) := by
  induction c generalizing W evenM oddM with
  | zero =>
    have h1 : W * (1 <<< 0) = W := by simp
    rw [h1]
    dsimp [buildThueMorseParityAux]
    cases Nat.beq rMod2 0 <;> assumption
  | succ c ih =>
    change buildThueMorseParityAux rMod2 c (Nat.shiftLeft W 1)
      (Nat.lor evenM (Nat.shiftLeft oddM W)) (Nat.lor oddM (Nat.shiftLeft evenM W)) <
      2 ^ (W * (1 <<< (c + 1)))
    have hW1 : Nat.shiftLeft W 1 = 2 * W := by
      change W <<< 1 = 2 * W
      rw [Nat.shiftLeft_eq, Nat.pow_one]
      omega
    have hMul : W * (1 <<< (c + 1)) = (Nat.shiftLeft W 1) * (1 <<< c) := by
      rw [shiftLeft_one_succ, hW1, ← Nat.mul_assoc W 2, Nat.mul_comm W 2]
    rw [hMul]
    exact ih (Nat.shiftLeft W 1)
      (Nat.lor evenM (Nat.shiftLeft oddM W))
      (Nat.lor oddM (Nat.shiftLeft evenM W))
      (lor_shiftLeft_lt_two_pow evenM oddM W hEven hOdd)
      (lor_shiftLeft_lt_two_pow oddM evenM W hOdd hEven)

theorem testBit_lor_shiftLeft_low (a b W r : Nat) (hr : r < W) :
    Nat.testBit (Nat.lor a (Nat.shiftLeft b W)) r = Nat.testBit a r := by
  rw [testBit_lor, testBit_shiftLeft, decide_eq_false (by omega), Bool.false_and, Bool.or_false]

theorem testBit_lor_shiftLeft_high (a b W r : Nat) (ha : a < 2 ^ W) :
    Nat.testBit (Nat.lor a (Nat.shiftLeft b W)) (W + r) = Nat.testBit b r := by
  have ha_ge : a < 2 ^ (W + r) :=
    Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))
  rw [testBit_lor, Nat.testBit_lt_two_pow ha_ge, Bool.false_or,
      testBit_shiftLeft, decide_eq_true (by omega), Bool.true_and, Nat.add_sub_cancel_left]

theorem testBit_buildThueMorseParityAux (rMod2 c W evenM oddM q r : Nat)
    (hrMod2 : rMod2 < 2) (hW : 0 < W) (hEven : evenM < 2 ^ W) (hOdd : oddM < 2 ^ W)
    (hq : q < (1 <<< c)) (hr : r < W) :
    Nat.testBit (buildThueMorseParityAux rMod2 c W evenM oddM) (q * W + r) =
      if (popcountK c q + rMod2) % 2 = 0 then Nat.testBit evenM r else Nat.testBit oddM r := by
  induction c generalizing W evenM oddM q r with
  | zero =>
    have hq0 : q = 0 := by
      have : 1 <<< 0 = 1 := rfl
      omega
    subst hq0
    rw [Nat.zero_mul, Nat.zero_add]
    dsimp [buildThueMorseParityAux, popcountK]
    rcases hr01 : rMod2 with _ | _ | k
    · rfl
    · rfl
    · omega
  | succ c ih =>
    let nextW := Nat.shiftLeft W 1
    let nextEven := Nat.lor evenM (Nat.shiftLeft oddM W)
    let nextOdd := Nat.lor oddM (Nat.shiftLeft evenM W)
    have hNextW_eq : nextW = 2 * W := by
      change W <<< 1 = 2 * W
      rw [Nat.shiftLeft_eq, Nat.pow_one]
      omega
    have hNextW_pos : 0 < nextW := by omega
    have hNextEven : nextEven < 2 ^ nextW := lor_shiftLeft_lt_two_pow evenM oddM W hEven hOdd
    have hNextOdd : nextOdd < 2 ^ nextW := lor_shiftLeft_lt_two_pow oddM evenM W hOdd hEven
    have hq_div : q / 2 < (1 <<< c) := by
      rw [shiftLeft_one_succ] at hq
      omega
    let r' := (q % 2) * W + r
    have hr'_lt : r' < nextW := by
      dsimp [r']
      have : q % 2 < 2 := Nat.mod_lt q (by decide)
      rcases (by omega : q % 2 = 0 ∨ q % 2 = 1) with h0 | h1
      · rw [h0]; omega
      · rw [h1]; omega
    have hIdx : q * W + r = (q / 2) * nextW + r' := by
      dsimp [r']
      rw [hNextW_eq]
      have hq_eq : q = 2 * (q / 2) + q % 2 := (Nat.div_add_mod q 2).symm
      calc q * W + r
        _ = (2 * (q / 2) + q % 2) * W + r := by rw [← hq_eq]
        _ = (2 * (q / 2)) * W + (q % 2) * W + r := by rw [Nat.add_mul]
        _ = (q / 2) * (2 * W) + ((q % 2) * W + r) := by
          rw [Nat.mul_comm 2 (q / 2), Nat.mul_assoc (q / 2) 2 W, Nat.add_assoc]
    change Nat.testBit (buildThueMorseParityAux rMod2 c nextW nextEven nextOdd) (q * W + r) = _
    rw [hIdx, ih nextW nextEven nextOdd (q / 2) r' hNextW_pos hNextEven hNextOdd hq_div hr'_lt]
    dsimp [popcountK]
    rcases (by omega : q % 2 = 0 ∨ q % 2 = 1) with hq0 | hq1
    · have hr'_eq : r' = r := by dsimp [r']; rw [hq0, Nat.zero_mul, Nat.zero_add]
      rw [hr'_eq, hq0, Nat.zero_add,
          testBit_lor_shiftLeft_low evenM oddM W r hr,
          testBit_lor_shiftLeft_low oddM evenM W r hr]
    · have hr'_eq : r' = W + r := by dsimp [r']; rw [hq1, Nat.one_mul]
      rw [hr'_eq, hq1,
          testBit_lor_shiftLeft_high evenM oddM W r hEven,
          testBit_lor_shiftLeft_high oddM evenM W r hOdd]
      by_cases hPar : (popcountK c (q / 2) + rMod2) % 2 = 0
      · have hPar1 : (1 + popcountK c (q / 2) + rMod2) % 2 ≠ 0 := by omega
        rw [if_pos hPar, if_neg hPar1]
      · have hPar1 : (1 + popcountK c (q / 2) + rMod2) % 2 = 0 := by omega
        rw [if_neg hPar, if_pos hPar1]

def wordOnes : Nat → Nat → Nat
  | 0, _ => 0
  | m + 1, q => (if q % 3 = 1 then 1 else 0) + wordOnes m (q / 3)

theorem wordK_eq_wordOnes_add_popcount (m q : Nat) :
    wordK m q = wordOnes m q + popcountK (wordK m q) (wordSign m q) := by
  induction m generalizing q with
  | zero => rfl
  | succ m' ih =>
    dsimp [wordK, wordOnes, wordSign]
    have hSub := ih (q / 3)
    have hMod : q % 3 < 3 := Nat.mod_lt q (by decide)
    by_cases h0 : q % 3 = 0
    · rw [if_pos h0, if_pos h0, if_neg (by omega), Nat.zero_add]
      exact hSub
    · rw [if_neg h0, if_neg h0]
      dsimp [popcountK]
      rcases (by omega : q % 3 = 1 ∨ q % 3 = 2) with h1 | h2
      · rw [h1, if_pos rfl]
        have hDiv : (2 * wordSign m' (q / 3) + (1 - 1)) / 2 = wordSign m' (q / 3) := by omega
        have hRem : (2 * wordSign m' (q / 3) + (1 - 1)) % 2 = 0 := by omega
        rw [hDiv, hRem]
        omega
      · rw [h2, if_neg (by decide)]
        have hDiv : (2 * wordSign m' (q / 3) + (2 - 1)) / 2 = wordSign m' (q / 3) := by omega
        have hRem : (2 * wordSign m' (q / 3) + (2 - 1)) % 2 = 1 := by omega
        rw [hDiv, hRem]
        omega

theorem wordOnes_succ_right (e q : Nat) :
    wordOnes (e + 1) q = wordOnes e q + (if (q / 3 ^ e) % 3 = 1 then 1 else 0) := by
  induction e generalizing q with
  | zero =>
    dsimp [wordOnes]
    rw [Nat.div_one]
    split <;> omega
  | succ e' ih =>
    change (if q % 3 = 1 then 1 else 0) + wordOnes (e' + 1) (q / 3) =
      ((if q % 3 = 1 then 1 else 0) + wordOnes e' (q / 3)) +
        (if (q / 3 ^ (e' + 1)) % 3 = 1 then 1 else 0)
    rw [ih (q / 3), Nat.pow_succ', ← Nat.div_div_eq_div_mul]
    omega

theorem popcount_wordSign_succ_right (e q : Nat) :
    popcountK (wordK (e + 1) q) (wordSign (e + 1) q) =
      popcountK (wordK e q) (wordSign e q) + (if (q / 3 ^ e) % 3 = 2 then 1 else 0) := by
  have h1 := wordK_eq_wordOnes_add_popcount e q
  have h2 := wordK_eq_wordOnes_add_popcount (e + 1) q
  have hK := wordK_succ_right e q
  have hO := wordOnes_succ_right e q
  have hd : (q / 3 ^ e) % 3 < 3 := Nat.mod_lt _ (by decide)
  rcases (by omega : (q / 3 ^ e) % 3 = 0 ∨ (q / 3 ^ e) % 3 = 1 ∨ (q / 3 ^ e) % 3 = 2) with h | h | h <;>
  · rw [h] at hK hO ⊢
    dsimp at hK hO ⊢
    omega

theorem wordOnes_permTraceVal_eq_of_le (p : Nat → Nat) (hp : ∀ d < 3, p d < 3)
    (r : Nat) (b : Nat → Color) (e k m s : Nat) (hek : e ≤ k) (hkm : k ≤ m) :
    wordOnes e (permTraceVal p r b k s) = wordOnes e (permTraceVal p r b m s) := by
  induction e with
  | zero => rfl
  | succ e' ih =>
    rw [wordOnes_succ_right, wordOnes_succ_right, ih (by omega),
        permTraceVal_div_pow3_mod_three p hp r b k s e' (by omega),
        permTraceVal_div_pow3_mod_three p hp r b m s e' (by omega)]

theorem popcount_wordSign_permTraceVal_eq_of_le (p : Nat → Nat) (hp : ∀ d < 3, p d < 3)
    (r : Nat) (b : Nat → Color) (e k m s : Nat) (hek : e ≤ k) (hkm : k ≤ m) :
    popcountK (wordK e (permTraceVal p r b k s)) (wordSign e (permTraceVal p r b k s)) =
      popcountK (wordK e (permTraceVal p r b m s)) (wordSign e (permTraceVal p r b m s)) := by
  have h1 := wordK_eq_wordOnes_add_popcount e (permTraceVal p r b k s)
  have h2 := wordK_eq_wordOnes_add_popcount e (permTraceVal p r b m s)
  have hK := wordK_permTraceVal_eq_of_le p hp r b e k m s hek (by omega)
  have hO := wordOnes_permTraceVal_eq_of_le p hp r b e k m s hek hkm
  omega

theorem wordOnes_or_popcount_eq_rangeDigitOneCount
    (c : Configuration) (b : BoundaryColoring c) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp0 : ∀ d < 3, p d = 0 ↔ d = 0)
    (e : Nat) (he : e ≤ c.ringSize) :
    let X_full := permTraceVal p c.ringSize b c.ringSize 0
    (p 1 = 1 ∧ p 2 = 2 → wordOnes e X_full = rangeDigitOneCount c.ringSize b 0 e) ∧
    (p 1 = 2 ∧ p 2 = 1 → popcountK (wordK e X_full) (wordSign e X_full) = rangeDigitOneCount c.ringSize b 0 e) := by
  intro X_full
  induction e with
  | zero =>
    rw [rangeDigitOneCount_eq_zero c.ringSize b 0 0 (by omega)]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ e' ih =>
    have he'_lt : e' < c.ringSize := Nat.lt_of_succ_le he
    rcases ih (Nat.le_of_lt he'_lt) with ⟨ih1, ih2⟩
    have hMod : (X_full / 3 ^ e') % 3 = p (edgeDigitAt c.ringSize b e') := by
      dsimp [X_full]
      rw [permTraceVal_div_pow3_mod_three p hp3 c.ringSize b c.ringSize 0 e' he'_lt, Nat.zero_add]
    have hSplit : rangeDigitOneCount c.ringSize b 0 (e' + 1) =
        rangeDigitOneCount c.ringSize b 0 e' + (if edgeDigitAt c.ringSize b e' == 1 then 1 else 0) := by
      rw [rangeDigitOneCount_split c.ringSize b 0 e' (e' + 1) (Nat.zero_le e') (Nat.le_succ e'),
          rangeDigitOneCount_step c.ringSize b e' (e' + 1) (Nat.lt_succ_self e'),
          rangeDigitOneCount_eq_zero c.ringSize b (e' + 1) (e' + 1) (by omega),
          Nat.add_zero]
    have hd_lt : edgeDigitAt c.ringSize b e' < 3 := edgeDigitAt_lt_three c.ringSize b e'
    have hp_zero : p 0 = 0 := (hp0 0 (by decide)).mpr rfl
    refine ⟨?_, ?_⟩
    · intro ⟨hp1, hp2⟩
      rw [wordOnes_succ_right, ih1 ⟨hp1, hp2⟩, hMod, hSplit]
      rcases (by omega : edgeDigitAt c.ringSize b e' = 0 ∨ edgeDigitAt c.ringSize b e' = 1 ∨ edgeDigitAt c.ringSize b e' = 2) with h | h | h <;>
      · rw [h]; simp [hp_zero, hp1, hp2]
    · intro ⟨hp1, hp2⟩
      rw [popcount_wordSign_succ_right, ih2 ⟨hp1, hp2⟩, hMod, hSplit]
      rcases (by omega : edgeDigitAt c.ringSize b e' = 0 ∨ edgeDigitAt c.ringSize b e' = 1 ∨ edgeDigitAt c.ringSize b e' = 2) with h | h | h <;>
      · rw [h]; simp [hp_zero, hp1, hp2]

theorem wordK_full_and_popcount_parity (c : Configuration) (b : BoundaryColoring c)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp0 : ∀ d < 3, p d = 0 ↔ d = 0)
    (hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)))
    (mMax : Nat) (hr : c.ringSize = mMax + 1)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd) :
    let X := permTraceVal p c.ringSize b mMax 0
    let X_full := permTraceVal p c.ringSize b c.ringSize 0
    let kBucket := wordK mMax X
    let isEven := Nat.beq (Nat.mod kBucket 2) 0
    let twoP := selectBool isEven kBucket (Nat.add kBucket 1)
    ∃ m : List (Nat × Nat),
      IsExtractedMatching c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd) 0 c.ringSize m ∧
      wordK c.ringSize X_full = twoP ∧
      2 * m.length = twoP ∧
      (kBucket % 2 = 0 → (popcountK kBucket (wordSign mMax X) + c.ringSize % 2) % 2 = 0) := by
  intro X X_full kBucket isEven twoP
  rcases exists_ncMatching_of_partition c b equiv_ab equiv_cd h_ring hPart with ⟨m, _, hExt⟩
  have hDiff := wordK_extractedMatching_eq c b (partEquiv equiv_ab equiv_cd) p hp3 hp0 h_ring hb hExt
  change wordK c.ringSize X_full = wordK 0 X_full + 2 * m.length at hDiff
  have hK0 : wordK 0 X_full = 0 := rfl
  rw [hK0, Nat.zero_add] at hDiff
  have hKm_eq : wordK mMax X_full = kBucket :=
    (wordK_permTraceVal_eq_of_le p hp3 c.ringSize b mMax mMax c.ringSize 0 (Nat.le_refl mMax) (by omega)).symm
  have hKr_step : wordK c.ringSize X_full = kBucket + (if (X_full / 3 ^ mMax) % 3 = 0 then 0 else 1) := by
    have h1 := wordK_succ_right mMax X_full
    rw [← hr, hKm_eq] at h1
    exact h1
  have hTwoP_eq : wordK c.ringSize X_full = twoP := by
    dsimp [twoP, isEven]
    cases hEvenB : Nat.beq (Nat.mod kBucket 2) 0 with
    | true =>
      have hEven : kBucket % 2 = 0 := Nat.beq_eq.mp hEvenB
      dsimp
      split at hKr_step <;> omega
    | false =>
      have hOdd : kBucket % 2 ≠ 0 := by
        intro h0
        have : Nat.beq (Nat.mod kBucket 2) 0 = true := Nat.beq_eq.mpr h0
        rw [hEvenB] at this; contradiction
      dsimp
      split at hKr_step <;> omega
  refine ⟨m, hExt, hTwoP_eq, by omega, ?_⟩
  intro hEven
  have hLast0 : (X_full / 3 ^ mMax) % 3 = 0 := by
    split at hKr_step
    · assumption
    · omega
  have hPop_eq : popcountK kBucket (wordSign mMax X) =
      popcountK (wordK c.ringSize X_full) (wordSign c.ringSize X_full) := by
    have h1 := popcount_wordSign_permTraceVal_eq_of_le p hp3 c.ringSize b mMax mMax c.ringSize 0 (Nat.le_refl mMax) (by omega)
    change popcountK kBucket (wordSign mMax X) = popcountK (wordK mMax X_full) (wordSign mMax X_full) at h1
    have h2 := popcount_wordSign_succ_right mMax X_full
    rw [← hr, hLast0, if_neg (by decide), Nat.add_zero] at h2
    omega
  rw [hPop_eq]
  have hSum := wordK_eq_wordOnes_add_popcount c.ringSize X_full
  have hRel := wordOnes_or_popcount_eq_rangeDigitOneCount c b p hp3 hp0 c.ringSize (Nat.le_refl c.ringSize)
  change (p 1 = 1 ∧ p 2 = 2 → wordOnes c.ringSize X_full = rangeDigitOneCount c.ringSize b 0 c.ringSize) ∧
    (p 1 = 2 ∧ p 2 = 1 → popcountK (wordK c.ringSize X_full) (wordSign c.ringSize X_full) =
      rangeDigitOneCount c.ringSize b 0 c.ringSize) at hRel
  have hPar := rangeDigitOneCount_prefix_mod_two c b h_ring hb c.ringSize (Nat.le_refl c.ringSize)
  rw [Nat.mod_self] at hPar
  rcases hp12 1 2 (Or.inl ⟨rfl, rfl⟩) with h12 | h21
  · have hO := hRel.1 h12
    omega
  · have hP := hRel.2 h21
    omega

theorem testBit_evenParityMask_wordBlock (r mMax X : Nat)
    (hmMax : mMax ≤ 13)
    (hPar : (popcountK (wordK mMax X) (wordSign mMax X) + r % 2) % 2 = 0) :
    let kBucket := wordK mMax X
    let M := binom mMax kBucket
    let pCell := buildThueMorseParityAux (Nat.mod r 2) kBucket 1 1 0
    let ep := repeatBlock pCell (Nat.shiftLeft 1 kBucket) M
    Nat.testBit ep (wordBlock mMax X) = true := by
  intro kBucket M pCell ep
  have hStride_pos : 0 < (1 <<< kBucket) := shiftLeft_one_pos kBucket
  have hpCell_lt : pCell < 2 ^ (1 <<< kBucket) := by
    have h1 := buildThueMorseParityAux_lt (r % 2) kBucket 1 1 0 (by decide) (by decide)
    rw [Nat.one_mul] at h1
    exact h1
  change Nat.testBit (repeatBlock pCell (1 <<< kBucket) M)
    (wordCell mMax X * (1 <<< kBucket) + wordSign mMax X) = true
  rw [testBit_repeatBlock pCell (1 <<< kBucket) M _ hStride_pos hpCell_lt]
  have hCell_lt : wordCell mMax X < M := wordCell_lt mMax X hmMax
  have hSign_lt : wordSign mMax X < (1 <<< kBucket) := wordSign_lt mMax X
  have hIdx_lt : wordCell mMax X * (1 <<< kBucket) + wordSign mMax X < M * (1 <<< kBucket) :=
    mul_add_lt_mul (wordCell mMax X) M (1 <<< kBucket) (wordSign mMax X) hCell_lt hSign_lt
  have hIdx_mod : (wordCell mMax X * (1 <<< kBucket) + wordSign mMax X) % (1 <<< kBucket) = wordSign mMax X := by
    rw [Nat.add_comm (wordCell mMax X * (1 <<< kBucket)) (wordSign mMax X),
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hSign_lt]
  rw [decide_eq_true hIdx_lt, Bool.true_and, hIdx_mod]
  have hTest := testBit_buildThueMorseParityAux (r % 2) kBucket 1 1 0 (wordSign mMax X) 0
    (Nat.mod_lt r (by decide)) (by decide) (by decide) (by decide) hSign_lt (by decide)
  rw [Nat.mul_one, Nat.add_zero] at hTest
  change Nat.testBit (buildThueMorseParityAux (r % 2) kBucket 1 1 0) (wordSign mMax X) = true
  rw [hTest, if_pos hPar]
  rfl

theorem testBit_evenHalfMask_wordProj (mMax X : Nat)
    (hmMax : mMax ≤ 13)
    (hk : 0 < wordK mMax X) :
    let kBucket := wordK mMax X
    let numBits := kBucket - 1
    let M := binom mMax kBucket
    let hCell := Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.sub kBucket 1))) 1
    let eh := repeatBlock hCell (Nat.shiftLeft 1 kBucket) M
    Nat.testBit eh (wordProj mMax numBits X) = true := by
  intro kBucket numBits M hCell eh
  have hStride_pos : 0 < (1 <<< kBucket) := shiftLeft_one_pos kBucket
  have hCell_eq : hCell = 2 ^ (1 <<< numBits) - 1 := by
    change (1 <<< (1 <<< numBits)) - 1 = 2 ^ (1 <<< numBits) - 1
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hHalf_le : (1 <<< numBits) ≤ (1 <<< kBucket) := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.one_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hCell_lt : hCell < 2 ^ (1 <<< kBucket) := by
    rw [hCell_eq]
    have h1 : 2 ^ (1 <<< numBits) ≤ 2 ^ (1 <<< kBucket) :=
      Nat.pow_le_pow_right (by decide) hHalf_le
    have h2 : 0 < 2 ^ (1 <<< numBits) := Nat.two_pow_pos (1 <<< numBits)
    omega
  change Nat.testBit (repeatBlock hCell (1 <<< kBucket) M)
    (wordCell mMax X * (1 <<< kBucket) + wordSign mMax X % (1 <<< numBits)) = true
  rw [testBit_repeatBlock hCell (1 <<< kBucket) M _ hStride_pos hCell_lt]
  have hc_lt : wordCell mMax X < M := wordCell_lt mMax X hmMax
  have hMod_lt : wordSign mMax X % (1 <<< numBits) < (1 <<< numBits) :=
    wordSign_mod_lt mMax numBits X
  have hMod_lt_k : wordSign mMax X % (1 <<< numBits) < (1 <<< kBucket) :=
    Nat.lt_of_lt_of_le hMod_lt hHalf_le
  have hIdx_lt : wordCell mMax X * (1 <<< kBucket) + wordSign mMax X % (1 <<< numBits) < M * (1 <<< kBucket) :=
    mul_add_lt_mul (wordCell mMax X) M (1 <<< kBucket) (wordSign mMax X % (1 <<< numBits)) hc_lt hMod_lt_k
  have hIdx_mod : (wordCell mMax X * (1 <<< kBucket) + wordSign mMax X % (1 <<< numBits)) % (1 <<< kBucket) =
      wordSign mMax X % (1 <<< numBits) := by
    rw [Nat.add_comm (wordCell mMax X * (1 <<< kBucket)) _,
        Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hMod_lt_k]
  rw [decide_eq_true hIdx_lt, Bool.true_and, hIdx_mod, hCell_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hMod_lt

theorem buildBucketCatalanSpec_succ (r mMax k' : Nat) :
    (buildBucketCatalanSpec r mMax (k' + 1)).val =
      let kBucket := k' + 1
      let M := binom mMax kBucket
      let isEven := Nat.beq (Nat.mod kBucket 2) 0
      let numBits := selectBool isEven (Nat.sub kBucket 1) kBucket
      let twoP := selectBool isEven kBucket (Nat.add kBucket 1)
      let halfShift := selectBool isEven (Nat.shiftLeft 1 (Nat.sub kBucket 1)) 0
      let eh := selectBool isEven
        (let hCell := Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.sub kBucket 1))) 1
         repeatBlock hCell (Nat.shiftLeft 1 kBucket) M) 0
      let ep := selectBool isEven
        (let pCell := buildThueMorseParityAux (Nat.mod r 2) kBucket 1 1 0
         repeatBlock pCell (Nat.shiftLeft 1 kBucket) M) 0
      let m0List := (buildM0List kBucket numBits M).val
      let trie := (buildCatalanTrieAux twoP m0List 20 [(0, twoP)]).val
      BucketCatalanSpec.mk kBucket isEven halfShift eh ep trie := rfl

theorem evalBucketSpec_buildBucketCatalanSpec_false_sound
    (c : Configuration) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp0 : ∀ d < 3, p d = 0 ↔ d = 0)
    (hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)))
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (b : BoundaryColoring c) (mMax B : Nat)
    (hr : c.ringSize = mMax + 1) (hmMax : mMax ≤ 13)
    (h_ring : IsRingCycle c)
    (hb : IsValidBoundaryColoring c b)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd)
    (hFalse :
      let X := permTraceVal p c.ringSize b mMax 0
      let kBucket := wordK mMax X
      let bSpec := (buildBucketCatalanSpec c.ringSize mMax kBucket).val
      Nat.testBit (evalBucketSpec bSpec B) (wordBlock mMax X) = false) :
    ∃ b',
      SameActiveClass c p equiv_ab equiv_cd b b' ∧
      Nat.testBit B (wordBlock mMax (permTraceVal p c.ringSize b' mMax 0)) = false := by
  let X := permTraceVal p c.ringSize b mMax 0
  let X_full := permTraceVal p c.ringSize b c.ringSize 0
  let kBucket := wordK mMax X
  rcases hk : kBucket with _ | k'
  · dsimp at hFalse
    change Nat.testBit (evalBucketSpec (buildBucketCatalanSpec c.ringSize mMax kBucket).val B) (wordBlock mMax X) = false at hFalse
    rw [hk] at hFalse
    exact ⟨b, sameActiveClass_refl c p equiv_ab equiv_cd b, hFalse⟩
  · have hk_pos : 0 < kBucket := by omega
    have hk_beq : Nat.beq kBucket 0 = false := by
      rw [hk]; rfl
    rcases wordK_full_and_popcount_parity c b equiv_ab equiv_cd p hp3 hp0 hp12 mMax hr h_ring hb hPart with
      ⟨m, hExt, hTwoP_eq, h2m_eq, hParEven⟩
    let isEven := Nat.beq (Nat.mod kBucket 2) 0
    let numBits := selectBool isEven (Nat.sub kBucket 1) kBucket
    let twoP := selectBool isEven kBucket (Nat.add kBucket 1)
    let M := binom mMax kBucket
    let m0List := (buildM0List kBucket numBits M).val
    let trie := (buildCatalanTrieAux twoP m0List 20 [(0, twoP)]).val
    change wordK c.ringSize X_full = twoP at hTwoP_eq
    change 2 * m.length = twoP at h2m_eq
    change kBucket % 2 = 0 → (popcountK kBucket (wordSign mMax X) + c.ringSize % 2) % 2 = 0 at hParEven
    have hSpec_eq : (buildBucketCatalanSpec c.ringSize mMax kBucket).val =
        let halfShift := selectBool isEven (Nat.shiftLeft 1 (Nat.sub kBucket 1)) 0
        let eh := selectBool isEven
          (let hCell := Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.sub kBucket 1))) 1
           repeatBlock hCell (Nat.shiftLeft 1 kBucket) M) 0
        let ep := selectBool isEven
          (let pCell := buildThueMorseParityAux (Nat.mod c.ringSize 2) kBucket 1 1 0
           repeatBlock pCell (Nat.shiftLeft 1 kBucket) M) 0
        BucketCatalanSpec.mk kBucket isEven halfShift eh ep trie := by
      have h1 := buildBucketCatalanSpec_succ c.ringSize mMax k'
      rw [← hk] at h1
      exact h1
    dsimp at hFalse
    change Nat.testBit (evalBucketSpec (buildBucketCatalanSpec c.ringSize mMax kBucket).val B) (wordBlock mMax X) = false at hFalse
    rw [hSpec_eq] at hFalse
    have hK_le_mMax : kBucket ≤ mMax := wordK_le mMax X
    have hTwoP_pos : 2 ≤ twoP := by
      dsimp [twoP, isEven]
      cases hE : Nat.beq (Nat.mod kBucket 2) 0 with
      | true =>
        have : kBucket % 2 = 0 := Nat.beq_eq.mp hE
        dsimp; omega
      | false =>
        dsimp; omega
    have hm_pos : 0 < m.length := by omega
    have hm_le20 : m.length + 0 ≤ 20 := by
      have : twoP ≤ 14 := by
        dsimp [twoP]
        cases isEven <;> dsimp <;> omega
      omega
    have hStack : ValidIntervalStack c.ringSize (theta1Pair b) (partEquiv equiv_ab equiv_cd)
        X_full twoP [(0, twoP)] (m.length + 0) := by
      have h0 : (0 : Nat) = wordK 0 X_full := rfl
      rw [h0, ← hTwoP_eq]
      exact ValidIntervalStack.cons 0 c.ringSize 0 m [] hExt hm_pos (by omega) ValidIntervalStack.nil
    cases hEvenB : isEven with
    | false =>
      have hNum_eq : numBits = kBucket := by dsimp [numBits]; rw [hEvenB]
      have hTwoP_sub : twoP - 1 = numBits := by
        dsimp [twoP, numBits]; rw [hEvenB]; rfl
      have hTrieFalse : Nat.testBit (evalCatalanTrie trie B) (wordBlock mMax X) = false := by
        rw [hEvenB] at hFalse
        exact evalBucketSpec_odd_false_sound kBucket _ _ _ trie B (wordBlock mMax X) hk_beq hFalse
      have hProj_eq : ∀ q, wordK mMax q = kBucket → wordProj mMax numBits q = wordBlock mMax q := by
        intro q hKq
        dsimp [wordProj, wordBlock]
        rw [hNum_eq, ← hKq, Nat.mod_eq_of_lt (wordSign_lt mMax q)]
      rw [← hProj_eq X rfl] at hTrieFalse
      have hNum_le : numBits ≤ wordK mMax (permTraceVal p c.ringSize b mMax 0) := by
        change numBits ≤ kBucket; omega
      rcases evalCatalanTrie_buildCatalanTrieAux_false_sound c p hp3 hp0 hp12 equiv_ab equiv_cd b
        mMax numBits twoP 20 (m.length + 0) [(0, twoP)] hr hmMax h_ring hb hPart
        hNum_le hTwoP_sub hStack hm_le20 B hTrieFalse with ⟨b', hSame', hB'⟩
      have hKb' : wordK mMax (permTraceVal p c.ringSize b' mMax 0) = kBucket := by
        rw [wordK_permTraceVal_eq_of_le p hp3 c.ringSize b' mMax mMax c.ringSize 0 (Nat.le_refl mMax) (by omega),
            hSame'.2 mMax,
            ← wordK_permTraceVal_eq_of_le p hp3 c.ringSize b mMax mMax c.ringSize 0 (Nat.le_refl mMax) (by omega)]
      rw [hProj_eq _ hKb'] at hB'
      exact ⟨b', hSame', hB'⟩
    | true =>
      have hEven : kBucket % 2 = 0 := Nat.beq_eq.mp hEvenB
      have hNum_eq : numBits = kBucket - 1 := by dsimp [numBits]; rw [hEvenB]
      have hTwoP_sub : twoP - 1 = numBits := by
        dsimp [twoP, numBits]; rw [hEvenB]
      let halfShift := Nat.shiftLeft 1 (Nat.sub kBucket 1)
      let hCell := Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.sub kBucket 1))) 1
      let eh := repeatBlock hCell (Nat.shiftLeft 1 kBucket) M
      let pCell := buildThueMorseParityAux (Nat.mod c.ringSize 2) kBucket 1 1 0
      let ep := repeatBlock pCell (Nat.shiftLeft 1 kBucket) M
      have hEp_true : Nat.testBit ep (wordBlock mMax X) = true :=
        testBit_evenParityMask_wordBlock c.ringSize mMax X hmMax (hParEven hEven)
      rw [hEvenB] at hFalse
      dsimp at hFalse
      have hEvenSound := evalBucketSpec_even_false_sound kBucket halfShift eh ep trie B
        (wordBlock mMax X) hk_beq hEp_true hFalse
      let workB := Nat.lor (Nat.land B eh) (Nat.land (Nat.shiftRight B halfShift) eh)
      change Nat.testBit (evalCatalanTrie trie workB) (wordBlock mMax X) = false ∧
        (halfShift ≤ wordBlock mMax X →
          Nat.testBit (evalCatalanTrie trie workB) (wordBlock mMax X - halfShift) = false) at hEvenSound
      have hHalf_eq : halfShift = 1 <<< numBits := by
        change 1 <<< (kBucket - 1) = 1 <<< numBits
        rw [hNum_eq]
      have hSign_lt : wordSign mMax X < 2 * halfShift := by
        have h1 := wordSign_lt mMax X
        change wordSign mMax X < (1 <<< kBucket) at h1
        have h2 : kBucket = numBits + 1 := by omega
        rw [h2, shiftLeft_one_succ, ← hHalf_eq] at h1
        exact h1
      have hTrieFalse : Nat.testBit (evalCatalanTrie trie workB) (wordProj mMax numBits X) = false := by
        by_cases hLt : wordSign mMax X < halfShift
        · have hEq : wordProj mMax numBits X = wordBlock mMax X := by
            dsimp [wordProj, wordBlock]
            rw [← hHalf_eq, Nat.mod_eq_of_lt hLt]
          rw [hEq]
          exact hEvenSound.1
        · have hLe : halfShift ≤ wordBlock mMax X := by
            dsimp [wordBlock]; omega
          have hEq : wordProj mMax numBits X = wordBlock mMax X - halfShift := by
            dsimp [wordProj, wordBlock]
            rw [← hHalf_eq]
            have hMod : wordSign mMax X % halfShift = wordSign mMax X - halfShift := by
              have hSub : wordSign mMax X - halfShift < halfShift := by omega
              have hAdd : wordSign mMax X = (wordSign mMax X - halfShift) + halfShift * 1 := by omega
              conv => lhs; rw [hAdd]
              rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hSub]
            rw [hMod]
            omega
          rw [hEq]
          exact hEvenSound.2 hLe
      have hNum_le : numBits ≤ wordK mMax (permTraceVal p c.ringSize b mMax 0) := by
        change numBits ≤ kBucket; omega
      rcases evalCatalanTrie_buildCatalanTrieAux_false_sound c p hp3 hp0 hp12 equiv_ab equiv_cd b
        mMax numBits twoP 20 (m.length + 0) [(0, twoP)] hr hmMax h_ring hb hPart
        hNum_le hTwoP_sub hStack hm_le20 workB hTrieFalse with ⟨b', hSame', hWorkB'⟩
      let X' := permTraceVal p c.ringSize b' mMax 0
      have hKb' : wordK mMax X' = kBucket := by
        dsimp [X']
        rw [wordK_permTraceVal_eq_of_le p hp3 c.ringSize b' mMax mMax c.ringSize 0 (Nat.le_refl mMax) (by omega),
            hSame'.2 mMax,
            ← wordK_permTraceVal_eq_of_le p hp3 c.ringSize b mMax mMax c.ringSize 0 (Nat.le_refl mMax) (by omega)]
      have hEh' : Nat.testBit eh (wordProj mMax numBits X') = true := by
        have h1 := testBit_evenHalfMask_wordProj mMax X' hmMax (by omega)
        change Nat.testBit
          (repeatBlock (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.sub (wordK mMax X') 1))) 1)
            (Nat.shiftLeft 1 (wordK mMax X')) (binom mMax (wordK mMax X')))
          (wordProj mMax (wordK mMax X' - 1) X') = true at h1
        rw [hKb', ← hNum_eq] at h1
        exact h1
      change Nat.testBit (Nat.lor (Nat.land B eh) (Nat.land (Nat.shiftRight B halfShift) eh))
        (wordProj mMax numBits X') = false at hWorkB'
      rw [testBit_lor, Bool.or_eq_false_iff, testBit_land, hEh', Bool.and_true,
          testBit_land, hEh', Bool.and_true, testBit_shiftRight] at hWorkB'
      have hSign'_lt : wordSign mMax X' < 2 * halfShift := by
        have h1 := wordSign_lt mMax X'
        rw [hKb'] at h1
        have h2 : kBucket = numBits + 1 := by omega
        rw [h2, shiftLeft_one_succ, ← hHalf_eq] at h1
        exact h1
      refine ⟨b', hSame', ?_⟩
      change Nat.testBit B (wordBlock mMax X') = false
      by_cases hLt' : wordSign mMax X' < halfShift
      · have hEq' : wordBlock mMax X' = wordProj mMax numBits X' := by
          dsimp [wordBlock, wordProj]
          rw [hKb', ← hHalf_eq, Nat.mod_eq_of_lt hLt']
        rw [hEq']
        exact hWorkB'.1
      · have hEq' : wordBlock mMax X' = halfShift + wordProj mMax numBits X' := by
          dsimp [wordBlock, wordProj]
          rw [hKb', ← hHalf_eq]
          have hMod : wordSign mMax X' % halfShift = wordSign mMax X' - halfShift := by
            have hSub : wordSign mMax X' - halfShift < halfShift := by omega
            have hAdd : wordSign mMax X' = (wordSign mMax X' - halfShift) + halfShift * 1 := by omega
            conv => lhs; rw [hAdd]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hSub]
          rw [hMod]
          omega
        rw [hEq']
        exact hWorkB'.2

noncomputable def mapEvalBuckets : List BucketCatalanSpec → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | bSpec :: restSpecs, B :: restB => evalBucketSpec bSpec B :: mapEvalBuckets restSpecs restB

theorem revList_evalAllBucketsRev (specs : List BucketCatalanSpec) (buckets acc : List Nat) :
    revList (evalAllBucketsRev specs buckets acc) = acc.reverse ++ mapEvalBuckets specs buckets := by
  rw [revList_eq_reverse]
  induction specs generalizing buckets acc with
  | nil =>
    change acc.reverse = acc.reverse ++ []
    rw [List.append_nil]
  | cons bSpec restSpecs ih =>
    cases buckets with
    | nil =>
      change acc.reverse = acc.reverse ++ []
      rw [List.append_nil]
    | cons B restB =>
      dsimp [mapEvalBuckets]
      change (evalAllBucketsRev restSpecs restB (evalBucketSpec bSpec B :: acc)).reverse = _
      rw [ih restB _, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem evalAllBuckets_eq_mapEvalBuckets (specs : List BucketCatalanSpec) (buckets : List Nat) :
    evalAllBuckets specs buckets = mapEvalBuckets specs buckets := by
  unfold evalAllBuckets
  rw [revList_evalAllBucketsRev, List.reverse_nil, List.nil_append]

theorem mapEvalBuckets_length (specs : List BucketCatalanSpec) (buckets : List Nat)
    (h : specs.length ≤ buckets.length) :
    (mapEvalBuckets specs buckets).length = specs.length := by
  induction specs generalizing buckets with
  | nil => rfl
  | cons bSpec restSpecs ih =>
    cases buckets with
    | nil => dsimp at h; omega
    | cons B restB =>
      dsimp [mapEvalBuckets]
      rw [ih restB (by dsimp at h; omega)]

theorem mapEvalBuckets_getD (specs : List BucketCatalanSpec) (buckets : List Nat) (k : Nat)
    (hk : k < specs.length) (h : specs.length ≤ buckets.length) :
    (mapEvalBuckets specs buckets).getD k 0 =
      evalBucketSpec (specs.getD k default) (buckets.getD k 0) := by
  induction specs generalizing buckets k with
  | nil => dsimp at hk; omega
  | cons bSpec restSpecs ih =>
    cases buckets with
    | nil => dsimp at h; omega
    | cons B restB =>
      cases k with
      | zero => rfl
      | succ k' =>
        dsimp [mapEvalBuckets]
        rw [list_getD_succ, list_getD_succ, list_getD_succ]
        exact ih restB k' (by dsimp at hk; omega) (by dsimp at h; omega)

noncomputable def bucketSpecsPrefix (r mMax : Nat) : Nat → List BucketCatalanSpec
  | 0 => []
  | c + 1 => bucketSpecsPrefix r mMax c ++ [(buildBucketCatalanSpec r mMax c).val]

theorem buildAllBucketSpecs_eq (r mMax : Nat) :
    (buildAllBucketSpecs r mMax).val = bucketSpecsPrefix r mMax r := by
  unfold buildAllBucketSpecs
  have hAux : ∀ (c : Nat) (acc : List BucketCatalanSpec),
      (@Nat.rec (fun _ => List BucketCatalanSpec → StrictBox (List BucketCatalanSpec))
        (fun acc => StrictBox.mk acc)
        (fun kIdx ih acc => ih ((buildBucketCatalanSpec r mMax kIdx).val :: acc))
        c acc).val = bucketSpecsPrefix r mMax c ++ acc := by
    intro c
    induction c with
    | zero => intro acc; rfl
    | succ c' ih =>
      intro acc
      change _ = bucketSpecsPrefix r mMax c' ++ [(buildBucketCatalanSpec r mMax c').val] ++ acc
      rw [List.append_assoc, List.singleton_append]
      exact ih ((buildBucketCatalanSpec r mMax c').val :: acc)
  have hMain := hAux r []
  rw [List.append_nil] at hMain
  exact hMain

theorem bucketSpecsPrefix_length (r mMax c : Nat) :
    (bucketSpecsPrefix r mMax c).length = c := by
  induction c with
  | zero => rfl
  | succ c' ih =>
    dsimp [bucketSpecsPrefix]
    rw [List.length_append, ih, List.length_singleton]

theorem bucketSpecsPrefix_getD (r mMax c k : Nat) (hk : k < c) :
    (bucketSpecsPrefix r mMax c).getD k default = (buildBucketCatalanSpec r mMax k).val := by
  induction c with
  | zero => omega
  | succ c' ih =>
    dsimp [bucketSpecsPrefix]
    by_cases hEq : k = c'
    · subst hEq
      have hLen := bucketSpecsPrefix_length r mMax k
      conv => lhs; arg 2; rw [← hLen]
      exact list_getD_append_singleton_self (bucketSpecsPrefix r mMax k) (buildBucketCatalanSpec r mMax k).val default
    · have hLt : k < (bucketSpecsPrefix r mMax c').length := by
        rw [bucketSpecsPrefix_length]; omega
      rw [list_getD_append_left _ _ _ default hLt]
      exact ih (by omega)

theorem evalAllBuckets_false_sound
    (c : Configuration) (p : Nat → Nat)
    (hp3 : ∀ d < 3, p d < 3)
    (hp0 : ∀ d < 3, p d = 0 ↔ d = 0)
    (hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)))
    (equiv_ab equiv_cd : Nat → Nat → Prop)
    (b : BoundaryColoring c) (mMax : Nat) (buckets : List Nat)
    (hr : c.ringSize = mMax + 1) (hmMax : mMax ≤ 13)
    (hLen : c.ringSize ≤ buckets.length)
    (h_ring : IsRingCycle c)
    (hb : IsValidBoundaryColoring c b)
    (hPart : IsJointPlanarRingPartition c b theta1 equiv_ab equiv_cd)
    (hFalse :
      let X := permTraceVal p c.ringSize b mMax 0
      let kBucket := wordK mMax X
      let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
      Nat.testBit ((evalAllBuckets bucketSpecs buckets).getD kBucket 0) (wordBlock mMax X) = false) :
    ∃ b',
      SameActiveClass c p equiv_ab equiv_cd b b' ∧
      let X' := permTraceVal p c.ringSize b' mMax 0
      Nat.testBit (buckets.getD (wordK mMax X') 0) (wordBlock mMax X') = false := by
  let X := permTraceVal p c.ringSize b mMax 0
  let kBucket := wordK mMax X
  have hk_lt : kBucket < c.ringSize := by
    have := wordK_le mMax X
    omega
  dsimp at hFalse
  rw [buildAllBucketSpecs_eq, evalAllBuckets_eq_mapEvalBuckets,
      mapEvalBuckets_getD _ buckets kBucket
        (by rw [bucketSpecsPrefix_length]; exact hk_lt)
        (by rw [bucketSpecsPrefix_length]; exact hLen),
      bucketSpecsPrefix_getD c.ringSize mMax c.ringSize kBucket hk_lt] at hFalse
  rcases evalBucketSpec_buildBucketCatalanSpec_false_sound c p hp3 hp0 hp12 equiv_ab equiv_cd b
    mMax (buckets.getD kBucket 0) hr hmMax h_ring hb hPart hFalse with ⟨b', hSame', hB'⟩
  have hKb' : wordK mMax (permTraceVal p c.ringSize b' mMax 0) = kBucket := by
    rw [wordK_permTraceVal_eq_of_le p hp3 c.ringSize b' mMax mMax c.ringSize 0 (Nat.le_refl mMax) (by omega),
        hSame'.2 mMax,
        ← wordK_permTraceVal_eq_of_le p hp3 c.ringSize b mMax mMax c.ringSize 0 (Nat.le_refl mMax) (by omega)]
  refine ⟨b', hSame', ?_⟩
  dsimp
  rw [hKb']
  exact hB'

/-!
### Part 6: Full-Round Soundness of `kempeRound` and `stepKempeRounds`
-/

def IsPerm3 (p : Nat → Nat) : Prop :=
  p 0 < 3 ∧ p 1 < 3 ∧ p 2 < 3 ∧ p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 1 ≠ p 2

theorem isPerm3_lt_three {p : Nat → Nat} (hp : IsPerm3 p) (d : Nat) (hd : d < 3) :
    p d < 3 := by
  rcases hp with ⟨h0, h1, h2, _⟩
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> assumption

theorem isPerm3_comp {f g : Nat → Nat} (hf : IsPerm3 f) (hg : IsPerm3 g) :
    IsPerm3 (fun d => f (g d)) := by
  rcases hf with ⟨hf0, hf1, hf2, hf01, hf02, hf12⟩
  rcases hg with ⟨hg0, hg1, hg2, hg01, hg02, hg12⟩
  dsimp [IsPerm3]
  rcases (by omega : g 0 = 0 ∨ g 0 = 1 ∨ g 0 = 2) with h0 | h0 | h0 <;>
  rcases (by omega : g 1 = 0 ∨ g 1 = 1 ∨ g 1 = 2) with h1 | h1 | h1 <;>
  rcases (by omega : g 2 = 0 ∨ g 2 = 1 ∨ g 2 = 2) with h2 | h2 | h2 <;>
  · rw [h0, h1, h2]; omega

theorem isPerm3_id : IsPerm3 (fun d => d) := by
  dsimp [IsPerm3]; omega

theorem isPerm3_swap12 : IsPerm3 swap12Digit := by
  unfold IsPerm3; decide

theorem isPerm3_swap01 : IsPerm3 swap01Digit := by
  unfold IsPerm3; decide

theorem isPerm3_swap02 : IsPerm3 swap02Digit := by
  unfold IsPerm3; decide

theorem isPerm3_canonDigitPerm (r : Nat) (b : Nat → Color) :
    IsPerm3 (canonDigitPerm r b) := by
  unfold canonDigitPerm canonPairing
  split <;> (unfold IsPerm3; decide)

theorem isPerm3_zero_fix {p q : Nat → Nat} (hp : IsPerm3 p) (hq : IsPerm3 q)
    (dTop : Nat) (hdTop : dTop < 3) (hpTop : p dTop = 0) (hqTop : q dTop = 0) :
    (∀ d < 3, p d = q d) ∨ (∀ d < 3, p d = swap12Digit (q d)) := by
  rcases hp with ⟨hp0, hp1, hp2, hp01, hp02, hp12⟩
  rcases hq with ⟨hq0, hq1, hq2, hq01, hq02, hq12⟩
  have hCases :
      (p 0 = q 0 ∧ p 1 = q 1 ∧ p 2 = q 2) ∨
      (p 0 = swap12Digit (q 0) ∧ p 1 = swap12Digit (q 1) ∧ p 2 = swap12Digit (q 2)) := by
    rcases (by omega : dTop = 0 ∨ dTop = 1 ∨ dTop = 2) with rfl | rfl | rfl
    · rcases (by omega : (p 1 = 1 ∧ p 2 = 2) ∨ (p 1 = 2 ∧ p 2 = 1)) with ⟨hp1', hp2'⟩ | ⟨hp1', hp2'⟩ <;>
      rcases (by omega : (q 1 = 1 ∧ q 2 = 2) ∨ (q 1 = 2 ∧ q 2 = 1)) with ⟨hq1', hq2'⟩ | ⟨hq1', hq2'⟩ <;>
      · rw [hpTop, hqTop, hp1', hp2', hq1', hq2']; decide
    · rcases (by omega : (p 0 = 1 ∧ p 2 = 2) ∨ (p 0 = 2 ∧ p 2 = 1)) with ⟨hp0', hp2'⟩ | ⟨hp0', hp2'⟩ <;>
      rcases (by omega : (q 0 = 1 ∧ q 2 = 2) ∨ (q 0 = 2 ∧ q 2 = 1)) with ⟨hq0', hq2'⟩ | ⟨hq0', hq2'⟩ <;>
      · rw [hpTop, hqTop, hp0', hp2', hq0', hq2']; decide
    · rcases (by omega : (p 0 = 1 ∧ p 1 = 2) ∨ (p 0 = 2 ∧ p 1 = 1)) with ⟨hp0', hp1'⟩ | ⟨hp0', hp1'⟩ <;>
      rcases (by omega : (q 0 = 1 ∧ q 1 = 2) ∨ (q 0 = 2 ∧ q 1 = 1)) with ⟨hq0', hq1'⟩ | ⟨hq0', hq1'⟩ <;>
      · rw [hpTop, hqTop, hp0', hp1', hq0', hq1']; decide
  rcases hCases with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · left
    intro d hd
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> assumption
  · right
    intro d hd
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> assumption

theorem exists_theta_of_isPerm3 {π : Nat → Nat} (hπ : IsPerm3 π) :
    ∃ (θ : ColorPairing) (p : Nat → Nat),
      (p = (fun d => d) ∨ p = swap12Digit) ∧
      ∀ d < 3, π d = p (relabelDigit θ d) := by
  rcases hπ with ⟨h0, h1, h2, h01, h02, h12⟩
  have h6 :
      (π 0 = 0 ∧ π 1 = 1 ∧ π 2 = 2) ∨
      (π 0 = 0 ∧ π 1 = 2 ∧ π 2 = 1) ∨
      (π 0 = 1 ∧ π 1 = 0 ∧ π 2 = 2) ∨
      (π 0 = 2 ∧ π 1 = 0 ∧ π 2 = 1) ∨
      (π 0 = 2 ∧ π 1 = 1 ∧ π 2 = 0) ∨
      (π 0 = 1 ∧ π 1 = 2 ∧ π 2 = 0) := by omega
  rcases h6 with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · refine ⟨theta1, fun d => d, Or.inl rfl, ?_⟩
    intro d hd; rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> (try rw [e0]) <;> (try rw [e1]) <;> (try rw [e2]) <;> decide
  · refine ⟨theta1, swap12Digit, Or.inr rfl, ?_⟩
    intro d hd; rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> (try rw [e0]) <;> (try rw [e1]) <;> (try rw [e2]) <;> decide
  · refine ⟨theta2, fun d => d, Or.inl rfl, ?_⟩
    intro d hd; rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> (try rw [e0]) <;> (try rw [e1]) <;> (try rw [e2]) <;> decide
  · refine ⟨theta2, swap12Digit, Or.inr rfl, ?_⟩
    intro d hd; rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> (try rw [e0]) <;> (try rw [e1]) <;> (try rw [e2]) <;> decide
  · refine ⟨theta3, fun d => d, Or.inl rfl, ?_⟩
    intro d hd; rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> (try rw [e0]) <;> (try rw [e1]) <;> (try rw [e2]) <;> decide
  · refine ⟨theta3, swap12Digit, Or.inr rfl, ?_⟩
    intro d hd; rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;> (try rw [e0]) <;> (try rw [e1]) <;> (try rw [e2]) <;> decide

theorem permTraceVal_succ_right (p : Nat → Nat) (r : Nat) (b : Nat → Color) (k i : Nat) :
    permTraceVal p r b (k + 1) i = permTraceVal p r b k i + p (edgeDigitAt r b (i + k)) * 3 ^ k := by
  induction k generalizing i with
  | zero =>
    dsimp [permTraceVal]
    omega
  | succ k' ih =>
    change p (edgeDigitAt r b i) + 3 * permTraceVal p r b (k' + 1) (i + 1) =
      (p (edgeDigitAt r b i) + 3 * permTraceVal p r b k' (i + 1)) +
        p (edgeDigitAt r b (i + (k' + 1))) * 3 ^ (k' + 1)
    rw [ih (i + 1), Nat.mul_add, Nat.pow_succ']
    have hAdd : i + 1 + k' = i + (k' + 1) := by omega
    rw [hAdd, ← Nat.mul_assoc 3 _ (3 ^ k'), Nat.mul_comm 3 (p (edgeDigitAt r b (i + (k' + 1)))),
        Nat.mul_assoc]
    omega

theorem permTraceVal_div_mod_pow3 (p : Nat → Nat) (hp : ∀ d < 3, p d < 3)
    (r : Nat) (b : Nat → Color) (k : Nat) :
    let X := permTraceVal p r b (k + 1) 0
    X / 3 ^ k = p (edgeDigitAt r b k) ∧
    X % 3 ^ k = permTraceVal p r b k 0 := by
  intro X
  have hEq : X = permTraceVal p r b k 0 + p (edgeDigitAt r b k) * 3 ^ k := by
    dsimp [X]
    rw [permTraceVal_succ_right, Nat.zero_add]
  have hLt : permTraceVal p r b k 0 < 3 ^ k := permTraceVal_lt_pow3 p hp r b k 0
  have hPos : 0 < 3 ^ k := pow3_pos k
  refine ⟨?_, ?_⟩
  · rw [hEq, Nat.add_mul_div_right _ _ hPos, Nat.div_eq_of_lt hLt, Nat.zero_add]
  · rw [hEq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hLt]

theorem packToBuckets_perm_false_sound (c : Configuration) (b' : BoundaryColoring c)
    (p : Nat → Nat) (hp : IsPerm3 p)
    (mMax L2 : Nat)
    (hr : c.ringSize = mMax + 1) (hmMax_lo : 1 ≤ mMax) (hmMax_hi : mMax ≤ 13)
    (hFalse :
      let mMax1 := mMax - 1
      let pTop := pow3 mMax1
      let swapSteps1 := (buildSwapSteps mMax1).val
      let l2_01 := swapDigits01 swapSteps1 L2
      let l2_02 := swapDigits02 swapSteps1 L2
      let d0_1 := Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop)
      let buckets := packToBuckets (buildAllPackUnpackLevels mMax).1 [L2, d0_1]
      let X' := permTraceVal p c.ringSize b' mMax 0
      Nat.testBit (buckets.getD (wordK mMax X') 0) (wordBlock mMax X') = false) :
    Nat.testBit L2 (canonIdx c.ringSize b') = false ∨
    Nat.testBit L2 (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b')) = false := by
  let mMax1 := mMax - 1
  let P_0 := 3 ^ mMax1
  let pTop := pow3 mMax1
  let swapSteps1 := (buildSwapSteps mMax1).val
  let l2_01 := swapDigits01 swapSteps1 L2
  let l2_02 := swapDigits02 swapSteps1 L2
  let d0_1 := Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop)
  let X' := permTraceVal p c.ringSize b' mMax 0
  have hp3 : ∀ d < 3, p d < 3 := isPerm3_lt_three hp
  have hmMax_eq : mMax = mMax1 + 1 := by omega
  have hDivMod : X' / P_0 = p (edgeDigitAt c.ringSize b' mMax1) ∧
      X' % P_0 = permTraceVal p c.ringSize b' mMax1 0 := by
    dsimp [X', P_0]
    rw [hmMax_eq]
    exact permTraceVal_div_mod_pow3 p hp3 c.ringSize b' mMax1
  have hBase := packToBuckets_false_sound mMax X' L2 d0_1 hmMax_lo hmMax_hi hFalse
  change Nat.testBit ([L2, d0_1].getD (wordK 1 (X' / P_0)) 0)
    (wordBlock 1 (X' / P_0) * P_0 + (X' % P_0)) = false at hBase
  let dTop := edgeDigitAt c.ringSize b' mMax1
  have hdTop_lt : dTop < 3 := edgeDigitAt_lt_three c.ringSize b' mMax1
  have hpTop_lt : p dTop < 3 := hp3 dTop hdTop_lt
  have hqLow_lt : permTraceVal p c.ringSize b' mMax1 0 < P_0 :=
    permTraceVal_lt_pow3 p hp3 c.ringSize b' mMax1 0
  have hP0_eq : pTop = P_0 := kernel_pow3_eq mMax1
  have hK1_0 : wordK 1 0 = 0 := rfl
  have hK1_1 : wordK 1 1 = 1 := rfl
  have hK1_2 : wordK 1 2 = 1 := rfl
  have hB1_0 : wordBlock 1 0 = 0 := rfl
  have hB1_1 : wordBlock 1 1 = 0 := rfl
  have hB1_2 : wordBlock 1 2 = 1 := rfl
  have hExF : ∃ f : Nat → Nat, IsPerm3 f ∧ f (p dTop) = 0 ∧
      Nat.testBit L2 (mapTernaryDigits f mMax1 (permTraceVal p c.ringSize b' mMax1 0)) = false := by
    rw [hDivMod.1, hDivMod.2] at hBase
    rcases (by omega : p dTop = 0 ∨ p dTop = 1 ∨ p dTop = 2) with h0 | h1 | h2
    · refine ⟨fun d => d, isPerm3_id, h0, ?_⟩
      rw [h0, hK1_0, hB1_0, Nat.zero_mul, Nat.zero_add, list_getD_zero] at hBase
      rwa [mapTernaryDigits_id mMax1 _ hqLow_lt]
    · refine ⟨swap01Digit, isPerm3_swap01, by rw [h1]; rfl, ?_⟩
      rw [h1, hK1_1, hB1_1, Nat.zero_mul, Nat.zero_add, list_getD_succ, list_getD_zero] at hBase
      change Nat.testBit (Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop))
        (permTraceVal p c.ringSize b' mMax1 0) = false at hBase
      rw [testBit_lor, Bool.or_eq_false_iff] at hBase
      exact swapDigits01_buildSwapSteps_false_sound mMax1 L2 _ hqLow_lt hBase.1
    · refine ⟨swap02Digit, isPerm3_swap02, by rw [h2]; rfl, ?_⟩
      rw [h2, hK1_2, hB1_2, Nat.one_mul, list_getD_succ, list_getD_zero] at hBase
      change Nat.testBit (Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop))
        (P_0 + permTraceVal p c.ringSize b' mMax1 0) = false at hBase
      rw [hP0_eq, testBit_lor, Bool.or_eq_false_iff] at hBase
      have hShift := hBase.2
      rw [testBit_shiftLeft, decide_eq_true (Nat.le_add_right P_0 _), Bool.true_and,
          Nat.add_sub_cancel_left] at hShift
      exact swapDigits02_buildSwapSteps_false_sound mMax1 L2 _ hqLow_lt hShift
  rcases hExF with ⟨f, hf, hfTop, hL2False⟩
  rw [mapTernaryDigits_permTraceVal f p hp3 c.ringSize b' mMax1 0] at hL2False
  have hSub2 : c.ringSize - 2 = mMax1 := by omega
  have hCanonTop : canonDigitPerm c.ringSize b' dTop = 0 := by
    dsimp [dTop]
    rw [← hSub2]
    exact canonDigitPerm_top_eq_zero c.ringSize b'
  rcases isPerm3_zero_fix (isPerm3_comp hf hp) (isPerm3_canonDigitPerm c.ringSize b')
    dTop hdTop_lt hfTop hCanonTop with hEqId | hEqSwap
  · left
    have hCongr : permTraceVal (fun d => f (p d)) c.ringSize b' mMax1 0 = canonIdx c.ringSize b' := by
      unfold canonIdx
      rw [hSub2]
      exact permTraceVal_congr (fun d => f (p d)) (canonDigitPerm c.ringSize b') hEqId c.ringSize b' mMax1 0
    rwa [← hCongr]
  · right
    have hCongr : permTraceVal (fun d => f (p d)) c.ringSize b' mMax1 0 =
        swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b') := by
      unfold swap12Idx canonIdx
      rw [hSub2, mapTernaryDigits_permTraceVal swap12Digit (canonDigitPerm c.ringSize b')
        (canonDigitPerm_lt_three c.ringSize b') c.ringSize b' mMax1 0]
      exact permTraceVal_congr (fun d => f (p d))
        (fun d => swap12Digit (canonDigitPerm c.ringSize b' d)) hEqSwap c.ringSize b' mMax1 0
    rwa [← hCongr]

theorem permTraceVal_relabelBoundary (c : Configuration) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (θ : ColorPairing) (p : Nat → Nat) (m i : Nat) (h_le : i + m ≤ c.ringSize) :
    permTraceVal p c.ringSize (relabelBoundary θ b) m i =
      permTraceVal (fun d => p (relabelDigit θ d)) c.ringSize b m i := by
  induction m generalizing i with
  | zero => rfl
  | succ m' ih =>
    have hi : i < c.ringSize := by omega
    have h_nxt : (i + 1) % c.ringSize < c.ringSize :=
      Nat.mod_lt (i + 1) (by have := h_ring.1; omega)
    have h_adj : c.adj i ((i + 1) % c.ringSize) = true := h_ring.2 i hi
    have h_ne : b i ≠ b ((i + 1) % c.ringSize) := hb i ((i + 1) % c.ringSize) hi h_nxt h_adj
    dsimp [permTraceVal]
    have hDigit : edgeDigitAt c.ringSize (relabelBoundary θ b) i =
        relabelDigit θ (edgeDigitAt c.ringSize b i) :=
      edge_digit_relabel θ (b i) (b ((i + 1) % c.ringSize)) h_ne
    rw [hDigit, ih (i + 1) (by omega)]

theorem elim_of_unpack_perm_false (c : Configuration) (b : BoundaryColoring c)
    (π : Nat → Nat) (hπ : IsPerm3 π)
    (mMax L2 : Nat)
    (hr : c.ringSize = mMax + 1) (hmMax_lo : 1 ≤ mMax) (hmMax_hi : mMax ≤ 13)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (hInv : KernelLiveInvariant c L2)
    (hX : permTraceVal π c.ringSize b mMax 0 < 2 * 3 ^ (mMax - 1))
    (hFalse :
      let mMax1 := mMax - 1
      let P_0 := 3 ^ mMax1
      let pTop := pow3 mMax1
      let swapSteps1 := (buildSwapSteps mMax1).val
      let l2_01 := swapDigits01 swapSteps1 L2
      let l2_02 := swapDigits02 swapSteps1 L2
      let d0_1 := Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop)
      let (packLevels, unpackRevLevels) := buildAllPackUnpackLevels mMax
      let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
      let buckets := packToBuckets packLevels [L2, d0_1]
      let covBuckets := evalAllBuckets bucketSpecs buckets
      let finalD := unpackFromBucketsAux unpackRevLevels covBuckets
      let X := permTraceVal π c.ringSize b mMax 0
      Nat.testBit (finalD.getD (X / P_0) 0) (X % P_0) = false) :
    Eliminated c b := by
  let mMax1 := mMax - 1
  let P_0 := 3 ^ mMax1
  let pTop := pow3 mMax1
  let swapSteps1 := (buildSwapSteps mMax1).val
  let l2_01 := swapDigits01 swapSteps1 L2
  let l2_02 := swapDigits02 swapSteps1 L2
  let d0_1 := Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop)
  let packLevels := (buildAllPackUnpackLevels mMax).1
  let unpackRevLevels := (buildAllPackUnpackLevels mMax).2
  let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
  let buckets := packToBuckets packLevels [L2, d0_1]
  let covBuckets := evalAllBuckets bucketSpecs buckets
  let X := permTraceVal π c.ringSize b mMax 0
  have hBucketsLen : c.ringSize ≤ buckets.length := by
    dsimp [buckets, packLevels]
    rw [buildAllPackUnpackLevels_eq]
    dsimp
    have h1 := packLevelsPrefix_length_out mMax (mMax - 1) [L2, d0_1] (Nat.le_refl 2)
    omega
  have hCovLen : mMax + 1 ≤ covBuckets.length := by
    dsimp [covBuckets, bucketSpecs]
    rw [buildAllBucketSpecs_eq, evalAllBuckets_eq_mapEvalBuckets,
        mapEvalBuckets_length _ _ (by rw [bucketSpecsPrefix_length]; exact hBucketsLen),
        bucketSpecsPrefix_length]
    omega
  have hCovFalse : Nat.testBit (covBuckets.getD (wordK mMax X) 0) (wordBlock mMax X) = false :=
    unpackFromBuckets_false_sound_lt mMax X covBuckets hmMax_lo hmMax_hi hCovLen hX hFalse
  rcases exists_theta_of_isPerm3 hπ with ⟨θ, p, hp_or, hπ_eq⟩
  have hp3 : ∀ d < 3, p d < 3 := by
    rcases hp_or with rfl | rfl
    · exact fun d hd => hd
    · exact swap12Digit_lt_three
  have hp0 : ∀ d < 3, p d = 0 ↔ d = 0 := by
    rcases hp_or with rfl | rfl
    · exact fun _ _ => Iff.rfl
    · intro d hd; revert d hd; decide
  have hp12 : ∀ d1 d2, ((d1 = 1 ∧ d2 = 2) ∨ (d1 = 2 ∧ d2 = 1)) →
      ((p d1 = 1 ∧ p d2 = 2) ∨ (p d1 = 2 ∧ p d2 = 1)) := by
    rcases hp_or with rfl | rfl
    · exact fun _ _ h => h
    · intro d1 d2 h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  apply Eliminated.kempe_choice c b θ hb
  intro equiv_ab equiv_cd hPart
  let b_rel := relabelBoundary θ b
  have hb_rel : IsValidBoundaryColoring c b_rel := relabelBoundary_valid c b θ hb
  have hX_rel : permTraceVal p c.ringSize b_rel mMax 0 = X := by
    dsimp [b_rel, X]
    rw [permTraceVal_relabelBoundary c h_ring b hb θ p mMax 0 (by omega)]
    exact permTraceVal_congr (fun d => p (relabelDigit θ d)) π (fun d hd => (hπ_eq d hd).symm)
      c.ringSize b mMax 0
  have hCovFalse_rel :
      let X_r := permTraceVal p c.ringSize b_rel mMax 0
      Nat.testBit (covBuckets.getD (wordK mMax X_r) 0) (wordBlock mMax X_r) = false := by
    dsimp
    rw [hX_rel]
    exact hCovFalse
  rcases relabelBoundary_partition c b θ equiv_ab equiv_cd hPart with hPart1 | hPart2
  · rcases evalAllBuckets_false_sound c p hp3 hp0 hp12 equiv_ab equiv_cd b_rel mMax buckets
      hr hmMax_hi hBucketsLen h_ring hb_rel hPart1 hCovFalse_rel with
      ⟨b'_rel, ⟨⟨S, hS_rel, rfl⟩, _⟩, hBuck'⟩
    have hS : IsValidSwapChoice c b θ equiv_ab equiv_cd S :=
      validSwapChoice_relabel c b_rel b theta1 θ equiv_ab equiv_cd S hS_rel
    let b' := boundaryKempeSwap c b θ S
    have hb' : IsValidBoundaryColoring c b' := swap_preserves_valid c b θ equiv_ab equiv_cd S hb hPart hS
    have hRelSwap : boundaryKempeSwap c b_rel theta1 S = relabelBoundary θ b' :=
      (relabelBoundary_swap c b θ S).symm
    have hX'_eq : permTraceVal p c.ringSize (boundaryKempeSwap c b_rel theta1 S) mMax 0 =
        permTraceVal π c.ringSize b' mMax 0 := by
      rw [hRelSwap, permTraceVal_relabelBoundary c h_ring b' hb' θ p mMax 0 (by omega)]
      exact permTraceVal_congr (fun d => p (relabelDigit θ d)) π (fun d hd => (hπ_eq d hd).symm)
        c.ringSize b' mMax 0
    dsimp at hBuck'
    rw [hX'_eq] at hBuck'
    have hL2' := packToBuckets_perm_false_sound c b' π hπ mMax L2 hr hmMax_lo hmMax_hi hBuck'
    exact ⟨S, hS, hInv b' hb' hL2'⟩
  · rcases evalAllBuckets_false_sound c p hp3 hp0 hp12 equiv_cd equiv_ab b_rel mMax buckets
      hr hmMax_hi hBucketsLen h_ring hb_rel hPart2 hCovFalse_rel with
      ⟨b'_rel, ⟨⟨S, hS_rel, rfl⟩, _⟩, hBuck'⟩
    have hS : IsValidSwapChoice c b θ equiv_ab equiv_cd S :=
      validSwapChoice_symm c b_rel b theta1 θ equiv_ab equiv_cd S hS_rel
    let b' := boundaryKempeSwap c b θ S
    have hb' : IsValidBoundaryColoring c b' := swap_preserves_valid c b θ equiv_ab equiv_cd S hb hPart hS
    have hRelSwap : boundaryKempeSwap c b_rel theta1 S = relabelBoundary θ b' :=
      (relabelBoundary_swap c b θ S).symm
    have hX'_eq : permTraceVal p c.ringSize (boundaryKempeSwap c b_rel theta1 S) mMax 0 =
        permTraceVal π c.ringSize b' mMax 0 := by
      rw [hRelSwap, permTraceVal_relabelBoundary c h_ring b' hb' θ p mMax 0 (by omega)]
      exact permTraceVal_congr (fun d => p (relabelDigit θ d)) π (fun d hd => (hπ_eq d hd).symm)
        c.ringSize b' mMax 0
    dsimp at hBuck'
    rw [hX'_eq] at hBuck'
    have hL2' := packToBuckets_perm_false_sound c b' π hπ mMax L2 hr hmMax_lo hmMax_hi hBuck'
    exact ⟨S, hS, hInv b' hb' hL2'⟩

theorem testBit_selectBool_beq_zero (m rest j : Nat)
    (h : Nat.testBit (selectBool (Nat.beq m 0) 0 rest) j = false) :
    Nat.testBit m j = false ∨ Nat.testBit rest j = false := by
  cases hBeq : Nat.beq m 0 with
  | true =>
    left
    rw [Nat.beq_eq.mp hBeq]
    exact Nat.zero_testBit j
  | false =>
    right
    rw [hBeq] at h
    exact h

theorem elim_of_m1_false (c : Configuration) (b : BoundaryColoring c)
    (π0 : Nat → Nat) (hπ0 : IsPerm3 π0)
    (mMax L2 : Nat)
    (hr : c.ringSize = mMax + 1) (hmMax_lo : 1 ≤ mMax) (hmMax_hi : mMax ≤ 13)
    (h_ring : IsRingCycle c) (hb : IsValidBoundaryColoring c b)
    (hInv : KernelLiveInvariant c L2)
    (hπ0_top : π0 (edgeDigitAt c.ringSize b (mMax - 1)) = 0)
    (hFalse :
      let mMax1 := mMax - 1
      let pTop := pow3 mMax1
      let swapSteps1 := (buildSwapSteps mMax1).val
      let l2_01 := swapDigits01 swapSteps1 L2
      let l2_02 := swapDigits02 swapSteps1 L2
      let d0_1 := Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop)
      let (packLevels, unpackRevLevels) := buildAllPackUnpackLevels mMax
      let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
      let buckets := packToBuckets packLevels [L2, d0_1]
      let covBuckets := evalAllBuckets bucketSpecs buckets
      let finalD := unpackFromBucketsAux unpackRevLevels covBuckets
      let u0 := finalD.getD 0 0
      let u1 := finalD.getD 1 0
      let m0 := Nat.land L2 u0
      let w1 := swapDigits01 swapSteps1 u1
      let m1 := Nat.land m0 w1
      Nat.testBit m1 (permTraceVal π0 c.ringSize b mMax1 0) = false) :
    Eliminated c b := by
  let mMax1 := mMax - 1
  let P_0 := 3 ^ mMax1
  let pTop := pow3 mMax1
  let swapSteps1 := (buildSwapSteps mMax1).val
  let l2_01 := swapDigits01 swapSteps1 L2
  let l2_02 := swapDigits02 swapSteps1 L2
  let d0_1 := Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop)
  let packLevels := (buildAllPackUnpackLevels mMax).1
  let unpackRevLevels := (buildAllPackUnpackLevels mMax).2
  let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
  let buckets := packToBuckets packLevels [L2, d0_1]
  let covBuckets := evalAllBuckets bucketSpecs buckets
  let finalD := unpackFromBucketsAux unpackRevLevels covBuckets
  let u0 := finalD.getD 0 0
  let u1 := finalD.getD 1 0
  let q := permTraceVal π0 c.ringSize b mMax1 0
  have hπ0_3 : ∀ d < 3, π0 d < 3 := isPerm3_lt_three hπ0
  have hq_lt : q < P_0 := permTraceVal_lt_pow3 π0 hπ0_3 c.ringSize b mMax1 0
  have hSub2 : c.ringSize - 2 = mMax1 := by omega
  let dTop := edgeDigitAt c.ringSize b mMax1
  have hdTop_lt : dTop < 3 := edgeDigitAt_lt_three c.ringSize b mMax1
  have hCanonTop : canonDigitPerm c.ringSize b dTop = 0 := by
    dsimp [dTop]
    rw [← hSub2]
    exact canonDigitPerm_top_eq_zero c.ringSize b
  change Nat.testBit (Nat.land (Nat.land L2 u0) (swapDigits01 swapSteps1 u1)) q = false at hFalse
  rw [testBit_land, testBit_land, Bool.and_eq_false_iff, Bool.and_eq_false_iff] at hFalse
  rcases hFalse with (hL2 | hu0) | hw1
  · apply hInv b hb
    rcases isPerm3_zero_fix hπ0 (isPerm3_canonDigitPerm c.ringSize b) dTop hdTop_lt hπ0_top hCanonTop
      with hEqId | hEqSwap
    · left
      have hCongr : q = canonIdx c.ringSize b := by
        dsimp [q]; unfold canonIdx; rw [hSub2]
        exact permTraceVal_congr π0 (canonDigitPerm c.ringSize b) hEqId c.ringSize b mMax1 0
      rwa [← hCongr]
    · right
      have hCongr : q = swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b) := by
        dsimp [q]; unfold swap12Idx canonIdx
        rw [hSub2, mapTernaryDigits_permTraceVal swap12Digit (canonDigitPerm c.ringSize b)
          (canonDigitPerm_lt_three c.ringSize b) c.ringSize b mMax1 0]
        exact permTraceVal_congr π0
          (fun d => swap12Digit (canonDigitPerm c.ringSize b d)) hEqSwap c.ringSize b mMax1 0
      rwa [← hCongr]
  · have hmMax_eq : mMax = mMax1 + 1 := by omega
    have hDivMod0 : permTraceVal π0 c.ringSize b mMax 0 / P_0 = π0 dTop ∧
        permTraceVal π0 c.ringSize b mMax 0 % P_0 = q := by
      dsimp [P_0, dTop, q]
      rw [hmMax_eq]
      exact permTraceVal_div_mod_pow3 π0 hπ0_3 c.ringSize b mMax1
    rcases hDivMod0 with ⟨hDiv0, hMod0⟩
    have hX0_lt : permTraceVal π0 c.ringSize b mMax 0 < 2 * P_0 := by
      have hDivMod := (Nat.div_add_mod (permTraceVal π0 c.ringSize b mMax 0) P_0).symm
      have hdTop0 : π0 dTop = 0 := hπ0_top
      rw [hDiv0, hdTop0, hMod0] at hDivMod
      omega
    apply elim_of_unpack_perm_false c b π0 hπ0 mMax L2 hr hmMax_lo hmMax_hi h_ring hb hInv hX0_lt
    change Nat.testBit (finalD.getD (permTraceVal π0 c.ringSize b mMax 0 / P_0) 0)
      (permTraceVal π0 c.ringSize b mMax 0 % P_0) = false
    rw [hDiv0, hπ0_top, hMod0]
    exact hu0
  · have hu1 : Nat.testBit u1 (swap01Idx mMax1 q) = false :=
      swapDigits01_buildSwapSteps_false_sound mMax1 u1 q hq_lt hw1
    let π1 := fun d => swap01Digit (π0 d)
    have hπ1 : IsPerm3 π1 := isPerm3_comp isPerm3_swap01 hπ0
    have hπ1_3 : ∀ d < 3, π1 d < 3 := isPerm3_lt_three hπ1
    have hπ1_top : π1 dTop = 1 := by
      dsimp [π1, dTop]
      rw [hπ0_top]
      rfl
    have hπ1_low : permTraceVal π1 c.ringSize b mMax1 0 = swap01Idx mMax1 q := by
      dsimp [π1, q, swap01Idx]
      exact (mapTernaryDigits_permTraceVal swap01Digit π0 hπ0_3 c.ringSize b mMax1 0).symm
    have hmMax_eq : mMax = mMax1 + 1 := by omega
    have hDivMod1 : permTraceVal π1 c.ringSize b mMax 0 / P_0 = π1 dTop ∧
        permTraceVal π1 c.ringSize b mMax 0 % P_0 = permTraceVal π1 c.ringSize b mMax1 0 := by
      dsimp [P_0, dTop]
      rw [hmMax_eq]
      exact permTraceVal_div_mod_pow3 π1 hπ1_3 c.ringSize b mMax1
    rcases hDivMod1 with ⟨hDiv1, hMod1⟩
    have hX1_lt : permTraceVal π1 c.ringSize b mMax 0 < 2 * P_0 := by
      have hDivMod := (Nat.div_add_mod (permTraceVal π1 c.ringSize b mMax 0) P_0).symm
      rw [hDiv1, hπ1_top, hMod1] at hDivMod
      have hLowLt : permTraceVal π1 c.ringSize b mMax1 0 < P_0 :=
        permTraceVal_lt_pow3 π1 hπ1_3 c.ringSize b mMax1 0
      omega
    apply elim_of_unpack_perm_false c b π1 hπ1 mMax L2 hr hmMax_lo hmMax_hi h_ring hb hInv hX1_lt
    change Nat.testBit (finalD.getD (permTraceVal π1 c.ringSize b mMax 0 / P_0) 0)
      (permTraceVal π1 c.ringSize b mMax 0 % P_0) = false
    rw [hDiv1, hπ1_top, hMod1, hπ1_low]
    exact hu1

theorem kempeRound_preserves_invariant (c : Configuration) (mMax L2 : Nat)
    (hr : c.ringSize = mMax + 1) (hmMax_lo : 1 ≤ mMax) (hmMax_hi : mMax ≤ 13)
    (h_ring : IsRingCycle c)
    (hInv : KernelLiveInvariant c L2) :
    let mMax1 := mMax - 1
    let pTop := pow3 mMax1
    let swapSteps1 := (buildSwapSteps mMax1).val
    let (packLevels, unpackRevLevels) := buildAllPackUnpackLevels mMax
    let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
    KernelLiveInvariant c
      (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2) := by
  dsimp
  intro b hb hNextOr
  let mMax1 := mMax - 1
  let P_0 := 3 ^ mMax1
  let pTop := pow3 mMax1
  let swapSteps1 := (buildSwapSteps mMax1).val
  let l2_01 := swapDigits01 swapSteps1 L2
  let l2_02 := swapDigits02 swapSteps1 L2
  let d0_1 := Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop)
  let packLevels := (buildAllPackUnpackLevels mMax).1
  let unpackRevLevels := (buildAllPackUnpackLevels mMax).2
  let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
  let buckets := packToBuckets packLevels [L2, d0_1]
  let covBuckets := evalAllBuckets bucketSpecs buckets
  let finalD := unpackFromBucketsAux unpackRevLevels covBuckets
  let u0 := finalD.getD 0 0
  let u1 := finalD.getD 1 0
  let m0 := Nat.land L2 u0
  let w1 := swapDigits01 swapSteps1 u1
  let m1 := Nat.land m0 w1
  have hSub2 : c.ringSize - 2 = mMax1 := by omega
  have hBucketsLen : c.ringSize ≤ buckets.length := by
    dsimp [buckets, packLevels]
    rw [buildAllPackUnpackLevels_eq]
    dsimp
    have h1 := packLevelsPrefix_length_out mMax (mMax - 1) [L2, d0_1] (Nat.le_refl 2)
    omega
  have hCovLen : mMax + 1 ≤ covBuckets.length := by
    dsimp [covBuckets, bucketSpecs]
    rw [buildAllBucketSpecs_eq, evalAllBuckets_eq_mapEvalBuckets,
        mapEvalBuckets_length _ _ (by rw [bucketSpecsPrefix_length]; exact hBucketsLen),
        bucketSpecsPrefix_length]
    omega
  have hFinalLen : 2 ≤ finalD.length := by
    dsimp [finalD, unpackRevLevels]
    rw [buildAllPackUnpackLevels_eq]
    dsimp
    exact unpackLevelsPrefix_length_out mMax (mMax - 1) covBuckets (by omega)
  have hRoundEq :
      kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2 =
      selectBool (Nat.beq m0 0) 0
        (selectBool (Nat.beq m1 0) 0
          (Nat.land m1 (swapDigits12 swapSteps1 m1))) := by
    unfold kempeRound
    exact withUnpackFromBucketsPair_eq unpackRevLevels covBuckets _ 0 hFinalLen
  have hStep : ∀ (π0 : Nat → Nat), IsPerm3 π0 →
      π0 (edgeDigitAt c.ringSize b mMax1) = 0 →
      Nat.testBit (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
        (permTraceVal π0 c.ringSize b mMax1 0) = false →
      Eliminated c b := by
    intro π0 hπ0 hπ0_top hBit
    rw [hRoundEq] at hBit
    have hπ0_3 : ∀ d < 3, π0 d < 3 := isPerm3_lt_three hπ0
    let q := permTraceVal π0 c.ringSize b mMax1 0
    have hq_lt : q < P_0 := permTraceVal_lt_pow3 π0 hπ0_3 c.ringSize b mMax1 0
    rcases testBit_selectBool_beq_zero m0 _ q hBit with hm0 | hBit1
    · apply elim_of_m1_false c b π0 hπ0 mMax L2 hr hmMax_lo hmMax_hi h_ring hb hInv hπ0_top
      change Nat.testBit (Nat.land m0 w1) q = false
      rw [testBit_land, hm0, Bool.false_and]
    · rcases testBit_selectBool_beq_zero m1 _ q hBit1 with hm1 | hBit2
      · exact elim_of_m1_false c b π0 hπ0 mMax L2 hr hmMax_lo hmMax_hi h_ring hb hInv hπ0_top hm1
      · rw [testBit_land, Bool.and_eq_false_iff] at hBit2
        rcases hBit2 with hm1 | hSwap12
        · exact elim_of_m1_false c b π0 hπ0 mMax L2 hr hmMax_lo hmMax_hi h_ring hb hInv hπ0_top hm1
        · have hm1_swap : Nat.testBit m1 (swap12Idx mMax1 q) = false :=
            swapDigits12_buildSwapSteps_false_sound mMax1 m1 q hq_lt hSwap12
          let π0' := fun d => swap12Digit (π0 d)
          have hπ0' : IsPerm3 π0' := isPerm3_comp isPerm3_swap12 hπ0
          have hπ0'_top : π0' (edgeDigitAt c.ringSize b mMax1) = 0 := by
            dsimp [π0']
            rw [hπ0_top]
            rfl
          have hq'_eq : permTraceVal π0' c.ringSize b mMax1 0 = swap12Idx mMax1 q := by
            dsimp [π0', q, swap12Idx]
            exact (mapTernaryDigits_permTraceVal swap12Digit π0 hπ0_3 c.ringSize b mMax1 0).symm
          apply elim_of_m1_false c b π0' hπ0' mMax L2 hr hmMax_lo hmMax_hi h_ring hb hInv hπ0'_top
          change Nat.testBit m1 (permTraceVal π0' c.ringSize b mMax1 0) = false
          rw [hq'_eq]
          exact hm1_swap
  have hCanonTop : canonDigitPerm c.ringSize b (edgeDigitAt c.ringSize b mMax1) = 0 := by
    rw [← hSub2]
    exact canonDigitPerm_top_eq_zero c.ringSize b
  rcases hNextOr with hFalse0 | hFalse1
  · apply hStep (canonDigitPerm c.ringSize b) (isPerm3_canonDigitPerm c.ringSize b) hCanonTop
    have hEq0 : permTraceVal (canonDigitPerm c.ringSize b) c.ringSize b mMax1 0 = canonIdx c.ringSize b := by
      unfold canonIdx; rw [hSub2]
    rw [hEq0]
    exact hFalse0
  · let πSwap := fun d => swap12Digit (canonDigitPerm c.ringSize b d)
    have hπSwap : IsPerm3 πSwap := isPerm3_comp isPerm3_swap12 (isPerm3_canonDigitPerm c.ringSize b)
    have hSwapTop : πSwap (edgeDigitAt c.ringSize b mMax1) = 0 := by
      dsimp [πSwap]
      rw [hCanonTop]
      rfl
    apply hStep πSwap hπSwap hSwapTop
    have hEq1 : permTraceVal πSwap c.ringSize b mMax1 0 =
        swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b) := by
      dsimp [πSwap]
      unfold swap12Idx canonIdx
      rw [hSub2, mapTernaryDigits_permTraceVal swap12Digit (canonDigitPerm c.ringSize b)
        (canonDigitPerm_lt_three c.ringSize b) c.ringSize b mMax1 0]
    rw [hEq1]
    exact hFalse1

theorem stepKempeRounds_preserves_invariant (c : Configuration) (mMax steps L2 : Nat)
    (hr : c.ringSize = mMax + 1) (hmMax_lo : 1 ≤ mMax) (hmMax_hi : mMax ≤ 13)
    (h_ring : IsRingCycle c)
    (hInv : KernelLiveInvariant c L2) :
    let mMax1 := mMax - 1
    let pTop := pow3 mMax1
    let swapSteps1 := (buildSwapSteps mMax1).val
    let (packLevels, unpackRevLevels) := buildAllPackUnpackLevels mMax
    let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
    KernelLiveInvariant c
      (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps L2) := by
  induction steps generalizing L2 with
  | zero => exact hInv
  | succ s ih =>
    let mMax1 := mMax - 1
    let pTop := pow3 mMax1
    let swapSteps1 := (buildSwapSteps mMax1).val
    let packLevels := (buildAllPackUnpackLevels mMax).1
    let unpackRevLevels := (buildAllPackUnpackLevels mMax).2
    let bucketSpecs := (buildAllBucketSpecs c.ringSize mMax).val
    let nextL2 := kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2
    change KernelLiveInvariant c
      (seqNat nextL2 (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs s nextL2))
    rw [seqNat_eq]
    exact ih nextL2 (kempeRound_preserves_invariant c mMax L2 hr hmMax_lo hmMax_hi h_ring hInv)

end KernelSoundness
end Math
