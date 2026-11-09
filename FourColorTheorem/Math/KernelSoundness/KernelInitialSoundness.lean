import FourColorTheorem.Math.KernelSoundness.KernelSlice

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
# Checkpoint K4.2: Soundness and Completeness of `dfsInterior`, `lookupRingCols`, and Alias Relaxation

This module establishes the bit-level specifications of `KernelReducer`'s interior extension and
contracted extension engines:
1. **`DfsWitness`, `dfsInterior_submask`, `dfsInterior_sound`, `dfsInterior_complete`:**
   Exact characterization of when bit `j` is cleared from `remCanon` by the bit-parallel interior-first
   DFS engine `dfsInterior`.
2. **`lookupRingCols`, `sameRingColMask`, `filterRingContractNbrs`, `getAlias`:**
   Structural lemmas for ring vertex color masks and contracted alias lookup.
3. **`canonRingColorNat` & `canonRingColor`:**
   Canonical ring coloring induced by slice index `j < 3^{r-2}` with `c(0) = 1` and
   `c(u + 1) = c(u) ^^^ (((j / 3^u) % 3) + 1)`.
-/

/-!
### Part 1: Bit-Parallel Interior DFS (`dfsInterior`) Soundness and Completeness
-/

/-- Inductive witness that slice index `j` admits a valid interior 4-coloring branch through
    `steps : List IntVertexStep` starting from interior color masks `(c0, c1, c2, c3)`. -/
inductive DfsWitness : List IntVertexStep → Nat → Nat → Nat → Nat → Nat → Prop where
  | nil (c0 c1 c2 c3 j : Nat) : DfsWitness [] c0 c1 c2 c3 j
  | br0 {bitV reqMask checkMask f0 f1 f2 f3 : Nat} {rest : List IntVertexStep}
      {c0 c1 c2 c3 j : Nat}
      (hReq : Nat.land c0 checkMask = reqMask)
      (hF : Nat.testBit f0 j = true)
      (hNext : DfsWitness rest (Nat.lor c0 bitV) c1 c2 c3 j) :
      DfsWitness (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: rest) c0 c1 c2 c3 j
  | br1 {bitV reqMask checkMask f0 f1 f2 f3 : Nat} {rest : List IntVertexStep}
      {c0 c1 c2 c3 j : Nat}
      (hReq : Nat.land c1 checkMask = reqMask)
      (hF : Nat.testBit f1 j = true)
      (hNext : DfsWitness rest c0 (Nat.lor c1 bitV) c2 c3 j) :
      DfsWitness (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: rest) c0 c1 c2 c3 j
  | br2 {bitV reqMask checkMask f0 f1 f2 f3 : Nat} {rest : List IntVertexStep}
      {c0 c1 c2 c3 j : Nat}
      (hReq : Nat.land c2 checkMask = reqMask)
      (hF : Nat.testBit f2 j = true)
      (hNext : DfsWitness rest c0 c1 (Nat.lor c2 bitV) c3 j) :
      DfsWitness (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: rest) c0 c1 c2 c3 j
  | br3 {bitV reqMask checkMask f0 f1 f2 f3 : Nat} {rest : List IntVertexStep}
      {c0 c1 c2 c3 j : Nat}
      (hReq : Nat.land c3 checkMask = reqMask)
      (hF : Nat.testBit f3 j = true)
      (hNext : DfsWitness rest c0 c1 c2 (Nat.lor c3 bitV) j) :
      DfsWitness (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: rest) c0 c1 c2 c3 j

/-- `A` is a bitwise submask of `B`: every set bit of `A` is also set in `B`. -/
def IsSubmask (A B : Nat) : Prop :=
  ∀ i : Nat, Nat.testBit A i = true → Nat.testBit B i = true

theorem isSubmask_refl (A : Nat) : IsSubmask A A :=
  fun _ h => h

theorem isSubmask_trans {A B C : Nat} (h1 : IsSubmask A B) (h2 : IsSubmask B C) :
    IsSubmask A C :=
  fun i hi => h2 i (h1 i hi)

theorem isSubmask_land_left (A B : Nat) : IsSubmask (Nat.land A B) A := by
  intro i hi
  rw [testBit_land] at hi
  exact (Bool.and_eq_true_iff.mp hi).1

theorem isSubmask_land_right (A B : Nat) : IsSubmask (Nat.land A B) B := by
  intro i hi
  rw [testBit_land] at hi
  exact (Bool.and_eq_true_iff.mp hi).2

theorem testBit_false_of_isSubmask {A B : Nat} (hSub : IsSubmask A B) (i : Nat)
    (hFalse : Nat.testBit B i = false) : Nat.testBit A i = false := by
  cases hA : Nat.testBit A i with
  | false => rfl
  | true =>
    have hB := hSub i hA
    rw [hB] at hFalse
    contradiction

/-- `dfsInterior` always returns a submask of `rem0` whenever `compat` is a submask of `rem0`. -/
theorem dfsInterior_submask (steps : List IntVertexStep)
    (c0 c1 c2 c3 compat rem0 : Nat)
    (hSub : IsSubmask compat rem0) :
    IsSubmask (dfsInterior steps c0 c1 c2 c3 compat rem0) rem0 := by
  induction steps generalizing c0 c1 c2 c3 compat rem0 with
  | nil =>
    intro i hi
    change Nat.testBit (Nat.xor rem0 compat) i = true at hi
    rw [testBit_xor] at hi
    cases hR : Nat.testBit rem0 i with
    | true => rfl
    | false =>
      have hC : Nat.testBit compat i = false := testBit_false_of_isSubmask hSub i hR
      rw [hR, hC] at hi
      contradiction
  | cons step rest ih =>
    cases step with
    | mk bitV reqMask checkMask f0 f1 f2 f3 =>
      change IsSubmask
        (let r1 :=
           tryDfsBranch0 c0 checkMask reqMask compat rem0 f0
             (fun next0 => dfsInterior rest (Nat.lor c0 bitV) c1 c2 c3 next0 rem0)
         let r2 :=
           tryDfsBranch c1 checkMask reqMask compat r1 f1
             (fun next1 => dfsInterior rest c0 (Nat.lor c1 bitV) c2 c3 next1 r1)
         let r3 :=
           tryDfsBranch c2 checkMask reqMask compat r2 f2
             (fun next2 => dfsInterior rest c0 c1 (Nat.lor c2 bitV) c3 next2 r2)
         tryDfsBranch c3 checkMask reqMask compat r3 f3
           (fun next3 => dfsInterior rest c0 c1 c2 (Nat.lor c3 bitV) next3 r3))
        rem0
      have hSub_branch0 : ∀ (cMask fMask : Nat) (c0' c1' c2' c3' : Nat),
          IsSubmask
            (tryDfsBranch0 cMask checkMask reqMask compat rem0 fMask
              (fun nextC => dfsInterior rest c0' c1' c2' c3' nextC rem0))
            rem0 := by
        intro cMask fMask c0' c1' c2' c3'
        dsimp
        cases Nat.beq (Nat.land cMask checkMask) reqMask with
        | false => exact isSubmask_refl rem0
        | true =>
          dsimp
          cases Nat.beq (Nat.land compat fMask) 0 with
          | true => exact isSubmask_refl rem0
          | false =>
            exact ih c0' c1' c2' c3' (Nat.land compat fMask) rem0
              (isSubmask_trans (isSubmask_land_left compat fMask) hSub)
      have hSub_branch : ∀ (cMask fMask rPrev : Nat) (c0' c1' c2' c3' : Nat),
          IsSubmask
            (tryDfsBranch cMask checkMask reqMask compat rPrev fMask
              (fun nextC => dfsInterior rest c0' c1' c2' c3' nextC rPrev))
            rPrev := by
        intro cMask fMask rPrev c0' c1' c2' c3'
        dsimp
        cases Nat.beq (Nat.land cMask checkMask) reqMask with
        | false => exact isSubmask_refl rPrev
        | true =>
          dsimp
          cases Nat.beq (Nat.land (Nat.land compat rPrev) fMask) 0 with
          | true => exact isSubmask_refl rPrev
          | false =>
            exact ih c0' c1' c2' c3' (Nat.land (Nat.land compat rPrev) fMask) rPrev
              (isSubmask_trans (isSubmask_land_left _ fMask) (isSubmask_land_right compat rPrev))
      exact isSubmask_trans (hSub_branch c3 f3 _ _ _ _ _)
        (isSubmask_trans (hSub_branch c2 f2 _ _ _ _ _)
          (isSubmask_trans (hSub_branch c1 f1 _ _ _ _ _)
            (hSub_branch0 c0 f0 _ _ _ _)))

/-- **Soundness of `dfsInterior` (`dfsInterior_sound`):**
    If `Nat.testBit rem0 j = true` and `Nat.testBit (dfsInterior steps c0 c1 c2 c3 compat rem0) j = false`,
    then `Nat.testBit compat j = true` and `DfsWitness steps c0 c1 c2 c3 j` holds. -/
theorem dfsInterior_sound (steps : List IntVertexStep)
    (c0 c1 c2 c3 compat rem0 j : Nat)
    (hRem : Nat.testBit rem0 j = true)
    (hCleared : Nat.testBit (dfsInterior steps c0 c1 c2 c3 compat rem0) j = false) :
    Nat.testBit compat j = true ∧ DfsWitness steps c0 c1 c2 c3 j := by
  induction steps generalizing c0 c1 c2 c3 compat rem0 with
  | nil =>
    change Nat.testBit (Nat.xor rem0 compat) j = false at hCleared
    rw [testBit_xor, hRem] at hCleared
    cases hC : Nat.testBit compat j with
    | false =>
      rw [hC] at hCleared
      contradiction
    | true =>
      exact ⟨rfl, DfsWitness.nil c0 c1 c2 c3 j⟩
  | cons step rest ih =>
    cases step with
    | mk bitV reqMask checkMask f0 f1 f2 f3 =>
      let r1 :=
        tryDfsBranch0 c0 checkMask reqMask compat rem0 f0
          (fun next0 => dfsInterior rest (Nat.lor c0 bitV) c1 c2 c3 next0 rem0)
      let r2 :=
        tryDfsBranch c1 checkMask reqMask compat r1 f1
          (fun next1 => dfsInterior rest c0 (Nat.lor c1 bitV) c2 c3 next1 r1)
      let r3 :=
        tryDfsBranch c2 checkMask reqMask compat r2 f2
          (fun next2 => dfsInterior rest c0 c1 (Nat.lor c2 bitV) c3 next2 r2)
      let r4 :=
        tryDfsBranch c3 checkMask reqMask compat r3 f3
          (fun next3 => dfsInterior rest c0 c1 c2 (Nat.lor c3 bitV) next3 r3)
      change Nat.testBit r4 j = false at hCleared
      cases hr1 : Nat.testBit r1 j with
      | false =>
        dsimp [r1] at hr1
        cases hBeq : Nat.beq (Nat.land c0 checkMask) reqMask with
        | false =>
          rw [hBeq] at hr1; dsimp at hr1; rw [hRem] at hr1; contradiction
        | true =>
          rw [hBeq] at hr1; dsimp at hr1
          cases hZ : Nat.beq (Nat.land compat f0) 0 with
          | true =>
            rw [hZ] at hr1; dsimp at hr1; rw [hRem] at hr1; contradiction
          | false =>
            rw [hZ] at hr1; dsimp at hr1
            rcases ih (Nat.lor c0 bitV) c1 c2 c3 (Nat.land compat f0) rem0 hRem hr1 with ⟨hNext0, hW0⟩
            rw [testBit_land] at hNext0
            rcases Bool.and_eq_true_iff.mp hNext0 with ⟨hComp, hF0⟩
            exact ⟨hComp, DfsWitness.br0 (Nat.beq_eq.mp hBeq) hF0 hW0⟩
      | true =>
        cases hr2 : Nat.testBit r2 j with
        | false =>
          dsimp [r2] at hr2
          cases hBeq : Nat.beq (Nat.land c1 checkMask) reqMask with
          | false =>
            rw [hBeq] at hr2; dsimp at hr2; rw [hr1] at hr2; contradiction
          | true =>
            rw [hBeq] at hr2; dsimp at hr2
            cases hZ : Nat.beq (Nat.land (Nat.land compat r1) f1) 0 with
            | true =>
              rw [hZ] at hr2; dsimp at hr2; rw [hr1] at hr2; contradiction
            | false =>
              rw [hZ] at hr2; dsimp at hr2
              rcases ih c0 (Nat.lor c1 bitV) c2 c3 (Nat.land (Nat.land compat r1) f1) r1 hr1 hr2 with ⟨hNext1, hW1⟩
              rw [testBit_land, testBit_land] at hNext1
              rcases Bool.and_eq_true_iff.mp hNext1 with ⟨hCR, hF1⟩
              rcases Bool.and_eq_true_iff.mp hCR with ⟨hComp, _⟩
              exact ⟨hComp, DfsWitness.br1 (Nat.beq_eq.mp hBeq) hF1 hW1⟩
        | true =>
          cases hr3 : Nat.testBit r3 j with
          | false =>
            dsimp [r3] at hr3
            cases hBeq : Nat.beq (Nat.land c2 checkMask) reqMask with
            | false =>
              rw [hBeq] at hr3; dsimp at hr3; rw [hr2] at hr3; contradiction
            | true =>
              rw [hBeq] at hr3; dsimp at hr3
              cases hZ : Nat.beq (Nat.land (Nat.land compat r2) f2) 0 with
              | true =>
                rw [hZ] at hr3; dsimp at hr3; rw [hr2] at hr3; contradiction
              | false =>
                rw [hZ] at hr3; dsimp at hr3
                rcases ih c0 c1 (Nat.lor c2 bitV) c3 (Nat.land (Nat.land compat r2) f2) r2 hr2 hr3 with ⟨hNext2, hW2⟩
                rw [testBit_land, testBit_land] at hNext2
                rcases Bool.and_eq_true_iff.mp hNext2 with ⟨hCR, hF2⟩
                rcases Bool.and_eq_true_iff.mp hCR with ⟨hComp, _⟩
                exact ⟨hComp, DfsWitness.br2 (Nat.beq_eq.mp hBeq) hF2 hW2⟩
          | true =>
            dsimp [r4] at hCleared
            cases hBeq : Nat.beq (Nat.land c3 checkMask) reqMask with
            | false =>
              rw [hBeq] at hCleared; dsimp at hCleared; rw [hr3] at hCleared; contradiction
            | true =>
              rw [hBeq] at hCleared; dsimp at hCleared
              cases hZ : Nat.beq (Nat.land (Nat.land compat r3) f3) 0 with
              | true =>
                rw [hZ] at hCleared; dsimp at hCleared; rw [hr3] at hCleared; contradiction
              | false =>
                rw [hZ] at hCleared; dsimp at hCleared
                rcases ih c0 c1 c2 (Nat.lor c3 bitV) (Nat.land (Nat.land compat r3) f3) r3 hr3 hCleared with ⟨hNext3, hW3⟩
                rw [testBit_land, testBit_land] at hNext3
                rcases Bool.and_eq_true_iff.mp hNext3 with ⟨hCR, hF3⟩
                rcases Bool.and_eq_true_iff.mp hCR with ⟨hComp, _⟩
                exact ⟨hComp, DfsWitness.br3 (Nat.beq_eq.mp hBeq) hF3 hW3⟩

/-- If `Nat.testBit X j = true`, then `Nat.beq X 0 = false`. -/
theorem beq_zero_false_of_testBit_true {X j : Nat} (h : Nat.testBit X j = true) :
    Nat.beq X 0 = false := by
  cases hZ : Nat.beq X 0 with
  | false => rfl
  | true =>
    have hX : X = 0 := Nat.beq_eq.mp hZ
    subst hX
    rw [Nat.zero_testBit] at h
    contradiction

/-- **Completeness of `dfsInterior` (`dfsInterior_complete`):**
    If `compat` is a submask of `rem0`, `Nat.testBit compat j = true`, and
    `DfsWitness steps c0 c1 c2 c3 j` holds, then
    `Nat.testBit (dfsInterior steps c0 c1 c2 c3 compat rem0) j = false`. -/
theorem dfsInterior_complete (steps : List IntVertexStep)
    (c0 c1 c2 c3 compat rem0 j : Nat)
    (hSub : IsSubmask compat rem0)
    (hComp : Nat.testBit compat j = true)
    (hW : DfsWitness steps c0 c1 c2 c3 j) :
    Nat.testBit (dfsInterior steps c0 c1 c2 c3 compat rem0) j = false := by
  induction hW generalizing compat rem0 with
  | nil c0 c1 c2 c3 j =>
    change Nat.testBit (Nat.xor rem0 compat) j = false
    have hRem : Nat.testBit rem0 j = true := hSub j hComp
    rw [testBit_xor, hRem, hComp]
    rfl
  | @br0 bitV reqMask checkMask f0 f1 f2 f3 rest c0 c1 c2 c3 j hReq hF hNext ih =>
    let r1 :=
      tryDfsBranch0 c0 checkMask reqMask compat rem0 f0
        (fun next0 => dfsInterior rest (Nat.lor c0 bitV) c1 c2 c3 next0 rem0)
    let r2 :=
      tryDfsBranch c1 checkMask reqMask compat r1 f1
        (fun next1 => dfsInterior rest c0 (Nat.lor c1 bitV) c2 c3 next1 r1)
    let r3 :=
      tryDfsBranch c2 checkMask reqMask compat r2 f2
        (fun next2 => dfsInterior rest c0 c1 (Nat.lor c2 bitV) c3 next2 r2)
    let r4 :=
      tryDfsBranch c3 checkMask reqMask compat r3 f3
        (fun next3 => dfsInterior rest c0 c1 c2 (Nat.lor c3 bitV) next3 r3)
    change Nat.testBit r4 j = false
    have hSub_branch : ∀ (cMask fMask rPrev : Nat) (c0' c1' c2' c3' : Nat),
        IsSubmask
          (tryDfsBranch cMask checkMask reqMask compat rPrev fMask
            (fun nextC => dfsInterior rest c0' c1' c2' c3' nextC rPrev))
          rPrev := by
      intro cMask fMask rPrev c0' c1' c2' c3'
      dsimp
      cases Nat.beq (Nat.land cMask checkMask) reqMask with
      | false => exact isSubmask_refl rPrev
      | true =>
        dsimp
        cases Nat.beq (Nat.land (Nat.land compat rPrev) fMask) 0 with
        | true => exact isSubmask_refl rPrev
        | false =>
          exact dfsInterior_submask rest c0' c1' c2' c3' (Nat.land (Nat.land compat rPrev) fMask) rPrev
            (isSubmask_trans (isSubmask_land_left _ fMask) (isSubmask_land_right compat rPrev))
    have hSub41 : IsSubmask r4 r1 :=
      isSubmask_trans (hSub_branch c3 f3 r3 _ _ _ _)
        (isSubmask_trans (hSub_branch c2 f2 r2 _ _ _ _)
          (hSub_branch c1 f1 r1 _ _ _ _))
    have hr1_false : Nat.testBit r1 j = false := by
      dsimp [r1]
      have hBeq : Nat.beq (Nat.land c0 checkMask) reqMask = true := Nat.beq_eq.mpr hReq
      have hNext0_bit : Nat.testBit (Nat.land compat f0) j = true := by
        rw [testBit_land, hComp, hF]; rfl
      have hZ : Nat.beq (Nat.land compat f0) 0 = false := beq_zero_false_of_testBit_true hNext0_bit
      rw [hBeq, hZ]
      dsimp
      exact ih (Nat.land compat f0) rem0
        (isSubmask_trans (isSubmask_land_left compat f0) hSub) hNext0_bit
    exact testBit_false_of_isSubmask hSub41 j hr1_false
  | @br1 bitV reqMask checkMask f0 f1 f2 f3 rest c0 c1 c2 c3 j hReq hF hNext ih =>
    let r1 :=
      tryDfsBranch0 c0 checkMask reqMask compat rem0 f0
        (fun next0 => dfsInterior rest (Nat.lor c0 bitV) c1 c2 c3 next0 rem0)
    let r2 :=
      tryDfsBranch c1 checkMask reqMask compat r1 f1
        (fun next1 => dfsInterior rest c0 (Nat.lor c1 bitV) c2 c3 next1 r1)
    let r3 :=
      tryDfsBranch c2 checkMask reqMask compat r2 f2
        (fun next2 => dfsInterior rest c0 c1 (Nat.lor c2 bitV) c3 next2 r2)
    let r4 :=
      tryDfsBranch c3 checkMask reqMask compat r3 f3
        (fun next3 => dfsInterior rest c0 c1 c2 (Nat.lor c3 bitV) next3 r3)
    change Nat.testBit r4 j = false
    have hSub_branch : ∀ (cMask fMask rPrev : Nat) (c0' c1' c2' c3' : Nat),
        IsSubmask
          (tryDfsBranch cMask checkMask reqMask compat rPrev fMask
            (fun nextC => dfsInterior rest c0' c1' c2' c3' nextC rPrev))
          rPrev := by
      intro cMask fMask rPrev c0' c1' c2' c3'
      dsimp
      cases Nat.beq (Nat.land cMask checkMask) reqMask with
      | false => exact isSubmask_refl rPrev
      | true =>
        dsimp
        cases Nat.beq (Nat.land (Nat.land compat rPrev) fMask) 0 with
        | true => exact isSubmask_refl rPrev
        | false =>
          exact dfsInterior_submask rest c0' c1' c2' c3' (Nat.land (Nat.land compat rPrev) fMask) rPrev
            (isSubmask_trans (isSubmask_land_left _ fMask) (isSubmask_land_right compat rPrev))
    have hSub42 : IsSubmask r4 r2 :=
      isSubmask_trans (hSub_branch c3 f3 r3 _ _ _ _)
        (hSub_branch c2 f2 r2 _ _ _ _)
    have hr2_false : Nat.testBit r2 j = false := by
      cases hr1 : Nat.testBit r1 j with
      | false =>
        exact testBit_false_of_isSubmask (hSub_branch c1 f1 r1 _ _ _ _) j hr1
      | true =>
        dsimp [r2]
        have hBeq : Nat.beq (Nat.land c1 checkMask) reqMask = true := Nat.beq_eq.mpr hReq
        have hNext1_bit : Nat.testBit (Nat.land (Nat.land compat r1) f1) j = true := by
          rw [testBit_land, testBit_land, hComp, hr1, hF]; rfl
        have hZ : Nat.beq (Nat.land (Nat.land compat r1) f1) 0 = false :=
          beq_zero_false_of_testBit_true hNext1_bit
        rw [hBeq, hZ]
        dsimp
        exact ih (Nat.land (Nat.land compat r1) f1) r1
          (isSubmask_trans (isSubmask_land_left _ f1) (isSubmask_land_right compat r1)) hNext1_bit
    exact testBit_false_of_isSubmask hSub42 j hr2_false
  | @br2 bitV reqMask checkMask f0 f1 f2 f3 rest c0 c1 c2 c3 j hReq hF hNext ih =>
    let r1 :=
      tryDfsBranch0 c0 checkMask reqMask compat rem0 f0
        (fun next0 => dfsInterior rest (Nat.lor c0 bitV) c1 c2 c3 next0 rem0)
    let r2 :=
      tryDfsBranch c1 checkMask reqMask compat r1 f1
        (fun next1 => dfsInterior rest c0 (Nat.lor c1 bitV) c2 c3 next1 r1)
    let r3 :=
      tryDfsBranch c2 checkMask reqMask compat r2 f2
        (fun next2 => dfsInterior rest c0 c1 (Nat.lor c2 bitV) c3 next2 r2)
    let r4 :=
      tryDfsBranch c3 checkMask reqMask compat r3 f3
        (fun next3 => dfsInterior rest c0 c1 c2 (Nat.lor c3 bitV) next3 r3)
    change Nat.testBit r4 j = false
    have hSub_branch : ∀ (cMask fMask rPrev : Nat) (c0' c1' c2' c3' : Nat),
        IsSubmask
          (tryDfsBranch cMask checkMask reqMask compat rPrev fMask
            (fun nextC => dfsInterior rest c0' c1' c2' c3' nextC rPrev))
          rPrev := by
      intro cMask fMask rPrev c0' c1' c2' c3'
      dsimp
      cases Nat.beq (Nat.land cMask checkMask) reqMask with
      | false => exact isSubmask_refl rPrev
      | true =>
        dsimp
        cases Nat.beq (Nat.land (Nat.land compat rPrev) fMask) 0 with
        | true => exact isSubmask_refl rPrev
        | false =>
          exact dfsInterior_submask rest c0' c1' c2' c3' (Nat.land (Nat.land compat rPrev) fMask) rPrev
            (isSubmask_trans (isSubmask_land_left _ fMask) (isSubmask_land_right compat rPrev))
    have hSub43 : IsSubmask r4 r3 := hSub_branch c3 f3 r3 _ _ _ _
    have hr3_false : Nat.testBit r3 j = false := by
      cases hr2 : Nat.testBit r2 j with
      | false =>
        exact testBit_false_of_isSubmask (hSub_branch c2 f2 r2 _ _ _ _) j hr2
      | true =>
        dsimp [r3]
        have hBeq : Nat.beq (Nat.land c2 checkMask) reqMask = true := Nat.beq_eq.mpr hReq
        have hNext2_bit : Nat.testBit (Nat.land (Nat.land compat r2) f2) j = true := by
          rw [testBit_land, testBit_land, hComp, hr2, hF]; rfl
        have hZ : Nat.beq (Nat.land (Nat.land compat r2) f2) 0 = false :=
          beq_zero_false_of_testBit_true hNext2_bit
        rw [hBeq, hZ]
        dsimp
        exact ih (Nat.land (Nat.land compat r2) f2) r2
          (isSubmask_trans (isSubmask_land_left _ f2) (isSubmask_land_right compat r2)) hNext2_bit
    exact testBit_false_of_isSubmask hSub43 j hr3_false
  | @br3 bitV reqMask checkMask f0 f1 f2 f3 rest c0 c1 c2 c3 j hReq hF hNext ih =>
    let r1 :=
      tryDfsBranch0 c0 checkMask reqMask compat rem0 f0
        (fun next0 => dfsInterior rest (Nat.lor c0 bitV) c1 c2 c3 next0 rem0)
    let r2 :=
      tryDfsBranch c1 checkMask reqMask compat r1 f1
        (fun next1 => dfsInterior rest c0 (Nat.lor c1 bitV) c2 c3 next1 r1)
    let r3 :=
      tryDfsBranch c2 checkMask reqMask compat r2 f2
        (fun next2 => dfsInterior rest c0 c1 (Nat.lor c2 bitV) c3 next2 r2)
    let r4 :=
      tryDfsBranch c3 checkMask reqMask compat r3 f3
        (fun next3 => dfsInterior rest c0 c1 c2 (Nat.lor c3 bitV) next3 r3)
    change Nat.testBit r4 j = false
    have hSub_branch : ∀ (cMask fMask rPrev : Nat) (c0' c1' c2' c3' : Nat),
        IsSubmask
          (tryDfsBranch cMask checkMask reqMask compat rPrev fMask
            (fun nextC => dfsInterior rest c0' c1' c2' c3' nextC rPrev))
          rPrev := by
      intro cMask fMask rPrev c0' c1' c2' c3'
      dsimp
      cases Nat.beq (Nat.land cMask checkMask) reqMask with
      | false => exact isSubmask_refl rPrev
      | true =>
        dsimp
        cases Nat.beq (Nat.land (Nat.land compat rPrev) fMask) 0 with
        | true => exact isSubmask_refl rPrev
        | false =>
          exact dfsInterior_submask rest c0' c1' c2' c3' (Nat.land (Nat.land compat rPrev) fMask) rPrev
            (isSubmask_trans (isSubmask_land_left _ fMask) (isSubmask_land_right compat rPrev))
    cases hr3 : Nat.testBit r3 j with
    | false =>
      exact testBit_false_of_isSubmask (hSub_branch c3 f3 r3 _ _ _ _) j hr3
    | true =>
      dsimp [r4]
      have hBeq : Nat.beq (Nat.land c3 checkMask) reqMask = true := Nat.beq_eq.mpr hReq
      have hNext3_bit : Nat.testBit (Nat.land (Nat.land compat r3) f3) j = true := by
        rw [testBit_land, testBit_land, hComp, hr3, hF]; rfl
      have hZ : Nat.beq (Nat.land (Nat.land compat r3) f3) 0 = false :=
        beq_zero_false_of_testBit_true hNext3_bit
      rw [hBeq, hZ]
      dsimp
      exact ih (Nat.land (Nat.land compat r3) f3) r3
        (isSubmask_trans (isSubmask_land_left _ f3) (isSubmask_land_right compat r3)) hNext3_bit

/-!
### Part 2: Canonical Ring Coloring `canonRingColorNat` & `canonRingColor`
-/

/-- Canonical `Nat` color (`∈ {0, 1, 2, 3}`) of ring vertex `u` for slice index `j < 3^{r-2}`:
    - Vertex `0` has color `1`.
    - Vertex `u + 1` has color `canonRingColorNat j u ^^^ (((j / 3 ^ u) % 3) + 1)`. -/
def canonRingColorNat (j : Nat) : Nat → Nat
  | 0 => 1
  | u + 1 => canonRingColorNat j u ^^^ (((j / 3 ^ u) % 3) + 1)

/-- Canonical `Color` of ring vertex `u` for slice index `j`. -/
def canonRingColor (j : Nat) (u : Nat) : Color :=
  colorOfNat (canonRingColorNat j u)

theorem xor_lt_four (a b : Nat) (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 := by
  rcases a with _ | _ | _ | _ | a <;> rcases b with _ | _ | _ | _ | b <;> (try decide) <;> omega

theorem canonRingColorNat_lt_four (j u : Nat) : canonRingColorNat j u < 4 := by
  induction u with
  | zero =>
    dsimp [canonRingColorNat]
    decide
  | succ u ih =>
    dsimp [canonRingColorNat]
    have hd : ((j / 3 ^ u) % 3) + 1 < 4 := by
      have := Nat.mod_lt (j / 3 ^ u) (by decide : 0 < 3)
      omega
    exact xor_lt_four _ _ ih hd

theorem toNat_canonRingColor (j u : Nat) :
    (canonRingColor j u).toNat = canonRingColorNat j u := by
  unfold canonRingColor
  exact toNat_colorOfNat (canonRingColorNat_lt_four j u)

theorem xor_self_xor_right (a b : Nat) (ha : a < 4) (hb : b < 4) :
    a ^^^ (a ^^^ b) = b := by
  rcases a with _ | _ | _ | _ | a <;> rcases b with _ | _ | _ | _ | b <;> (try decide) <;> omega

/-- For every `e < r - 1`, `edgeDigitAt r (canonRingColor j) e` equals `(j / 3 ^ e) % 3`. -/
theorem edgeDigitAt_canonRingColor (r j e : Nat) (he : e + 1 < r) :
    edgeDigitAt r (canonRingColor j) e = (j / 3 ^ e) % 3 := by
  dsimp [edgeDigitAt]
  have hMod : (e + 1) % r = e + 1 := Nat.mod_eq_of_lt he
  rw [hMod, toNat_canonRingColor, toNat_canonRingColor]
  dsimp [canonRingColorNat]
  have hlt1 := canonRingColorNat_lt_four j e
  have hd_lt : (j / 3 ^ e) % 3 < 3 := Nat.mod_lt (j / 3 ^ e) (by decide)
  have hlt2 : ((j / 3 ^ e) % 3) + 1 < 4 := by omega
  rw [xor_self_xor_right _ _ hlt1 hlt2]
  have hPos : (j / 3 ^ e) % 3 + 1 > 0 := by omega
  rw [if_pos hPos]
  omega

/-- Canonical 1-before-2 symmetry predicate on the first `u` base-3 digits of `j`:
    scanning digits from `u - 1` down to `0`, either all digits are `0` or the highest non-zero digit is `1`. -/
def isCanon12 : Nat → Nat → Bool
  | 0, _ => true
  | u + 1, j =>
    let d := (j / 3 ^ u) % 3
    (decide (d = 0) && isCanon12 u j) || decide (d = 1)

theorem div_pow3_add_mul_pow3 (j c i u : Nat) (hi : i < u) :
    ((j + c * 3 ^ u) / 3 ^ i) % 3 = (j / 3 ^ i) % 3 := by
  have hSplit : 3 ^ u = 3 ^ i * (3 * 3 ^ (u - 1 - i)) := by
    rw [← Nat.pow_succ', ← Nat.pow_add]
    congr 1
    omega
  have hEq : j + c * 3 ^ u = j + 3 ^ i * (3 * (3 ^ (u - 1 - i) * c)) := by
    rw [hSplit, Nat.mul_comm c]
    simp [Nat.mul_assoc]
  rw [hEq, Nat.add_mul_div_left _ _ (pow3_pos i), Nat.add_mul_mod_self_left]

theorem canonRingColorNat_add_mul_pow3 (j c u v : Nat) (hv : v ≤ u) :
    canonRingColorNat (j + c * 3 ^ u) v = canonRingColorNat j v := by
  induction v with
  | zero => rfl
  | succ v ih =>
    dsimp [canonRingColorNat]
    rw [ih (by omega), div_pow3_add_mul_pow3 j c v u (by omega)]

theorem canonRingColorNat_sub_pow3 (j u : Nat) (hLe : 3 ^ u ≤ j) :
    canonRingColorNat (j - 3 ^ u) u = canonRingColorNat j u := by
  have h := canonRingColorNat_add_mul_pow3 (j - 3 ^ u) 1 u u (Nat.le_refl u)
  rw [Nat.one_mul, Nat.sub_add_cancel hLe] at h
  exact h.symm

theorem canonRingColorNat_sub_two_pow3 (j u : Nat) (hLe : 2 * 3 ^ u ≤ j) :
    canonRingColorNat (j - 2 * 3 ^ u) u = canonRingColorNat j u := by
  have h := canonRingColorNat_add_mul_pow3 (j - 2 * 3 ^ u) 2 u u (Nat.le_refl u)
  rw [Nat.sub_add_cancel hLe] at h
  exact h.symm

theorem canonRingColorNat_mod_pow3 (j u : Nat) :
    canonRingColorNat (j % 3 ^ u) u = canonRingColorNat j u := by
  have h := canonRingColorNat_add_mul_pow3 (j % 3 ^ u) (j / 3 ^ u) u u (Nat.le_refl u)
  have hEq : j % 3 ^ u + j / 3 ^ u * 3 ^ u = j := by
    have hDiv := Nat.div_add_mod j (3 ^ u)
    rw [Nat.mul_comm] at hDiv
    omega
  rw [hEq] at h
  exact h.symm

theorem lt_two_pow_of_testBit (x P : Nat) (h : ∀ j, P ≤ j → Nat.testBit x j = false) :
    x < 2 ^ P := by
  have hEq : x = x % 2 ^ P := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < P
    · rw [decide_eq_true hi, Bool.true_and]
    · rw [decide_eq_false hi, Bool.false_and, h i (by omega)]
  rw [hEq]
  exact Nat.mod_lt x (Nat.two_pow_pos P)

theorem testBit_mul_repFactor (col x u topU j : Nat) (hLe : u ≤ topU)
    (hx : ∀ i, Nat.testBit x i = (decide (i < 3 ^ u) && decide (canonRingColorNat i u = col)))
    (hj : j < 3 ^ topU) :
    Nat.testBit
      (Nat.mul x (Nat.div (Nat.sub (Nat.shiftLeft 1 (3 ^ topU)) 1) (Nat.sub (Nat.shiftLeft 1 (3 ^ u)) 1))) j =
      decide (canonRingColorNat j u = col) := by
  let count := 3 ^ (topU - u)
  have hCountMul : count * 3 ^ u = 3 ^ topU := by
    dsimp [count]
    rw [← Nat.pow_add]
    congr 1
    omega
  have hS1 : Nat.sub (Nat.shiftLeft 1 (3 ^ topU)) 1 = 2 ^ (count * 3 ^ u) - 1 := by
    change 1 <<< (3 ^ topU) - 1 = 2 ^ (count * 3 ^ u) - 1
    rw [Nat.shiftLeft_eq, Nat.one_mul, hCountMul]
  have hS2 : Nat.sub (Nat.shiftLeft 1 (3 ^ u)) 1 = 2 ^ (3 ^ u) - 1 := by
    change 1 <<< (3 ^ u) - 1 = 2 ^ (3 ^ u) - 1
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have hPos : 0 < 2 ^ (3 ^ u) - 1 := by
    have : 2 ^ 1 ≤ 2 ^ (3 ^ u) := Nat.pow_le_pow_right (by decide) (pow3_pos u)
    omega
  have hRep : Nat.div (Nat.sub (Nat.shiftLeft 1 (3 ^ topU)) 1) (Nat.sub (Nat.shiftLeft 1 (3 ^ u)) 1) =
      geomRepeat 1 (3 ^ u) count := by
    change (Nat.sub (Nat.shiftLeft 1 (3 ^ topU)) 1) / (Nat.sub (Nat.shiftLeft 1 (3 ^ u)) 1) = _
    rw [hS1, hS2, ← geomRepeat_one_mul_sub (3 ^ u) count, Nat.mul_div_cancel _ hPos]
  have hMul : Nat.mul x (Nat.div (Nat.sub (Nat.shiftLeft 1 (3 ^ topU)) 1) (Nat.sub (Nat.shiftLeft 1 (3 ^ u)) 1)) =
      geomRepeat x (3 ^ u) count := by
    rw [hRep]
    exact (geomRepeat_mul_cell x (3 ^ u) count).symm
  rw [hMul]
  have hxLt : x < 2 ^ (3 ^ u) := by
    apply lt_two_pow_of_testBit
    intro i hi
    rw [hx i, decide_eq_false (by omega), Bool.false_and]
  rw [testBit_geomRepeat x (3 ^ u) count j hxLt, hCountMul, decide_eq_true hj, Bool.true_and,
      hx (j % 3 ^ u), decide_eq_true (Nat.mod_lt j (pow3_pos u)), Bool.true_and,
      canonRingColorNat_mod_pow3]

theorem xor_eq_iff (x y z : Nat) (hx : x < 4) (hy : y < 4) (hz : z < 4) :
    (x ^^^ y = z) ↔ (x = z ^^^ y) := by
  rcases x with _ | _ | _ | _ | x <;>
  rcases y with _ | _ | _ | _ | y <;>
  rcases z with _ | _ | _ | _ | z <;> (try decide) <;> omega

theorem div_pow3_of_range1 (j u : Nat) (h1 : 3 ^ u ≤ j) (h2 : j < 2 * 3 ^ u) :
    j / 3 ^ u = 1 := by
  have hP : 0 < 3 ^ u := pow3_pos u
  have hSub : (j - 3 ^ u) / 3 ^ u = 0 := Nat.div_eq_of_lt (by omega)
  rw [sub_div_self j (3 ^ u) hP h1] at hSub
  have hGe : 1 ≤ j / 3 ^ u := (Nat.le_div_iff_mul_le hP).mpr (by omega)
  omega

theorem div_pow3_of_range2 (j u : Nat) (h1 : 2 * 3 ^ u ≤ j) (h2 : j < 3 * 3 ^ u) :
    j / 3 ^ u = 2 := by
  have hP : 0 < 3 ^ u := pow3_pos u
  have hSub : (j - 2 * 3 ^ u) / 3 ^ u = 0 := Nat.div_eq_of_lt (by omega)
  rw [sub_two_mul_div_self j (3 ^ u) hP h1] at hSub
  have hGe : 2 ≤ j / 3 ^ u := (Nat.le_div_iff_mul_le hP).mpr (by omega)
  omega

theorem stepRow8_bit1 (u col a b c j : Nat) (hCol : col < 4)
    (ha : ∀ i, Nat.testBit a i = (decide (i < 3 ^ u) && decide (canonRingColorNat i u = col ^^^ 1)))
    (hb : ∀ i, Nat.testBit b i = (decide (i < 3 ^ u) && decide (canonRingColorNat i u = col ^^^ 2)))
    (hc : ∀ i, Nat.testBit c i = (decide (i < 3 ^ u) && decide (canonRingColorNat i u = col ^^^ 3))) :
    Nat.testBit (Nat.lor a (Nat.lor (Nat.shiftLeft b (3 ^ u)) (Nat.shiftLeft c (2 * 3 ^ u)))) j =
      (decide (j < 3 ^ (u + 1)) && decide (canonRingColorNat j (u + 1) = col)) := by
  rw [testBit_lor, testBit_lor, testBit_shiftLeft, testBit_shiftLeft, ha, hb, hc]
  have hPow : 3 ^ (u + 1) = 3 * 3 ^ u := Nat.pow_succ'
  have hCu : canonRingColorNat j u < 4 := canonRingColorNat_lt_four j u
  by_cases hj0 : j < 3 ^ u
  · have hj3 : j < 3 ^ (u + 1) := by omega
    have hGe1 : ¬ (j ≥ 3 ^ u) := by omega
    have hGe2 : ¬ (j ≥ 2 * 3 ^ u) := by omega
    have hDiv : j / 3 ^ u = 0 := Nat.div_eq_of_lt hj0
    dsimp [canonRingColorNat]
    rw [decide_eq_true hj0, decide_eq_true hj3, decide_eq_false hGe1, decide_eq_false hGe2, hDiv]
    simp [xor_eq_iff (canonRingColorNat j u) 1 col hCu (by decide) hCol]
  · by_cases hj1 : j < 2 * 3 ^ u
    · have hj3 : j < 3 ^ (u + 1) := by omega
      have hGe1 : j ≥ 3 ^ u := by omega
      have hSub1 : j - 3 ^ u < 3 ^ u := by omega
      have hGe2 : ¬ (j ≥ 2 * 3 ^ u) := by omega
      have hDiv : j / 3 ^ u = 1 := div_pow3_of_range1 j u hGe1 hj1
      dsimp [canonRingColorNat]
      rw [decide_eq_false hj0, decide_eq_true hj3, decide_eq_true hGe1, decide_eq_true hSub1,
          decide_eq_false hGe2, hDiv, canonRingColorNat_sub_pow3 j u hGe1]
      simp [xor_eq_iff (canonRingColorNat j u) 2 col hCu (by decide) hCol]
    · by_cases hj2 : j < 3 * 3 ^ u
      · have hj3 : j < 3 ^ (u + 1) := by omega
        have hGe1 : j ≥ 3 ^ u := by omega
        have hSub1 : ¬ (j - 3 ^ u < 3 ^ u) := by omega
        have hGe2 : j ≥ 2 * 3 ^ u := by omega
        have hSub2 : j - 2 * 3 ^ u < 3 ^ u := by omega
        have hDiv : j / 3 ^ u = 2 := div_pow3_of_range2 j u hGe2 hj2
        dsimp [canonRingColorNat]
        rw [decide_eq_false hj0, decide_eq_true hj3, decide_eq_true hGe1, decide_eq_false hSub1,
            decide_eq_true hGe2, decide_eq_true hSub2, hDiv, canonRingColorNat_sub_two_pow3 j u hGe2]
        simp [xor_eq_iff (canonRingColorNat j u) 3 col hCu (by decide) hCol]
      · have hj3 : ¬ (j < 3 ^ (u + 1)) := by omega
        have hSub1 : ¬ (j - 3 ^ u < 3 ^ u) := by omega
        have hSub2 : ¬ (j - 2 * 3 ^ u < 3 ^ u) := by omega
        rw [decide_eq_false hj0, decide_eq_false hj3, decide_eq_false hSub1, decide_eq_false hSub2]
        simp

theorem stepRow8_bit0 (u col a0 b j : Nat) (hCol : col < 4)
    (ha0 : ∀ i, Nat.testBit a0 i = (decide (i < 3 ^ u) && decide (canonRingColorNat i u = col ^^^ 1) && isCanon12 u i))
    (hb : ∀ i, Nat.testBit b i = (decide (i < 3 ^ u) && decide (canonRingColorNat i u = col ^^^ 2))) :
    Nat.testBit (Nat.lor a0 (Nat.shiftLeft b (3 ^ u))) j =
      (decide (j < 3 ^ (u + 1)) && decide (canonRingColorNat j (u + 1) = col) && isCanon12 (u + 1) j) := by
  rw [testBit_lor, testBit_shiftLeft, ha0, hb]
  have hPow : 3 ^ (u + 1) = 3 * 3 ^ u := Nat.pow_succ'
  have hCu : canonRingColorNat j u < 4 := canonRingColorNat_lt_four j u
  by_cases hj0 : j < 3 ^ u
  · have hj3 : j < 3 ^ (u + 1) := by omega
    have hGe1 : ¬ (j ≥ 3 ^ u) := by omega
    have hDiv : j / 3 ^ u = 0 := Nat.div_eq_of_lt hj0
    dsimp [canonRingColorNat, isCanon12]
    rw [decide_eq_true hj0, decide_eq_true hj3, decide_eq_false hGe1, hDiv]
    simp [xor_eq_iff (canonRingColorNat j u) 1 col hCu (by decide) hCol]
  · by_cases hj1 : j < 2 * 3 ^ u
    · have hj3 : j < 3 ^ (u + 1) := by omega
      have hGe1 : j ≥ 3 ^ u := by omega
      have hSub1 : j - 3 ^ u < 3 ^ u := by omega
      have hDiv : j / 3 ^ u = 1 := div_pow3_of_range1 j u hGe1 hj1
      dsimp [canonRingColorNat, isCanon12]
      rw [decide_eq_false hj0, decide_eq_true hj3, decide_eq_true hGe1, decide_eq_true hSub1,
          hDiv, canonRingColorNat_sub_pow3 j u hGe1]
      simp [xor_eq_iff (canonRingColorNat j u) 2 col hCu (by decide) hCol]
    · by_cases hj2 : j < 3 * 3 ^ u
      · have hj3 : j < 3 ^ (u + 1) := by omega
        have hSub1 : ¬ (j - 3 ^ u < 3 ^ u) := by omega
        have hDiv : j / 3 ^ u = 2 := div_pow3_of_range2 j u (by omega) hj2
        dsimp [isCanon12]
        rw [decide_eq_false hj0, decide_eq_true hj3, decide_eq_false hSub1, hDiv]
        simp
      · have hj3 : ¬ (j < 3 ^ (u + 1)) := by omega
        have hSub1 : ¬ (j - 3 ^ u < 3 ^ u) := by omega
        rw [decide_eq_false hj0, decide_eq_false hj3, decide_eq_false hSub1]
        simp

def Row8Invariant (u : Nat) (v00 v01 v10 v11 v20 v21 v30 v31 : Nat) : Prop :=
  ∀ j,
    Nat.testBit v01 j = (decide (j < 3 ^ u) && decide (canonRingColorNat j u = 1)) ∧
    Nat.testBit v11 j = (decide (j < 3 ^ u) && decide (canonRingColorNat j u = 0)) ∧
    Nat.testBit v21 j = (decide (j < 3 ^ u) && decide (canonRingColorNat j u = 3)) ∧
    Nat.testBit v31 j = (decide (j < 3 ^ u) && decide (canonRingColorNat j u = 2)) ∧
    Nat.testBit v00 j = (decide (j < 3 ^ u) && decide (canonRingColorNat j u = 1) && isCanon12 u j) ∧
    Nat.testBit v10 j = (decide (j < 3 ^ u) && decide (canonRingColorNat j u = 0) && isCanon12 u j) ∧
    Nat.testBit v20 j = (decide (j < 3 ^ u) && decide (canonRingColorNat j u = 3) && isCanon12 u j) ∧
    Nat.testBit v30 j = (decide (j < 3 ^ u) && decide (canonRingColorNat j u = 2) && isCanon12 u j)

theorem row8Invariant_zero : Row8Invariant 0 1 1 0 0 0 0 0 0 := by
  intro j
  by_cases hj : j < 1
  · have hj0 : j = 0 := by omega
    subst hj0
    decide
  · have hPow : 3 ^ 0 = 1 := rfl
    rw [hPow, decide_eq_false hj]
    have h1 : Nat.testBit 1 j = false := by
      apply Nat.testBit_lt_two_pow
      have : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [h1, Nat.zero_testBit]
    simp

theorem stepRow8_preserves {α : Type} [Inhabited α] (u : Nat)
    (v00 v01 v10 v11 v20 v21 v30 v31 : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → α)
    (Q : α → Prop)
    (hRow : Row8Invariant u v00 v01 v10 v11 v20 v21 v30 v31)
    (hk : ∀ n00 n01 n10 n11 n20 n21 n30 n31,
      Row8Invariant (u + 1) n00 n01 n10 n11 n20 n21 n30 n31 →
      Q (k n00 n01 n10 n11 n20 n21 n30 n31)) :
    Q (stepRow8 (3 ^ u) (2 * 3 ^ u) v00 v01 v10 v11 v20 v21 v30 v31 k) := by
  unfold stepRow8
  apply hk
  intro j
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepRow8_bit1 u 1 v11 v21 v31 j (by decide)
      (fun i => (hRow i).2.1) (fun i => (hRow i).2.2.1) (fun i => (hRow i).2.2.2.1)
  · exact stepRow8_bit1 u 0 v01 v31 v21 j (by decide)
      (fun i => (hRow i).1) (fun i => (hRow i).2.2.2.1) (fun i => (hRow i).2.2.1)
  · exact stepRow8_bit1 u 3 v31 v01 v11 j (by decide)
      (fun i => (hRow i).2.2.2.1) (fun i => (hRow i).1) (fun i => (hRow i).2.1)
  · exact stepRow8_bit1 u 2 v21 v11 v01 j (by decide)
      (fun i => (hRow i).2.2.1) (fun i => (hRow i).2.1) (fun i => (hRow i).1)
  · exact stepRow8_bit0 u 1 v10 v21 j (by decide)
      (fun i => (hRow i).2.2.2.2.2.1) (fun i => (hRow i).2.2.1)
  · exact stepRow8_bit0 u 0 v00 v31 j (by decide)
      (fun i => (hRow i).2.2.2.2.1) (fun i => (hRow i).2.2.2.1)
  · exact stepRow8_bit0 u 3 v30 v01 j (by decide)
      (fun i => (hRow i).2.2.2.2.2.2.2) (fun i => (hRow i).1)
  · exact stepRow8_bit0 u 2 v20 v11 j (by decide)
      (fun i => (hRow i).2.2.2.2.2.2.1) (fun i => (hRow i).2.1)

def ValidRingColsAt (canonValid : Nat) (rings : List RingColMasks) (u : Nat) : Prop :=
  ∃ c0 c1 c2 c3 : Nat,
    (∀ {α : Type} (k : Nat → Nat → Nat → Nat → α), lookupRingCols u rings k = k c0 c1 c2 c3) ∧
    ∀ j,
      Nat.testBit c0 j = (Nat.testBit canonValid j && decide (canonRingColorNat j u = 0)) ∧
      Nat.testBit c1 j = (Nat.testBit canonValid j && decide (canonRingColorNat j u = 1)) ∧
      Nat.testBit c2 j = (Nat.testBit canonValid j && decide (canonRingColorNat j u = 2)) ∧
      Nat.testBit c3 j = (Nat.testBit canonValid j && decide (canonRingColorNat j u = 3))

theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hBeq : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (Nat.beq_eq.mp hBeq))

theorem lookupRingCols_cons_eq (u c0 c1 c2 c3 : Nat) (rest : List RingColMasks)
    {α : Type} (k : Nat → Nat → Nat → Nat → α) :
    lookupRingCols u (RingColMasks.mk u c0 c1 c2 c3 :: rest) k = k c0 c1 c2 c3 := by
  change Bool.rec (lookupRingCols u rest k) (k c0 c1 c2 c3) (Nat.beq u u) = k c0 c1 c2 c3
  rw [Nat.beq_refl]

theorem lookupRingCols_cons_ne (hu u c0 c1 c2 c3 : Nat) (rest : List RingColMasks)
    (hNe : hu ≠ u) {α : Type} (k : Nat → Nat → Nat → Nat → α) :
    lookupRingCols u (RingColMasks.mk hu c0 c1 c2 c3 :: rest) k = lookupRingCols u rest k := by
  change Bool.rec (lookupRingCols u rest k) (k c0 c1 c2 c3) (Nat.beq hu u) = lookupRingCols u rest k
  rw [nat_beq_false_of_ne hNe]

theorem validRingColsAt_cons_ne (canonValid hu u c0 c1 c2 c3 : Nat) (rest : List RingColMasks)
    (hNe : hu ≠ u) (hRest : ValidRingColsAt canonValid rest u) :
    ValidRingColsAt canonValid (RingColMasks.mk hu c0 c1 c2 c3 :: rest) u := by
  rcases hRest with ⟨rc0, rc1, rc2, rc3, hLook, hBits⟩
  refine ⟨rc0, rc1, rc2, rc3, ?_, hBits⟩
  intro α k
  rw [lookupRingCols_cons_ne hu u c0 c1 c2 c3 rest hNe k, hLook]

theorem buildRingColLoop_base_spec (mMax x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 : Nat)
    (hm : 2 ≤ mMax)
    (hRow : Row8Invariant (mMax - 1) x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31) :
    let canonValid := Nat.lor x1_00 (Nat.lor x1_30 x1_20)
    let rings :=
      RingColMasks.mk 0 0 canonValid 0 0 ::
      RingColMasks.mk (Nat.sub mMax 1) 0 x1_00 x1_30 x1_20 ::
      RingColMasks.mk mMax x1_00 0 x1_20 x1_30 :: []
    (∀ j, Nat.testBit canonValid j =
      (decide (j < 3 ^ (mMax - 1)) && decide (canonRingColorNat j (mMax - 1) ≠ 0) && isCanon12 (mMax - 1) j)) ∧
    ValidRingColsAt canonValid rings 0 ∧
    ValidRingColsAt canonValid rings (mMax - 1) ∧
    ValidRingColsAt canonValid rings mMax := by
  let canonValid := Nat.lor x1_00 (Nat.lor x1_30 x1_20)
  have hCV : ∀ j, Nat.testBit canonValid j =
      (decide (j < 3 ^ (mMax - 1)) && decide (canonRingColorNat j (mMax - 1) ≠ 0) && isCanon12 (mMax - 1) j) := by
    intro j
    rcases hRow j with ⟨_, _, _, _, h00, _, h20, h30⟩
    change Nat.testBit (Nat.lor x1_00 (Nat.lor x1_30 x1_20)) j = _
    rw [testBit_lor, testBit_lor, h00, h30, h20]
    have hLt4 := canonRingColorNat_lt_four j (mMax - 1)
    rcases hC : canonRingColorNat j (mMax - 1) with _ | _ | _ | _ | c
    · simp
    · simp
    · simp
    · simp
    · omega
  refine ⟨hCV, ?_, ?_, ?_⟩
  · refine ⟨0, canonValid, 0, 0, ?_, ?_⟩
    · intro α k
      exact lookupRingCols_cons_eq 0 0 canonValid 0 0 _ k
    · intro j
      have hd0 : decide (canonRingColorNat j 0 = 0) = false := rfl
      have hd1 : decide (canonRingColorNat j 0 = 1) = true := rfl
      have hd2 : decide (canonRingColorNat j 0 = 2) = false := rfl
      have hd3 : decide (canonRingColorNat j 0 = 3) = false := rfl
      rw [hd0, hd1, hd2, hd3, Nat.zero_testBit, Bool.and_false, Bool.and_true]
      exact ⟨rfl, rfl, rfl, rfl⟩
  · apply validRingColsAt_cons_ne _ 0 (mMax - 1) 0 canonValid 0 0 _ (by omega)
    refine ⟨0, x1_00, x1_30, x1_20, ?_, ?_⟩
    · intro α k
      exact lookupRingCols_cons_eq (mMax - 1) 0 x1_00 x1_30 x1_20 _ k
    · intro j
      rcases hRow j with ⟨_, _, _, _, h00, _, h20, h30⟩
      rw [hCV j, h00, h30, h20]
      have hLt4 := canonRingColorNat_lt_four j (mMax - 1)
      rcases hC : canonRingColorNat j (mMax - 1) with _ | _ | _ | _ | c
      · simp
      · simp
      · simp
      · simp
      · omega
  · apply validRingColsAt_cons_ne _ 0 mMax 0 canonValid 0 0 _ (by omega)
    apply validRingColsAt_cons_ne _ (mMax - 1) mMax 0 x1_00 x1_30 x1_20 _ (by omega)
    refine ⟨x1_00, 0, x1_20, x1_30, ?_, ?_⟩
    · intro α k
      exact lookupRingCols_cons_eq mMax x1_00 0 x1_20 x1_30 _ k
    · intro j
      rcases hRow j with ⟨_, _, _, _, h00, _, h20, h30⟩
      rw [hCV j, h00, h20, h30]
      by_cases hj : j < 3 ^ (mMax - 1)
      · have hEqM : mMax = (mMax - 1) + 1 := by omega
        have hStep : canonRingColorNat j mMax = canonRingColorNat j (mMax - 1) ^^^ 1 := by
          rw [hEqM]
          dsimp [canonRingColorNat]
          rw [Nat.div_eq_of_lt hj]
        rw [hStep]
        have hLt4 := canonRingColorNat_lt_four j (mMax - 1)
        rcases hC : canonRingColorNat j (mMax - 1) with _ | _ | _ | _ | c
        · simp [decide_eq_true hj]
        · simp [decide_eq_true hj]
        · simp [decide_eq_true hj]
        · simp [decide_eq_true hj]
        · omega
      · rw [decide_eq_false hj]
        simp

theorem buildRingColLoop_spec {α : Type} [Inhabited α] (mMax steps u : Nat)
    (x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 : Nat)
    (k : Nat → Nat → List RingColMasks → α)
    (Q : α → Prop)
    (hm : 2 ≤ mMax)
    (hu : 2 ≤ u)
    (hSum : (u - 1) + steps = mMax - 1)
    (hRow : Row8Invariant (u - 1) x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31)
    (hk : ∀ canonValid totalMask rings,
      totalMask = Nat.sub (Nat.shiftLeft 1 (3 ^ (mMax - 1))) 1 →
      (∀ j, Nat.testBit canonValid j =
        (decide (j < 3 ^ (mMax - 1)) && decide (canonRingColorNat j (mMax - 1) ≠ 0) && isCanon12 (mMax - 1) j)) →
      (∀ v, (v = 0 ∨ (u - 1 ≤ v ∧ v ≤ mMax)) → ValidRingColsAt canonValid rings v) →
      Q (k canonValid totalMask rings)) :
    Q (buildRingColLoop mMax steps u (3 ^ (u - 1)) x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 k) := by
  induction steps generalizing u x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 k with
  | zero =>
    have hU : u - 1 = mMax - 1 := by omega
    change Q
      (let canonValid := Nat.lor x1_00 (Nat.lor x1_30 x1_20)
       let totalMask := Nat.sub (Nat.shiftLeft 1 (3 ^ (u - 1))) 1
       seqNat canonValid (seqNat totalMask
         (k canonValid totalMask
           (RingColMasks.mk 0 0 canonValid 0 0 ::
            RingColMasks.mk (Nat.sub mMax 1) 0 x1_00 x1_30 x1_20 ::
            RingColMasks.mk mMax x1_00 0 x1_20 x1_30 :: []))))
    rw [seqNat_eq, seqNat_eq]
    rw [hU] at hRow ⊢
    rcases buildRingColLoop_base_spec mMax x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 hm hRow with
      ⟨hCV, h0, hM1, hM⟩
    apply hk _ _ _ rfl hCV
    intro v hv
    rcases hv with rfl | ⟨hGe, hLe⟩
    · exact h0
    · have hCases : v = mMax - 1 ∨ v = mMax := by omega
      rcases hCases with rfl | rfl
      · exact hM1
      · exact hM
  | succ steps ih =>
    change Q (stepRow8 (3 ^ (u - 1)) (2 * 3 ^ (u - 1)) x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31
      (fun n1_00 n1_01 n1_10 n1_11 n1_20 n1_21 n1_30 n1_31 =>
        buildRingColLoop mMax steps (u + 1) (3 * 3 ^ (u - 1))
          n1_00 n1_01 n1_10 n1_11 n1_20 n1_21 n1_30 n1_31
          (fun canonValid totalMask rest =>
            let repFactor := Nat.div totalMask (Nat.sub (Nat.shiftLeft 1 (3 ^ (u - 1))) 1)
            let c0_u := Nat.land canonValid (Nat.mul x1_11 repFactor)
            let c1_u := Nat.land canonValid (Nat.mul x1_01 repFactor)
            let c2_u := Nat.land canonValid (Nat.mul x1_31 repFactor)
            let c3_u := Nat.land canonValid (Nat.mul x1_21 repFactor)
            seqNat c0_u (seqNat c1_u (seqNat c2_u (seqNat c3_u
              (k canonValid totalMask (RingColMasks.mk (Nat.sub u 1) c0_u c1_u c2_u c3_u :: rest))))))))
    apply stepRow8_preserves (u - 1) x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 _ Q hRow
    intro n1_00 n1_01 n1_10 n1_11 n1_20 n1_21 n1_30 n1_31 hNextRow
    have hPowEq : 3 * 3 ^ (u - 1) = 3 ^ ((u + 1) - 1) := by
      have : (u + 1) - 1 = (u - 1) + 1 := by omega
      rw [this, Nat.pow_succ']
    have hNextRow' : Row8Invariant ((u + 1) - 1) n1_00 n1_01 n1_10 n1_11 n1_20 n1_21 n1_30 n1_31 := by
      have : (u + 1) - 1 = (u - 1) + 1 := by omega
      rw [this]
      exact hNextRow
    rw [hPowEq]
    apply ih (u + 1) n1_00 n1_01 n1_10 n1_11 n1_20 n1_21 n1_30 n1_31 _
      (by omega) (by omega) hNextRow'
    intro canonValid totalMask rest hTot hCV hRest
    dsimp only []
    rw [seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq]
    apply hk canonValid totalMask _ hTot hCV
    intro v hv
    by_cases hEqV : u - 1 = v
    · subst hEqV
      let repFactor := Nat.div totalMask (Nat.sub (Nat.shiftLeft 1 (3 ^ (u - 1))) 1)
      let c0_u := Nat.land canonValid (Nat.mul x1_11 repFactor)
      let c1_u := Nat.land canonValid (Nat.mul x1_01 repFactor)
      let c2_u := Nat.land canonValid (Nat.mul x1_31 repFactor)
      let c3_u := Nat.land canonValid (Nat.mul x1_21 repFactor)
      refine ⟨c0_u, c1_u, c2_u, c3_u, ?_, ?_⟩
      · intro β kCol
        exact lookupRingCols_cons_eq (u - 1) c0_u c1_u c2_u c3_u rest kCol
      · intro j
        change
          Nat.testBit (Nat.land canonValid (Nat.mul x1_11 repFactor)) j = _ ∧
          Nat.testBit (Nat.land canonValid (Nat.mul x1_01 repFactor)) j = _ ∧
          Nat.testBit (Nat.land canonValid (Nat.mul x1_31 repFactor)) j = _ ∧
          Nat.testBit (Nat.land canonValid (Nat.mul x1_21 repFactor)) j = _
        rw [testBit_land, testBit_land, testBit_land, testBit_land]
        change
          (Nat.testBit canonValid j && Nat.testBit (Nat.mul x1_11 (Nat.div totalMask (Nat.sub (Nat.shiftLeft 1 (3 ^ (u - 1))) 1))) j) = _ ∧
          (Nat.testBit canonValid j && Nat.testBit (Nat.mul x1_01 (Nat.div totalMask (Nat.sub (Nat.shiftLeft 1 (3 ^ (u - 1))) 1))) j) = _ ∧
          (Nat.testBit canonValid j && Nat.testBit (Nat.mul x1_31 (Nat.div totalMask (Nat.sub (Nat.shiftLeft 1 (3 ^ (u - 1))) 1))) j) = _ ∧
          (Nat.testBit canonValid j && Nat.testBit (Nat.mul x1_21 (Nat.div totalMask (Nat.sub (Nat.shiftLeft 1 (3 ^ (u - 1))) 1))) j) = _
        rw [hTot]
        by_cases hj : j < 3 ^ (mMax - 1)
        · rw [testBit_mul_repFactor 0 x1_11 (u - 1) (mMax - 1) j (by omega) (fun i => (hRow i).2.1) hj,
              testBit_mul_repFactor 1 x1_01 (u - 1) (mMax - 1) j (by omega) (fun i => (hRow i).1) hj,
              testBit_mul_repFactor 2 x1_31 (u - 1) (mMax - 1) j (by omega) (fun i => (hRow i).2.2.2.1) hj,
              testBit_mul_repFactor 3 x1_21 (u - 1) (mMax - 1) j (by omega) (fun i => (hRow i).2.2.1) hj]
          exact ⟨rfl, rfl, rfl, rfl⟩
        · have hCVFalse : Nat.testBit canonValid j = false := by
            rw [hCV j, decide_eq_false hj, Bool.false_and, Bool.false_and]
          rw [hCVFalse]
          simp
    · apply validRingColsAt_cons_ne canonValid (u - 1) v _ _ _ _ rest hEqV
      apply hRest v
      rcases hv with rfl | ⟨hGe, hLe⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by omega, hLe⟩

theorem withRingColMasks_spec {α : Type} [Inhabited α] (mMax : Nat)
    (k : Nat → List RingColMasks → α) (Q : α → Prop)
    (hm : 2 ≤ mMax)
    (hk : ∀ canonValid rings,
      (∀ j, Nat.testBit canonValid j =
        (decide (j < 3 ^ (mMax - 1)) && decide (canonRingColorNat j (mMax - 1) ≠ 0) && isCanon12 (mMax - 1) j)) →
      (∀ v ≤ mMax, ValidRingColsAt canonValid rings v) →
      Q (k canonValid rings)) :
    Q (withRingColMasks mMax k) := by
  unfold withRingColMasks
  change Q (stepRow8 (3 ^ 0) (2 * 3 ^ 0) 1 1 0 0 0 0 0 0
    (fun x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 =>
      buildRingColLoop mMax (mMax - 2) 2 (3 ^ (2 - 1))
        x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31
        (fun canonValid _totalMask rings => k canonValid rings)))
  apply stepRow8_preserves 0 1 1 0 0 0 0 0 0 _ Q row8Invariant_zero
  intro x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 hRow1
  apply buildRingColLoop_spec mMax (mMax - 2) 2
    x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 _ Q hm (by decide) (by omega) hRow1
  intro canonValid _totalMask rings _ hCV hRings
  apply hk canonValid rings hCV
  intro v hv
  apply hRings v
  by_cases hv0 : v = 0
  · exact Or.inl hv0
  · exact Or.inr ⟨by omega, hv⟩

/-!
## Part 4: Canonical Slice Representative & Affine Coloring Equivalence
-/

theorem div_pow3_mapTernaryDigits (f : Nat → Nat) (hf : ∀ d < 3, f d < 3)
    (k i j : Nat) (hi : i < k) :
    ((mapTernaryDigits f k j) / 3 ^ i) % 3 = f ((j / 3 ^ i) % 3) := by
  induction k generalizing i j with
  | zero => omega
  | succ k ih =>
    dsimp [mapTernaryDigits]
    have hd : f (j % 3) < 3 := hf (j % 3) (Nat.mod_lt j (by decide))
    rcases i with _ | i
    · rw [Nat.pow_zero, Nat.div_one, Nat.div_one]
      omega
    · have hDiv : (f (j % 3) + 3 * mapTernaryDigits f k (j / 3)) / 3 ^ (i + 1) =
          mapTernaryDigits f k (j / 3) / 3 ^ i := by
        rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        have h1 : (f (j % 3) + 3 * mapTernaryDigits f k (j / 3)) / 3 = mapTernaryDigits f k (j / 3) := by omega
        rw [h1]
      have hDivJ : j / 3 ^ (i + 1) = (j / 3) / 3 ^ i := by
        rw [Nat.pow_succ', Nat.div_div_eq_div_mul]
      rw [hDiv, hDivJ, ih i (j / 3) (by omega)]

theorem div_pow3_permTraceVal (p : Nat → Nat) (hp : ∀ d < 3, p d < 3)
    (r : Nat) (b : Nat → Color) (rem i e : Nat) (he : e < rem) :
    ((permTraceVal p r b rem i) / 3 ^ e) % 3 = p (edgeDigitAt r b (i + e)) := by
  induction rem generalizing i e with
  | zero => omega
  | succ rem ih =>
    dsimp [permTraceVal]
    have hd : p (edgeDigitAt r b i) < 3 := hp _ (edgeDigitAt_lt_three r b i)
    rcases e with _ | e
    · have hAdd0 : i + 0 = i := Nat.add_zero i
      rw [hAdd0, Nat.pow_zero, Nat.div_one]
      omega
    · have hDiv : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b rem (i + 1)) / 3 ^ (e + 1) =
          permTraceVal p r b rem (i + 1) / 3 ^ e := by
        rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        have h1 : (p (edgeDigitAt r b i) + 3 * permTraceVal p r b rem (i + 1)) / 3 =
            permTraceVal p r b rem (i + 1) := by omega
        rw [h1]
      rw [hDiv, ih (i + 1) e (by omega)]
      have hAdd : i + 1 + e = i + (e + 1) := by omega
      rw [hAdd]

theorem isCanon12_or_swap12Idx (m u j : Nat) (hLe : u ≤ m) :
    isCanon12 u j = true ∨ isCanon12 u (swap12Idx m j) = true := by
  induction u with
  | zero => exact Or.inl rfl
  | succ u ih =>
    have hSwapDig : ((swap12Idx m j) / 3 ^ u) % 3 = swap12Digit ((j / 3 ^ u) % 3) :=
      div_pow3_mapTernaryDigits swap12Digit swap12Digit_lt_three m u j (by omega)
    have hd : (j / 3 ^ u) % 3 < 3 := Nat.mod_lt _ (by decide)
    dsimp [isCanon12]
    rw [hSwapDig]
    rcases hEq : (j / 3 ^ u) % 3 with _ | _ | _ | d
    · have hS0 : swap12Digit 0 = 0 := rfl
      rw [hS0]
      simp [ih (by omega)]
    · exact Or.inl (by simp)
    · have hS2 : swap12Digit 2 = 1 := rfl
      rw [hS2]
      exact Or.inr (by simp)
    · omega

theorem permTraceVal_congr (p1 p2 : Nat → Nat) (hEq : ∀ d < 3, p1 d = p2 d)
    (r : Nat) (b : Nat → Color) (rem i : Nat) :
    permTraceVal p1 r b rem i = permTraceVal p2 r b rem i := by
  induction rem generalizing i with
  | zero => rfl
  | succ rem ih =>
    dsimp [permTraceVal]
    rw [hEq _ (edgeDigitAt_lt_three r b i), ih (i + 1)]

theorem canonDigitPerm_eq_permDigit (r : Nat) (b : Nat → Color) :
    ∃ k : Fin 6,
      (∀ d < 3, canonDigitPerm r b d = permDigit k d) ∧
      (∃ kSwap : Fin 6, ∀ d < 3, swap12Digit (canonDigitPerm r b d) = permDigit kSwap d) := by
  unfold canonDigitPerm canonPairing
  split
  · refine ⟨⟨0, by decide⟩, ?_, ⟨1, by decide⟩, ?_⟩ <;> (intro d hd; revert d hd; decide)
  · refine ⟨⟨2, by decide⟩, ?_, ⟨4, by decide⟩, ?_⟩ <;> (intro d hd; revert d hd; decide)
  · refine ⟨⟨5, by decide⟩, ?_, ⟨3, by decide⟩, ?_⟩ <;> (intro d hd; revert d hd; decide)

theorem affineColor_xor_edgeDigit (k : Fin 6) (dCol col1 col2 : Color) (hne : col1 ≠ col2) :
    (affineColor k dCol col1).toNat ^^^
      (permDigit k (let diff := col1.toNat ^^^ col2.toNat; if diff > 0 then diff - 1 else 0) + 1) =
      (affineColor k dCol col2).toNat := by
  revert k hne
  cases dCol <;> cases col1 <;> cases col2 <;> decide

theorem canonRingColorNat_eq_affineColor (c : Configuration) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (k : Fin 6) (j : Nat)
    (hj : j = permTraceVal (permDigit k) c.ringSize b (c.ringSize - 2) 0)
    (hTop : permDigit k (edgeDigitAt c.ringSize b (c.ringSize - 2)) = 0)
    (u : Nat) (hu : u < c.ringSize) :
    canonRingColorNat j u =
      (affineColor k (xorColorCol Color.c1 (permColor k (b 0))) (b u)).toNat := by
  let dCol := xorColorCol Color.c1 (permColor k (b 0))
  induction u with
  | zero =>
    dsimp [canonRingColorNat, dCol]
    rw [← affineColor_zero k Color.c1 (b 0)]
    rfl
  | succ u ih =>
    dsimp [canonRingColorNat]
    rw [ih (by omega)]
    have hj_lt : j < 3 ^ (c.ringSize - 2) := by
      rw [hj]
      exact permTraceVal_lt_pow3 (permDigit k) (permDigit_lt_three k) c.ringSize b (c.ringSize - 2) 0
    have hDig : (j / 3 ^ u) % 3 = permDigit k (edgeDigitAt c.ringSize b u) := by
      by_cases hu2 : u < c.ringSize - 2
      · rw [hj, div_pow3_permTraceVal (permDigit k) (permDigit_lt_three k) c.ringSize b (c.ringSize - 2) 0 u hu2,
            Nat.zero_add]
      · have hEqU : u = c.ringSize - 2 := by omega
        subst hEqU
        rw [Nat.div_eq_of_lt hj_lt, Nat.zero_mod, hTop]
    rw [hDig]
    have hMod : (u + 1) % c.ringSize = u + 1 := Nat.mod_eq_of_lt hu
    have hAdj : c.adj u (u + 1) = true := by
      have := h_ring.2 u (by omega)
      rwa [hMod] at this
    have hNe : b u ≠ b (u + 1) := hb u (u + 1) (by omega) hu hAdj
    unfold edgeDigitAt
    rw [hMod]
    exact affineColor_xor_edgeDigit k dCol (b u) (b (u + 1)) hNe

theorem canonRingColor_eq_affineColor (c : Configuration) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (k : Fin 6) (j : Nat)
    (hj : j = permTraceVal (permDigit k) c.ringSize b (c.ringSize - 2) 0)
    (hTop : permDigit k (edgeDigitAt c.ringSize b (c.ringSize - 2)) = 0)
    (u : Nat) (hu : u < c.ringSize) :
    canonRingColor j u =
      affineColor k (xorColorCol Color.c1 (permColor k (b 0))) (b u) := by
  unfold canonRingColor
  rw [canonRingColorNat_eq_affineColor c h_ring b hb k j hj hTop u hu, Soundness.colorOfNat_toNat]

theorem canonRingColorNat_top_ne_zero (c : Configuration) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (k : Fin 6) (j : Nat)
    (hj : j = permTraceVal (permDigit k) c.ringSize b (c.ringSize - 2) 0)
    (hTop : permDigit k (edgeDigitAt c.ringSize b (c.ringSize - 2)) = 0) :
    canonRingColorNat j (c.ringSize - 2) ≠ 0 := by
  have hr : c.ringSize ≥ 2 := h_ring.1
  let dCol := xorColorCol Color.c1 (permColor k (b 0))
  have hLast := canonRingColorNat_eq_affineColor c h_ring b hb k j hj hTop (c.ringSize - 1) (by omega)
  have hj_lt : j < 3 ^ (c.ringSize - 2) := by
    rw [hj]
    exact permTraceVal_lt_pow3 (permDigit k) (permDigit_lt_three k) c.ringSize b (c.ringSize - 2) 0
  have hStep : canonRingColorNat j (c.ringSize - 1) = canonRingColorNat j (c.ringSize - 2) ^^^ 1 := by
    have hEqR : c.ringSize - 1 = (c.ringSize - 2) + 1 := by omega
    rw [hEqR]
    dsimp [canonRingColorNat]
    rw [Nat.div_eq_of_lt hj_lt]
  have hAdj0 : c.adj (c.ringSize - 1) 0 = true := by
    have h1 := h_ring.2 (c.ringSize - 1) (by omega)
    have hMod : (c.ringSize - 1 + 1) % c.ringSize = 0 := by
      have : c.ringSize - 1 + 1 = c.ringSize := by omega
      rw [this, Nat.mod_self]
    rwa [hMod] at h1
  have hNe0 : b (c.ringSize - 1) ≠ b 0 := hb (c.ringSize - 1) 0 (by omega) (by omega) hAdj0
  have hAffNe : affineColor k dCol (b (c.ringSize - 1)) ≠ Color.c1 := by
    intro hEqC1
    have h0 : affineColor k dCol (b 0) = Color.c1 := (affineColor_zero k Color.c1 (b 0)).symm
    exact hNe0 (affineColor_inj k dCol _ _ (hEqC1.trans h0.symm))
  intro hZero
  rw [hZero] at hStep
  have hOne : (affineColor k dCol (b (c.ringSize - 1))).toNat = 1 := hLast.symm.trans hStep
  have hColEq : affineColor k dCol (b (c.ringSize - 1)) = Color.c1 := by
    rw [← Soundness.colorOfNat_toNat (affineColor k dCol (b (c.ringSize - 1))), hOne]
    rfl
  exact hAffNe hColEq

theorem exists_canon_slice_rep (c : Configuration) (h_ring : IsRingCycle c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b) :
    ∃ (k : Fin 6) (j : Nat),
      (j = canonIdx c.ringSize b ∨ j = swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)) ∧
      j < 3 ^ (c.ringSize - 2) ∧
      canonRingColorNat j (c.ringSize - 2) ≠ 0 ∧
      isCanon12 (c.ringSize - 2) j = true ∧
      (∀ u < c.ringSize,
        canonRingColor j u = affineColor k (xorColorCol Color.c1 (permColor k (b 0))) (b u)) := by
  let j0 := canonIdx c.ringSize b
  let j1 := swap12Idx (c.ringSize - 2) j0
  rcases canonDigitPerm_eq_permDigit c.ringSize b with ⟨k0, hk0, k1, hk1⟩
  have hdTop := edgeDigitAt_lt_three c.ringSize b (c.ringSize - 2)
  have hTop0 : permDigit k0 (edgeDigitAt c.ringSize b (c.ringSize - 2)) = 0 := by
    rw [← hk0 _ hdTop]
    exact canonDigitPerm_top_eq_zero c.ringSize b
  have hTop1 : permDigit k1 (edgeDigitAt c.ringSize b (c.ringSize - 2)) = 0 := by
    rw [← hk1 _ hdTop, canonDigitPerm_top_eq_zero c.ringSize b]
    rfl
  have hj0_eq : j0 = permTraceVal (permDigit k0) c.ringSize b (c.ringSize - 2) 0 :=
    permTraceVal_congr (canonDigitPerm c.ringSize b) (permDigit k0) hk0 c.ringSize b (c.ringSize - 2) 0
  have hj1_eq : j1 = permTraceVal (permDigit k1) c.ringSize b (c.ringSize - 2) 0 := by
    dsimp [j1, j0, canonIdx, swap12Idx]
    rw [mapTernaryDigits_permTraceVal swap12Digit (canonDigitPerm c.ringSize b)
          (canonDigitPerm_lt_three c.ringSize b) c.ringSize b (c.ringSize - 2) 0]
    exact permTraceVal_congr _ (permDigit k1) hk1 c.ringSize b (c.ringSize - 2) 0
  rcases isCanon12_or_swap12Idx (c.ringSize - 2) (c.ringSize - 2) j0 (Nat.le_refl _) with hC0 | hC1
  · refine ⟨k0, j0, Or.inl rfl, canonIdx_lt c.ringSize b,
      canonRingColorNat_top_ne_zero c h_ring b hb k0 j0 hj0_eq hTop0, hC0,
      canonRingColor_eq_affineColor c h_ring b hb k0 j0 hj0_eq hTop0⟩
  · refine ⟨k1, j1, Or.inr rfl, swap12Idx_lt (c.ringSize - 2) j0,
      canonRingColorNat_top_ne_zero c h_ring b hb k1 j1 hj1_eq hTop1, hC1,
      canonRingColor_eq_affineColor c h_ring b hb k1 j1 hj1_eq hTop1⟩

/-!
## Part 5: Extra `RConf` Structural Verification
-/

noncomputable def checkContractAliases : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], _ => true
  | (u, v) :: rest, al => Nat.beq (getAlias u al) (getAlias v al) && checkContractAliases rest al

noncomputable def checkRConfKernelExtra (rc : FastReducer.RConf) : Bool :=
  let al := (withBuildAlias rc.contractEdges.toList StrictBox.mk).val
  Nat.ble 3 rc.r &&
  Nat.beq rc.earlier.toList.length rc.n &&
  checkContractAliases rc.contractEdges.toList al

noncomputable def checkRConfListKernelExtra : List FastReducer.RConf → Bool
  | [] => true
  | rc :: rest => checkRConfKernelExtra rc && checkRConfListKernelExtra rest

theorem checkRConfListKernelExtra_sound (L : List FastReducer.RConf) (k : Nat)
    (hk : k < L.length) (h : checkRConfListKernelExtra L = true) :
    checkRConfKernelExtra (L[k]'hk) = true := by
  induction L generalizing k with
  | nil => contradiction
  | cons hd tl ih =>
    dsimp [checkRConfListKernelExtra] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h_hd, h_tl⟩
    cases k with
    | zero => exact h_hd
    | succ k' =>
      have hk' : k' < tl.length := by dsimp at hk; omega
      exact ih k' hk' h_tl

set_option maxRecDepth 100000 in
theorem parsedRConfList_kernelExtra_verified :
    checkRConfListKernelExtra parsedRConfList = true := by
  rfl

theorem sharedCfgs_kernelExtra_verified (idx : Nat) (h_lt : idx < 633) :
    checkRConfKernelExtra Batch.sharedCfgs[idx]! = true := by
  have h_len : idx < parsedRConfList.length := by
    rw [parsedRConfList_length]; exact h_lt
  have h_arr : Batch.sharedCfgs[idx]! = parsedRConfList[idx]'h_len := by
    let arr : Array FastReducer.RConf := ⟨parsedRConfList⟩
    have h_sz : idx < arr.size := h_len
    change arr[idx]! = parsedRConfList[idx]'h_len
    rw [getElem!_pos arr idx h_sz]
    rfl
  rw [h_arr]
  exact checkRConfListKernelExtra_sound parsedRConfList idx h_len parsedRConfList_kernelExtra_verified

/-!
## Part 6: D-Reducibility Interior DFS Soundness
-/

theorem testBit_shiftLeft_self (u : Nat) : Nat.testBit (Nat.shiftLeft 1 u) u = true := by
  rw [testBit_shiftLeft, decide_eq_true (Nat.le_refl u), Bool.true_and, Nat.sub_self]
  rfl

theorem lt_of_ble_eq_false {a b : Nat} (h : Nat.ble a b = false) : b < a := by
  cases hLe : Nat.ble a b with
  | false =>
    have : ¬ (a ≤ b) := fun hle => by rw [Nat.ble_eq_true_of_le hle] at h; contradiction
    omega
  | true => rw [hLe] at h; contradiction

noncomputable def buildIntForbidLoop {α : Type} (r : Nat) (rings : List RingColMasks)
    (k : Nat → Nat → Nat → Nat → Nat → α) : List Nat → Nat → Nat → Nat → Nat → Nat → α
  | [], intMask, u0, u1, u2, u3 => k intMask u0 u1 u2 u3
  | u :: rest, intMask, u0, u1, u2, u3 =>
    selectBool (Nat.ble r u)
      (buildIntForbidLoop r rings k rest (Nat.lor intMask (Nat.shiftLeft 1 u)) u0 u1 u2 u3)
      (lookupRingCols u rings (fun c0 c1 c2 c3 =>
        buildIntForbidLoop r rings k rest intMask
          (Nat.lor u0 c0) (Nat.lor u1 c1) (Nat.lor u2 c2) (Nat.lor u3 c3)))

theorem buildIntForbidAux_eq_loop {α : Type} [Inhabited α] (r : Nat) (rings : List RingColMasks)
    (us : List Nat) (k : Nat → Nat → Nat → Nat → Nat → α) :
    buildIntForbidAux r rings us k = buildIntForbidLoop r rings k us 0 0 0 0 0 := by
  unfold buildIntForbidAux
  have h : ∀ (xs : List Nat) (intMask u0 u1 u2 u3 : Nat),
      @List.rec Nat (fun _ => Nat → Nat → Nat → Nat → Nat → α)
        (fun intMask u0 u1 u2 u3 => k intMask u0 u1 u2 u3)
        (fun u _ ih intMask u0 u1 u2 u3 =>
          selectBool (Nat.ble r u)
            (let nextInt := Nat.lor intMask (Nat.shiftLeft 1 u)
             ih nextInt u0 u1 u2 u3)
            (lookupRingCols u rings (fun c0 c1 c2 c3 =>
              let nu0 := Nat.lor u0 c0
              let nu1 := Nat.lor u1 c1
              let nu2 := Nat.lor u2 c2
              let nu3 := Nat.lor u3 c3
              ih intMask nu0 nu1 nu2 nu3)))
        xs intMask u0 u1 u2 u3 = buildIntForbidLoop r rings k xs intMask u0 u1 u2 u3 := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons u rest ih =>
      intro intMask u0 u1 u2 u3
      dsimp [buildIntForbidLoop]
      cases Nat.ble r u with
      | true => exact ih _ _ _ _ _
      | false =>
        change lookupRingCols u rings _ = lookupRingCols u rings _
        congr 1
        funext c0 c1 c2 c3
        exact ih _ _ _ _ _
  exact h us 0 0 0 0 0

theorem buildIntForbidLoop_map {α β : Type} (r : Nat) (rings : List RingColMasks)
    (g : α → β) (k : Nat → Nat → Nat → Nat → Nat → α)
    (xs : List Nat) (intMask u0 u1 u2 u3 : Nat) :
    g (buildIntForbidLoop r rings k xs intMask u0 u1 u2 u3) =
      buildIntForbidLoop r rings (fun a b c d e => g (k a b c d e)) xs intMask u0 u1 u2 u3 := by
  induction xs generalizing intMask u0 u1 u2 u3 with
  | nil => rfl
  | cons u rest ih =>
    dsimp [buildIntForbidLoop]
    cases Nat.ble r u with
    | true => exact ih _ _ _ _ _
    | false =>
      have hLookup : ∀ (ms : List RingColMasks) (f : Nat → Nat → Nat → Nat → α),
          g (lookupRingCols u ms f) = lookupRingCols u ms (fun c0 c1 c2 c3 => g (f c0 c1 c2 c3)) := by
        intro ms f
        induction ms with
        | nil => rfl
        | cons hd tl ihM =>
          rcases hd with ⟨hu, c0, c1, c2, c3⟩
          change g (Bool.rec (lookupRingCols u tl f) (f c0 c1 c2 c3) (Nat.beq hu u)) =
            Bool.rec (lookupRingCols u tl (fun c0 c1 c2 c3 => g (f c0 c1 c2 c3))) (g (f c0 c1 c2 c3)) (Nat.beq hu u)
          cases Nat.beq hu u with
          | true => rfl
          | false => exact ihM
      rw [hLookup]
      congr 1
      funext c0 c1 c2 c3
      exact ih _ _ _ _ _

theorem buildIntForbidLoop_spec {α : Type} (r canonValid j : Nat)
    (rings : List RingColMasks) (xs : List Nat)
    (intMask u0 u1 u2 u3 : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → α) (Q : α → Prop)
    (hCV : Nat.testBit canonValid j = true)
    (hRings : ∀ u < r, ValidRingColsAt canonValid rings u)
    (hk : ∀ intMask' u0' u1' u2' u3',
      (∀ w, Nat.testBit intMask w = true → Nat.testBit intMask' w = true) →
      (Nat.testBit u0 j = true → Nat.testBit u0' j = true) →
      (Nat.testBit u1 j = true → Nat.testBit u1' j = true) →
      (Nat.testBit u2 j = true → Nat.testBit u2' j = true) →
      (Nat.testBit u3 j = true → Nat.testBit u3' j = true) →
      (∀ u ∈ xs, r ≤ u → Nat.testBit intMask' u = true) →
      (∀ u ∈ xs, u < r →
        (canonRingColor j u = Color.c0 → Nat.testBit u0' j = true) ∧
        (canonRingColor j u = Color.c1 → Nat.testBit u1' j = true) ∧
        (canonRingColor j u = Color.c2 → Nat.testBit u2' j = true) ∧
        (canonRingColor j u = Color.c3 → Nat.testBit u3' j = true)) →
      Q (k intMask' u0' u1' u2' u3')) :
    Q (buildIntForbidLoop r rings k xs intMask u0 u1 u2 u3) := by
  induction xs generalizing intMask u0 u1 u2 u3 with
  | nil =>
    exact hk intMask u0 u1 u2 u3 (fun _ h => h) id id id id
      (fun _ h => False.elim (List.not_mem_nil h))
      (fun _ h => False.elim (List.not_mem_nil h))
  | cons u rest ih =>
    dsimp [buildIntForbidLoop]
    cases hBle : Nat.ble r u with
    | true =>
      have hGe : r ≤ u := Nat.le_of_ble_eq_true hBle
      change Q (buildIntForbidLoop r rings k rest (Nat.lor intMask (Nat.shiftLeft 1 u)) u0 u1 u2 u3)
      apply ih (Nat.lor intMask (Nat.shiftLeft 1 u)) u0 u1 u2 u3
      intro intMask' u0' u1' u2' u3' hIntSub h0Sub h1Sub h2Sub h3Sub hIntRest hColRest
      apply hk intMask' u0' u1' u2' u3'
      · intro w hw; apply hIntSub w; rw [testBit_lor, hw, Bool.true_or]
      · exact h0Sub
      · exact h1Sub
      · exact h2Sub
      · exact h3Sub
      · intro u' hu' hGe'
        rcases List.mem_cons.mp hu' with rfl | hMem
        · apply hIntSub u'; rw [testBit_lor, testBit_shiftLeft_self, Bool.or_true]
        · exact hIntRest u' hMem hGe'
      · intro u' hu' hLt'
        rcases List.mem_cons.mp hu' with rfl | hMem
        · omega
        · exact hColRest u' hMem hLt'
    | false =>
      have hLt : u < r := lt_of_ble_eq_false hBle
      rcases hRings u hLt with ⟨c0, c1, c2, c3, hLook, hBits⟩
      change Q (lookupRingCols u rings (fun c0 c1 c2 c3 =>
        buildIntForbidLoop r rings k rest intMask
          (Nat.lor u0 c0) (Nat.lor u1 c1) (Nat.lor u2 c2) (Nat.lor u3 c3)))
      rw [hLook]
      apply ih intMask (Nat.lor u0 c0) (Nat.lor u1 c1) (Nat.lor u2 c2) (Nat.lor u3 c3)
      intro intMask' u0' u1' u2' u3' hIntSub h0Sub h1Sub h2Sub h3Sub hIntRest hColRest
      apply hk intMask' u0' u1' u2' u3' hIntSub
      · intro h; apply h0Sub; rw [testBit_lor, h, Bool.true_or]
      · intro h; apply h1Sub; rw [testBit_lor, h, Bool.true_or]
      · intro h; apply h2Sub; rw [testBit_lor, h, Bool.true_or]
      · intro h; apply h3Sub; rw [testBit_lor, h, Bool.true_or]
      · intro u' hu' hGe'
        rcases List.mem_cons.mp hu' with rfl | hMem
        · omega
        · exact hIntRest u' hMem hGe'
      · intro u' hu' hLt'
        rcases List.mem_cons.mp hu' with rfl | hMem
        · rcases hBits j with ⟨hb0, hb1, hb2, hb3⟩
          rw [hCV, Bool.true_and] at hb0 hb1 hb2 hb3
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro hc0
            apply h0Sub
            have hNat : canonRingColorNat j u' = 0 := by
              rw [← toNat_canonRingColor j u', hc0]; rfl
            rw [testBit_lor, hb0, decide_eq_true hNat, Bool.or_true]
          · intro hc1
            apply h1Sub
            have hNat : canonRingColorNat j u' = 1 := by
              rw [← toNat_canonRingColor j u', hc1]; rfl
            rw [testBit_lor, hb1, decide_eq_true hNat, Bool.or_true]
          · intro hc2
            apply h2Sub
            have hNat : canonRingColorNat j u' = 2 := by
              rw [← toNat_canonRingColor j u', hc2]; rfl
            rw [testBit_lor, hb2, decide_eq_true hNat, Bool.or_true]
          · intro hc3
            apply h3Sub
            have hNat : canonRingColorNat j u' = 3 := by
              rw [← toNat_canonRingColor j u', hc3]; rfl
            rw [testBit_lor, hb3, decide_eq_true hNat, Bool.or_true]
        · exact hColRest u' hMem hLt'

noncomputable def buildIntStepsDList (r canonValid : Nat) (rings : List RingColMasks) :
    List (Array Nat) → Nat → List IntVertexStep
  | [], _ => []
  | row :: rest, v =>
    let nextV := Nat.succ v
    selectBool (Nat.ble r v)
      (let bitV := Nat.shiftLeft 1 v
       buildIntForbidLoop r rings
         (fun intMask u0 u1 u2 u3 =>
           let f0 := Nat.xor canonValid u0
           let f1 := Nat.xor canonValid u1
           let f2 := Nat.xor canonValid u2
           let f3 := Nat.xor canonValid u3
           IntVertexStep.mk bitV 0 intMask f0 f1 f2 f3 ::
             buildIntStepsDList r canonValid rings rest nextV)
         row.toList 0 0 0 0 0)
      (buildIntStepsDList r canonValid rings rest nextV)

theorem withIntStepsD_eq_list {α : Type} [Inhabited α] (r canonValid : Nat)
    (rings : List RingColMasks) (rows : List (Array Nat)) (k : List IntVertexStep → α) :
    withIntStepsD r canonValid rings rows k = k (buildIntStepsDList r canonValid rings rows 0) := by
  unfold withIntStepsD
  have h : ∀ (xs : List (Array Nat)) (v : Nat) (k : List IntVertexStep → α),
      @List.rec (Array Nat) (fun _ => Nat → (List IntVertexStep → α) → α)
        (fun _ k => k [])
        (fun row _ ih v k =>
          let nextV := Nat.succ v
          selectBool (Nat.ble r v)
            (let bitV := Nat.shiftLeft 1 v
             buildIntForbidAux r rings row.toList (fun intMask u0 u1 u2 u3 =>
               let f0 := Nat.xor canonValid u0
               let f1 := Nat.xor canonValid u1
               let f2 := Nat.xor canonValid u2
               let f3 := Nat.xor canonValid u3
               seqNat bitV (seqNat intMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
                 (ih nextV (fun rest =>
                   k (IntVertexStep.mk bitV 0 intMask f0 f1 f2 f3 :: rest))))))))))
            (ih nextV k))
        xs v k = k (buildIntStepsDList r canonValid rings xs v) := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons row rest ih =>
      intro v k
      dsimp [buildIntStepsDList]
      cases Nat.ble r v with
      | false => exact ih (v + 1) k
      | true =>
        change buildIntForbidAux r rings row.toList _ = k (buildIntForbidLoop r rings _ row.toList 0 0 0 0 0)
        rw [buildIntForbidAux_eq_loop, buildIntForbidLoop_map r rings k]
        congr 1
        funext intMask u0 u1 u2 u3
        rw [seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq]
        exact ih (v + 1) _
  exact h rows 0 k

def PartialColorInv (r v : Nat) (c0 c1 c2 c3 : Nat) (colFn : Nat → Color) : Prop :=
  ∀ u, r ≤ u → u < v →
    (colFn u = Color.c0 → Nat.testBit c0 u = true) ∧
    (colFn u = Color.c1 → Nat.testBit c1 u = true) ∧
    (colFn u = Color.c2 → Nat.testBit c2 u = true) ∧
    (colFn u = Color.c3 → Nat.testBit c3 u = true)

theorem forbid_branch_ne (r v canonValid j cMask intMask uMask : Nat)
    (us : List Nat) (col : Color) (colFn : Nat → Color)
    (hCV : Nat.testBit canonValid j = true)
    (hRingFn : ∀ u < r, colFn u = canonRingColor j u)
    (hReq : Nat.land cMask intMask = 0)
    (hF : Nat.testBit (Nat.xor canonValid uMask) j = true)
    (hInt : ∀ u ∈ us, r ≤ u → Nat.testBit intMask u = true)
    (hRingCol : ∀ u ∈ us, u < r → canonRingColor j u = col → Nat.testBit uMask j = true)
    (hIntCol : ∀ u, r ≤ u → u < v → colFn u = col → Nat.testBit cMask u = true)
    (u : Nat) (hu : u ∈ us) (hu_lt : u < v) :
    colFn u ≠ col := by
  intro hEq
  by_cases hu_r : u < r
  · rw [hRingFn u hu_r] at hEq
    have hBitU := hRingCol u hu hu_r hEq
    rw [testBit_xor, hCV, hBitU] at hF
    contradiction
  · have hGe : r ≤ u := by omega
    have hBitC := hIntCol u hGe hu_lt hEq
    have hBitI := hInt u hu hGe
    have hLand : Nat.testBit (Nat.land cMask intMask) u = true := by
      rw [testBit_land, hBitC, hBitI]; rfl
    rw [hReq, Nat.zero_testBit] at hLand
    contradiction

theorem dfsWitness_buildIntStepsDList_sound (r canonValid j : Nat)
    (rings : List RingColMasks) (xs : List (Array Nat))
    (v c0 c1 c2 c3 : Nat) (colFn : Nat → Color)
    (hCV : Nat.testBit canonValid j = true)
    (hRings : ∀ u < r, ValidRingColsAt canonValid rings u)
    (hWit : DfsWitness (buildIntStepsDList r canonValid rings xs v) c0 c1 c2 c3 j)
    (hRingFn : ∀ u < r, colFn u = canonRingColor j u)
    (hInv : PartialColorInv r v c0 c1 c2 c3 colFn) :
    ∃ full : Nat → Color,
      (∀ u < r, full u = canonRingColor j u) ∧
      (∀ u < v, full u = colFn u) ∧
      (∀ w < xs.length, r ≤ v + w → ∀ u ∈ (listGetD xs w #[]).toList, u < v + w →
        full u ≠ full (v + w)) := by
  induction xs generalizing v c0 c1 c2 c3 colFn with
  | nil =>
    refine ⟨colFn, hRingFn, fun _ _ => rfl, ?_⟩
    intro w hw; simp at hw
  | cons row rest ih =>
    dsimp [buildIntStepsDList] at hWit
    cases hBle : Nat.ble r v with
    | false =>
      rw [hBle] at hWit
      have hLtR : v < r := lt_of_ble_eq_false hBle
      have hInvNext : PartialColorInv r (v + 1) c0 c1 c2 c3 colFn := by
        intro u hGe hLt
        omega
      rcases ih (v + 1) c0 c1 c2 c3 colFn hWit hRingFn hInvNext with ⟨full, hRingFull, hPre, hValid⟩
      refine ⟨full, hRingFull, fun u hu => hPre u (by omega), ?_⟩
      intro w hw hGeW u hu hu_lt
      cases w with
      | zero => omega
      | succ w' =>
        dsimp [listGetD] at hu
        have hAdd : v + (w' + 1) = (v + 1) + w' := by omega
        rw [hAdd] at hGeW hu_lt ⊢
        exact hValid w' (by dsimp at hw; omega) hGeW u hu hu_lt
    | true =>
      rw [hBle] at hWit
      have hGeR : r ≤ v := Nat.le_of_ble_eq_true hBle
      change DfsWitness (buildIntForbidLoop r rings _ row.toList 0 0 0 0 0) c0 c1 c2 c3 j at hWit
      have hStepBranch : ∀ (col : Color) (nc0 nc1 nc2 nc3 : Nat),
          DfsWitness (buildIntStepsDList r canonValid rings rest (v + 1)) nc0 nc1 nc2 nc3 j →
          (∀ u ∈ row.toList, u < v → colFn u ≠ col) →
          PartialColorInv r (v + 1) nc0 nc1 nc2 nc3 (fun u => if u = v then col else colFn u) →
          ∃ full : Nat → Color,
            (∀ u < r, full u = canonRingColor j u) ∧
            (∀ u < v, full u = colFn u) ∧
            (∀ w < (row :: rest).length, r ≤ v + w → ∀ u ∈ (listGetD (row :: rest) w #[]).toList, u < v + w →
              full u ≠ full (v + w)) := by
        intro col nc0 nc1 nc2 nc3 hNext hNeV hInvNext
        let colFn' := fun u => if u = v then col else colFn u
        have hRingFn' : ∀ u < r, colFn' u = canonRingColor j u := by
          intro u hu
          dsimp [colFn']
          rw [if_neg (by omega), hRingFn u hu]
        rcases ih (v + 1) nc0 nc1 nc2 nc3 colFn' hNext hRingFn' hInvNext with ⟨full, hRingFull, hPre, hValid⟩
        refine ⟨full, hRingFull, ?_, ?_⟩
        · intro u hu
          rw [hPre u (by omega)]
          dsimp [colFn']
          rw [if_neg (by omega)]
        · intro w hw hGeW u hu hu_lt
          cases w with
          | zero =>
            dsimp [listGetD] at hu
            rw [Nat.add_zero] at hu_lt ⊢
            rw [hPre u (by omega), hPre v (by omega)]
            dsimp [colFn']
            rw [if_neg (by omega), if_pos rfl]
            exact hNeV u hu hu_lt
          | succ w' =>
            dsimp [listGetD] at hu
            have hAdd : v + (w' + 1) = (v + 1) + w' := by omega
            rw [hAdd] at hGeW hu_lt ⊢
            exact hValid w' (by dsimp at hw; omega) hGeW u hu hu_lt
      refine buildIntForbidLoop_spec r canonValid j rings row.toList 0 0 0 0 0
        (fun intMask u0 u1 u2 u3 =>
          let f0 := Nat.xor canonValid u0
          let f1 := Nat.xor canonValid u1
          let f2 := Nat.xor canonValid u2
          let f3 := Nat.xor canonValid u3
          IntVertexStep.mk (Nat.shiftLeft 1 v) 0 intMask f0 f1 f2 f3 ::
            buildIntStepsDList r canonValid rings rest (v + 1))
        (fun steps => DfsWitness steps c0 c1 c2 c3 j →
          ∃ full : Nat → Color,
            (∀ u < r, full u = canonRingColor j u) ∧
            (∀ u < v, full u = colFn u) ∧
            (∀ w < (row :: rest).length, r ≤ v + w → ∀ u ∈ (listGetD (row :: rest) w #[]).toList, u < v + w →
              full u ≠ full (v + w)))
        hCV hRings ?_ hWit
      intro intMask u0 u1 u2 u3 _ _ _ _ _ hInt hRingCol hWitStep
      dsimp only [] at hWitStep
      cases hWitStep with
      | br0 hReq hF hNext =>
        apply hStepBranch Color.c0 _ _ _ _ hNext
        · intro u hu hu_lt
          exact forbid_branch_ne r v canonValid j c0 intMask u0 row.toList Color.c0 colFn
            hCV hRingFn hReq hF hInt (fun u hu hlt => (hRingCol u hu hlt).1)
            (fun u hge hlt => (hInv u hge hlt).1) u hu hu_lt
        · intro u hGeU hLtU
          by_cases hEq : u = v
          · subst hEq
            simp [testBit_lor]
          · have hLtV : u < v := by omega
            rcases hInv u hGeU hLtV with ⟨h0, h1, h2, h3⟩
            simp only [if_neg hEq]
            refine ⟨fun h => by rw [testBit_lor, h0 h, Bool.true_or], h1, h2, h3⟩
      | br1 hReq hF hNext =>
        apply hStepBranch Color.c1 _ _ _ _ hNext
        · intro u hu hu_lt
          exact forbid_branch_ne r v canonValid j c1 intMask u1 row.toList Color.c1 colFn
            hCV hRingFn hReq hF hInt (fun u hu hlt => (hRingCol u hu hlt).2.1)
            (fun u hge hlt => (hInv u hge hlt).2.1) u hu hu_lt
        · intro u hGeU hLtU
          by_cases hEq : u = v
          · subst hEq
            simp [testBit_lor]
          · have hLtV : u < v := by omega
            rcases hInv u hGeU hLtV with ⟨h0, h1, h2, h3⟩
            simp only [if_neg hEq]
            refine ⟨h0, fun h => by rw [testBit_lor, h1 h, Bool.true_or], h2, h3⟩
      | br2 hReq hF hNext =>
        apply hStepBranch Color.c2 _ _ _ _ hNext
        · intro u hu hu_lt
          exact forbid_branch_ne r v canonValid j c2 intMask u2 row.toList Color.c2 colFn
            hCV hRingFn hReq hF hInt (fun u hu hlt => (hRingCol u hu hlt).2.2.1)
            (fun u hge hlt => (hInv u hge hlt).2.2.1) u hu hu_lt
        · intro u hGeU hLtU
          by_cases hEq : u = v
          · subst hEq
            simp [testBit_lor]
          · have hLtV : u < v := by omega
            rcases hInv u hGeU hLtV with ⟨h0, h1, h2, h3⟩
            simp only [if_neg hEq]
            refine ⟨h0, h1, fun h => by rw [testBit_lor, h2 h, Bool.true_or], h3⟩
      | br3 hReq hF hNext =>
        apply hStepBranch Color.c3 _ _ _ _ hNext
        · intro u hu hu_lt
          exact forbid_branch_ne r v canonValid j c3 intMask u3 row.toList Color.c3 colFn
            hCV hRingFn hReq hF hInt (fun u hu hlt => (hRingCol u hu hlt).2.2.2)
            (fun u hge hlt => (hInv u hge hlt).2.2.2) u hu hu_lt
        · intro u hGeU hLtU
          by_cases hEq : u = v
          · subst hEq
            simp [testBit_lor]
          · have hLtV : u < v := by omega
            rcases hInv u hGeU hLtV with ⟨h0, h1, h2, h3⟩
            simp only [if_neg hEq]
            refine ⟨h0, h1, h2, fun h => by rw [testBit_lor, h3 h, Bool.true_or]⟩

def invPermIdx : Fin 6 → Fin 6
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, _⟩ => ⟨4, by decide⟩
  | ⟨4, _⟩ => ⟨3, by decide⟩
  | ⟨5, _⟩ => ⟨5, by decide⟩

def affineColorInv (k : Fin 6) (dCol : Color) (col : Color) : Color :=
  permColor (invPermIdx k) (xorColorCol col dCol)

theorem affineColorInv_left (k : Fin 6) (dCol col : Color) :
    affineColorInv k dCol (affineColor k dCol col) = col := by
  revert k
  cases dCol <;> cases col <;> decide

theorem affineColorInv_inj (k : Fin 6) (dCol col1 col2 : Color)
    (h : affineColorInv k dCol col1 = affineColorInv k dCol col2) :
    col1 = col2 := by
  revert k h
  cases dCol <;> cases col1 <;> cases col2 <;> decide

theorem listGetD_earlier_eq (rc : FastReducer.RConf) (v : Nat) :
    (listGetD rc.earlier.toList v #[]).toList = (rc.earlier.getD v #[]).toList := by
  rw [listGetD_eq_array_getD rc.earlier v #[]]

theorem extendsToInterior_of_dfsFull (rc : FastReducer.RConf)
    (hLe : rc.r ≤ rc.n) (hLen : rc.earlier.toList.length = rc.n)
    (b : BoundaryColoring (configOfRConf rc))
    (hb : IsValidBoundaryColoring (configOfRConf rc) b)
    (k : Fin 6) (dCol : Color) (j : Nat)
    (hAff : ∀ u < rc.r, canonRingColor j u = affineColor k dCol (b u))
    (full : Nat → Color)
    (hRingFull : ∀ u < rc.r, full u = canonRingColor j u)
    (hIntValid : ∀ w < rc.earlier.toList.length, rc.r ≤ w →
      ∀ u ∈ (listGetD rc.earlier.toList w #[]).toList, u < w → full u ≠ full w) :
    extendsToInterior (configOfRConf rc) b := by
  let c := configOfRConf rc
  have hTot : c.totalNodes = rc.n := by
    dsimp [c, configOfRConf, Configuration.totalNodes]
    omega
  let fullB : Nat → Color := fun u => affineColorInv k dCol (full u)
  refine ⟨fullB, ?_, ?_⟩
  · intro u hu
    dsimp [fullB]
    rw [hRingFull u hu, hAff u hu, affineColorInv_left]
  · intro u v hu hv hAdj
    rw [hTot] at hu hv
    have hNeFull : full u ≠ full v := by
      by_cases huv_r : u < rc.r ∧ v < rc.r
      · rw [hRingFull u huv_r.1, hRingFull v huv_r.2, hAff u huv_r.1, hAff v huv_r.2]
        intro hEqAff
        exact hb u v huv_r.1 huv_r.2 hAdj (affineColor_inj k dCol _ _ hEqAff)
      · dsimp [c, configOfRConf, symAdj] at hAdj
        by_cases hLt : u < v
        · rw [if_pos hLt] at hAdj
          have hGeV : rc.r ≤ v := by omega
          have hMem : u ∈ (listGetD rc.earlier.toList v #[]).toList := by
            rw [listGetD_earlier_eq]
            exact List.elem_iff.mp hAdj
          exact hIntValid v (by rw [hLen]; exact hv) hGeV u hMem hLt
        · rw [if_neg hLt] at hAdj
          by_cases hGt : v < u
          · rw [if_pos hGt] at hAdj
            have hGeU : rc.r ≤ u := by omega
            have hMem : v ∈ (listGetD rc.earlier.toList u #[]).toList := by
              rw [listGetD_earlier_eq]
              exact List.elem_iff.mp hAdj
            exact Ne.symm (hIntValid u (by rw [hLen]; exact hu) hGeU v hMem hGt)
          · rw [if_neg hGt] at hAdj
            contradiction
    intro hEqB
    exact hNeFull (affineColorInv_inj k dCol _ _ hEqB)

theorem computeInitialLiveD_rc_sound (rc : FastReducer.RConf)
    (h_ring : IsRingCycle (configOfRConf rc))
    (h3 : 3 ≤ rc.r) (hLe : rc.r ≤ rc.n) (hLen : rc.earlier.toList.length = rc.n) :
    KernelLiveInvariant (configOfRConf rc)
      (computeInitialLiveD rc.r (Nat.sub rc.r 1)
        (buildSwapSteps (Nat.sub (Nat.sub rc.r 1) 1)).val rc) := by
  let c := configOfRConf rc
  unfold computeInitialLiveD
  refine withRingColMasks_spec (rc.r - 1) Prod.mk
    (fun p => KernelLiveInvariant c
      (@Prod.rec _ _ (fun _ => _)
        (fun canonValid rings =>
          computeInitialLiveDWithRings rc.r canonValid rings (buildSwapSteps (rc.r - 1 - 1)).val rc) p))
    (by omega) ?_
  intro canonValid rings hCV_spec hRings b hb hBit
  dsimp only [] at hBit
  unfold computeInitialLiveDWithRings at hBit
  rw [seqNat_eq] at hBit
  let intSteps := (withIntStepsD rc.r canonValid rings rc.earlier.toList StrictBox.mk).val
  let canonLive := dfsInterior intSteps 0 0 0 0 canonValid canonValid
  rcases exists_canon_slice_rep c h_ring b hb with ⟨k, j, hj_or, hj_lt, hTopNe, hCanon12, hAff⟩
  have hSubEq : rc.r - 1 - 1 = c.ringSize - 2 := by
    dsimp [c, configOfRConf]; omega
  have hCV_j : Nat.testBit canonValid j = true := by
    rw [hCV_spec j, hSubEq, decide_eq_true hj_lt, decide_eq_true hTopNe, hCanon12]
    rfl
  have hCL_j : Nat.testBit canonLive j = false := by
    change
      Nat.testBit (Nat.lor canonLive (swapDigits12 (buildSwapSteps (rc.r - 1 - 1)).val canonLive))
        (canonIdx c.ringSize b) = false ∨
      Nat.testBit (Nat.lor canonLive (swapDigits12 (buildSwapSteps (rc.r - 1 - 1)).val canonLive))
        (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)) = false at hBit
    rw [hSubEq] at hBit
    rcases hBit with hB0 | hB1
    · rw [testBit_lor, Bool.or_eq_false_iff] at hB0
      rcases hj_or with rfl | rfl
      · exact hB0.1
      · exact swapDigits12_buildSwapSteps_false_sound (c.ringSize - 2) canonLive
          (canonIdx c.ringSize b) (canonIdx_lt c.ringSize b) hB0.2
    · rw [testBit_lor, Bool.or_eq_false_iff] at hB1
      rcases hj_or with rfl | rfl
      · have hS := swapDigits12_buildSwapSteps_false_sound (c.ringSize - 2) canonLive
          (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b))
          (swap12Idx_lt (c.ringSize - 2) (canonIdx c.ringSize b)) hB1.2
        rwa [swap12Idx_involutive (c.ringSize - 2) (canonIdx c.ringSize b) hj_lt] at hS
      · exact hB1.1
  have hWit : DfsWitness intSteps 0 0 0 0 j :=
    (dfsInterior_sound intSteps 0 0 0 0 canonValid canonValid j hCV_j hCL_j).2
  have hStepsEq : intSteps = buildIntStepsDList rc.r canonValid rings rc.earlier.toList 0 := by
    dsimp [intSteps]
    rw [withIntStepsD_eq_list]
  rw [hStepsEq] at hWit
  have hRingsLt : ∀ u < rc.r, ValidRingColsAt canonValid rings u :=
    fun u hu => hRings u (by omega)
  have hPart0 : PartialColorInv rc.r 0 0 0 0 0 (canonRingColor j) := by
    intro u _ hLt0; omega
  rcases dfsWitness_buildIntStepsDList_sound rc.r canonValid j rings rc.earlier.toList
      0 0 0 0 0 (canonRingColor j) hCV_j hRingsLt hWit (fun _ _ => rfl) hPart0 with
    ⟨full, hRingFull, _, hIntValid⟩
  have hIntValid0 : ∀ w < rc.earlier.toList.length, rc.r ≤ w →
      ∀ u ∈ (listGetD rc.earlier.toList w #[]).toList, u < w → full u ≠ full w := by
    intro w hw hGe u hu hu_lt
    have h1 := hIntValid w hw (by omega) u hu (by omega)
    rwa [Nat.zero_add] at h1
  exact Eliminated.ext b (extendsToInterior_of_dfsFull rc hLe hLen b hb k
    (xorColorCol Color.c1 (permColor k (b 0))) j hAff full hRingFull hIntValid0)

theorem initLiveIdx_sound (idx : Nat) (hIdx : idx < 633) :
    KernelLiveInvariant (theUnavoidableSet[idx]!) (initLiveIdx idx) := by
  unfold initLiveIdx
  change KernelLiveInvariant (theUnavoidableSet[idx]!)
    (let c := getRConf idx
     computeInitialLiveD c.r (Nat.sub c.r 1) (buildSwapSteps (Nat.sub (Nat.sub c.r 1) 1)).val c)
  rw [getRConf_eq_sharedCfgs idx hIdx, theUnavoidableSet_getElem! idx hIdx]
  have h_ring : IsRingCycle (configOfRConf Batch.sharedCfgs[idx]!) := by
    rw [← theUnavoidableSet_getElem! idx hIdx]
    exact unavoidable_is_ring_cycle idx hIdx
  have h_struct := sharedCfgs_structural_verified idx hIdx
  dsimp [checkRConfStructural] at h_struct
  rcases Bool.and_eq_true_iff.mp h_struct with ⟨h123, _⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, _⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hLeB, _⟩
  have h_extra := sharedCfgs_kernelExtra_verified idx hIdx
  dsimp [checkRConfKernelExtra] at h_extra
  rcases Bool.and_eq_true_iff.mp h_extra with ⟨h3Len, _⟩
  rcases Bool.and_eq_true_iff.mp h3Len with ⟨h3B, hLenB⟩
  exact computeInitialLiveD_rc_sound Batch.sharedCfgs[idx]! h_ring
    (Nat.le_of_ble_eq_true h3B) (Nat.le_of_ble_eq_true hLeB) (Nat.beq_eq.mp hLenB)

/-!
## Part 7: C-Reducibility Contracted DFS Completeness (`contractCanonIdx_sound`)
-/

def ValidAliasFor (full : Nat → Color) (al : List (Nat × Nat)) : Prop :=
  ∀ w, full (getAlias w al) = full w ∧ getAlias w al ≤ w

theorem getAlias_cons (k mn w : Nat) (al : List (Nat × Nat)) :
    getAlias w ((k, mn) :: al) = if k = w then mn else getAlias w al := by
  unfold getAlias
  dsimp
  cases h : Nat.beq k w with
  | true =>
    rw [if_pos (Nat.beq_eq.mp h)]
  | false =>
    have hNe : k ≠ w := fun hEq => by rw [Nat.beq_eq.mpr hEq] at h; contradiction
    rw [if_neg hNe]

theorem lt_of_blt_eq_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

theorem ge_of_blt_eq_false {a b : Nat} (h : Nat.blt a b = false) : b ≤ a := by
  have : a + 1 > b := lt_of_ble_eq_false h
  omega

theorem withSetAliasMin_valid {α : Type} [Inhabited α] (full : Nat → Color)
    (k mn : Nat) (al : List (Nat × Nat)) (cont : List (Nat × Nat) → α) (Q : α → Prop)
    (hAl : ValidAliasFor full al)
    (hCol : full mn = full k)
    (hCont : ∀ al', ValidAliasFor full al' → Q (cont al')) :
    Q (withSetAliasMin k mn al cont) := by
  unfold withSetAliasMin
  dsimp only []
  cases hBlt : Nat.blt mn (getAlias k al) with
  | false => exact hCont al hAl
  | true =>
    have hLt : mn < getAlias k al := lt_of_blt_eq_true hBlt
    change Q (seqNat k (seqNat mn (cont ((k, mn) :: al))))
    rw [seqNat_eq, seqNat_eq]
    apply hCont ((k, mn) :: al)
    intro w
    rw [getAlias_cons]
    by_cases hEq : k = w
    · subst hEq
      rw [if_pos rfl]
      have hLeK := (hAl k).2
      exact ⟨hCol, by omega⟩
    · rw [if_neg hEq]
      exact hAl w

theorem withRelaxContractEdges_valid {α : Type} [Inhabited α] (full : Nat → Color)
    (edges : List (Nat × Nat)) (al : List (Nat × Nat)) (cont : List (Nat × Nat) → α) (Q : α → Prop)
    (hEdges : ∀ uv ∈ edges, full uv.1 = full uv.2)
    (hAl : ValidAliasFor full al)
    (hCont : ∀ al', ValidAliasFor full al' → Q (cont al')) :
    Q (withRelaxContractEdges edges al cont) := by
  induction edges generalizing al cont with
  | nil => exact hCont al hAl
  | cons uv rest ih =>
    rcases uv with ⟨u, v⟩
    have hUV : full u = full v := hEdges (u, v) List.mem_cons_self
    have hRest : ∀ xy ∈ rest, full xy.1 = full xy.2 :=
      fun xy hxy => hEdges xy (List.mem_cons_of_mem _ hxy)
    unfold withRelaxContractEdges
    change Q (
      let ru := getAlias u al
      let rv := getAlias v al
      let mn := selectBool (Nat.ble ru rv) ru rv
      withSetAliasMin rv mn al (fun al1 =>
      withSetAliasMin ru mn al1 (fun al2 =>
      withSetAliasMin v mn al2 (fun al3 =>
      withSetAliasMin u mn al3 (fun al4 =>
        withRelaxContractEdges rest al4 cont)))))
    let ru := getAlias u al
    let rv := getAlias v al
    let mn := selectBool (Nat.ble ru rv) ru rv
    have hColRU : full ru = full u := (hAl u).1
    have hColRV : full rv = full v := (hAl v).1
    have hColMnU : full mn = full u := by
      dsimp [mn]
      cases Nat.ble ru rv with
      | true => exact hColRU
      | false => exact hColRV.trans hUV.symm
    have hColMnV : full mn = full v := hColMnU.trans hUV
    have hColMnRU : full mn = full ru := hColMnU.trans hColRU.symm
    have hColMnRV : full mn = full rv := hColMnV.trans hColRV.symm
    apply withSetAliasMin_valid full rv mn al _ Q hAl hColMnRV
    intro al1 hAl1
    apply withSetAliasMin_valid full ru mn al1 _ Q hAl1 hColMnRU
    intro al2 hAl2
    apply withSetAliasMin_valid full v mn al2 _ Q hAl2 hColMnV
    intro al3 hAl3
    apply withSetAliasMin_valid full u mn al3 _ Q hAl3 hColMnU
    intro al4 hAl4
    exact ih al4 cont hRest hAl4 hCont

theorem withBuildAlias_valid {α : Type} [Inhabited α] (full : Nat → Color)
    (edges : List (Nat × Nat)) (cont : List (Nat × Nat) → α) (Q : α → Prop)
    (hEdges : ∀ uv ∈ edges, full uv.1 = full uv.2)
    (hCont : ∀ al, ValidAliasFor full al → Q (cont al)) :
    Q (withBuildAlias edges cont) := by
  unfold withBuildAlias
  have hStep : ∀ (n : Nat) (al : List (Nat × Nat)) (cont : List (Nat × Nat) → α),
      ValidAliasFor full al →
      (∀ al', ValidAliasFor full al' → Q (cont al')) →
      Q (@Nat.rec (fun _ => List (Nat × Nat) → (List (Nat × Nat) → α) → α)
        (fun al cont => cont al)
        (fun _ ih al cont =>
          withRelaxContractEdges edges al (fun nextAl => ih nextAl cont))
        n al cont) := by
    intro n
    induction n with
    | zero => intro al cont hAl hC; exact hC al hAl
    | succ n ih =>
      intro al cont hAl hC
      exact withRelaxContractEdges_valid full edges al _ Q hEdges hAl
        (fun nextAl hNext => ih nextAl cont hNext hC)
  apply hStep 4 [] cont
  · intro w
    exact ⟨rfl, Nat.le_refl w⟩
  · exact hCont

theorem checkContractAliases_mem (edges al : List (Nat × Nat))
    (h : checkContractAliases edges al = true) (u v : Nat)
    (hMem : (u, v) ∈ edges) : getAlias u al = getAlias v al := by
  induction edges with
  | nil => contradiction
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    dsimp [checkContractAliases] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨hAB, hTl⟩
    rcases List.mem_cons.mp hMem with hEq | hInTl
    · injection hEq with h1 h2
      subst h1; subst h2
      exact Nat.beq_eq.mp hAB
    · exact ih hTl hInTl

theorem isContractEdge_false_of_alias_ne (edges al : List (Nat × Nat)) (u v : Nat)
    (hAliases : checkContractAliases edges al = true)
    (hNe : Nat.beq (getAlias u al) (getAlias v al) = false) :
    isContractEdge edges u v = false := by
  have hNeEq : getAlias u al ≠ getAlias v al :=
    fun hEq => by rw [Nat.beq_eq.mpr hEq] at hNe; contradiction
  unfold isContractEdge
  apply Bool.or_eq_false_iff.mpr
  refine ⟨?_, ?_⟩
  · cases h1 : edges.contains (u, v) with
    | false => rfl
    | true =>
      exact False.elim (hNeEq (checkContractAliases_mem edges al hAliases u v (List.elem_iff.mp h1)))
  · cases h2 : edges.contains (v, u) with
    | false => rfl
    | true =>
      exact False.elim (hNeEq (checkContractAliases_mem edges al hAliases v u (List.elem_iff.mp h2)).symm)

theorem sameRingColMask_spec (canonValid j u v : Nat) (rings : List RingColMasks)
    (hCV : Nat.testBit canonValid j = true)
    (hU : ValidRingColsAt canonValid rings u)
    (hV : ValidRingColsAt canonValid rings v) :
    Nat.testBit (sameRingColMask u v rings) j = decide (canonRingColor j u = canonRingColor j v) := by
  unfold sameRingColMask
  rcases hU with ⟨uc0, uc1, uc2, uc3, hLookU, hBitsU⟩
  rcases hV with ⟨vc0, vc1, vc2, vc3, hLookV, hBitsV⟩
  rw [hLookU, hLookV]
  rcases hBitsU j with ⟨hu0, hu1, hu2, hu3⟩
  rcases hBitsV j with ⟨hv0, hv1, hv2, hv3⟩
  simp only [testBit_lor, testBit_land, hu0, hu1, hu2, hu3, hv0, hv1, hv2, hv3, hCV, Bool.true_and]
  have hLtU := canonRingColorNat_lt_four j u
  have hLtV := canonRingColorNat_lt_four j v
  unfold canonRingColor
  rcases hNatU : canonRingColorNat j u with _ | _ | _ | _ | nU <;>
    rcases hNatV : canonRingColorNat j v with _ | _ | _ | _ | nV <;>
    (try decide) <;> omega

theorem filterRingContractNbrs_spec (v rv canonValid j : Nat)
    (al : List (Nat × Nat)) (rings : List RingColMasks)
    (us : List Nat) (compat : Nat) (full : Nat → Color) (r : Nat)
    (hCV : Nat.testBit canonValid j = true)
    (hCompat : Nat.testBit compat j = true)
    (hV : v < r)
    (hRV : rv = getAlias v al)
    (hAl : ValidAliasFor full al)
    (hRings : ∀ w < r, ValidRingColsAt canonValid rings w)
    (hFullRing : ∀ w < r, full w = canonRingColor j w)
    (hUs : ∀ u ∈ us, u < r ∧ full u ≠ full v) :
    Nat.testBit (filterRingContractNbrs v rv canonValid al rings us compat) j = true := by
  unfold filterRingContractNbrs
  have hLoop : ∀ (xs : List Nat) (acc : Nat),
      Nat.testBit acc j = true →
      (∀ u ∈ xs, u < r ∧ full u ≠ full v) →
      Nat.testBit
        (@List.rec Nat (fun _ => Nat → Nat)
          (fun acc => acc)
          (fun u _ ih acc =>
            let ru := getAlias u al
            selectBool (Nat.beq ru rv)
              0
              (let sameVU := sameRingColMask v u rings
               let diffVU := Nat.xor canonValid sameVU
               let nextAcc := Nat.land acc diffVU
               seqNat nextAcc (ih nextAcc)))
          xs acc) j = true := by
    intro xs
    induction xs with
    | nil => intro acc hAcc _; exact hAcc
    | cons u rest ih =>
      intro acc hAcc hSub
      rcases hSub u List.mem_cons_self with ⟨hu_r, hNeUV⟩
      have hNotEqAlias : Nat.beq (getAlias u al) rv = false := by
        cases hBeq : Nat.beq (getAlias u al) rv with
        | false => rfl
        | true =>
          have hEqA : getAlias u al = getAlias v al := by
            rw [← hRV]
            exact Nat.beq_eq.mp hBeq
          have hEqCol : full u = full v := by
            rw [← (hAl u).1, hEqA, (hAl v).1]
          exact False.elim (hNeUV hEqCol)
      change Nat.testBit (selectBool (Nat.beq (getAlias u al) rv) 0 _) j = true
      rw [hNotEqAlias]
      dsimp only []
      rw [seqNat_eq]
      apply ih
      · rw [testBit_land, hAcc, Bool.true_and, testBit_xor, hCV,
            sameRingColMask_spec canonValid j v u rings hCV (hRings v hV) (hRings u hu_r)]
        have hNeCanon : canonRingColor j v ≠ canonRingColor j u := by
          rw [← hFullRing v hV, ← hFullRing u hu_r]
          exact Ne.symm hNeUV
        rw [decide_eq_false hNeCanon]
        rfl
      · intro u' hu'
        exact hSub u' (List.mem_cons_of_mem _ hu')
  exact hLoop us compat hCompat hUs

theorem testBit_shiftLeft_one (u w : Nat) :
    Nat.testBit (Nat.shiftLeft 1 u) w = decide (w = u) := by
  rw [testBit_shiftLeft]
  by_cases hEq : w = u
  · subst hEq
    rw [decide_eq_true (Nat.le_refl _), decide_eq_true rfl, Bool.true_and, Nat.sub_self]
    rfl
  · rw [decide_eq_false hEq]
    by_cases hGe : w ≥ u
    · rw [decide_eq_true hGe, Bool.true_and]
      rcases hSub : w - u with _ | k
      · omega
      · rw [Nat.testBit_succ]
        exact Nat.zero_testBit k
    · rw [decide_eq_false hGe, Bool.false_and]

noncomputable def buildContractIntForbidLoop {α : Type} (r rv canonValid : Nat)
    (alias : List (Nat × Nat)) (rings : List RingColMasks)
    (k : Nat → Nat → Nat → Nat → Nat → α) : List Nat → Nat → Nat → Nat → Nat → Nat → α
  | [], intDiff, f0, f1, f2, f3 => k intDiff f0 f1 f2 f3
  | u :: rest, intDiff, f0, f1, f2, f3 =>
    let ru := getAlias u alias
    selectBool (Nat.beq ru rv)
      (buildContractIntForbidLoop r rv canonValid alias rings k rest intDiff f0 f1 f2 f3)
      (selectBool (Nat.ble r u)
        (buildContractIntForbidLoop r rv canonValid alias rings k rest
          (Nat.lor intDiff (Nat.shiftLeft 1 u)) f0 f1 f2 f3)
        (lookupRingCols u rings (fun uc0 uc1 uc2 uc3 =>
          buildContractIntForbidLoop r rv canonValid alias rings k rest intDiff
            (Nat.land f0 (Nat.xor canonValid uc0))
            (Nat.land f1 (Nat.xor canonValid uc1))
            (Nat.land f2 (Nat.xor canonValid uc2))
            (Nat.land f3 (Nat.xor canonValid uc3)))))

theorem buildContractIntForbidAux_eq_loop {α : Type} [Inhabited α] (r rv canonValid : Nat)
    (alias : List (Nat × Nat)) (rings : List RingColMasks) (us : List Nat)
    (initF0 initF1 initF2 initF3 : Nat) (k : Nat → Nat → Nat → Nat → Nat → α) :
    buildContractIntForbidAux r rv canonValid alias rings us initF0 initF1 initF2 initF3 k =
      buildContractIntForbidLoop r rv canonValid alias rings k us 0 initF0 initF1 initF2 initF3 := by
  unfold buildContractIntForbidAux
  have h : ∀ (xs : List Nat) (intDiff f0 f1 f2 f3 : Nat),
      @List.rec Nat (fun _ => Nat → Nat → Nat → Nat → Nat → α)
        (fun intDiff f0 f1 f2 f3 => k intDiff f0 f1 f2 f3)
        (fun u _ ih intDiff f0 f1 f2 f3 =>
          let ru := getAlias u alias
          selectBool (Nat.beq ru rv)
            (ih intDiff f0 f1 f2 f3)
            (selectBool (Nat.ble r u)
              (let nextDiff := Nat.lor intDiff (Nat.shiftLeft 1 u)
               ih nextDiff f0 f1 f2 f3)
              (lookupRingCols u rings (fun uc0 uc1 uc2 uc3 =>
                let nf0 := Nat.land f0 (Nat.xor canonValid uc0)
                let nf1 := Nat.land f1 (Nat.xor canonValid uc1)
                let nf2 := Nat.land f2 (Nat.xor canonValid uc2)
                let nf3 := Nat.land f3 (Nat.xor canonValid uc3)
                ih intDiff nf0 nf1 nf2 nf3))))
        xs intDiff f0 f1 f2 f3 =
      buildContractIntForbidLoop r rv canonValid alias rings k xs intDiff f0 f1 f2 f3 := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons u rest ih =>
      intro intDiff f0 f1 f2 f3
      dsimp [buildContractIntForbidLoop]
      cases Nat.beq (getAlias u alias) rv with
      | true => exact ih _ _ _ _ _
      | false =>
        cases Nat.ble r u with
        | true => exact ih _ _ _ _ _
        | false =>
          change lookupRingCols u rings _ = lookupRingCols u rings _
          congr 1
          funext uc0 uc1 uc2 uc3
          exact ih _ _ _ _ _
  exact h us 0 initF0 initF1 initF2 initF3

theorem buildContractIntForbidLoop_spec {α : Type} (r v rv canonValid j : Nat)
    (alias : List (Nat × Nat)) (rings : List RingColMasks) (xs : List Nat)
    (intDiff f0 f1 f2 f3 : Nat) (full : Nat → Color)
    (k : Nat → Nat → Nat → Nat → Nat → α) (Q : α → Prop)
    (hCV : Nat.testBit canonValid j = true)
    (hRings : ∀ u < r, ValidRingColsAt canonValid rings u)
    (hFullRing : ∀ u < r, full u = canonRingColor j u)
    (hUs : ∀ u ∈ xs, Nat.beq (getAlias u alias) rv = false → full u ≠ full v)
    (hDiff0 : ∀ w, Nat.testBit intDiff w = true → r ≤ w ∧ full w ≠ full v)
    (hF0 : full v = Color.c0 → Nat.testBit f0 j = true)
    (hF1 : full v = Color.c1 → Nat.testBit f1 j = true)
    (hF2 : full v = Color.c2 → Nat.testBit f2 j = true)
    (hF3 : full v = Color.c3 → Nat.testBit f3 j = true)
    (hk : ∀ intDiff' f0' f1' f2' f3',
      (∀ w, Nat.testBit intDiff' w = true → r ≤ w ∧ full w ≠ full v) →
      (full v = Color.c0 → Nat.testBit f0' j = true) →
      (full v = Color.c1 → Nat.testBit f1' j = true) →
      (full v = Color.c2 → Nat.testBit f2' j = true) →
      (full v = Color.c3 → Nat.testBit f3' j = true) →
      Q (k intDiff' f0' f1' f2' f3')) :
    Q (buildContractIntForbidLoop r rv canonValid alias rings k xs intDiff f0 f1 f2 f3) := by
  induction xs generalizing intDiff f0 f1 f2 f3 with
  | nil => exact hk intDiff f0 f1 f2 f3 hDiff0 hF0 hF1 hF2 hF3
  | cons u rest ih =>
    dsimp [buildContractIntForbidLoop]
    have hRest : ∀ u' ∈ rest, Nat.beq (getAlias u' alias) rv = false → full u' ≠ full v :=
      fun u' hu' => hUs u' (List.mem_cons_of_mem _ hu')
    cases hBeq : Nat.beq (getAlias u alias) rv with
    | true =>
      exact ih intDiff f0 f1 f2 f3 hRest hDiff0 hF0 hF1 hF2 hF3
    | false =>
      have hNeUV : full u ≠ full v := hUs u List.mem_cons_self hBeq
      cases hBle : Nat.ble r u with
      | true =>
        have hGeU : r ≤ u := Nat.le_of_ble_eq_true hBle
        apply ih (Nat.lor intDiff (Nat.shiftLeft 1 u)) f0 f1 f2 f3 hRest ?_ hF0 hF1 hF2 hF3
        intro w hw
        rw [testBit_lor, testBit_shiftLeft_one, Bool.or_eq_true] at hw
        rcases hw with hw0 | hEqW
        · exact hDiff0 w hw0
        · rw [of_decide_eq_true hEqW]
          exact ⟨hGeU, hNeUV⟩
      | false =>
        have hLtU : u < r := lt_of_ble_eq_false hBle
        rcases hRings u hLtU with ⟨uc0, uc1, uc2, uc3, hLook, hBits⟩
        change Q (lookupRingCols u rings _)
        rw [hLook]
        rcases hBits j with ⟨hb0, hb1, hb2, hb3⟩
        rw [hCV, Bool.true_and] at hb0 hb1 hb2 hb3
        have hNeCanon : canonRingColor j u ≠ full v := by
          rw [← hFullRing u hLtU]
          exact hNeUV
        apply ih intDiff
          (Nat.land f0 (Nat.xor canonValid uc0))
          (Nat.land f1 (Nat.xor canonValid uc1))
          (Nat.land f2 (Nat.xor canonValid uc2))
          (Nat.land f3 (Nat.xor canonValid uc3))
          hRest hDiff0
        · intro hc0
          have hNot0 : canonRingColorNat j u ≠ 0 := by
            intro h0; apply hNeCanon; rw [hc0]; unfold canonRingColor; rw [h0]; rfl
          rw [testBit_land, hF0 hc0, testBit_xor, hCV, hb0, decide_eq_false hNot0]; rfl
        · intro hc1
          have hNot1 : canonRingColorNat j u ≠ 1 := by
            intro h1; apply hNeCanon; rw [hc1]; unfold canonRingColor; rw [h1]; rfl
          rw [testBit_land, hF1 hc1, testBit_xor, hCV, hb1, decide_eq_false hNot1]; rfl
        · intro hc2
          have hNot2 : canonRingColorNat j u ≠ 2 := by
            intro h2; apply hNeCanon; rw [hc2]; unfold canonRingColor; rw [h2]; rfl
          rw [testBit_land, hF2 hc2, testBit_xor, hCV, hb2, decide_eq_false hNot2]; rfl
        · intro hc3
          have hNot3 : canonRingColorNat j u ≠ 3 := by
            intro h3; apply hNeCanon; rw [hc3]; unfold canonRingColor; rw [h3]; rfl
          rw [testBit_land, hF3 hc3, testBit_xor, hCV, hb3, decide_eq_false hNot3]; rfl

def ExactColorInv (r v : Nat) (c0 c1 c2 c3 : Nat) (full : Nat → Color) : Prop :=
  ∀ w,
    Nat.testBit c0 w = (decide (r ≤ w) && decide (w < v) && decide (full w = Color.c0)) ∧
    Nat.testBit c1 w = (decide (r ≤ w) && decide (w < v) && decide (full w = Color.c1)) ∧
    Nat.testBit c2 w = (decide (r ≤ w) && decide (w < v) && decide (full w = Color.c2)) ∧
    Nat.testBit c3 w = (decide (r ≤ w) && decide (w < v) && decide (full w = Color.c3))

theorem land_checkMask_eq_reqMask (r v rv cMask intDiff : Nat) (col : Color) (full : Nat → Color)
    (hColV : full v = col)
    (hColRV : full rv = full v)
    (hMask : ∀ w, Nat.testBit cMask w = (decide (r ≤ w) && decide (w < v) && decide (full w = col)))
    (hDiff : ∀ w, Nat.testBit intDiff w = true → r ≤ w ∧ full w ≠ full v) :
    let reqMask := selectBool (and (Nat.ble r rv) (Nat.blt rv v)) (Nat.shiftLeft 1 rv) 0
    Nat.land cMask (Nat.lor reqMask intDiff) = reqMask := by
  intro reqMask
  apply Nat.eq_of_testBit_eq
  intro w
  rw [testBit_land, testBit_lor]
  cases hReqW : Nat.testBit reqMask w with
  | true =>
    have hCMaskW : Nat.testBit cMask w = true := by
      dsimp [reqMask] at hReqW
      cases hCond : (Nat.ble r rv && Nat.blt rv v) with
      | false =>
        rw [hCond] at hReqW
        change Nat.testBit 0 w = true at hReqW
        rw [Nat.zero_testBit] at hReqW
        contradiction
      | true =>
        rw [hCond] at hReqW
        change Nat.testBit (Nat.shiftLeft 1 rv) w = true at hReqW
        rw [testBit_shiftLeft_one] at hReqW
        have hEqW : w = rv := of_decide_eq_true hReqW
        subst hEqW
        rcases Bool.and_eq_true_iff.mp hCond with ⟨hBle, hBlt⟩
        have hGe : r ≤ w := Nat.le_of_ble_eq_true hBle
        have hLt : w < v := lt_of_blt_eq_true hBlt
        have hColW : full w = col := hColRV.trans hColV
        rw [hMask w, decide_eq_true hGe, decide_eq_true hLt, decide_eq_true hColW]
        rfl
    rw [hCMaskW, Bool.true_and, Bool.true_or]
  | false =>
    rw [Bool.false_or]
    cases hDiffW : Nat.testBit intDiff w with
    | false => rw [Bool.and_false]
    | true =>
      have hNeW : full w ≠ col := by
        rw [← hColV]
        exact (hDiff w hDiffW).2
      rw [hMask w, decide_eq_false hNeW, Bool.and_false, Bool.false_and]

theorem exactColorInv_step_c0 (r v c0 c1 c2 c3 : Nat) (full : Nat → Color)
    (hGe : r ≤ v) (hCol : full v = Color.c0)
    (hInv : ExactColorInv r v c0 c1 c2 c3 full) :
    ExactColorInv r (v + 1) (Nat.lor c0 (Nat.shiftLeft 1 v)) c1 c2 c3 full := by
  intro w
  rcases hInv w with ⟨h0, h1, h2, h3⟩
  rw [testBit_lor, testBit_shiftLeft_one, h0, h1, h2, h3]
  by_cases hEq : w = v
  · subst hEq
    have hLt1 : w < w + 1 := Nat.lt_succ_self w
    have hNotLt : ¬ (w < w) := Nat.lt_irrefl w
    simp [hGe, hLt1, hNotLt, hCol]
  · have hLtIff : (w < v + 1) ↔ (w < v) := by omega
    simp [hEq, hLtIff]

theorem exactColorInv_step_c1 (r v c0 c1 c2 c3 : Nat) (full : Nat → Color)
    (hGe : r ≤ v) (hCol : full v = Color.c1)
    (hInv : ExactColorInv r v c0 c1 c2 c3 full) :
    ExactColorInv r (v + 1) c0 (Nat.lor c1 (Nat.shiftLeft 1 v)) c2 c3 full := by
  intro w
  rcases hInv w with ⟨h0, h1, h2, h3⟩
  rw [testBit_lor, testBit_shiftLeft_one, h0, h1, h2, h3]
  by_cases hEq : w = v
  · subst hEq
    have hLt1 : w < w + 1 := Nat.lt_succ_self w
    have hNotLt : ¬ (w < w) := Nat.lt_irrefl w
    simp [hGe, hLt1, hNotLt, hCol]
  · have hLtIff : (w < v + 1) ↔ (w < v) := by omega
    simp [hEq, hLtIff]

theorem exactColorInv_step_c2 (r v c0 c1 c2 c3 : Nat) (full : Nat → Color)
    (hGe : r ≤ v) (hCol : full v = Color.c2)
    (hInv : ExactColorInv r v c0 c1 c2 c3 full) :
    ExactColorInv r (v + 1) c0 c1 (Nat.lor c2 (Nat.shiftLeft 1 v)) c3 full := by
  intro w
  rcases hInv w with ⟨h0, h1, h2, h3⟩
  rw [testBit_lor, testBit_shiftLeft_one, h0, h1, h2, h3]
  by_cases hEq : w = v
  · subst hEq
    have hLt1 : w < w + 1 := Nat.lt_succ_self w
    have hNotLt : ¬ (w < w) := Nat.lt_irrefl w
    simp [hGe, hLt1, hNotLt, hCol]
  · have hLtIff : (w < v + 1) ↔ (w < v) := by omega
    simp [hEq, hLtIff]

theorem exactColorInv_step_c3 (r v c0 c1 c2 c3 : Nat) (full : Nat → Color)
    (hGe : r ≤ v) (hCol : full v = Color.c3)
    (hInv : ExactColorInv r v c0 c1 c2 c3 full) :
    ExactColorInv r (v + 1) c0 c1 c2 (Nat.lor c3 (Nat.shiftLeft 1 v)) full := by
  intro w
  rcases hInv w with ⟨h0, h1, h2, h3⟩
  rw [testBit_lor, testBit_shiftLeft_one, h0, h1, h2, h3]
  by_cases hEq : w = v
  · subst hEq
    have hLt1 : w < w + 1 := Nat.lt_succ_self w
    have hNotLt : ¬ (w < w) := Nat.lt_irrefl w
    simp [hGe, hLt1, hNotLt, hCol]
  · have hLtIff : (w < v + 1) ↔ (w < v) := by omega
    simp [hEq, hLtIff]

noncomputable def withContractStepsCLoop {α : Type} [Inhabited α] (r canonValid : Nat)
    (al : List (Nat × Nat)) (rings : List RingColMasks) :
    List (Array Nat) → Nat → Nat → (Nat → List IntVertexStep → α) → α
  | [], _, compat, k => k compat []
  | row :: rest, v, compat, k =>
    let nextV := Nat.succ v
    let rv := getAlias v al
    selectBool (Nat.blt v r)
      (let compat1 :=
        selectBool (Nat.blt rv v)
          (Nat.land compat (sameRingColMask v rv rings))
          compat
       let compat2 := filterRingContractNbrs v rv canonValid al rings row.toList compat1
       seqNat compat2 (withContractStepsCLoop r canonValid al rings rest nextV compat2 k))
      (let bitV := Nat.shiftLeft 1 v
       let reqMask := selectBool (and (Nat.ble r rv) (Nat.blt rv v)) (Nat.shiftLeft 1 rv) 0
       let withInitF {β : Type} (kf : Nat → Nat → Nat → Nat → β) : β :=
         selectBool (Nat.blt rv r)
           (lookupRingCols rv rings kf)
           (kf canonValid canonValid canonValid canonValid)
       withInitF (fun i0 i1 i2 i3 =>
         buildContractIntForbidAux r rv canonValid al rings row.toList i0 i1 i2 i3
           (fun intDiff f0 f1 f2 f3 =>
             let checkMask := Nat.lor reqMask intDiff
             seqNat bitV (seqNat reqMask (seqNat checkMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
               (withContractStepsCLoop r canonValid al rings rest nextV compat (fun finalCompat restSteps =>
                 k finalCompat
                   (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: restSteps))))))))))))

theorem withContractStepsC_eq_loop {α : Type} [Inhabited α] (r canonValid initCompat : Nat)
    (al : List (Nat × Nat)) (rings : List RingColMasks) (rows : List (Array Nat))
    (k : Nat → List IntVertexStep → α) :
    withContractStepsC r canonValid initCompat al rings rows k =
      withContractStepsCLoop r canonValid al rings rows 0 initCompat k := by
  unfold withContractStepsC
  have h : ∀ (xs : List (Array Nat)) (v compat : Nat) (k : Nat → List IntVertexStep → α),
      @List.rec (Array Nat) (fun _ => Nat → Nat → (Nat → List IntVertexStep → α) → α)
        (fun _ compat k => k compat [])
        (fun row _ ih v compat k =>
          let nextV := Nat.succ v
          let rv := getAlias v al
          selectBool (Nat.blt v r)
            (let compat1 :=
              selectBool (Nat.blt rv v)
                (Nat.land compat (sameRingColMask v rv rings))
                compat
             let compat2 := filterRingContractNbrs v rv canonValid al rings row.toList compat1
             seqNat compat2 (ih nextV compat2 k))
            (let bitV := Nat.shiftLeft 1 v
             let reqMask := selectBool (and (Nat.ble r rv) (Nat.blt rv v)) (Nat.shiftLeft 1 rv) 0
             let withInitF {β : Type} (kf : Nat → Nat → Nat → Nat → β) : β :=
               selectBool (Nat.blt rv r)
                 (lookupRingCols rv rings kf)
                 (kf canonValid canonValid canonValid canonValid)
             withInitF (fun i0 i1 i2 i3 =>
               buildContractIntForbidAux r rv canonValid al rings row.toList i0 i1 i2 i3
                 (fun intDiff f0 f1 f2 f3 =>
                   let checkMask := Nat.lor reqMask intDiff
                   seqNat bitV (seqNat reqMask (seqNat checkMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
                     (ih nextV compat (fun finalCompat rest =>
                       k finalCompat
                         (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: rest)))))))))))))
        xs v compat k =
      withContractStepsCLoop r canonValid al rings xs v compat k := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons row rest ih =>
      intro v compat k
      dsimp [withContractStepsCLoop]
      cases Nat.blt v r with
      | true =>
        dsimp only []
        rw [ih]
      | false =>
        dsimp only []
        have hBody : ∀ i0 i1 i2 i3 : Nat,
            buildContractIntForbidAux r (getAlias v al) canonValid al rings row.toList i0 i1 i2 i3
              (fun intDiff f0 f1 f2 f3 =>
                let reqMask := selectBool (and (Nat.ble r (getAlias v al)) (Nat.blt (getAlias v al) v))
                  (Nat.shiftLeft 1 (getAlias v al)) 0
                let checkMask := Nat.lor reqMask intDiff
                seqNat (Nat.shiftLeft 1 v) (seqNat reqMask (seqNat checkMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
                  (@List.rec (Array Nat) (fun _ => Nat → Nat → (Nat → List IntVertexStep → α) → α)
                    (fun _ compat k => k compat [])
                    (fun row _ ih v compat k =>
                      let nextV := Nat.succ v
                      let rv := getAlias v al
                      selectBool (Nat.blt v r)
                        (let compat1 :=
                          selectBool (Nat.blt rv v)
                            (Nat.land compat (sameRingColMask v rv rings))
                            compat
                         let compat2 := filterRingContractNbrs v rv canonValid al rings row.toList compat1
                         seqNat compat2 (ih nextV compat2 k))
                        (let bitV := Nat.shiftLeft 1 v
                         let reqMask := selectBool (and (Nat.ble r rv) (Nat.blt rv v)) (Nat.shiftLeft 1 rv) 0
                         let withInitF {β : Type} (kf : Nat → Nat → Nat → Nat → β) : β :=
                           selectBool (Nat.blt rv r)
                             (lookupRingCols rv rings kf)
                             (kf canonValid canonValid canonValid canonValid)
                         withInitF (fun i0 i1 i2 i3 =>
                           buildContractIntForbidAux r rv canonValid al rings row.toList i0 i1 i2 i3
                             (fun intDiff f0 f1 f2 f3 =>
                               let checkMask := Nat.lor reqMask intDiff
                               seqNat bitV (seqNat reqMask (seqNat checkMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
                                 (ih nextV compat (fun finalCompat rest =>
                                   k finalCompat
                                     (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: rest)))))))))))))
                    rest (v + 1) compat (fun finalCompat restSteps =>
                      k finalCompat
                        (IntVertexStep.mk (Nat.shiftLeft 1 v) reqMask checkMask f0 f1 f2 f3 :: restSteps)))))))))) =
            buildContractIntForbidAux r (getAlias v al) canonValid al rings row.toList i0 i1 i2 i3
              (fun intDiff f0 f1 f2 f3 =>
                let reqMask := selectBool (and (Nat.ble r (getAlias v al)) (Nat.blt (getAlias v al) v))
                  (Nat.shiftLeft 1 (getAlias v al)) 0
                let checkMask := Nat.lor reqMask intDiff
                seqNat (Nat.shiftLeft 1 v) (seqNat reqMask (seqNat checkMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
                  (withContractStepsCLoop r canonValid al rings rest (v + 1) compat (fun finalCompat restSteps =>
                    k finalCompat
                      (IntVertexStep.mk (Nat.shiftLeft 1 v) reqMask checkMask f0 f1 f2 f3 :: restSteps)))))))))) := by
          intro i0 i1 i2 i3
          congr 1
          funext intDiff f0 f1 f2 f3
          dsimp only []
          rw [seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq]
          rw [seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq]
          exact ih (v + 1) compat _
        cases Nat.blt (getAlias v al) r with
        | false => exact hBody _ _ _ _
        | true =>
          change lookupRingCols (getAlias v al) rings _ = lookupRingCols (getAlias v al) rings _
          congr 1
          funext i0 i1 i2 i3
          exact hBody i0 i1 i2 i3
  exact h rows 0 initCompat k

theorem withContractStepsCLoop_spec {α : Type} [Inhabited α] (r canonValid j : Nat)
    (al : List (Nat × Nat)) (rings : List RingColMasks) (xs : List (Array Nat))
    (v compat c0 c1 c2 c3 : Nat) (full : Nat → Color)
    (k : Nat → List IntVertexStep → α) (Q : α → Prop)
    (hCV : Nat.testBit canonValid j = true)
    (hCompat : Nat.testBit compat j = true)
    (hAl : ValidAliasFor full al)
    (hRings : ∀ u < r, ValidRingColsAt canonValid rings u)
    (hFullRing : ∀ u < r, full u = canonRingColor j u)
    (hInv : ExactColorInv r v c0 c1 c2 c3 full)
    (hRowsV : ∀ w < xs.length, ∀ u ∈ (listGetD xs w #[]).toList,
      u < v + w ∧
      (v + w < r → full u ≠ full (v + w)) ∧
      (Nat.beq (getAlias u al) (getAlias (v + w) al) = false → full u ≠ full (v + w)))
    (hk : ∀ finalCompat steps,
      Nat.testBit finalCompat j = true →
      DfsWitness steps c0 c1 c2 c3 j →
      Q (k finalCompat steps)) :
    Q (withContractStepsCLoop r canonValid al rings xs v compat k) := by
  induction xs generalizing v compat c0 c1 c2 c3 k with
  | nil => exact hk compat [] hCompat (DfsWitness.nil c0 c1 c2 c3 j)
  | cons row rest ih =>
    dsimp [withContractStepsCLoop]
    have hRestV : ∀ w < rest.length, ∀ u ∈ (listGetD rest w #[]).toList,
        u < (v + 1) + w ∧
        ((v + 1) + w < r → full u ≠ full ((v + 1) + w)) ∧
        (Nat.beq (getAlias u al) (getAlias ((v + 1) + w) al) = false → full u ≠ full ((v + 1) + w)) := by
      intro w hw u hu
      have hAdd : (v + 1) + w = v + (w + 1) := by omega
      rw [hAdd]
      exact hRowsV (w + 1) (by dsimp; omega) u hu
    have hRow0 : ∀ u ∈ row.toList,
        u < v ∧
        (v < r → full u ≠ full v) ∧
        (Nat.beq (getAlias u al) (getAlias v al) = false → full u ≠ full v) := by
      intro u hu
      have h0 := hRowsV 0 (by dsimp; omega) u hu
      rwa [Nat.add_zero] at h0
    let rv := getAlias v al
    cases hBltVR : Nat.blt v r with
    | true =>
      dsimp only []
      rw [seqNat_eq]
      have hLtVR : v < r := lt_of_blt_eq_true hBltVR
      let compat1 := selectBool (Nat.blt rv v) (Nat.land compat (sameRingColMask v rv rings)) compat
      let compat2 := filterRingContractNbrs v rv canonValid al rings row.toList compat1
      have hCompat1 : Nat.testBit compat1 j = true := by
        dsimp [compat1]
        cases hBltRV : Nat.blt rv v with
        | false => exact hCompat
        | true =>
          have hLtRV : rv < r := Nat.lt_trans (lt_of_blt_eq_true hBltRV) hLtVR
          have hColEq : canonRingColor j v = canonRingColor j rv := by
            rw [← hFullRing v hLtVR, ← hFullRing rv hLtRV, (hAl v).1]
          change Nat.testBit (Nat.land compat (sameRingColMask v rv rings)) j = true
          rw [testBit_land, hCompat, Bool.true_and,
              sameRingColMask_spec canonValid j v rv rings hCV (hRings v hLtVR) (hRings rv hLtRV),
              decide_eq_true hColEq]
      have hCompat2 : Nat.testBit compat2 j = true := by
        apply filterRingContractNbrs_spec v rv canonValid j al rings row.toList compat1 full r
          hCV hCompat1 hLtVR rfl hAl hRings hFullRing
        intro u hu
        rcases hRow0 u hu with ⟨hu_lt, hNeRing, _⟩
        exact ⟨Nat.lt_trans hu_lt hLtVR, hNeRing hLtVR⟩
      have hInvNext : ExactColorInv r (v + 1) c0 c1 c2 c3 full := by
        intro w
        rcases hInv w with ⟨h0, h1, h2, h3⟩
        by_cases hGeW : r ≤ w
        · have hF1 : ¬ (w < v) := by omega
          have hF2 : ¬ (w < v + 1) := by omega
          simp [h0, h1, h2, h3, hGeW, hF1, hF2]
        · simp [h0, h1, h2, h3, hGeW]
      exact ih (v + 1) compat2 c0 c1 c2 c3 k hCompat2 hInvNext hRestV hk
    | false =>
      dsimp only []
      have hGeVR : r ≤ v := ge_of_blt_eq_false hBltVR
      let bitV := Nat.shiftLeft 1 v
      let reqMask := selectBool (and (Nat.ble r rv) (Nat.blt rv v)) (Nat.shiftLeft 1 rv) 0
      have hStepForbid : ∀ i0 i1 i2 i3 : Nat,
          (full v = Color.c0 → Nat.testBit i0 j = true) →
          (full v = Color.c1 → Nat.testBit i1 j = true) →
          (full v = Color.c2 → Nat.testBit i2 j = true) →
          (full v = Color.c3 → Nat.testBit i3 j = true) →
          Q (buildContractIntForbidAux r rv canonValid al rings row.toList i0 i1 i2 i3
            (fun intDiff f0 f1 f2 f3 =>
              let checkMask := Nat.lor reqMask intDiff
              seqNat bitV (seqNat reqMask (seqNat checkMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
                (withContractStepsCLoop r canonValid al rings rest (v + 1) compat (fun finalCompat restSteps =>
                  k finalCompat
                    (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: restSteps))))))))))) := by
        intro i0 i1 i2 i3 hi0 hi1 hi2 hi3
        rw [buildContractIntForbidAux_eq_loop]
        apply buildContractIntForbidLoop_spec r v rv canonValid j al rings row.toList
          0 i0 i1 i2 i3 full _ Q hCV hRings hFullRing
          (fun u hu => (hRow0 u hu).2.2)
          (fun w hw => by rw [Nat.zero_testBit] at hw; contradiction)
          hi0 hi1 hi2 hi3
        intro intDiff f0 f1 f2 f3 hDiff hf0 hf1 hf2 hf3
        dsimp only []
        rw [seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq, seqNat_eq]
        cases hColV : full v with
        | c0 =>
          apply ih (v + 1) compat (Nat.lor c0 bitV) c1 c2 c3 _ hCompat
            (exactColorInv_step_c0 r v c0 c1 c2 c3 full hGeVR hColV hInv) hRestV
          intro finalCompat restSteps hFC hWitRest
          apply hk finalCompat _ hFC
          exact DfsWitness.br0
            (land_checkMask_eq_reqMask r v rv c0 intDiff Color.c0 full hColV (hAl v).1
              (fun w => (hInv w).1) hDiff)
            (hf0 hColV) hWitRest
        | c1 =>
          apply ih (v + 1) compat c0 (Nat.lor c1 bitV) c2 c3 _ hCompat
            (exactColorInv_step_c1 r v c0 c1 c2 c3 full hGeVR hColV hInv) hRestV
          intro finalCompat restSteps hFC hWitRest
          apply hk finalCompat _ hFC
          exact DfsWitness.br1
            (land_checkMask_eq_reqMask r v rv c1 intDiff Color.c1 full hColV (hAl v).1
              (fun w => (hInv w).2.1) hDiff)
            (hf1 hColV) hWitRest
        | c2 =>
          apply ih (v + 1) compat c0 c1 (Nat.lor c2 bitV) c3 _ hCompat
            (exactColorInv_step_c2 r v c0 c1 c2 c3 full hGeVR hColV hInv) hRestV
          intro finalCompat restSteps hFC hWitRest
          apply hk finalCompat _ hFC
          exact DfsWitness.br2
            (land_checkMask_eq_reqMask r v rv c2 intDiff Color.c2 full hColV (hAl v).1
              (fun w => (hInv w).2.2.1) hDiff)
            (hf2 hColV) hWitRest
        | c3 =>
          apply ih (v + 1) compat c0 c1 c2 (Nat.lor c3 bitV) _ hCompat
            (exactColorInv_step_c3 r v c0 c1 c2 c3 full hGeVR hColV hInv) hRestV
          intro finalCompat restSteps hFC hWitRest
          apply hk finalCompat _ hFC
          exact DfsWitness.br3
            (land_checkMask_eq_reqMask r v rv c3 intDiff Color.c3 full hColV (hAl v).1
              (fun w => (hInv w).2.2.2) hDiff)
            (hf3 hColV) hWitRest
      cases hBltRVR : Nat.blt rv r with
      | false =>
        exact hStepForbid canonValid canonValid canonValid canonValid
          (fun _ => hCV) (fun _ => hCV) (fun _ => hCV) (fun _ => hCV)
      | true =>
        have hLtRVR : rv < r := lt_of_blt_eq_true hBltRVR
        rcases hRings rv hLtRVR with ⟨rc0, rc1, rc2, rc3, hLookRV, hBitsRV⟩
        change Q (lookupRingCols rv rings _)
        rw [hLookRV]
        rcases hBitsRV j with ⟨hr0, hr1, hr2, hr3⟩
        rw [hCV, Bool.true_and] at hr0 hr1 hr2 hr3
        have hColEqRV : canonRingColor j rv = full v := by
          rw [← hFullRing rv hLtRVR, (hAl v).1]
        apply hStepForbid rc0 rc1 rc2 rc3
        · intro hc0
          have hNat : canonRingColorNat j rv = 0 := by
            rw [← toNat_canonRingColor j rv, hColEqRV, hc0]; rfl
          rw [hr0, decide_eq_true hNat]
        · intro hc1
          have hNat : canonRingColorNat j rv = 1 := by
            rw [← toNat_canonRingColor j rv, hColEqRV, hc1]; rfl
          rw [hr1, decide_eq_true hNat]
        · intro hc2
          have hNat : canonRingColorNat j rv = 2 := by
            rw [← toNat_canonRingColor j rv, hColEqRV, hc2]; rfl
          rw [hr2, decide_eq_true hNat]
        · intro hc3
          have hNat : canonRingColorNat j rv = 3 := by
            rw [← toNat_canonRingColor j rv, hColEqRV, hc3]; rfl
          rw [hr3, decide_eq_true hNat]

theorem computeContractCanon_rc_sound (rc : FastReducer.RConf)
    (h_ring : IsRingCycle (configOfRConf rc))
    (h_wf : IsWellFormedEarlier (configOfRConf rc) rc.earlier)
    (h3 : 3 ≤ rc.r) (hLe : rc.r ≤ rc.n) (hLen : rc.earlier.toList.length = rc.n)
    (hAliases : checkContractAliases rc.contractEdges.toList
      (withBuildAlias rc.contractEdges.toList StrictBox.mk).val = true)
    (b : BoundaryColoring (configOfRConf rc))
    (hb : IsValidBoundaryColoring (configOfRConf rc) b)
    (hExtC : extendsToContracted (configOfRConf rc) b) :
    let c := configOfRConf rc
    let contractCanon := computeContractCanon rc.r (Nat.sub rc.r 1) rc
    Nat.testBit contractCanon (canonIdx c.ringSize b) = true ∨
    Nat.testBit contractCanon (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)) = true := by
  intro c contractCanon
  have hSubEq : rc.r - 1 - 1 = c.ringSize - 2 := by
    dsimp [c, configOfRConf]; omega
  rcases exists_canon_slice_rep c h_ring b hb with ⟨k, j, hj_or, hj_lt, hTopNe, hCanon12, hAff⟩
  rcases hExtC with ⟨full0, hRing0, hContr0, hAdj0⟩
  let dCol := xorColorCol Color.c1 (permColor k (b 0))
  let full : Nat → Color := fun u => affineColor k dCol (full0 u)
  have hFullRing : ∀ u < rc.r, full u = canonRingColor j u := by
    intro u hu
    dsimp [full]
    rw [hRing0 u hu, hAff u hu]
  have hEdgesCol : ∀ uv ∈ rc.contractEdges.toList, full uv.1 = full uv.2 := by
    intro uv huv
    dsimp [full]
    rw [(hContr0 uv huv).2.2]
  have hAl : ValidAliasFor full (withBuildAlias rc.contractEdges.toList StrictBox.mk).val :=
    withBuildAlias_valid full rc.contractEdges.toList StrictBox.mk
      (fun box => ValidAliasFor full box.val) hEdgesCol (fun _ h => h)
  let al := (withBuildAlias rc.contractEdges.toList StrictBox.mk).val
  have hTot : c.totalNodes = rc.n := by
    dsimp [c, configOfRConf, Configuration.totalNodes]; omega
  have hRows : ∀ w < rc.earlier.toList.length, ∀ u ∈ (listGetD rc.earlier.toList w #[]).toList,
      u < w ∧
      (w < rc.r → full u ≠ full w) ∧
      (Nat.beq (getAlias u al) (getAlias w al) = false → full u ≠ full w) := by
    intro w hw u hu
    rw [listGetD_earlier_eq] at hu
    have hw_tot : w < c.totalNodes := by omega
    rcases h_wf w hw_tot u hu with ⟨hu_lt, hAdjWU⟩
    have hu_tot : u < c.totalNodes := by omega
    have hAdjUW : c.adj u w = true := by
      dsimp [c, configOfRConf, symAdj]
      rw [if_pos hu_lt]
      exact List.elem_iff.mpr hu
    refine ⟨hu_lt, ?_, ?_⟩
    · intro hw_r
      have hu_r : u < rc.r := Nat.lt_trans hu_lt hw_r
      rw [hFullRing u hu_r, hFullRing w hw_r, hAff u hu_r, hAff w hw_r]
      intro hEq
      exact hb u w hu_r hw_r hAdjUW (affineColor_inj k dCol _ _ hEq)
    · intro hNeAl
      have hNotCE : isContractEdge c.contractEdges u w = false :=
        isContractEdge_false_of_alias_ne rc.contractEdges.toList al u w hAliases hNeAl
      have hNe0 : full0 u ≠ full0 w := hAdj0 u w hu_tot hw_tot hAdjUW hNotCE
      intro hEq
      exact hNe0 (affineColor_inj k dCol _ _ hEq)
  dsimp [contractCanon]
  unfold computeContractCanon
  refine withRingColMasks_spec (rc.r - 1) Prod.mk
    (fun p : Nat × List RingColMasks =>
      let cc := @Prod.rec _ _ (fun _ => _)
        (fun canonValid rings => computeContractCanonWithRings rc.r canonValid rings rc) p
      Nat.testBit cc (canonIdx c.ringSize b) = true ∨
      Nat.testBit cc (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)) = true)
    (by omega) ?_
  intro canonValid rings hCV_spec hRings
  dsimp only []
  have hCV_j : Nat.testBit canonValid j = true := by
    rw [hCV_spec j, hSubEq, decide_eq_true hj_lt, decide_eq_true hTopNe, hCanon12]
    rfl
  have hRingsLt : ∀ u < rc.r, ValidRingColsAt canonValid rings u :=
    fun u hu => hRings u (by omega)
  have hInv0 : ExactColorInv rc.r 0 0 0 0 0 full := by
    intro w
    have hNotLt : ¬ (w < 0) := Nat.not_lt_zero w
    simp [hNotLt]
  dsimp [computeContractCanonWithRings]
  rw [withContractStepsC_eq_loop]
  refine withContractStepsCLoop_spec rc.r canonValid j al rings rc.earlier.toList
    0 canonValid 0 0 0 0 full Prod.mk
    (fun p : Nat × List IntVertexStep =>
      let cc := @Prod.rec _ _ (fun _ => _)
        (fun ringCompat intStepsC =>
          seqNat ringCompat
            (let unextContract := dfsInterior intStepsC 0 0 0 0 ringCompat ringCompat
             let contractCanon := Nat.xor ringCompat unextContract
             seqNat contractCanon contractCanon)) p
      Nat.testBit cc (canonIdx c.ringSize b) = true ∨
      Nat.testBit cc (swap12Idx (c.ringSize - 2) (canonIdx c.ringSize b)) = true)
    hCV_j hCV_j hAl hRingsLt hFullRing hInv0
    (fun w hw u hu => by rw [Nat.zero_add]; exact hRows w hw u hu) ?_
  intro ringCompat intStepsC hRC_j hWit
  dsimp only []
  rw [seqNat_eq, seqNat_eq]
  have hDfsFalse : Nat.testBit (dfsInterior intStepsC 0 0 0 0 ringCompat ringCompat) j = false :=
    dfsInterior_complete intStepsC 0 0 0 0 ringCompat ringCompat j (fun _ h => h) hRC_j hWit
  have hBitTrue : Nat.testBit (Nat.xor ringCompat (dfsInterior intStepsC 0 0 0 0 ringCompat ringCompat)) j = true := by
    rw [testBit_xor, hRC_j, hDfsFalse]
    rfl
  rcases hj_or with rfl | rfl
  · exact Or.inl hBitTrue
  · exact Or.inr hBitTrue

theorem contractCanonIdx_sound (idx : Nat) (hIdx : idx < 633) :
    ∀ (b : BoundaryColoring (theUnavoidableSet[idx]!)),
      IsValidBoundaryColoring (theUnavoidableSet[idx]!) b →
      extendsToContracted (theUnavoidableSet[idx]!) b →
      Nat.testBit (contractCanonIdx idx) (canonIdx (theUnavoidableSet[idx]!).ringSize b) = true ∨
      Nat.testBit (contractCanonIdx idx)
        (swap12Idx ((theUnavoidableSet[idx]!).ringSize - 2) (canonIdx (theUnavoidableSet[idx]!).ringSize b)) = true ∨
      Eliminated (theUnavoidableSet[idx]!) b := by
  unfold contractCanonIdx
  change
    ∀ (b : BoundaryColoring (theUnavoidableSet[idx]!)),
      IsValidBoundaryColoring (theUnavoidableSet[idx]!) b →
      extendsToContracted (theUnavoidableSet[idx]!) b →
      let c := getRConf idx
      Nat.testBit (computeContractCanon c.r (Nat.sub c.r 1) c)
        (canonIdx (theUnavoidableSet[idx]!).ringSize b) = true ∨
      Nat.testBit (computeContractCanon c.r (Nat.sub c.r 1) c)
        (swap12Idx ((theUnavoidableSet[idx]!).ringSize - 2)
          (canonIdx (theUnavoidableSet[idx]!).ringSize b)) = true ∨
      Eliminated (theUnavoidableSet[idx]!) b
  rw [getRConf_eq_sharedCfgs idx hIdx, theUnavoidableSet_getElem! idx hIdx]
  intro b hb hExtC
  have h_ring : IsRingCycle (configOfRConf Batch.sharedCfgs[idx]!) := by
    rw [← theUnavoidableSet_getElem! idx hIdx]
    exact unavoidable_is_ring_cycle idx hIdx
  have h_wf : IsWellFormedEarlier (configOfRConf Batch.sharedCfgs[idx]!) Batch.sharedCfgs[idx]!.earlier := by
    rw [← theUnavoidableSet_getElem! idx hIdx]
    exact unavoidable_is_well_formed_earlier idx hIdx
  have h_struct := sharedCfgs_structural_verified idx hIdx
  dsimp [checkRConfStructural] at h_struct
  rcases Bool.and_eq_true_iff.mp h_struct with ⟨h123, _⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, _⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨hLeB, _⟩
  have h_extra := sharedCfgs_kernelExtra_verified idx hIdx
  dsimp [checkRConfKernelExtra] at h_extra
  rcases Bool.and_eq_true_iff.mp h_extra with ⟨h3Len, hAliases⟩
  rcases Bool.and_eq_true_iff.mp h3Len with ⟨h3B, hLenB⟩
  rcases computeContractCanon_rc_sound Batch.sharedCfgs[idx]! h_ring h_wf
      (Nat.le_of_ble_eq_true h3B) (Nat.le_of_ble_eq_true hLeB) (Nat.beq_eq.mp hLenB)
      hAliases b hb hExtC with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)

end KernelSoundness
end Math
