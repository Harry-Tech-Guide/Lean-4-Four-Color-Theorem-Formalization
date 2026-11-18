module

public import FourColorTheorem.Math.Soundness.StructuralVerification

@[expose] public section

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false

/-!
# Structural Verification of Ring Cycle Adjacency and Well-Formed Earlier Tables

This module proves two structural invariants across all 633 RSST configurations:
1. `IsRingCycle c`: Every consecutive pair of ring vertices `(i, (i + 1) % c.ringSize)`
   is adjacent in `c` (`c.adj i ((i + 1) % c.ringSize) = true`), closing Audit Gap G3.
2. `IsWellFormedEarlier c earlier`: Every entry `u ∈ earlier[v]` satisfies `u < v` and
   `c.adj v u = true`, enabling `extend_complete` and `extend_iff_extendsToInterior`
   across all 633 configurations, closing Audit Gap G1.
-/

/-- Every consecutive pair of ring vertices `(i, (i + 1) % c.ringSize)` is adjacent in `c`. -/
def IsRingCycle (c : Configuration) : Prop :=
  c.ringSize ≥ 2 ∧ ∀ i < c.ringSize, c.adj i ((i + 1) % c.ringSize) = true

/-- Proof-free structural list lookup (avoids dependent `dite` proof construction in `Array.getD` during kernel `whnf`). -/
def listGetD {α : Type} : List α → Nat → α → α
  | [], _, d => d
  | x :: _, 0, _ => x
  | _ :: xs, n + 1, d => listGetD xs n d

theorem listGetD_eq_getD_list {α : Type} (L : List α) (i : Nat) (d : α) :
    listGetD L i d = (⟨L⟩ : Array α).getD i d := by
  induction L generalizing i with
  | nil =>
    cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ n =>
      dsimp [listGetD]
      rw [ih n]
      unfold Array.getD
      by_cases h : n < xs.length
      · have h_sz1 : n < (⟨xs⟩ : Array α).size := h
        have h_sz2 : n + 1 < (⟨x :: xs⟩ : Array α).size := Nat.succ_lt_succ h
        rw [dif_pos h_sz1, dif_pos h_sz2]
        rfl
      · have h_sz1 : ¬ (n < (⟨xs⟩ : Array α).size) := h
        have h_sz2 : ¬ (n + 1 < (⟨x :: xs⟩ : Array α).size) :=
          fun hlt => h (Nat.lt_of_succ_lt_succ hlt)
        rw [dif_neg h_sz1, dif_neg h_sz2]

theorem listGetD_eq_array_getD {α : Type} (a : Array α) (i : Nat) (d : α) :
    listGetD a.toList i d = a.getD i d := by
  cases a with
  | mk L => exact listGetD_eq_getD_list L i d

/-- Proof-free structural list check that for every index `v`, every `u ∈ L[v]` satisfies `u < v`. -/
def checkEarlierListLt : List (Array Nat) → Nat → Bool
  | [], _ => true
  | arr :: rest, v =>
    arr.toList.all (fun u => Nat.blt u v) && checkEarlierListLt rest (v + 1)

theorem checkEarlierListLt_sound (L : List (Array Nat)) (base k : Nat)
    (h : checkEarlierListLt L base = true)
    (u : Nat) (hu : u ∈ (listGetD L k #[]).toList) :
    u < base + k := by
  induction L generalizing base k with
  | nil =>
    dsimp [listGetD] at hu
    contradiction
  | cons arr rest ih =>
    dsimp [checkEarlierListLt] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h_head, h_tail⟩
    cases k with
    | zero =>
      dsimp [listGetD] at hu
      rw [Nat.add_zero]
      exact Nat.blt_eq.mp (List.all_eq_true.mp h_head u hu)
    | succ k' =>
      dsimp [listGetD] at hu
      have h_ih := ih (base + 1) k' h_tail hu
      omega

theorem wellFormedEarlier_of_checkRConf (rc : RConf)
    (h_le : rc.r ≤ rc.n) (h : checkEarlierListLt rc.earlier.toList 0 = true) :
    IsWellFormedEarlier (configOfRConf rc) rc.earlier := by
  intro v _hv u hu
  rw [← listGetD_eq_array_getD rc.earlier v #[]] at hu
  have hu_lt : u < v := by
    have h0 := checkEarlierListLt_sound rc.earlier.toList 0 v h u hu
    omega
  refine ⟨hu_lt, ?_⟩
  dsimp [configOfRConf, symAdj]
  have h_not_vu : ¬ (v < u) := by omega
  rw [if_neg h_not_vu, if_pos hu_lt]
  rw [listGetD_eq_array_getD rc.earlier v #[]] at hu
  exact List.contains_iff_mem.mpr hu

/-- Proof-free ring cycle walk: given `r ≥ 2` and `rc.earlier.toList = e_0 :: rest`,
    checks `0 ∈ e_1, 1 ∈ e_2, ..., (r - 2) ∈ e_{r - 1}` and `0 ∈ e_{r - 1}`. -/
def checkRingListAux : List (Array Nat) → Nat → Nat → Bool
  | _, _, 0 => false
  | [], _, _ => false
  | e_next :: _, i, 1 =>
    e_next.toList.contains i && e_next.toList.contains 0
  | e_next :: rest, i, rem + 2 =>
    e_next.toList.contains i && checkRingListAux rest (i + 1) (rem + 1)

theorem checkRingListAux_sound (rem : Nat) (L : List (Array Nat)) (base : Nat)
    (h : checkRingListAux L base rem = true) :
    rem ≥ 1 ∧
    (∀ k < rem, (listGetD L k #[]).toList.contains (base + k) = true) ∧
    (listGetD L (rem - 1) #[]).toList.contains 0 = true := by
  induction rem generalizing L base with
  | zero =>
    unfold checkRingListAux at h
    contradiction
  | succ m ih =>
    cases m with
    | zero =>
      cases L with
      | nil =>
        dsimp [checkRingListAux] at h
        contradiction
      | cons e_next rest =>
        dsimp [checkRingListAux] at h
        rcases Bool.and_eq_true_iff.mp h with ⟨h_i, h_0⟩
        refine ⟨Nat.le_refl 1, ?_, ?_⟩
        · intro k hk
          have hk0 : k = 0 := by omega
          subst hk0
          dsimp [listGetD]
          exact h_i
        · dsimp [listGetD]
          exact h_0
    | succ m' =>
      cases L with
      | nil =>
        dsimp [checkRingListAux] at h
        contradiction
      | cons e_next rest =>
        dsimp [checkRingListAux] at h
        rcases Bool.and_eq_true_iff.mp h with ⟨h_i, h_rest⟩
        rcases ih rest (base + 1) h_rest with ⟨_, h_all_rest, h_0_rest⟩
        refine ⟨by omega, ?_, ?_⟩
        · intro k hk
          cases k with
          | zero =>
            dsimp [listGetD]
            exact h_i
          | succ k' =>
            dsimp [listGetD]
            have hk' : k' < m' + 1 := by omega
            have h_step := h_all_rest k' hk'
            have h_add : (base + 1) + k' = base + (k' + 1) := by omega
            rwa [h_add] at h_step
        · dsimp [listGetD]
          exact h_0_rest

def checkRConfRingCycle (rc : RConf) : Bool :=
  match rc.r, rc.earlier.toList with
  | r' + 2, _ :: rest => checkRingListAux rest 0 (r' + 1)
  | _, _ => false

theorem ringCycle_of_checkRConf (rc : RConf) (h : checkRConfRingCycle rc = true) :
    IsRingCycle (configOfRConf rc) := by
  dsimp [checkRConfRingCycle] at h
  cases hr : rc.r with
  | zero =>
    rw [hr] at h; contradiction
  | succ r1 =>
    cases r1 with
    | zero =>
      rw [hr] at h; contradiction
    | succ r' =>
      rw [hr] at h
      cases hL : rc.earlier.toList with
      | nil =>
        rw [hL] at h; contradiction
      | cons e0 rest =>
        rw [hL] at h
        dsimp at h
        rcases checkRingListAux_sound (r' + 1) rest 0 h with ⟨_, h_consec, h_wrap⟩
        refine ⟨by dsimp [configOfRConf]; omega, ?_⟩
        intro i hi
        dsimp [configOfRConf] at hi ⊢
        rw [hr] at hi ⊢
        by_cases h_last : i < r' + 1
        · have h_nxt : (i + 1) % (r' + 2) = i + 1 :=
            Nat.mod_eq_of_lt (by omega)
          rw [h_nxt]
          dsimp [symAdj]
          have h_lt : i < i + 1 := by omega
          rw [if_pos h_lt, ← listGetD_eq_array_getD rc.earlier (i + 1) #[]]
          rw [hL]
          dsimp [listGetD]
          have h_step := h_consec i h_last
          rwa [Nat.zero_add] at h_step
        · have hi_eq : i = r' + 1 := by omega
          subst hi_eq
          have h_nxt : (r' + 1 + 1) % (r' + 2) = 0 := Nat.mod_self (r' + 2)
          rw [h_nxt]
          dsimp [symAdj]
          rw [← listGetD_eq_array_getD rc.earlier (r' + 1) #[]]
          rw [hL]
          dsimp [listGetD]
          exact h_wrap

/-- Combined structural check on a parsed `RConf`. -/
def checkRConfStructural (rc : RConf) : Bool :=
  Nat.ble rc.r rc.n && checkRConfRingCycle rc && checkEarlierListLt rc.earlier.toList 0 && Nat.ble rc.r 15

/-- Single-pass structural check across a list of `RConf`s. -/
def checkRConfListStructural : List RConf → Bool
  | [] => true
  | rc :: rest => checkRConfStructural rc && checkRConfListStructural rest

theorem checkRConfListStructural_sound (L : List RConf) (k : Nat)
    (hk : k < L.length) (h : checkRConfListStructural L = true) :
    checkRConfStructural (L[k]'hk) = true := by
  induction L generalizing k with
  | nil => contradiction
  | cons hd tl ih =>
    dsimp [checkRConfListStructural] at h
    rcases Bool.and_eq_true_iff.mp h with ⟨h_hd, h_tl⟩
    cases k with
    | zero => exact h_hd
    | succ k' =>
      have hk' : k' < tl.length := by
        dsimp at hk
        omega
      exact ih k' hk' h_tl

set_option maxRecDepth 100000 in
/-- In-kernel verification across all 633 RSST configurations. -/
theorem parsedRConfList_structural_verified :
    checkRConfListStructural parsedRConfList = true := by
  rfl

theorem sharedCfgs_structural_verified (idx : Nat) (h_lt : idx < 633) :
    checkRConfStructural sharedCfgs[idx]! = true := by
  have h_len : idx < parsedRConfList.length := by
    rw [parsedRConfList_length]; exact h_lt
  have h_arr : sharedCfgs[idx]! = parsedRConfList[idx]'h_len := by
    let arr : Array RConf := ⟨parsedRConfList⟩
    have h_sz : idx < arr.size := h_len
    change arr[idx]! = parsedRConfList[idx]'h_len
    rw [getElem!_pos arr idx h_sz]
    rfl
  rw [h_arr]
  exact checkRConfListStructural_sound parsedRConfList idx h_len parsedRConfList_structural_verified

/-- Every configuration `theUnavoidableSet[idx]!` (`idx < 633`) has a valid ring cycle (`IsRingCycle`). -/
theorem unavoidable_is_ring_cycle (idx : Nat) (h_lt : idx < 633) :
    IsRingCycle theUnavoidableSet[idx]! := by
  rw [theUnavoidableSet_getElem! idx h_lt]
  have h_struct := sharedCfgs_structural_verified idx h_lt
  dsimp [checkRConfStructural] at h_struct
  rcases Bool.and_eq_true_iff.mp h_struct with ⟨h123, _⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, _⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨_, h_ring⟩
  exact ringCycle_of_checkRConf sharedCfgs[idx]! h_ring

/-- Every configuration `theUnavoidableSet[idx]!` (`idx < 633`) has a well-formed `earlier` table (`IsWellFormedEarlier`). -/
theorem unavoidable_is_well_formed_earlier (idx : Nat) (h_lt : idx < 633) :
    IsWellFormedEarlier theUnavoidableSet[idx]! sharedCfgs[idx]!.earlier := by
  rw [theUnavoidableSet_getElem! idx h_lt]
  have h_struct := sharedCfgs_structural_verified idx h_lt
  dsimp [checkRConfStructural] at h_struct
  rcases Bool.and_eq_true_iff.mp h_struct with ⟨h123, _⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, h_lt_ear⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨h_le, _⟩
  exact wellFormedEarlier_of_checkRConf sharedCfgs[idx]! (Nat.le_of_ble_eq_true h_le) h_lt_ear

theorem ring_le_15_of_ble (rc : RConf) (h : Nat.ble rc.r 15 = true) :
    (configOfRConf rc).ringSize ≤ 15 :=
  Nat.le_of_ble_eq_true h

/-- Every configuration `theUnavoidableSet[idx]!` (`idx < 633`) has ring size `≤ 15`. -/
theorem unavoidable_ring_le_15 (idx : Nat) (h_lt : idx < 633) :
    (theUnavoidableSet[idx]!).ringSize ≤ 15 := by
  rw [theUnavoidableSet_getElem! idx h_lt]
  have h_struct := sharedCfgs_structural_verified idx h_lt
  dsimp [checkRConfStructural] at h_struct
  rcases Bool.and_eq_true_iff.mp h_struct with ⟨_, h_r15⟩
  exact ring_le_15_of_ble sharedCfgs[idx]! h_r15

end CheckerSoundness
end Math
