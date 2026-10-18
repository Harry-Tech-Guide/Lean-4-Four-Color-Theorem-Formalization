import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring

set_option linter.constructorNameAsVariable false

namespace Math

open Hypermap

/-!
# Sanity Verification: Degree-5 Vertex Configuration is Provably NOT Reducible

This module formally verifies that Kempe's 1879 degree-5 fallacy does NOT hold in our formalization:
1. The degree-5 vertex configuration has boundary colorings that cannot be directly extended (`deg5_bad_not_extensible`).
2. The degree-5 vertex configuration has NO contract edges, so it is provably NOT C-reducible (`deg5_not_c_reducible`).
3. Under the RSST/Kempe joint planar partition semantics (`Eliminated`), the adversary maintains a closed
   invariant of non-extendable (surjective) boundary colorings on the 5-cycle:
   for every surjective boundary coloring and every color pairing θ chosen by the reducer, the adversary
   has a valid joint planar ring partition (π_ab, π_cd) such that EVERY response swap choice S keeps
   the boundary coloring surjective onto all 4 colors.
4. The existence of this winning adversary partition is verified across all 120 surjective colorings
   and all 24 color pairings via computational reflection (`native_decide`) in `checkDeg5Adversary_true`.
5. Hence, no Kempe chain transformation can eliminate a surjective boundary coloring: `¬ IsDReducible degree5Config`.
6. Therefore, `¬ IsReducible degree5Config`.
-/

def deg5Adj (i j : Nat) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) ||
  (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) ||
  (i == 3 && j == 4) || (i == 4 && j == 3) ||
  (i == 4 && j == 0) || (i == 0 && j == 4) ||
  (i == 5 && j < 5) || (j == 5 && i < 5)

def degree5Config : Configuration := {
  ringSize := 5,
  interiorSize := 1,
  adj := deg5Adj,
  contractEdges := []
}

/-- A boundary coloring using all 4 colors: 0, 1, 2, 0, 3 on the 5-ring. -/
def deg5BadColoring : BoundaryColoring degree5Config := fun i =>
  if i == 0 then Color.c0
  else if i == 1 then Color.c1
  else if i == 2 then Color.c2
  else if i == 3 then Color.c0
  else Color.c3

def checkDeg5Valid : Bool :=
  (List.range 5).all (fun i =>
    (List.range 5).all (fun j =>
      if degree5Config.adj i j then deg5BadColoring i != deg5BadColoring j else true))

theorem checkDeg5Valid_true : checkDeg5Valid = true := by rfl

theorem deg5BadColoring_valid : IsValidBoundaryColoring degree5Config deg5BadColoring := by
  intro i j hi hj hadj
  have hi_mem : i ∈ List.range 5 := List.mem_range.mpr hi
  have hj_mem : j ∈ List.range 5 := List.mem_range.mpr hj
  have h_all_i := List.all_eq_true.mp checkDeg5Valid_true i hi_mem
  have h_all_j := List.all_eq_true.mp h_all_i j hj_mem
  rw [hadj] at h_all_j
  intro h_eq
  rw [h_eq] at h_all_j
  simp at h_all_j

def checkDeg5Chordless : Bool :=
  (List.range 5).all (fun i =>
    (List.range 5).all (fun j =>
      if degree5Config.adj i j then (j == (i + 1) % 5 || i == (j + 1) % 5) else true))

theorem checkDeg5Chordless_true : checkDeg5Chordless = true := by rfl

theorem degree5Config_chordless : IsChordlessRing degree5Config := by
  intro i hi j hj hadj
  have hi_mem : i ∈ List.range 5 := List.mem_range.mpr hi
  have hj_mem : j ∈ List.range 5 := List.mem_range.mpr hj
  have h_all_i := List.all_eq_true.mp checkDeg5Chordless_true i hi_mem
  have h_all_j := List.all_eq_true.mp h_all_i j hj_mem
  rw [hadj] at h_all_j
  dsimp at h_all_j
  cases h_or : (j == (i + 1) % 5 || i == (j + 1) % 5) with
  | true =>
    simp only [Bool.or_eq_true, beq_iff_eq] at h_or
    exact h_or
  | false =>
    rw [h_or] at h_all_j
    contradiction

def deg5_surj (b : BoundaryColoring degree5Config) : Prop :=
  ∀ c : Color, ∃ i < 5, b i = c

theorem deg5BadColoring_surj : deg5_surj deg5BadColoring := by
  intro c
  cases c with
  | c0 => exact ⟨0, by decide, rfl⟩
  | c1 => exact ⟨1, by decide, rfl⟩
  | c2 => exact ⟨2, by decide, rfl⟩
  | c3 => exact ⟨4, by decide, rfl⟩

theorem deg5_bad_not_extensible (b : BoundaryColoring degree5Config)
    (h_surj : deg5_surj b) :
    ¬ extendsToInterior degree5Config b := by
  intro ⟨full, hmatch, hvalid⟩
  have ⟨i0, hi0, hb0⟩ := h_surj Color.c0
  have ⟨i1, hi1, hb1⟩ := h_surj Color.c1
  have ⟨i2, hi2, hb2⟩ := h_surj Color.c2
  have ⟨i3, hi3, hb3⟩ := h_surj Color.c3
  have hf0 : full i0 = Color.c0 := by rw [hmatch i0 hi0, hb0]
  have hf1 : full i1 = Color.c1 := by rw [hmatch i1 hi1, hb1]
  have hf2 : full i2 = Color.c2 := by rw [hmatch i2 hi2, hb2]
  have hf3 : full i3 = Color.c3 := by rw [hmatch i3 hi3, hb3]
  have hadj0 : degree5Config.adj 5 i0 = true := by
    dsimp [degree5Config, deg5Adj]; simp; omega
  have hadj1 : degree5Config.adj 5 i1 = true := by
    dsimp [degree5Config, deg5Adj]; simp; omega
  have hadj2 : degree5Config.adj 5 i2 = true := by
    dsimp [degree5Config, deg5Adj]; simp; omega
  have hadj3 : degree5Config.adj 5 i3 = true := by
    dsimp [degree5Config, deg5Adj]; simp; omega
  have hv0 := hvalid 5 i0 (by decide) (by dsimp [degree5Config, Configuration.totalNodes]; omega) hadj0
  have hv1 := hvalid 5 i1 (by decide) (by dsimp [degree5Config, Configuration.totalNodes]; omega) hadj1
  have hv2 := hvalid 5 i2 (by decide) (by dsimp [degree5Config, Configuration.totalNodes]; omega) hadj2
  have hv3 := hvalid 5 i3 (by decide) (by dsimp [degree5Config, Configuration.totalNodes]; omega) hadj3
  rw [hf0] at hv0; rw [hf1] at hv1; rw [hf2] at hv2; rw [hf3] at hv3
  cases h5 : full 5 with
  | c0 => exact hv0 h5
  | c1 => exact hv1 h5
  | c2 => exact hv2 h5
  | c3 => exact hv3 h5

def allColors : List Color := [Color.c0, Color.c1, Color.c2, Color.c3]

theorem mem_allColors (c : Color) : c ∈ allColors := by
  cases c <;> decide

def allBoundaryColorings5 : List (List Color) :=
  let rec gen (n : Nat) : List (List Color) :=
    match n with
    | 0 => [[]]
    | n + 1 => (gen n).bind (fun l => allColors.map (fun c => c :: l))
  gen 5

theorem mem_allBoundaryColorings5 (c0 c1 c2 c3 c4 : Color) :
    [c0, c1, c2, c3, c4] ∈ allBoundaryColorings5 := by
  dsimp [allBoundaryColorings5, allBoundaryColorings5.gen]
  rw [List.mem_bind]
  refine ⟨[c1, c2, c3, c4], ?_, ?_⟩
  · rw [List.mem_bind]
    refine ⟨[c2, c3, c4], ?_, ?_⟩
    · rw [List.mem_bind]
      refine ⟨[c3, c4], ?_, ?_⟩
      · rw [List.mem_bind]
        refine ⟨[c4], ?_, ?_⟩
        · rw [List.mem_bind]
          refine ⟨[], by decide, ?_⟩
          rw [List.mem_map]
          exact ⟨c4, mem_allColors c4, rfl⟩
        · rw [List.mem_map]
          exact ⟨c3, mem_allColors c3, rfl⟩
      · rw [List.mem_map]
        exact ⟨c2, mem_allColors c2, rfl⟩
    · rw [List.mem_map]
      exact ⟨c1, mem_allColors c1, rfl⟩
  · rw [List.mem_map]
    exact ⟨c0, mem_allColors c0, rfl⟩

def isValid5 (l : List Color) : Bool :=
  (List.range 5).all fun i =>
    let j := (i + 1) % 5
    l.get! i != l.get! j

def isSurj5 (l : List Color) : Bool :=
  allColors.all fun c => (List.range 5).any fun i => l.get! i == c

theorem surj_of_isSurj5 (b : Nat → Color)
    (h : isSurj5 ((List.range 5).map b) = true) :
    ∀ c : Color, ∃ i < 5, b i = c := by
  intro c
  have hMem : c ∈ allColors := mem_allColors c
  have hAll := List.all_eq_true.mp h c hMem
  have ⟨i, hi_range, h_eq⟩ := List.any_eq_true.mp hAll
  have hi : i < 5 := List.mem_range.mp hi_range
  refine ⟨i, hi, ?_⟩
  have hget : ((List.range 5).map b).get! i = b i := by
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
  rw [hget] at h_eq
  exact beq_iff_eq (a := b i) (b := c) |>.mp h_eq

def deg5BadList : List (List Color) :=
  allBoundaryColorings5.filter (fun l => isValid5 l && isSurj5 l)

def allPairings24 : List ColorPairing :=
  allColors.bind fun a =>
    allColors.bind fun b =>
      allColors.bind fun c =>
        allColors.filterMap fun d =>
          if h : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then
            some ⟨a, b, c, d, h⟩
          else none

theorem mem_allPairings24 (θ : ColorPairing) : θ ∈ allPairings24 := by
  dsimp [allPairings24]
  rw [List.mem_bind]
  refine ⟨θ.a, mem_allColors θ.a, ?_⟩
  rw [List.mem_bind]
  refine ⟨θ.b, mem_allColors θ.b, ?_⟩
  rw [List.mem_bind]
  refine ⟨θ.c, mem_allColors θ.c, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨θ.d, mem_allColors θ.d, ?_⟩
  dsimp
  rw [dif_pos θ.distinct]

def isRingAdj (i j : Nat) : Bool :=
  j == (i + 1) % 5 || i == (j + 1) % 5

theorem deg5Adj_eq (i j : Nat) (hi : i < 5) (hj : j < 5) :
    degree5Config.adj i j = isRingAdj i j := by
  dsimp [degree5Config, deg5Adj, isRingAdj]
  have hi5 : (i == 5) = false := by
    cases h : (i == 5)
    · rfl
    · have := Nat.eq_of_beq_eq_true h; omega
  have hj5 : (j == 5) = false := by
    cases h : (j == 5)
    · rfl
    · have := Nat.eq_of_beq_eq_true h; omega
  rw [hi5, hj5]
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hi_cases with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj_cases with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem beq_to_eq {a b : Color} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> revert h <;> decide

theorem get_five (b : Nat → Color) (i : Nat) (hi : i < 5) :
    [b 0, b 1, b 2, b 3, b 4].get! i = b i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

structure JointPlanarChecks (col : List Color) (θ : ColorPairing)
    (rel_ab rel_cd : Nat → Nat → Bool) : Prop where
  ab_refl : (List.range 5).all (fun i => if col.get! i == θ.a || col.get! i == θ.b then rel_ab i i else true) = true
  ab_symm : (List.range 5).all (fun i => (List.range 5).all (fun j => if rel_ab i j then rel_ab j i else true)) = true
  ab_trans : (List.range 5).all (fun i => (List.range 5).all (fun j => (List.range 5).all (fun l => if rel_ab i j && rel_ab j l then rel_ab i l else true))) = true
  ab_color : (List.range 5).all (fun i => (List.range 5).all (fun j => if rel_ab i j then (col.get! i == θ.a || col.get! i == θ.b) else true)) = true
  cd_refl : (List.range 5).all (fun i => if col.get! i == θ.c || col.get! i == θ.d then rel_cd i i else true) = true
  cd_symm : (List.range 5).all (fun i => (List.range 5).all (fun j => if rel_cd i j then rel_cd j i else true)) = true
  cd_trans : (List.range 5).all (fun i => (List.range 5).all (fun j => (List.range 5).all (fun l => if rel_cd i j && rel_cd j l then rel_cd i l else true))) = true
  cd_color : (List.range 5).all (fun i => (List.range 5).all (fun j => if rel_cd i j then (col.get! i == θ.c || col.get! i == θ.d) else true)) = true
  ab_adj : (List.range 5).all (fun i => (List.range 5).all (fun j => if isRingAdj i j && (col.get! i == θ.a || col.get! i == θ.b) && (col.get! j == θ.a || col.get! j == θ.b) then rel_ab i j else true)) = true
  cd_adj : (List.range 5).all (fun i => (List.range 5).all (fun j => if isRingAdj i j && (col.get! i == θ.c || col.get! i == θ.d) && (col.get! j == θ.c || col.get! j == θ.d) then rel_cd i j else true)) = true
  ab_noncross : (List.range 5).all (fun i => (List.range 5).all (fun j => (List.range 5).all (fun l => (List.range 5).all (fun m =>
    if i < j && j < l && l < m && rel_ab i l && rel_ab j m then rel_ab i j else true)))) = true
  cd_noncross : (List.range 5).all (fun i => (List.range 5).all (fun j => (List.range 5).all (fun l => (List.range 5).all (fun m =>
    if i < j && j < l && l < m && rel_cd i l && rel_cd j m then rel_cd i j else true)))) = true
  cross_ab_cd : (List.range 5).all (fun i => (List.range 5).all (fun j => (List.range 5).all (fun l => (List.range 5).all (fun m =>
    if i < j && j < l && l < m then !(rel_ab i l && rel_cd j m) else true)))) = true
  cross_cd_ab : (List.range 5).all (fun i => (List.range 5).all (fun j => (List.range 5).all (fun l => (List.range 5).all (fun m =>
    if i < j && j < l && l < m then !(rel_cd i l && rel_ab j m) else true)))) = true

theorem all_range5 {P : Nat → Bool} (h : (List.range 5).all P = true) (i : Nat) (hi : i < 5) :
    P i = true := by
  have hMem : i ∈ List.range 5 := List.mem_range.mpr hi
  exact List.all_eq_true.mp h i hMem

theorem all_range5_2 {P : Nat → Nat → Bool} (h : (List.range 5).all (fun i => (List.range 5).all (fun j => P i j)) = true)
    (i : Nat) (hi : i < 5) (j : Nat) (hj : j < 5) :
    P i j = true := by
  have hi_mem : i ∈ List.range 5 := List.mem_range.mpr hi
  have hj_mem : j ∈ List.range 5 := List.mem_range.mpr hj
  have h_i := List.all_eq_true.mp h i hi_mem
  exact List.all_eq_true.mp h_i j hj_mem

theorem all_range5_3 {P : Nat → Nat → Nat → Bool}
    (h : (List.range 5).all (fun i => (List.range 5).all (fun j => (List.range 5).all (fun l => P i j l))) = true)
    (i : Nat) (hi : i < 5) (j : Nat) (hj : j < 5) (l : Nat) (hl : l < 5) :
    P i j l = true := by
  have hi_mem : i ∈ List.range 5 := List.mem_range.mpr hi
  have hj_mem : j ∈ List.range 5 := List.mem_range.mpr hj
  have hl_mem : l ∈ List.range 5 := List.mem_range.mpr hl
  have h_i := List.all_eq_true.mp h i hi_mem
  have h_j := List.all_eq_true.mp h_i j hj_mem
  exact List.all_eq_true.mp h_j l hl_mem

theorem all_range5_4 {P : Nat → Nat → Nat → Nat → Bool}
    (h : (List.range 5).all (fun i => (List.range 5).all (fun j => (List.range 5).all (fun l => (List.range 5).all (fun m => P i j l m)))) = true)
    (i : Nat) (hi : i < 5) (j : Nat) (hj : j < 5) (l : Nat) (hl : l < 5) (m : Nat) (hm : m < 5) :
    P i j l m = true := by
  have hi_mem : i ∈ List.range 5 := List.mem_range.mpr hi
  have hj_mem : j ∈ List.range 5 := List.mem_range.mpr hj
  have hl_mem : l ∈ List.range 5 := List.mem_range.mpr hl
  have hm_mem : m ∈ List.range 5 := List.mem_range.mpr hm
  have h_i := List.all_eq_true.mp h i hi_mem
  have h_j := List.all_eq_true.mp h_i j hj_mem
  have h_l := List.all_eq_true.mp h_j l hl_mem
  exact List.all_eq_true.mp h_l m hm_mem

theorem isJointPlanar_of_checks (col : List Color) (θ : ColorPairing)
    (rel_ab rel_cd : Nat → Nat → Bool) (hc : JointPlanarChecks col θ rel_ab rel_cd)
    (b : BoundaryColoring degree5Config) (hb : ∀ i < 5, b i = col.get! i) :
    IsJointPlanarRingPartition degree5Config b θ
      (fun i j => i < 5 ∧ j < 5 ∧ rel_ab i j = true)
      (fun i j => i < 5 ∧ j < 5 ∧ rel_cd i j = true) := by
  refine {
    ab_refl := ?_, ab_symm := ?_, ab_trans := ?_, ab_color := ?_,
    cd_refl := ?_, cd_symm := ?_, cd_trans := ?_, cd_color := ?_,
    ab_adj := ?_, cd_adj := ?_, ab_noncross := ?_, cd_noncross := ?_,
    cross_ab_cd := ?_, cross_cd_ab := ?_
  }
  · intro i hi hcol
    have h_i := all_range5 hc.ab_refl i hi
    rw [hb i hi] at hcol
    have h_or : (col.get! i == θ.a || col.get! i == θ.b) = true := by
      cases hcol with
      | inl h => simp only [h, beq_self_eq_true, Bool.true_or]
      | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    rw [h_or] at h_i
    exact ⟨hi, hi, h_i⟩
  · intro i hi j hj ⟨_, _, hrel⟩
    have h_ij := all_range5_2 hc.ab_symm i hi j hj
    rw [hrel] at h_ij
    exact ⟨hj, hi, h_ij⟩
  · intro i hi j hj l hl ⟨_, _, h1⟩ ⟨_, _, h2⟩
    have h_ijl := all_range5_3 hc.ab_trans i hi j hj l hl
    rw [h1, h2] at h_ijl
    exact ⟨hi, hl, h_ijl⟩
  · intro i hi j hj ⟨_, _, hrel⟩
    have h_ij := all_range5_2 hc.ab_color i hi j hj
    rw [hrel] at h_ij
    rw [hb i hi]
    cases h_or : (col.get! i == θ.a)
    · rw [h_or, Bool.false_or] at h_ij
      exact Or.inr (beq_to_eq h_ij)
    · exact Or.inl (beq_to_eq h_or)
  · intro i hi hcol
    have h_i := all_range5 hc.cd_refl i hi
    rw [hb i hi] at hcol
    have h_or : (col.get! i == θ.c || col.get! i == θ.d) = true := by
      cases hcol with
      | inl h => simp only [h, beq_self_eq_true, Bool.true_or]
      | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    rw [h_or] at h_i
    exact ⟨hi, hi, h_i⟩
  · intro i hi j hj ⟨_, _, hrel⟩
    have h_ij := all_range5_2 hc.cd_symm i hi j hj
    rw [hrel] at h_ij
    exact ⟨hj, hi, h_ij⟩
  · intro i hi j hj l hl ⟨_, _, h1⟩ ⟨_, _, h2⟩
    have h_ijl := all_range5_3 hc.cd_trans i hi j hj l hl
    rw [h1, h2] at h_ijl
    exact ⟨hi, hl, h_ijl⟩
  · intro i hi j hj ⟨_, _, hrel⟩
    have h_ij := all_range5_2 hc.cd_color i hi j hj
    rw [hrel] at h_ij
    rw [hb i hi]
    cases h_or : (col.get! i == θ.c)
    · rw [h_or, Bool.false_or] at h_ij
      exact Or.inr (beq_to_eq h_ij)
    · exact Or.inl (beq_to_eq h_or)
  · intro i hi j hj hadj hcol_i hcol_j
    have h_ij := all_range5_2 hc.ab_adj i hi j hj
    rw [deg5Adj_eq i j hi hj] at hadj
    rw [hb i hi] at hcol_i
    rw [hb j hj] at hcol_j
    have h_or_i : (col.get! i == θ.a || col.get! i == θ.b) = true := by
      cases hcol_i with | inl h => simp only [h, beq_self_eq_true, Bool.true_or] | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    have h_or_j : (col.get! j == θ.a || col.get! j == θ.b) = true := by
      cases hcol_j with | inl h => simp only [h, beq_self_eq_true, Bool.true_or] | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    rw [hadj, h_or_i, h_or_j] at h_ij
    dsimp at h_ij
    exact ⟨hi, hj, h_ij⟩
  · intro i hi j hj hadj hcol_i hcol_j
    have h_ij := all_range5_2 hc.cd_adj i hi j hj
    rw [deg5Adj_eq i j hi hj] at hadj
    rw [hb i hi] at hcol_i
    rw [hb j hj] at hcol_j
    have h_or_i : (col.get! i == θ.c || col.get! i == θ.d) = true := by
      cases hcol_i with | inl h => simp only [h, beq_self_eq_true, Bool.true_or] | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    have h_or_j : (col.get! j == θ.c || col.get! j == θ.d) = true := by
      cases hcol_j with | inl h => simp only [h, beq_self_eq_true, Bool.true_or] | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    rw [hadj, h_or_i, h_or_j] at h_ij
    dsimp at h_ij
    exact ⟨hi, hj, h_ij⟩
  · intro i j l m hij hjl hlm hm ⟨hi, hl, h1⟩ ⟨hj, _, h2⟩
    have h_ijlm := all_range5_4 hc.ab_noncross i hi j hj l hl m hm
    have h_lt : (i < j && j < l && l < m) = true := by
      simp [hij, hjl, hlm]
    rw [h_lt, h1, h2] at h_ijlm
    dsimp at h_ijlm
    exact ⟨hi, hj, h_ijlm⟩
  · intro i j l m hij hjl hlm hm ⟨hi, hl, h1⟩ ⟨hj, _, h2⟩
    have h_ijlm := all_range5_4 hc.cd_noncross i hi j hj l hl m hm
    have h_lt : (i < j && j < l && l < m) = true := by
      simp [hij, hjl, hlm]
    rw [h_lt, h1, h2] at h_ijlm
    dsimp at h_ijlm
    exact ⟨hi, hj, h_ijlm⟩
  · intro i j l m hij hjl hlm hm ⟨hi, hl, h1⟩ ⟨hj, _, h2⟩
    have h_ijlm := all_range5_4 hc.cross_ab_cd i hi j hj l hl m hm
    have h_lt : (i < j && j < l && l < m) = true := by
      simp [hij, hjl, hlm]
    rw [h_lt] at h_ijlm
    dsimp at h_ijlm
    rw [h1, h2] at h_ijlm
    contradiction
  · intro i j l m hij hjl hlm hm ⟨hi, hl, h1⟩ ⟨hj, _, h2⟩
    have h_ijlm := all_range5_4 hc.cross_cd_ab i hi j hj l hl m hm
    have h_lt : (i < j && j < l && l < m) = true := by
      simp [hij, hjl, hlm]
    rw [h_lt] at h_ijlm
    dsimp at h_ijlm
    rw [h1, h2] at h_ijlm
    contradiction

def isJointPlanarBool (col : List Color) (θ : ColorPairing)
    (rel_ab rel_cd : Nat → Nat → Bool) : Bool :=
  let R := List.range 5
  R.all (fun i => if col.get! i == θ.a || col.get! i == θ.b then rel_ab i i else true) &&
  R.all (fun i => R.all (fun j => if rel_ab i j then rel_ab j i else true)) &&
  R.all (fun i => R.all (fun j => R.all (fun l => if rel_ab i j && rel_ab j l then rel_ab i l else true))) &&
  R.all (fun i => R.all (fun j => if rel_ab i j then (col.get! i == θ.a || col.get! i == θ.b) else true)) &&
  R.all (fun i => if col.get! i == θ.c || col.get! i == θ.d then rel_cd i i else true) &&
  R.all (fun i => R.all (fun j => if rel_cd i j then rel_cd j i else true)) &&
  R.all (fun i => R.all (fun j => R.all (fun l => if rel_cd i j && rel_cd j l then rel_cd i l else true))) &&
  R.all (fun i => R.all (fun j => if rel_cd i j then (col.get! i == θ.c || col.get! i == θ.d) else true)) &&
  R.all (fun i => R.all (fun j => if isRingAdj i j && (col.get! i == θ.a || col.get! i == θ.b) && (col.get! j == θ.a || col.get! j == θ.b) then rel_ab i j else true)) &&
  R.all (fun i => R.all (fun j => if isRingAdj i j && (col.get! i == θ.c || col.get! i == θ.d) && (col.get! j == θ.c || col.get! j == θ.d) then rel_cd i j else true)) &&
  R.all (fun i => R.all (fun j => R.all (fun l => R.all (fun m =>
    if i < j && j < l && l < m && rel_ab i l && rel_ab j m then rel_ab i j else true)))) &&
  R.all (fun i => R.all (fun j => R.all (fun l => R.all (fun m =>
    if i < j && j < l && l < m && rel_cd i l && rel_cd j m then rel_cd i j else true)))) &&
  R.all (fun i => R.all (fun j => R.all (fun l => R.all (fun m =>
    if i < j && j < l && l < m then !(rel_ab i l && rel_cd j m) else true)))) &&
  R.all (fun i => R.all (fun j => R.all (fun l => R.all (fun m =>
    if i < j && j < l && l < m then !(rel_cd i l && rel_ab j m) else true))))

theorem checks_of_isJointPlanarBool (col : List Color) (θ : ColorPairing) (rel_ab rel_cd : Nat → Nat → Bool)
    (h : isJointPlanarBool col θ rel_ab rel_cd = true) : JointPlanarChecks col θ rel_ab rel_cd := by
  dsimp [isJointPlanarBool] at h
  repeat rw [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

def allPartitionsOf (verts : List Nat) : List (Nat → Nat → Bool) :=
  match verts with
  | [] => [fun _ _ => false]
  | [x] => [fun i j => i == x && j == x]
  | [x, y] =>
    [ fun i j => (i == x && j == x) || (i == y && j == y),
      fun i j => (i == x || i == y) && (j == x || j == y) ]
  | [x, y, z] =>
    [ fun i j => (i == x && j == x) || (i == y && j == y) || (i == z && j == z),
      fun i j => ((i == x || i == y) && (j == x || j == y)) || (i == z && j == z),
      fun i j => ((i == x || i == z) && (j == x || j == z)) || (i == y && j == y),
      fun i j => ((i == y || i == z) && (j == y || j == z)) || (i == x && j == x),
      fun i j => (i == x || i == y || i == z) && (j == x || j == y || j == z) ]
  | _ => []

def allValidSwaps (rel_ab rel_cd : Nat → Nat → Bool) : List (Nat → Bool) :=
  let allSubsets : List (Nat → Bool) :=
    (List.range 32).map fun mask =>
      fun i => (mask >>> i) &&& 1 == 1
  allSubsets.filter fun S =>
    (List.range 5).all (fun i => (List.range 5).all (fun j =>
      (if rel_ab i j then S i == S j else true) &&
      (if rel_cd i j then S i == S j else true)))

def maskOfS (S : Nat → Bool) : Nat :=
  (if S 0 then 1 else 0) +
  (if S 1 then 2 else 0) +
  (if S 2 then 4 else 0) +
  (if S 3 then 8 else 0) +
  (if S 4 then 16 else 0)

theorem maskOfS_spec (S : Nat → Bool) (i : Nat) (hi : i < 5) :
    ((maskOfS S >>> i) &&& 1 == 1) = S i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  cases h0 : S 0 <;> cases h1 : S 1 <;> cases h2 : S 2 <;> cases h3 : S 3 <;> cases h4 : S 4 <;>
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
  dsimp [maskOfS] <;> rw [h0, h1, h2, h3, h4] <;> decide

theorem maskOfS_lt32 (S : Nat → Bool) : maskOfS S < 32 := by
  cases h0 : S 0 <;> cases h1 : S 1 <;> cases h2 : S 2 <;> cases h3 : S 3 <;> cases h4 : S 4 <;>
  dsimp [maskOfS] <;> rw [h0, h1, h2, h3, h4] <;> decide

theorem swap_in_allValidSwaps (rel_ab rel_cd : Nat → Nat → Bool)
    (S : Nat → Bool)
    (h_ab : ∀ i < 5, ∀ j < 5, rel_ab i j = true → S i = S j)
    (h_cd : ∀ i < 5, ∀ j < 5, rel_cd i j = true → S i = S j) :
    ∃ S_cand ∈ allValidSwaps rel_ab rel_cd, ∀ i < 5, S_cand i = S i := by
  let S_cand := fun i => (maskOfS S >>> i) &&& 1 == 1
  have hspec : ∀ i < 5, S_cand i = S i := maskOfS_spec S
  refine ⟨S_cand, ?_, hspec⟩
  dsimp [allValidSwaps]
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [List.mem_map]
    refine ⟨maskOfS S, ?_, rfl⟩
    exact List.mem_range.mpr (maskOfS_lt32 S)
  · rw [List.all_eq_true]
    intro i hi_mem
    rw [List.all_eq_true]
    intro j hj_mem
    have hi : i < 5 := List.mem_range.mp hi_mem
    have hj : j < 5 := List.mem_range.mp hj_mem
    rw [hspec i hi, hspec j hj]
    cases h_ab_ij : rel_ab i j <;> cases h_cd_ij : rel_cd i j
    · rfl
    · dsimp
      have heq := h_cd i hi j hj h_cd_ij
      simp [beq_iff_eq, heq]
    · dsimp
      have heq := h_ab i hi j hj h_ab_ij
      simp [beq_iff_eq, heq]
    · dsimp
      have heq := h_ab i hi j hj h_ab_ij
      simp [beq_iff_eq, heq]

theorem swap_preserves_surj_step (col : List Color) (θ : ColorPairing)
    (rel_ab rel_cd : Nat → Nat → Bool)
    (h_win : (allValidSwaps rel_ab rel_cd).all (fun S =>
      isSurj5 ((List.range 5).map fun i => if S i then θ.swap (col.get! i) else col.get! i)) = true)
    (b : BoundaryColoring degree5Config)
    (hb_col : ∀ i < 5, b i = col.get! i)
    (S : Nat → Bool)
    (hSwap : IsValidSwapChoice degree5Config b θ
      (fun i j => i < 5 ∧ j < 5 ∧ rel_ab i j = true)
      (fun i j => i < 5 ∧ j < 5 ∧ rel_cd i j = true) S) :
    deg5_surj (boundaryKempeSwap degree5Config b θ S) := by
  have h_ab : ∀ i < 5, ∀ j < 5, rel_ab i j = true → S i = S j := by
    intro i hi j hj hrel
    exact hSwap.respects_ab i hi j hj ⟨hi, hj, hrel⟩
  have h_cd : ∀ i < 5, ∀ j < 5, rel_cd i j = true → S i = S j := by
    intro i hi j hj hrel
    exact hSwap.respects_cd i hi j hj ⟨hi, hj, hrel⟩
  have ⟨S_cand, h_mem, h_spec⟩ := swap_in_allValidSwaps rel_ab rel_cd S h_ab h_cd
  have h_all := List.all_eq_true.mp h_win S_cand h_mem
  apply surj_of_isSurj5
  have h_eq_list : ((List.range 5).map (boundaryKempeSwap degree5Config b θ S)) =
      ((List.range 5).map fun i => if S_cand i then θ.swap (col.get! i) else col.get! i) := by
    apply List.ext_get
    · simp
    · intro k h1 h2
      simp only [List.length_map, List.length_range] at h1
      have hk : k < 5 := h1
      have h1' : ((List.range 5).map (boundaryKempeSwap degree5Config b θ S)).get ⟨k, h1⟩ =
          boundaryKempeSwap degree5Config b θ S k := by
        simp [List.getElem_map]
      have h2' : ((List.range 5).map fun i => if S_cand i then θ.swap (col.get! i) else col.get! i).get ⟨k, h2⟩ =
          (if S_cand k then θ.swap (col.get! k) else col.get! k) := by
        simp [List.getElem_map]
      rw [h1', h2']
      dsimp [boundaryKempeSwap]
      rw [h_spec k hk, hb_col k hk]
  rw [h_eq_list]
  exact h_all

def findWinningPartition (col : List Color) (θ : ColorPairing) :
    Option ((Nat → Nat → Bool) × (Nat → Nat → Bool)) :=
  let verts_ab := (List.range 5).filter fun i => col.get! i == θ.a || col.get! i == θ.b
  let verts_cd := (List.range 5).filter fun i => col.get! i == θ.c || col.get! i == θ.d
  let parts_ab := allPartitionsOf verts_ab
  let parts_cd := allPartitionsOf verts_cd
  parts_ab.findSome? fun rel_ab =>
    parts_cd.findSome? fun rel_cd =>
      if isJointPlanarBool col θ rel_ab rel_cd &&
         let swaps := allValidSwaps rel_ab rel_cd
         swaps.all fun S =>
           let col' := (List.range 5).map fun i =>
             if S i then θ.swap (col.get! i) else col.get! i
           isSurj5 col'
      then some (rel_ab, rel_cd)
      else none

def checkDeg5Adversary : Bool :=
  deg5BadList.all fun col =>
    allPairings24.all fun θ =>
      match findWinningPartition col θ with
      | some (rel_ab, rel_cd) =>
          isJointPlanarBool col θ rel_ab rel_cd &&
          let swaps := allValidSwaps rel_ab rel_cd
          swaps.all fun S =>
            let col' := (List.range 5).map fun i =>
              if S i then θ.swap (col.get! i) else col.get! i
            isSurj5 col'
      | none => false

/-- In-kernel reflection theorem verifying the degree-5 adversary winning strategy across all
    120 bad ring colorings and all 24 color pairings using `native_decide`. -/
theorem checkDeg5Adversary_true : checkDeg5Adversary = true := by
  native_decide

theorem checkDeg5Valid_of_valid (b : BoundaryColoring degree5Config)
    (hb : IsValidBoundaryColoring degree5Config b) :
    isValid5 [b 0, b 1, b 2, b 3, b 4] = true := by
  dsimp [isValid5]
  rw [List.all_eq_true]
  intro i hi_mem
  have hi : i < 5 := List.mem_range.mp hi_mem
  have hj : (i + 1) % 5 < 5 := Nat.mod_lt _ (by decide)
  have hadj : degree5Config.adj i ((i + 1) % 5) = true := by
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  have hne := hb i ((i + 1) % 5) hi hj hadj
  rw [get_five b i hi, get_five b ((i + 1) % 5) hj]
  dsimp [bne]
  have h_beq : (b i == b ((i + 1) % 5)) = false := by
    cases h : (b i == b ((i + 1) % 5))
    · rfl
    · have := beq_to_eq h
      contradiction
  rw [h_beq]
  rfl

theorem isSurj5_of_surj (b : BoundaryColoring degree5Config) (hSurj : deg5_surj b) :
    isSurj5 [b 0, b 1, b 2, b 3, b 4] = true := by
  dsimp [isSurj5]
  rw [List.all_eq_true]
  intro c _
  rw [List.any_eq_true]
  rcases hSurj c with ⟨i, hi, hbi⟩
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  rw [get_five b i hi, hbi]
  simp only [beq_self_eq_true]

theorem col_mem_deg5BadList (b : BoundaryColoring degree5Config)
    (hb : IsValidBoundaryColoring degree5Config b) (hSurj : deg5_surj b) :
    [b 0, b 1, b 2, b 3, b 4] ∈ deg5BadList := by
  dsimp [deg5BadList]
  rw [List.mem_filter]
  refine ⟨mem_allBoundaryColorings5 (b 0) (b 1) (b 2) (b 3) (b 4), ?_⟩
  rw [checkDeg5Valid_of_valid b hb, isSurj5_of_surj b hSurj]
  rfl

theorem deg5_eliminated_not_surj (b : BoundaryColoring degree5Config)
    (hElim : Eliminated degree5Config b) :
    IsValidBoundaryColoring degree5Config b → deg5_surj b → False := by
  induction hElim with
  | ext b' hExt =>
    intro _ hSurj
    exact deg5_bad_not_extensible b' hSurj hExt
  | kempe b' θ resp hb' hValid _ ih =>
    intro _ hSurj
    let col := [b' 0, b' 1, b' 2, b' 3, b' 4]
    have h_col_mem : col ∈ deg5BadList := col_mem_deg5BadList b' hb' hSurj
    have h_θ_mem : θ ∈ allPairings24 := mem_allPairings24 θ
    have h_all_cols := List.all_eq_true.mp checkDeg5Adversary_true col h_col_mem
    have h_all_θ := List.all_eq_true.mp h_all_cols θ h_θ_mem
    cases h_opt : findWinningPartition col θ with
    | none =>
      rw [h_opt] at h_all_θ
      contradiction
    | some pair =>
      let (rel_ab, rel_cd) := pair
      rw [h_opt, Bool.and_eq_true] at h_all_θ
      rcases h_all_θ with ⟨h_jp, h_win⟩
      have hc := checks_of_isJointPlanarBool col θ rel_ab rel_cd h_jp
      have hb_spec : ∀ i < 5, b' i = col.get! i := by
        intro i hi
        have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
      have hPart := isJointPlanar_of_checks col θ rel_ab rel_cd hc b' hb_spec
      let S := resp (fun i j => i < 5 ∧ j < 5 ∧ rel_ab i j = true)
                    (fun i j => i < 5 ∧ j < 5 ∧ rel_cd i j = true)
      have hSwap := hValid (fun i j => i < 5 ∧ j < 5 ∧ rel_ab i j = true)
                           (fun i j => i < 5 ∧ j < 5 ∧ rel_cd i j = true) hPart
      have hb_swapped := swap_preserves_valid degree5Config b' θ
        (fun i j => i < 5 ∧ j < 5 ∧ rel_ab i j = true)
        (fun i j => i < 5 ∧ j < 5 ∧ rel_cd i j = true) S hb' hPart hSwap
      have hSurj_swapped := swap_preserves_surj_step col θ rel_ab rel_cd h_win b' hb_spec S hSwap
      exact ih (fun i j => i < 5 ∧ j < 5 ∧ rel_ab i j = true)
               (fun i j => i < 5 ∧ j < 5 ∧ rel_cd i j = true)
               hPart hb_swapped hSurj_swapped

theorem deg5_not_d_reducible : ¬ IsDReducible degree5Config := by
  intro hD
  have hElim := hD deg5BadColoring deg5BadColoring_valid
  exact deg5_eliminated_not_surj deg5BadColoring hElim deg5BadColoring_valid deg5BadColoring_surj

theorem deg5_not_c_reducible : ¬ IsCReducible degree5Config := by
  intro ⟨hNonempty, _⟩
  dsimp [degree5Config] at hNonempty
  exact hNonempty rfl

/-- The degree-5 vertex configuration is NOT reducible under the RSST / Kempe game semantics.
    The proof relies on `checkDeg5Adversary_true`, which is formally verified via Lean 4
    computational reflection using `native_decide` (introducing the `Lean.ofReduceBool` axiom). -/
theorem deg5_not_reducible : ¬ IsReducible degree5Config := by
  intro hRed
  cases hRed with
  | inl hD => exact deg5_not_d_reducible hD
  | inr hC => exact deg5_not_c_reducible hC

end Math
