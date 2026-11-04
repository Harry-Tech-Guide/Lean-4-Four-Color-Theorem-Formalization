import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring

set_option linter.constructorNameAsVariable false

namespace Math

open Hypermap

def colorBeq : Color → Color → Bool
  | .c0, .c0 | .c1, .c1 | .c2, .c2 | .c3, .c3 => true
  | _, _ => false

local instance (priority := high) : BEq Color := ⟨colorBeq⟩

local instance (priority := high) : LawfulBEq Color where
  eq_of_beq {a b} h := by cases a <;> cases b <;> revert h <;> decide
  rfl {a} := by cases a <;> rfl

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
   and all 24 color pairings via computational reflection (`kernel reduction`) in `checkDeg5Adversary_true`.
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

theorem beq_to_eq {a b : Color} (h : (a == b) = true) : a = b :=
  LawfulBEq.eq_of_beq h

theorem bne_of_ne {x y : Color} (h : x ≠ y) : (x != y) = true := by
  cases x <;> cases y <;> revert h <;> decide

def rawPairings24 : List (Color × Color × Color × Color) :=
  allColors.bind fun a =>
    allColors.bind fun b =>
      allColors.bind fun c =>
        allColors.filterMap fun d =>
          if a != b && a != c && a != d && b != c && b != d && c != d then
            some (a, b, c, d)
          else none

def rawSwap (a b c d col : Color) : Color :=
  if col == a then b
  else if col == b then a
  else if col == c then d
  else if col == d then c
  else col

theorem rawSwap_eq_swap (θ : ColorPairing) (col : Color) :
    rawSwap θ.a θ.b θ.c θ.d col = θ.swap col := by
  dsimp [rawSwap, ColorPairing.swap]
  have h_beq (x y : Color) : (x == y) = decide (x = y) := by cases x <;> cases y <;> rfl
  rw [h_beq col θ.a, h_beq col θ.b, h_beq col θ.c, h_beq col θ.d]
  by_cases ha : col = θ.a <;> by_cases hb : col = θ.b <;> by_cases hc : col = θ.c <;> by_cases hd : col = θ.d <;>
  simp [ha, hb, hc, hd]

theorem mem_rawPairings24 (θ : ColorPairing) : (θ.a, θ.b, θ.c, θ.d) ∈ rawPairings24 := by
  rcases θ with ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd⟩
  dsimp [rawPairings24]
  rw [List.mem_bind]
  refine ⟨a, mem_allColors a, ?_⟩
  rw [List.mem_bind]
  refine ⟨b, mem_allColors b, ?_⟩
  rw [List.mem_bind]
  refine ⟨c, mem_allColors c, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨d, mem_allColors d, ?_⟩
  rw [bne_of_ne hab, bne_of_ne hac, bne_of_ne had, bne_of_ne hbc, bne_of_ne hbd, bne_of_ne hcd]
  rfl

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

theorem get_five (b : Nat → Color) (i : Nat) (hi : i < 5) :
    [b 0, b 1, b 2, b 3, b 4].get! i = b i := by
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

def fiveEdges : List (Nat × Nat) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

theorem mem_fiveEdges (i j : Nat) (hi : i < 5) (hj : j < 5) (hadj : degree5Config.adj i j = true) :
    (i, j) ∈ fiveEdges ∨ (j, i) ∈ fiveEdges := by
  have hi_c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  have hj_c : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hi_c with rfl | rfl | rfl | rfl | rfl <;>
  rcases hj_c with rfl | rfl | rfl | rfl | rfl <;>
  revert hadj <;> decide

def inPair (col : List Color) (x y : Color) (i : Nat) : Bool :=
  col.get! i == x || col.get! i == y

def kernelRel (in_set side : Nat → Bool) (i j : Nat) : Bool :=
  in_set i && in_set j && (side i == side j)

theorem kernelRel_refl (in_set side : Nat → Bool) (i : Nat) (h : in_set i = true) :
    kernelRel in_set side i i = true := by
  dsimp [kernelRel]; rw [h]; simp

theorem kernelRel_symm (in_set side : Nat → Bool) (i j : Nat) (h : kernelRel in_set side i j = true) :
    kernelRel in_set side j i = true := by
  dsimp [kernelRel] at h ⊢
  revert h
  cases in_set i <;> cases in_set j <;> cases side i <;> cases side j <;> decide

theorem kernelRel_trans (in_set side : Nat → Bool) (i j l : Nat)
    (h1 : kernelRel in_set side i j = true) (h2 : kernelRel in_set side j l = true) :
    kernelRel in_set side i l = true := by
  dsimp [kernelRel] at h1 h2 ⊢
  revert h1 h2
  cases in_set i <;> cases in_set j <;> cases in_set l <;>
  cases side i <;> cases side j <;> cases side l <;> decide

theorem kernelRel_color (in_set side : Nat → Bool) (i j : Nat) (h : kernelRel in_set side i j = true) :
    in_set i = true := by
  dsimp [kernelRel] at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.1

def fiveTuples4 : List (Nat × Nat × Nat × Nat) :=
  [(0, 1, 2, 3), (0, 1, 2, 4), (0, 1, 3, 4), (0, 2, 3, 4), (1, 2, 3, 4)]

theorem mem_fiveTuples4 (i j l m : Nat) (hij : i < j) (hjl : j < l) (hlm : l < m) (hm : m < 5) :
    (i, j, l, m) ∈ fiveTuples4 := by
  have : (i = 0 ∧ j = 1 ∧ l = 2 ∧ m = 3) ∨
         (i = 0 ∧ j = 1 ∧ l = 2 ∧ m = 4) ∨
         (i = 0 ∧ j = 1 ∧ l = 3 ∧ m = 4) ∨
         (i = 0 ∧ j = 2 ∧ l = 3 ∧ m = 4) ∨
         (i = 1 ∧ j = 2 ∧ l = 3 ∧ m = 4) := by omega
  rcases this with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;> decide

structure JointPlanarChecks (col : List Color) (θ : ColorPairing)
    (side_ab side_cd : Nat → Bool) : Prop where
  ab_adj : fiveEdges.all (fun (i, j) =>
    let rel_ab := kernelRel (inPair col θ.a θ.b) side_ab
    if inPair col θ.a θ.b i && inPair col θ.a θ.b j then rel_ab i j else true) = true
  cd_adj : fiveEdges.all (fun (i, j) =>
    let rel_cd := kernelRel (inPair col θ.c θ.d) side_cd
    if inPair col θ.c θ.d i && inPair col θ.c θ.d j then rel_cd i j else true) = true
  ab_noncross : fiveTuples4.all (fun (i, j, l, m) =>
    let rel_ab := kernelRel (inPair col θ.a θ.b) side_ab
    if rel_ab i l && rel_ab j m then rel_ab i j else true) = true
  cd_noncross : fiveTuples4.all (fun (i, j, l, m) =>
    let rel_cd := kernelRel (inPair col θ.c θ.d) side_cd
    if rel_cd i l && rel_cd j m then rel_cd i j else true) = true
  cross_ab_cd : fiveTuples4.all (fun (i, j, l, m) =>
    let rel_ab := kernelRel (inPair col θ.a θ.b) side_ab
    let rel_cd := kernelRel (inPair col θ.c θ.d) side_cd
    !(rel_ab i l && rel_cd j m)) = true
  cross_cd_ab : fiveTuples4.all (fun (i, j, l, m) =>
    let rel_ab := kernelRel (inPair col θ.a θ.b) side_ab
    let rel_cd := kernelRel (inPair col θ.c θ.d) side_cd
    !(rel_cd i l && rel_ab j m)) = true

theorem isJointPlanar_of_checks (col : List Color) (θ : ColorPairing)
    (side_ab side_cd : Nat → Bool) (hc : JointPlanarChecks col θ side_ab side_cd)
    (b : BoundaryColoring degree5Config) (hb : ∀ i < 5, b i = col.get! i) :
    let rel_ab := kernelRel (inPair col θ.a θ.b) side_ab
    let rel_cd := kernelRel (inPair col θ.c θ.d) side_cd
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
    rw [hb i hi] at hcol
    have h_or : inPair col θ.a θ.b i = true := by
      dsimp [inPair]
      cases hcol with
      | inl h => simp only [h, beq_self_eq_true, Bool.true_or]
      | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    exact ⟨hi, hi, kernelRel_refl _ _ i h_or⟩
  · intro i hi j hj ⟨_, _, hrel⟩
    exact ⟨hj, hi, kernelRel_symm _ _ i j hrel⟩
  · intro i hi j _ l hl ⟨_, _, h1⟩ ⟨_, _, h2⟩
    exact ⟨hi, hl, kernelRel_trans _ _ i j l h1 h2⟩
  · intro i hi _ _ ⟨_, _, hrel⟩
    have h_in := kernelRel_color _ _ i _ hrel
    dsimp [inPair] at h_in
    rw [hb i hi]
    cases h_or : (col.get! i == θ.a)
    · rw [h_or, Bool.false_or] at h_in
      exact Or.inr (beq_to_eq h_in)
    · exact Or.inl (beq_to_eq h_or)
  · intro i hi hcol
    rw [hb i hi] at hcol
    have h_or : inPair col θ.c θ.d i = true := by
      dsimp [inPair]
      cases hcol with
      | inl h => simp only [h, beq_self_eq_true, Bool.true_or]
      | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    exact ⟨hi, hi, kernelRel_refl _ _ i h_or⟩
  · intro i hi j hj ⟨_, _, hrel⟩
    exact ⟨hj, hi, kernelRel_symm _ _ i j hrel⟩
  · intro i hi j _ l hl ⟨_, _, h1⟩ ⟨_, _, h2⟩
    exact ⟨hi, hl, kernelRel_trans _ _ i j l h1 h2⟩
  · intro i hi _ _ ⟨_, _, hrel⟩
    have h_in := kernelRel_color _ _ i _ hrel
    dsimp [inPair] at h_in
    rw [hb i hi]
    cases h_or : (col.get! i == θ.c)
    · rw [h_or, Bool.false_or] at h_in
      exact Or.inr (beq_to_eq h_in)
    · exact Or.inl (beq_to_eq h_or)
  · intro i hi j hj hadj hcol_i hcol_j
    rw [hb i hi] at hcol_i
    rw [hb j hj] at hcol_j
    have h_or_i : inPair col θ.a θ.b i = true := by
      dsimp [inPair]; cases hcol_i with | inl h => simp only [h, beq_self_eq_true, Bool.true_or] | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    have h_or_j : inPair col θ.a θ.b j = true := by
      dsimp [inPair]; cases hcol_j with | inl h => simp only [h, beq_self_eq_true, Bool.true_or] | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    rcases mem_fiveEdges i j hi hj hadj with h_edge | h_edge
    · have h_ij := List.all_eq_true.mp hc.ab_adj (i, j) h_edge
      dsimp at h_ij; rw [h_or_i, h_or_j] at h_ij; dsimp at h_ij
      exact ⟨hi, hj, h_ij⟩
    · have h_ji := List.all_eq_true.mp hc.ab_adj (j, i) h_edge
      dsimp at h_ji; rw [h_or_j, h_or_i] at h_ji; dsimp at h_ji
      exact ⟨hi, hj, kernelRel_symm _ _ j i h_ji⟩
  · intro i hi j hj hadj hcol_i hcol_j
    rw [hb i hi] at hcol_i
    rw [hb j hj] at hcol_j
    have h_or_i : inPair col θ.c θ.d i = true := by
      dsimp [inPair]; cases hcol_i with | inl h => simp only [h, beq_self_eq_true, Bool.true_or] | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    have h_or_j : inPair col θ.c θ.d j = true := by
      dsimp [inPair]; cases hcol_j with | inl h => simp only [h, beq_self_eq_true, Bool.true_or] | inr h => simp only [h, beq_self_eq_true, Bool.or_true]
    rcases mem_fiveEdges i j hi hj hadj with h_edge | h_edge
    · have h_ij := List.all_eq_true.mp hc.cd_adj (i, j) h_edge
      dsimp at h_ij; rw [h_or_i, h_or_j] at h_ij; dsimp at h_ij
      exact ⟨hi, hj, h_ij⟩
    · have h_ji := List.all_eq_true.mp hc.cd_adj (j, i) h_edge
      dsimp at h_ji; rw [h_or_j, h_or_i] at h_ji; dsimp at h_ji
      exact ⟨hi, hj, kernelRel_symm _ _ j i h_ji⟩
  · intro i j l m hij hjl hlm hm ⟨hi, _, h1⟩ ⟨hj, _, h2⟩
    have h_ijlm := List.all_eq_true.mp hc.ab_noncross (i, j, l, m) (mem_fiveTuples4 i j l m hij hjl hlm hm)
    dsimp at h_ijlm; rw [h1, h2] at h_ijlm; dsimp at h_ijlm
    exact ⟨hi, hj, h_ijlm⟩
  · intro i j l m hij hjl hlm hm ⟨hi, _, h1⟩ ⟨hj, _, h2⟩
    have h_ijlm := List.all_eq_true.mp hc.cd_noncross (i, j, l, m) (mem_fiveTuples4 i j l m hij hjl hlm hm)
    dsimp at h_ijlm; rw [h1, h2] at h_ijlm; dsimp at h_ijlm
    exact ⟨hi, hj, h_ijlm⟩
  · intro i j l m hij hjl hlm hm ⟨_, _, h1⟩ ⟨_, _, h2⟩
    have h_ijlm := List.all_eq_true.mp hc.cross_ab_cd (i, j, l, m) (mem_fiveTuples4 i j l m hij hjl hlm hm)
    dsimp at h_ijlm; rw [h1, h2] at h_ijlm; contradiction
  · intro i j l m hij hjl hlm hm ⟨_, _, h1⟩ ⟨_, _, h2⟩
    have h_ijlm := List.all_eq_true.mp hc.cross_cd_ab (i, j, l, m) (mem_fiveTuples4 i j l m hij hjl hlm hm)
    dsimp at h_ijlm; rw [h1, h2] at h_ijlm; contradiction

def isJointPlanarBoolRaw (col : List Color) (a b c d : Color)
    (side_ab side_cd : Nat → Bool) : Bool :=
  let rel_ab := kernelRel (inPair col a b) side_ab
  let rel_cd := kernelRel (inPair col c d) side_cd
  fiveEdges.all (fun (i, j) => if inPair col a b i && inPair col a b j then rel_ab i j else true) &&
  fiveEdges.all (fun (i, j) => if inPair col c d i && inPair col c d j then rel_cd i j else true) &&
  fiveTuples4.all (fun (i, j, l, m) => if rel_ab i l && rel_ab j m then rel_ab i j else true) &&
  fiveTuples4.all (fun (i, j, l, m) => if rel_cd i l && rel_cd j m then rel_cd i j else true) &&
  fiveTuples4.all (fun (i, j, l, m) => !(rel_ab i l && rel_cd j m)) &&
  fiveTuples4.all (fun (i, j, l, m) => !(rel_cd i l && rel_ab j m))

theorem checks_of_isJointPlanarBoolRaw (col : List Color) (θ : ColorPairing) (side_ab side_cd : Nat → Bool)
    (h : isJointPlanarBoolRaw col θ.a θ.b θ.c θ.d side_ab side_cd = true) : JointPlanarChecks col θ side_ab side_cd := by
  dsimp [isJointPlanarBoolRaw] at h
  repeat rw [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  exact ⟨h1, h2, h3, h4, h5, h6⟩

def hasConnectedPair (col : List Color) (x y : Color) (rel : Nat → Nat → Bool) : Bool :=
  (List.range 5).any fun u =>
    col.get! u == x && (List.range 5).any fun v =>
      col.get! v == y && rel u v

theorem toNat_inj {x y : Color} (h : x.toNat = y.toNat) : x = y := by
  cases x <;> cases y <;> cases h <;> rfl

theorem toNat_lt_4 (x : Color) : x.toNat < 4 := by
  cases x <;> decide

theorem color_mem_pairing (θ : ColorPairing) (x : Color) :
    x = θ.a ∨ x = θ.b ∨ x = θ.c ∨ x = θ.d := by
  rcases θ with ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd⟩
  have ha := toNat_lt_4 a; have hb := toNat_lt_4 b; have hc := toNat_lt_4 c; have hd := toNat_lt_4 d; have hx := toNat_lt_4 x
  have hab' : a.toNat ≠ b.toNat := fun h => hab (toNat_inj h)
  have hac' : a.toNat ≠ c.toNat := fun h => hac (toNat_inj h)
  have had' : a.toNat ≠ d.toNat := fun h => had (toNat_inj h)
  have hbc' : b.toNat ≠ c.toNat := fun h => hbc (toNat_inj h)
  have hbd' : b.toNat ≠ d.toNat := fun h => hbd (toNat_inj h)
  have hcd' : c.toNat ≠ d.toNat := fun h => hcd (toNat_inj h)
  have h_nat : x.toNat = a.toNat ∨ x.toNat = b.toNat ∨ x.toNat = c.toNat ∨ x.toNat = d.toNat := by omega
  rcases h_nat with h | h | h | h
  · exact Or.inl (toNat_inj h)
  · exact Or.inr (Or.inl (toNat_inj h))
  · exact Or.inr (Or.inr (Or.inl (toNat_inj h)))
  · exact Or.inr (Or.inr (Or.inr (toNat_inj h)))

theorem swap_eq_b (θ : ColorPairing) : θ.swap θ.a = θ.b := by
  dsimp [ColorPairing.swap]
  rw [if_pos rfl]

theorem swap_eq_a (θ : ColorPairing) : θ.swap θ.b = θ.a := by
  dsimp [ColorPairing.swap]
  rw [if_neg (Ne.symm θ.distinct.1), if_pos rfl]

theorem swap_eq_d (θ : ColorPairing) : θ.swap θ.c = θ.d := by
  dsimp [ColorPairing.swap]
  rw [if_neg (Ne.symm θ.distinct.2.1), if_neg (Ne.symm θ.distinct.2.2.2.1), if_pos rfl]

theorem swap_eq_c (θ : ColorPairing) : θ.swap θ.d = θ.c := by
  dsimp [ColorPairing.swap]
  rw [if_neg (Ne.symm θ.distinct.2.2.1), if_neg (Ne.symm θ.distinct.2.2.2.2.1),
      if_neg (Ne.symm θ.distinct.2.2.2.2.2), if_pos rfl]

theorem swap_preserves_surj_step (col : List Color) (θ : ColorPairing)
    (rel_ab rel_cd : Nat → Nat → Bool)
    (h_win : (hasConnectedPair col θ.a θ.b rel_ab && hasConnectedPair col θ.c θ.d rel_cd) = true)
    (b : BoundaryColoring degree5Config)
    (hb_col : ∀ i < 5, b i = col.get! i)
    (S : Nat → Bool)
    (hSwap : IsValidSwapChoice degree5Config b θ
      (fun i j => i < 5 ∧ j < 5 ∧ rel_ab i j = true)
      (fun i j => i < 5 ∧ j < 5 ∧ rel_cd i j = true) S) :
    deg5_surj (boundaryKempeSwap degree5Config b θ S) := by
  rw [Bool.and_eq_true] at h_win
  rcases h_win with ⟨h_ab_pair, h_cd_pair⟩
  dsimp [hasConnectedPair] at h_ab_pair h_cd_pair
  rw [List.any_eq_true] at h_ab_pair h_cd_pair
  rcases h_ab_pair with ⟨u, hu_mem, hu_rest⟩
  rw [Bool.and_eq_true, List.any_eq_true] at hu_rest
  rcases hu_rest with ⟨hu_col, v, hv_mem, hv_rest⟩
  rw [Bool.and_eq_true] at hv_rest
  rcases hv_rest with ⟨hv_col, huv_rel⟩
  rcases h_cd_pair with ⟨x, hx_mem, hx_rest⟩
  rw [Bool.and_eq_true, List.any_eq_true] at hx_rest
  rcases hx_rest with ⟨hx_col, y, hy_mem, hy_rest⟩
  rw [Bool.and_eq_true] at hy_rest
  rcases hy_rest with ⟨hy_col, hxy_rel⟩
  have hu : u < 5 := List.mem_range.mp hu_mem
  have hv : v < 5 := List.mem_range.mp hv_mem
  have hx : x < 5 := List.mem_range.mp hx_mem
  have hy : y < 5 := List.mem_range.mp hy_mem
  have hbu : b u = θ.a := by rw [hb_col u hu]; exact beq_to_eq hu_col
  have hbv : b v = θ.b := by rw [hb_col v hv]; exact beq_to_eq hv_col
  have hbx : b x = θ.c := by rw [hb_col x hx]; exact beq_to_eq hx_col
  have hby : b y = θ.d := by rw [hb_col y hy]; exact beq_to_eq hy_col
  have hSuv : S u = S v := hSwap.respects_ab u hu v hv ⟨hu, hv, huv_rel⟩
  have hSxy : S x = S y := hSwap.respects_cd x hx y hy ⟨hx, hy, hxy_rel⟩
  intro c
  rcases color_mem_pairing θ c with rfl | rfl | rfl | rfl
  · cases hSu : S u
    · refine ⟨u, hu, ?_⟩
      dsimp [boundaryKempeSwap]; rw [hSu, if_neg Bool.false_ne_true, hbu]
    · refine ⟨v, hv, ?_⟩
      have hSv : S v = true := by rw [← hSuv, hSu]
      dsimp [boundaryKempeSwap]; rw [hSv, if_pos rfl, hbv, swap_eq_a]
  · cases hSu : S u
    · refine ⟨v, hv, ?_⟩
      have hSv : S v = false := by rw [← hSuv, hSu]
      dsimp [boundaryKempeSwap]; rw [hSv, if_neg Bool.false_ne_true, hbv]
    · refine ⟨u, hu, ?_⟩
      dsimp [boundaryKempeSwap]; rw [hSu, if_pos rfl, hbu, swap_eq_b]
  · cases hSx : S x
    · refine ⟨x, hx, ?_⟩
      dsimp [boundaryKempeSwap]; rw [hSx, if_neg Bool.false_ne_true, hbx]
    · refine ⟨y, hy, ?_⟩
      have hSy : S y = true := by rw [← hSxy, hSx]
      dsimp [boundaryKempeSwap]; rw [hSy, if_pos rfl, hby, swap_eq_c]
  · cases hSx : S x
    · refine ⟨y, hy, ?_⟩
      have hSy : S y = false := by rw [← hSxy, hSx]
      dsimp [boundaryKempeSwap]; rw [hSy, if_neg Bool.false_ne_true, hby]
    · refine ⟨x, hx, ?_⟩
      dsimp [boundaryKempeSwap]; rw [hSx, if_pos rfl, hbx, swap_eq_d]

def winningSides (col : List Color) (a b c d : Color) :
    (Nat → Bool) × (Nat → Bool) :=
  let verts_ab := (List.range 5).filter (inPair col a b)
  let verts_cd := (List.range 5).filter (inPair col c d)
  match verts_ab with
  | [u, v] => (fun _ => true, fun i => Nat.blt u i && Nat.blt i v)
  | _ =>
    match verts_cd with
    | [u, v] => (fun i => Nat.blt u i && Nat.blt i v, fun _ => true)
    | _ => (fun _ => false, fun _ => false)

def checkDeg5Adversary : Bool :=
  deg5BadList.all fun col =>
    rawPairings24.all fun (a, b, c, d) =>
      let (side_ab, side_cd) := winningSides col a b c d
      let rel_ab := kernelRel (inPair col a b) side_ab
      let rel_cd := kernelRel (inPair col c d) side_cd
      isJointPlanarBoolRaw col a b c d side_ab side_cd &&
      (hasConnectedPair col a b rel_ab && hasConnectedPair col c d rel_cd)

/-- In-kernel reflection theorem verifying the degree-5 adversary winning strategy across all
    120 bad ring colorings and all 24 color pairings using kernel reduction (`rfl`). -/
theorem checkDeg5Adversary_true : checkDeg5Adversary = true := by
  rfl

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
    have h_θ_mem : (θ.a, θ.b, θ.c, θ.d) ∈ rawPairings24 := mem_rawPairings24 θ
    have h_all_cols := List.all_eq_true.mp checkDeg5Adversary_true col h_col_mem
    have h_all_θ := List.all_eq_true.mp h_all_cols (θ.a, θ.b, θ.c, θ.d) h_θ_mem
    dsimp at h_all_θ
    rw [Bool.and_eq_true] at h_all_θ
    rcases h_all_θ with ⟨h_jp, h_win⟩
    have hc := checks_of_isJointPlanarBoolRaw col θ
      (winningSides col θ.a θ.b θ.c θ.d).1 (winningSides col θ.a θ.b θ.c θ.d).2 h_jp
    have hb_spec : ∀ i < 5, b' i = col.get! i := by
      intro i hi
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
    have hPart := isJointPlanar_of_checks col θ
      (winningSides col θ.a θ.b θ.c θ.d).1 (winningSides col θ.a θ.b θ.c θ.d).2 hc b' hb_spec
    let S := resp (fun i j => i < 5 ∧ j < 5 ∧ kernelRel (inPair col θ.a θ.b) (winningSides col θ.a θ.b θ.c θ.d).1 i j = true)
                  (fun i j => i < 5 ∧ j < 5 ∧ kernelRel (inPair col θ.c θ.d) (winningSides col θ.a θ.b θ.c θ.d).2 i j = true)
    have hSwap := hValid (fun i j => i < 5 ∧ j < 5 ∧ kernelRel (inPair col θ.a θ.b) (winningSides col θ.a θ.b θ.c θ.d).1 i j = true)
                         (fun i j => i < 5 ∧ j < 5 ∧ kernelRel (inPair col θ.c θ.d) (winningSides col θ.a θ.b θ.c θ.d).2 i j = true) hPart
    have hb_swapped := swap_preserves_valid degree5Config b' θ
      (fun i j => i < 5 ∧ j < 5 ∧ kernelRel (inPair col θ.a θ.b) (winningSides col θ.a θ.b θ.c θ.d).1 i j = true)
      (fun i j => i < 5 ∧ j < 5 ∧ kernelRel (inPair col θ.c θ.d) (winningSides col θ.a θ.b θ.c θ.d).2 i j = true) S hb' hPart hSwap
    have hSurj_swapped := swap_preserves_surj_step col θ
      (kernelRel (inPair col θ.a θ.b) (winningSides col θ.a θ.b θ.c θ.d).1)
      (kernelRel (inPair col θ.c θ.d) (winningSides col θ.a θ.b θ.c θ.d).2) h_win b' hb_spec S hSwap
    exact ih (fun i j => i < 5 ∧ j < 5 ∧ kernelRel (inPair col θ.a θ.b) (winningSides col θ.a θ.b θ.c θ.d).1 i j = true)
             (fun i j => i < 5 ∧ j < 5 ∧ kernelRel (inPair col θ.c θ.d) (winningSides col θ.a θ.b θ.c θ.d).2 i j = true)
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
    kernel reduction (`rfl`) with zero external axioms. -/
theorem deg5_not_reducible : ¬ IsReducible degree5Config := by
  intro hRed
  cases hRed with
  | inl hD => exact deg5_not_d_reducible hD
  | inr hC => exact deg5_not_c_reducible hC

end Math
