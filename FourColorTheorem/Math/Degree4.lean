import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring

set_option linter.constructorNameAsVariable false

namespace Math

/-!
# Degree-4 Vertex Configuration: Unconditional Reducibility under Kempe Semantics

This module formally proves that the degree-4 vertex configuration (a 4-cycle ring with one
interior vertex adjacent to all 4 ring vertices, with no contract edges) is unconditionally
reducible (`IsReducible degree4Config`), validating Kempe's classical 1879 argument.

## Mathematical Argument:
Given any valid boundary coloring `b` of the 4-ring:
1. If at least one color is unused on the ring, `b` directly extends to the interior vertex
   adjacent to all 4 ring vertices (`deg4_extends_of_unused_color`).
2. If all 4 colors are used, opposite vertices (0, 2) have distinct colors (a, c) and
   opposite vertices (1, 3) have distinct colors (b, d).
   The reducer selects the pairing θ = {{a, c}, {b, d}}.
   For every joint planar ring partition (π_ac, π_bd) presented by the adversary:
   - If 0 ~ 2 in π_ac, then by non-crossing planarity (`cross_ab_cd`), vertices 1 and 3
     cannot be related in π_bd (they would cross). Hence the reducer swaps {1}, changing
     vertex 1's color to d and leaving color b completely unused on the ring.
   - If 0 ≁ 2 in π_ac, the reducer swaps {0}, changing vertex 0's color to c and leaving
     color a completely unused on the ring.
   In both cases, only 3 colors remain on the ring, so the swapped coloring extends to the interior.
3. Therefore, every boundary coloring is eliminated, proving `IsDReducible degree4Config`
   and hence `IsReducible degree4Config` unconditionally.
-/

def deg4Adj (i j : Nat) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 0) ||
  (i == 1 && j == 2) || (i == 2 && j == 1) ||
  (i == 2 && j == 3) || (i == 3 && j == 2) ||
  (i == 3 && j == 0) || (i == 0 && j == 3) ||
  (i == 4 && j < 4) || (j == 4 && i < 4)

def degree4Config : Configuration := {
  ringSize := 4,
  interiorSize := 1,
  adj := deg4Adj,
  contractEdges := []
}

def checkDeg4Chordless : Bool :=
  (List.range 4).all (fun i =>
    (List.range 4).all (fun j =>
      if degree4Config.adj i j then (j == (i + 1) % 4 || i == (j + 1) % 4) else true))

theorem checkDeg4Chordless_true : checkDeg4Chordless = true := by rfl

theorem degree4Config_chordless : IsChordlessRing degree4Config := by
  intro i hi j hj hadj
  have hi_mem : i ∈ List.range 4 := List.mem_range.mpr hi
  have hj_mem : j ∈ List.range 4 := List.mem_range.mpr hj
  have h_all_i := List.all_eq_true.mp checkDeg4Chordless_true i hi_mem
  have h_all_j := List.all_eq_true.mp h_all_i j hj_mem
  rw [hadj] at h_all_j
  dsimp at h_all_j
  cases h_or : (j == (i + 1) % 4 || i == (j + 1) % 4) with
  | true =>
    simp only [Bool.or_eq_true, beq_iff_eq] at h_or
    exact h_or
  | false =>
    rw [h_or] at h_all_j
    contradiction

/-- Any boundary coloring with an unused color extends directly to the interior vertex. -/
theorem deg4_extends_of_unused_color (b : BoundaryColoring degree4Config)
    (hb : IsValidBoundaryColoring degree4Config b)
    (c : Color) (hc : ∀ i < 4, b i ≠ c) :
    extendsToInterior degree4Config b := by
  refine ⟨fun i => if i < 4 then b i else c, ?_, ?_⟩
  · intro i hi
    have hi4 : i < 4 := hi
    dsimp
    rw [if_pos hi4]
  · intro i j hi hj hadj
    dsimp [Configuration.totalNodes, degree4Config] at hi hj
    dsimp
    by_cases hi4 : i < 4 <;> by_cases hj4 : j < 4
    · rw [if_pos hi4, if_pos hj4]
      exact hb i j hi4 hj4 hadj
    · rw [if_pos hi4, if_neg hj4]
      have hj_eq : j = 4 := by omega
      subst hj_eq
      intro h_eq
      exact hc i hi4 h_eq
    · rw [if_neg hi4, if_pos hj4]
      have hi_eq : i = 4 := by omega
      subst hi_eq
      intro h_eq
      exact hc j hj4 h_eq.symm
    · have : i = 4 ∧ j = 4 := by omega
      rcases this with ⟨rfl, rfl⟩
      dsimp [degree4Config, deg4Adj] at hadj
      contradiction

def allCols : List Color := [Color.c0, Color.c1, Color.c2, Color.c3]

def deg4IsSurjCols (c0 c1 c2 c3 : Color) : Bool :=
  allCols.all fun c => (c0 == c || c1 == c || c2 == c || c3 == c)

theorem distinct_of_surj (c0 c1 c2 c3 : Color) (h : deg4IsSurjCols c0 c1 c2 c3 = true) :
    c0 ≠ c2 ∧ c0 ≠ c1 ∧ c0 ≠ c3 ∧ c2 ≠ c1 ∧ c2 ≠ c3 ∧ c1 ≠ c3 := by
  revert h
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> decide

def findUnusedCol (c0 c1 c2 c3 : Color) : Color :=
  if c0 != Color.c0 && c1 != Color.c0 && c2 != Color.c0 && c3 != Color.c0 then Color.c0
  else if c0 != Color.c1 && c1 != Color.c1 && c2 != Color.c1 && c3 != Color.c1 then Color.c1
  else if c0 != Color.c2 && c1 != Color.c2 && c2 != Color.c2 && c3 != Color.c2 then Color.c2
  else Color.c3

theorem unused_of_not_surj (c0 c1 c2 c3 : Color) (h : deg4IsSurjCols c0 c1 c2 c3 = false) :
    let c := findUnusedCol c0 c1 c2 c3
    c0 ≠ c ∧ c1 ≠ c ∧ c2 ≠ c ∧ c3 ≠ c := by
  revert h
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> decide

/-- The degree-4 vertex configuration is unconditionally D-reducible under Kempe semantics. -/
theorem deg4_d_reducible : IsDReducible degree4Config := by
  intro b hb
  cases hSurj : deg4IsSurjCols (b 0) (b 1) (b 2) (b 3) with
  | false =>
    have hUnused := unused_of_not_surj (b 0) (b 1) (b 2) (b 3) hSurj
    let c := findUnusedCol (b 0) (b 1) (b 2) (b 3)
    have hc : ∀ i < 4, b i ≠ c := by
      intro i hi
      have hi4 : i < 4 := hi
      if hi0 : i = 0 then subst hi0; exact hUnused.1
      else if hi1 : i = 1 then subst hi1; exact hUnused.2.1
      else if hi2 : i = 2 then subst hi2; exact hUnused.2.2.1
      else
        have : i = 3 := by omega
        subst this
        exact hUnused.2.2.2
    exact Eliminated.ext b (deg4_extends_of_unused_color b hb c hc)
  | true =>
    have ⟨h02, h01, h03, h21, h23, h13⟩ := distinct_of_surj (b 0) (b 1) (b 2) (b 3) hSurj
    let θ : ColorPairing := {
      a := b 0
      b := b 2
      c := b 1
      d := b 3
      distinct := ⟨h02, h01, h03, h21, h23, h13⟩
    }
    apply Eliminated.kempe_choice degree4Config b θ hb
    intro equiv_ab equiv_cd hPart
    by_cases h02_rel : equiv_ab 0 2
    · have h13_not : ¬ equiv_cd 1 3 := by
        intro h13_rel
        exact hPart.cross_ab_cd 0 1 2 3 (by decide) (by decide) (by decide) (by decide) h02_rel h13_rel
      let S : Nat → Bool := fun i => i == 1
      have hSwap : IsValidSwapChoice degree4Config b θ equiv_ab equiv_cd S := {
        ring_only := by
          intro i hi
          have : i = 1 := Nat.eq_of_beq_eq_true hi
          subst this; decide
        respects_ab := by
          intro i hi j hj hij
          have h_col_i := hPart.ab_color i hi j hj hij
          have h_col_j := hPart.ab_color j hj i hi (hPart.ab_symm i hi j hj hij)
          dsimp [S]
          have hi_ne1 : i ≠ 1 := by
            intro h; subst h
            cases h_col_i with
            | inl h => exact h01.symm h
            | inr h => exact h21.symm h
          have hj_ne1 : j ≠ 1 := by
            intro h; subst h
            cases h_col_j with
            | inl h => exact h01.symm h
            | inr h => exact h21.symm h
          rw [beq_false_of_ne hi_ne1, beq_false_of_ne hj_ne1]
        respects_cd := by
          intro i hi j hj hij
          have h_col_i := hPart.cd_color i hi j hj hij
          have h_col_j := hPart.cd_color j hj i hi (hPart.cd_symm i hi j hj hij)
          dsimp [S]
          have hi4 : i < 4 := hi
          have hj4 : j < 4 := hj
          have hi_mem : i = 1 ∨ i = 3 := by
            if hi0 : i = 0 then
              subst hi0; exfalso; cases h_col_i with | inl h => exact h01 h | inr h => exact h03 h
            else if hi1 : i = 1 then exact Or.inl hi1
            else if hi2 : i = 2 then
              subst hi2; exfalso; cases h_col_i with | inl h => exact h21 h | inr h => exact h23 h
            else
              exact Or.inr (by omega)
          have hj_mem : j = 1 ∨ j = 3 := by
            if hj0 : j = 0 then
              subst hj0; exfalso; cases h_col_j with | inl h => exact h01 h | inr h => exact h03 h
            else if hj1 : j = 1 then exact Or.inl hj1
            else if hj2 : j = 2 then
              subst hj2; exfalso; cases h_col_j with | inl h => exact h21 h | inr h => exact h23 h
            else
              exact Or.inr (by omega)
          rcases hi_mem with rfl | rfl <;> rcases hj_mem with rfl | rfl
          · rfl
          · exact False.elim (h13_not hij)
          · have h31 := hPart.cd_symm 3 hi 1 hj hij
            exact False.elim (h13_not h31)
          · rfl
      }
      refine ⟨S, hSwap, ?_⟩
      apply Eliminated.ext
      have h_unused' : ∀ i < 4, boundaryKempeSwap degree4Config b θ S i ≠ b 1 := by
        intro i hi
        dsimp [boundaryKempeSwap, S]
        have hi4 : i < 4 := hi
        if hi0 : i = 0 then
          subst hi0; dsimp; exact h01
        else if hi1 : i = 1 then
          subst hi1; dsimp; dsimp [θ, ColorPairing.swap]
          rw [if_neg (Ne.symm h01), if_neg (Ne.symm h21), if_pos rfl]
          exact h13.symm
        else if hi2 : i = 2 then
          subst hi2; dsimp; exact h21
        else
          have : i = 3 := by omega
          subst this; dsimp; exact h13.symm
      have hValSwapped := swap_preserves_valid degree4Config b θ equiv_ab equiv_cd S hb hPart hSwap
      exact deg4_extends_of_unused_color (boundaryKempeSwap degree4Config b θ S) hValSwapped (b 1) h_unused'
    · let S : Nat → Bool := fun i => i == 0
      have hSwap : IsValidSwapChoice degree4Config b θ equiv_ab equiv_cd S := {
        ring_only := by
          intro i hi
          have : i = 0 := Nat.eq_of_beq_eq_true hi
          subst this; decide
        respects_ab := by
          intro i hi j hj hij
          have h_col_i := hPart.ab_color i hi j hj hij
          have h_col_j := hPart.ab_color j hj i hi (hPart.ab_symm i hi j hj hij)
          dsimp [S]
          have hi4 : i < 4 := hi
          have hj4 : j < 4 := hj
          have hi_mem : i = 0 ∨ i = 2 := by
            if hi0 : i = 0 then exact Or.inl hi0
            else if hi1 : i = 1 then
              subst hi1; exfalso; cases h_col_i with | inl h => exact h01.symm h | inr h => exact h21.symm h
            else if hi2 : i = 2 then exact Or.inr hi2
            else
              have : i = 3 := by omega
              subst this; exfalso
              cases h_col_i with | inl h => exact h03.symm h | inr h => exact h23.symm h
          have hj_mem : j = 0 ∨ j = 2 := by
            if hj0 : j = 0 then exact Or.inl hj0
            else if hj1 : j = 1 then
              subst hj1; exfalso; cases h_col_j with | inl h => exact h01.symm h | inr h => exact h21.symm h
            else if hj2 : j = 2 then exact Or.inr hj2
            else
              have : j = 3 := by omega
              subst this; exfalso
              cases h_col_j with | inl h => exact h03.symm h | inr h => exact h23.symm h
          rcases hi_mem with rfl | rfl <;> rcases hj_mem with rfl | rfl
          · rfl
          · exact False.elim (h02_rel hij)
          · have h20 := hPart.ab_symm 2 hi 0 hj hij
            exact False.elim (h02_rel h20)
          · rfl
        respects_cd := by
          intro i hi j hj hij
          have h_col_i := hPart.cd_color i hi j hj hij
          have h_col_j := hPart.cd_color j hj i hi (hPart.cd_symm i hi j hj hij)
          dsimp [S]
          have hi_ne0 : i ≠ 0 := by
            intro h; subst h
            cases h_col_i with
            | inl h => exact h01 h
            | inr h => exact h03 h
          have hj_ne0 : j ≠ 0 := by
            intro h; subst h
            cases h_col_j with
            | inl h => exact h01 h
            | inr h => exact h03 h
          rw [beq_false_of_ne hi_ne0, beq_false_of_ne hj_ne0]
      }
      refine ⟨S, hSwap, ?_⟩
      apply Eliminated.ext
      have h_unused' : ∀ i < 4, boundaryKempeSwap degree4Config b θ S i ≠ b 0 := by
        intro i hi
        dsimp [boundaryKempeSwap, S]
        have hi4 : i < 4 := hi
        if hi0 : i = 0 then
          subst hi0; dsimp; dsimp [θ, ColorPairing.swap]
          rw [if_pos rfl]
          exact h02.symm
        else if hi1 : i = 1 then
          subst hi1; dsimp; exact h01.symm
        else if hi2 : i = 2 then
          subst hi2; dsimp; exact h02.symm
        else
          have : i = 3 := by omega
          subst this; dsimp; exact h03.symm
      have hValSwapped := swap_preserves_valid degree4Config b θ equiv_ab equiv_cd S hb hPart hSwap
      exact deg4_extends_of_unused_color (boundaryKempeSwap degree4Config b θ S) hValSwapped (b 0) h_unused'

/-- The degree-4 vertex configuration is unconditionally reducible. -/
theorem deg4_reducible : IsReducible degree4Config :=
  Or.inl deg4_d_reducible

end Math
