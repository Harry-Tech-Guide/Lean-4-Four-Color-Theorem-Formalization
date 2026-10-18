import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring

namespace Math

/-!
# Sanity Verification: Degree-5 Vertex Configuration is Provably NOT Reducible

This module formally verifies that Kempe's 1879 fallacy does NOT hold in our formalization:
1. The degree-5 vertex configuration has boundary colorings that cannot be directly extended (`deg5_bad_not_extensible`).
2. The degree-5 vertex configuration has NO contract edges, so it is provably NOT C-reducible (`deg5_not_c_reducible`).
3. Under chordless degree-5 Kempe boundary swaps, admissible swaps can only act uniformly on `{a, b}`,
   preserving the surjectivity of boundary colorings onto all 4 colors.
4. Hence, no Kempe chain transformation can eliminate the non-extensible coloring: `¬ IsDReducible degree5Config`.
5. Therefore, `¬ IsReducible degree5Config`.
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

theorem swapColor_eq_self_of_not_mem (col a b : Color) (h : ¬(col = a ∨ col = b)) :
    Hypermap.swapColor col a b = col := by
  revert h
  cases col <;> cases a <;> cases b <;> decide

def deg5AdversaryEquiv (b : BoundaryColoring degree5Config) (a b_col : Color) : Nat → Nat → Prop :=
  fun i j => (b i = a ∨ b i = b_col) ∧ (b j = a ∨ b j = b_col)

theorem deg5AdversaryEquiv_planar (b : BoundaryColoring degree5Config) (a b_col : Color) :
    IsPlanarRingPartition degree5Config b a b_col (deg5AdversaryEquiv b a b_col) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _ h; exact ⟨h, h⟩
  · intro i _ j _ h; exact ⟨h.2, h.1⟩
  · intro i _ j _ l _ hij hjl; exact ⟨hij.1, hjl.2⟩
  · intro i _ j _ h; exact h.1
  · intro i _ j _ _ hi hj; exact ⟨hi, hj⟩
  · intro i j l m _ _ _ _ hil hjm; exact ⟨hil.1, hjm.1⟩

theorem deg5_eliminated_not_surj (b : BoundaryColoring degree5Config)
    (hElim : Eliminated degree5Config b) :
    deg5_surj b → False := by
  induction hElim with
  | ext b' hExt =>
    intro hSurj
    exact deg5_bad_not_extensible b' hSurj hExt
  | kempe b' a b_col resp _ _ hValid _ ih =>
    intro hSurj
    let equiv := deg5AdversaryEquiv b' a b_col
    have hPlanar := deg5AdversaryEquiv_planar b' a b_col
    have hSwapChoice := hValid equiv hPlanar
    have ihNext := ih equiv hPlanar
    let S := resp equiv
    have hCases : (∀ i < 5, S i = false) ∨ (∀ i < 5, b' i = a ∨ b' i = b_col → S i = true) := by
      by_cases hAny : ∃ k < 5, S k = true
      · right
        rcases hAny with ⟨k, hk, hSk⟩
        intro i hi hMem_i
        have hMem_k := hSwapChoice.1 k hk hSk
        have hEquiv_ik : equiv i k := ⟨hMem_i, hMem_k⟩
        have hSeq : S i = S k := hSwapChoice.2 i hi k hk hEquiv_ik
        rw [hSeq, hSk]
      · left
        intro i hi
        by_cases hSi : S i = true
        · exact False.elim (hAny ⟨i, hi, hSi⟩)
        · cases h : S i with | true => contradiction | false => rfl
    cases hCases with
    | inl hAllFalse =>
      have hSurjNext : deg5_surj (boundaryKempeSwap degree5Config b' a b_col S) := by
        intro c
        rcases hSurj c with ⟨i, hi, hbi⟩
        refine ⟨i, hi, ?_⟩
        dsimp [boundaryKempeSwap]
        rw [hAllFalse i hi]
        dsimp
        exact hbi
      exact ihNext hSurjNext
    | inr hAllTrue =>
      have hSurjNext : deg5_surj (boundaryKempeSwap degree5Config b' a b_col S) := by
        intro c
        rcases hSurj (Hypermap.swapColor c a b_col) with ⟨i, hi, hbi⟩
        refine ⟨i, hi, ?_⟩
        dsimp [boundaryKempeSwap]
        by_cases hMem : b' i = a ∨ b' i = b_col
        · rw [hAllTrue i hi hMem]
          dsimp
          rw [hbi, Hypermap.swapColor_inv]
        · have hNotS : S i = false := by
            by_cases hSi : S i = true
            · exact False.elim (hMem (hSwapChoice.1 i hi hSi))
            · cases h : S i with | true => contradiction | false => rfl
          rw [hNotS]
          dsimp
          have hNotMem : ¬(Hypermap.swapColor c a b_col = a ∨ Hypermap.swapColor c a b_col = b_col) := by
            rw [hbi] at hMem
            exact hMem
          rw [swapColor_mem_iff] at hNotMem
          rw [hbi, swapColor_eq_self_of_not_mem c a b_col hNotMem]
      exact ihNext hSurjNext

theorem deg5_not_d_reducible : ¬ IsDReducible degree5Config := by
  intro hD
  have hElim := hD deg5BadColoring deg5BadColoring_valid
  exact deg5_eliminated_not_surj deg5BadColoring hElim deg5BadColoring_surj

theorem deg5_not_c_reducible : ¬ IsCReducible degree5Config := by
  intro ⟨hNonempty, _⟩
  dsimp [degree5Config] at hNonempty
  exact hNonempty rfl

/-- The degree-5 vertex configuration is NOT reducible under the main IsReducible definition. -/
theorem deg5_not_reducible : ¬ IsReducible degree5Config := by
  intro hRed
  cases hRed with
  | inl hD => exact deg5_not_d_reducible hD
  | inr hC => exact deg5_not_c_reducible hC

end Math
