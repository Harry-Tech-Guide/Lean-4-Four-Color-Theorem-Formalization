import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring

namespace Math

/-!
# Degree-4 Vertex Configuration Analysis: Kempe Reducibility vs Adversarial Formalization

This module investigates the degree-4 vertex configuration (a 4-cycle ring with one
interior vertex adjacent to all 4 ring vertices, with no contract edges), modeled on
`Degree5.lean`.

## Findings on `IsPlanarRingPartition` and `Eliminated`:
In Kempe's classical 1879 argument for a degree-4 vertex:
For any ring coloring using all 4 colors, opposite vertices (0, 2) have colors (a, c)
and opposite vertices (1, 3) have colors (b, d).
In any planar exterior graph, if (0, 2) are connected by an (a, c) Kempe chain,
then by the Jordan Curve Theorem, (1, 3) CANNOT be connected by a (b, d) Kempe chain.
Hence, the reducer adapts by swapping either (0, 2) or (1, 3).

HOWEVER, in the current formalization (`Reducibility.lean`):
1. In `Eliminated.kempe`:
   The reducer must choose a single pair of colors `(a, b_col)` OUTSIDE the universal
   quantifier `∀ (equiv : Nat → Nat → Prop)`. The reducer cannot adaptively choose
   the color pair after observing the exterior connectivity.
2. In `IsPlanarRingPartition`:
   The equivalence relation `equiv` is restricted by condition 4 to only relate vertices
   colored in `{a, b_col}`: `equiv i j → (b i = a ∨ b i = b_col)`.
   Consequently, condition 6 (`equiv i l → equiv j m → equiv i j`) is vacuously true
   whenever vertices `j` and `m` have colors outside `{a, b_col}`.
   Thus, for any chosen pair `(a, b_col)`, the adversary can always legally present the
   universal relation `equiv i j := (b i = a ∨ b i = b_col) ∧ (b j = a ∨ b j = b_col)`,
   forcing ALL vertices of colors {a, b_col} into a single equivalence class.
3. Under this adversarial relation, the only valid swap choices either do nothing or
   swap all vertices of colors {a, b_col} simultaneously (a global transposition on Color).
   This preserves surjectivity of the boundary coloring onto all 4 colors.
4. Since no surjective boundary coloring can extend to an interior vertex adjacent to all
   4 ring vertices, NO surjective boundary coloring can ever be eliminated!

Therefore, under the current definitions of `IsPlanarRingPartition` and `Eliminated`,
the degree-4 configuration is provably NOT reducible: `¬ IsReducible degree4Config`.
Proving `IsReducible degree4Config` unconditionally would require either:
- A joint planar topology linking all 4 colors (e.g. Gonthier's signed matchings / hypermaps), or
- Allowing the reducer's color choice to depend on the exterior graph's Kempe connectivity.
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

/-- A boundary coloring using all 4 colors on the 4-ring. -/
def deg4BadColoring : BoundaryColoring degree4Config := fun i =>
  if i == 0 then Color.c0
  else if i == 1 then Color.c1
  else if i == 2 then Color.c2
  else Color.c3

def checkDeg4Valid : Bool :=
  (List.range 4).all (fun i =>
    (List.range 4).all (fun j =>
      if degree4Config.adj i j then deg4BadColoring i != deg4BadColoring j else true))

theorem checkDeg4Valid_true : checkDeg4Valid = true := by rfl

theorem deg4BadColoring_valid : IsValidBoundaryColoring degree4Config deg4BadColoring := by
  intro i j hi hj hadj
  have hi_mem : i ∈ List.range 4 := List.mem_range.mpr hi
  have hj_mem : j ∈ List.range 4 := List.mem_range.mpr hj
  have h_all_i := List.all_eq_true.mp checkDeg4Valid_true i hi_mem
  have h_all_j := List.all_eq_true.mp h_all_i j hj_mem
  rw [hadj] at h_all_j
  intro h_eq
  rw [h_eq] at h_all_j
  simp at h_all_j

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

def deg4_surj (b : BoundaryColoring degree4Config) : Prop :=
  ∀ c : Color, ∃ i < 4, b i = c

theorem deg4BadColoring_surj : deg4_surj deg4BadColoring := by
  intro c
  cases c with
  | c0 => exact ⟨0, by decide, rfl⟩
  | c1 => exact ⟨1, by decide, rfl⟩
  | c2 => exact ⟨2, by decide, rfl⟩
  | c3 => exact ⟨3, by decide, rfl⟩

theorem deg4_bad_not_extensible (b : BoundaryColoring degree4Config)
    (h_surj : deg4_surj b) :
    ¬ extendsToInterior degree4Config b := by
  intro ⟨full, hmatch, hvalid⟩
  have ⟨i0, hi0, hb0⟩ := h_surj Color.c0
  have ⟨i1, hi1, hb1⟩ := h_surj Color.c1
  have ⟨i2, hi2, hb2⟩ := h_surj Color.c2
  have ⟨i3, hi3, hb3⟩ := h_surj Color.c3
  have hf0 : full i0 = Color.c0 := by rw [hmatch i0 hi0, hb0]
  have hf1 : full i1 = Color.c1 := by rw [hmatch i1 hi1, hb1]
  have hf2 : full i2 = Color.c2 := by rw [hmatch i2 hi2, hb2]
  have hf3 : full i3 = Color.c3 := by rw [hmatch i3 hi3, hb3]
  have hadj0 : degree4Config.adj 4 i0 = true := by
    dsimp [degree4Config, deg4Adj]; simp; omega
  have hadj1 : degree4Config.adj 4 i1 = true := by
    dsimp [degree4Config, deg4Adj]; simp; omega
  have hadj2 : degree4Config.adj 4 i2 = true := by
    dsimp [degree4Config, deg4Adj]; simp; omega
  have hadj3 : degree4Config.adj 4 i3 = true := by
    dsimp [degree4Config, deg4Adj]; simp; omega
  have hv0 := hvalid 4 i0 (by decide) (by dsimp [degree4Config, Configuration.totalNodes]; omega) hadj0
  have hv1 := hvalid 4 i1 (by decide) (by dsimp [degree4Config, Configuration.totalNodes]; omega) hadj1
  have hv2 := hvalid 4 i2 (by decide) (by dsimp [degree4Config, Configuration.totalNodes]; omega) hadj2
  have hv3 := hvalid 4 i3 (by decide) (by dsimp [degree4Config, Configuration.totalNodes]; omega) hadj3
  rw [hf0] at hv0; rw [hf1] at hv1; rw [hf2] at hv2; rw [hf3] at hv3
  cases h4 : full 4 with
  | c0 => exact hv0 h4
  | c1 => exact hv1 h4
  | c2 => exact hv2 h4
  | c3 => exact hv3 h4

theorem swapColor_eq_self_of_not_mem (col a b : Color) (h : ¬(col = a ∨ col = b)) :
    Hypermap.swapColor col a b = col := by
  revert h
  cases col <;> cases a <;> cases b <;> decide

def deg4AdversaryEquiv (b : BoundaryColoring degree4Config) (a b_col : Color) : Nat → Nat → Prop :=
  fun i j => (b i = a ∨ b i = b_col) ∧ (b j = a ∨ b j = b_col)

theorem deg4AdversaryEquiv_planar (b : BoundaryColoring degree4Config) (a b_col : Color) :
    IsPlanarRingPartition degree4Config b a b_col (deg4AdversaryEquiv b a b_col) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _ h; exact ⟨h, h⟩
  · intro i _ j _ h; exact ⟨h.2, h.1⟩
  · intro i _ j _ l _ hij hjl; exact ⟨hij.1, hjl.2⟩
  · intro i _ j _ h; exact h.1
  · intro i _ j _ _ hi hj; exact ⟨hi, hj⟩
  · intro i j l m _ _ _ _ hil hjm; exact ⟨hil.1, hjm.1⟩

theorem deg4_eliminated_not_surj (b : BoundaryColoring degree4Config)
    (hElim : Eliminated degree4Config b) :
    deg4_surj b → False := by
  induction hElim with
  | ext b' hExt =>
    intro hSurj
    exact deg4_bad_not_extensible b' hSurj hExt
  | kempe b' a b_col resp _ _ hValid _ ih =>
    intro hSurj
    let equiv := deg4AdversaryEquiv b' a b_col
    have hPlanar := deg4AdversaryEquiv_planar b' a b_col
    have hSwapChoice := hValid equiv hPlanar
    have ihNext := ih equiv hPlanar
    let S := resp equiv
    have hCases : (∀ i < 4, S i = false) ∨ (∀ i < 4, b' i = a ∨ b' i = b_col → S i = true) := by
      by_cases hAny : ∃ k < 4, S k = true
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
      have hSurjNext : deg4_surj (boundaryKempeSwap degree4Config b' a b_col S) := by
        intro c
        rcases hSurj c with ⟨i, hi, hbi⟩
        refine ⟨i, hi, ?_⟩
        dsimp [boundaryKempeSwap]
        rw [hAllFalse i hi]
        dsimp
        exact hbi
      exact ihNext hSurjNext
    | inr hAllTrue =>
      have hSurjNext : deg4_surj (boundaryKempeSwap degree4Config b' a b_col S) := by
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

theorem deg4_not_d_reducible : ¬ IsDReducible degree4Config := by
  intro hD
  have hElim := hD deg4BadColoring deg4BadColoring_valid
  exact deg4_eliminated_not_surj deg4BadColoring hElim deg4BadColoring_surj

theorem deg4_not_c_reducible : ¬ IsCReducible degree4Config := by
  intro ⟨hNonempty, _⟩
  dsimp [degree4Config] at hNonempty
  exact hNonempty rfl

/-- The degree-4 vertex configuration is provably NOT reducible under the current
    IsPlanarRingPartition / Eliminated definitions. -/
theorem deg4_not_reducible : ¬ IsReducible degree4Config := by
  intro hRed
  cases hRed with
  | inl hD => exact deg4_not_d_reducible hD
  | inr hC => exact deg4_not_c_reducible hC

end Math
