import FourColorTheorem.Math.CheckerSoundness.InitialLive

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-!
# Stage D4.2: Unconditional Proof of `InitialLiveSpec` (`initialLiveSpec_of_wellFormed`)

This module proves that `initialLiveTotal (rconfOfConfig c earlier) pow3` satisfies
`InitialLiveSpec c earlier pow3` unconditionally for any configuration `c` with:
- `IsRingCycle c`
- `IsSoundEarlier c earlier`
- `IsWellFormedEarlier c earlier`
- `IsIrreflexiveAdj c`
- `c.ringSize ≤ 15` (when `pow3 = sharedPow3`)
-/

/-!
### Part 1: `ByteArray` Helpers for `zeros` and `setOrbitLive`
-/

private theorem byteArray_push_zero_get! (b : ByteArray)
    (hb : ∀ i, b.get! i = 0) (j : Nat) :
    (b.push 0).get! j = 0 := by
  have h_prev := hb j
  change (b.data.push 0)[j]! = 0
  change b.data[j]! = 0 at h_prev
  simp only [Array.getElem!_eq_getD, Array.getD] at h_prev ⊢
  split
  · next hj =>
    change (b.data.push 0)[j]'hj = 0
    rw [Array.getElem_push]
    split
    · next h_lt =>
      rw [dif_pos h_lt] at h_prev
      exact h_prev
    · rfl
  · rfl

private theorem foldl_push_zero_get! (L : List Nat) (b : ByteArray)
    (hb : ∀ i, b.get! i = 0) (j : Nat) :
    (List.foldl (fun b _ => b.push 0) b L).get! j = 0 := by
  induction L generalizing b with
  | nil => exact hb j
  | cons _ rest ih =>
    exact ih (b.push 0) (byteArray_push_zero_get! b hb)

/-- Every entry of `zeros n` is `0`. -/
theorem zeros_get! (n j : Nat) : (zeros n).get! j = 0 := by
  unfold zeros
  simp
  exact foldl_push_zero_get! (List.range' 0 n) (ByteArray.emptyWithCapacity n) (fun _ => rfl) j

/-- `zeros n` satisfies `ByteArrayBinary`. -/
theorem zeros_binary (n : Nat) : ByteArrayBinary (zeros n) :=
  fun j => Or.inl (zeros_get! n j)

theorem byteArray_set!_one_binary (a : ByteArray) (i : Nat) (h_bin : ByteArrayBinary a) :
    ByteArrayBinary (a.set! i 1) := by
  intro j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · right
      exact byteArray_get!_set!_self a i 1 hi
    · left
      change (a.data.set! i 1)[i]! = 0
      simp [hi]
      rfl
  · rw [byteArray_get!_set!_ne a i j 1 hij]
    exact h_bin j

theorem setOrbitLive_size (live : ByteArray) (orb : Orbit6) :
    (setOrbitLive live orb).size = live.size := by
  unfold setOrbitLive
  rw [byteArray_size_set!, byteArray_size_set!, byteArray_size_set!,
      byteArray_size_set!, byteArray_size_set!, byteArray_size_set!]

theorem setOrbitLive_binary (live : ByteArray) (orb : Orbit6) (h_bin : ByteArrayBinary live) :
    ByteArrayBinary (setOrbitLive live orb) := by
  unfold setOrbitLive
  exact byteArray_set!_one_binary _ orb.j5
    (byteArray_set!_one_binary _ orb.j4
      (byteArray_set!_one_binary _ orb.j3
        (byteArray_set!_one_binary _ orb.j2
          (byteArray_set!_one_binary _ orb.j1
            (byteArray_set!_one_binary _ orb.j0 h_bin)))))

theorem setOrbitLive_preserves_one (live : ByteArray) (orb : Orbit6) (j : Nat)
    (hj : (live.get! j == 1) = true) :
    ((setOrbitLive live orb).get! j == 1) = true := by
  unfold setOrbitLive
  exact byteArray_get!_set!_one_mono _ orb.j5 j
    (byteArray_get!_set!_one_mono _ orb.j4 j
      (byteArray_get!_set!_one_mono _ orb.j3 j
        (byteArray_get!_set!_one_mono _ orb.j2 j
          (byteArray_get!_set!_one_mono _ orb.j1 j
            (byteArray_get!_set!_one_mono _ orb.j0 j hj)))))

theorem setOrbitLive_preserves_allLive (live : ByteArray) (orb o : Orbit6)
    (h_live : orbitAllLive live o) :
    orbitAllLive (setOrbitLive live orb) o :=
  ⟨setOrbitLive_preserves_one live orb o.j0 h_live.1,
   setOrbitLive_preserves_one live orb o.j1 h_live.2.1,
   setOrbitLive_preserves_one live orb o.j2 h_live.2.2.1,
   setOrbitLive_preserves_one live orb o.j3 h_live.2.2.2.1,
   setOrbitLive_preserves_one live orb o.j4 h_live.2.2.2.2.1,
   setOrbitLive_preserves_one live orb o.j5 h_live.2.2.2.2.2⟩

theorem setOrbitLive_allLive (live : ByteArray) (orb : Orbit6)
    (h_bnd : orbitBounded live.size orb) :
    orbitAllLive (setOrbitLive live orb) orb := by
  unfold setOrbitLive orbitAllLive
  let l0 := live.set! orb.j0 1
  let l1 := l0.set! orb.j1 1
  let l2 := l1.set! orb.j2 1
  let l3 := l2.set! orb.j3 1
  let l4 := l3.set! orb.j4 1
  let l5 := l4.set! orb.j5 1
  have hs0 : l0.size = live.size := byteArray_size_set! live orb.j0 1
  have hs1 : l1.size = live.size := (byteArray_size_set! l0 orb.j1 1).trans hs0
  have hs2 : l2.size = live.size := (byteArray_size_set! l1 orb.j2 1).trans hs1
  have hs3 : l3.size = live.size := (byteArray_size_set! l2 orb.j3 1).trans hs2
  have hs4 : l4.size = live.size := (byteArray_size_set! l3 orb.j4 1).trans hs3
  have h0 : (l0.get! orb.j0 == 1) = true := by
    rw [byteArray_get!_set!_self live orb.j0 1 h_bnd.1]; rfl
  have h1 : (l1.get! orb.j1 == 1) = true := by
    rw [byteArray_get!_set!_self l0 orb.j1 1 (hs0.symm ▸ h_bnd.2.1)]; rfl
  have h2 : (l2.get! orb.j2 == 1) = true := by
    rw [byteArray_get!_set!_self l1 orb.j2 1 (hs1.symm ▸ h_bnd.2.2.1)]; rfl
  have h3 : (l3.get! orb.j3 == 1) = true := by
    rw [byteArray_get!_set!_self l2 orb.j3 1 (hs2.symm ▸ h_bnd.2.2.2.1)]; rfl
  have h4 : (l4.get! orb.j4 == 1) = true := by
    rw [byteArray_get!_set!_self l3 orb.j4 1 (hs3.symm ▸ h_bnd.2.2.2.2.1)]; rfl
  have h5 : (l5.get! orb.j5 == 1) = true := by
    rw [byteArray_get!_set!_self l4 orb.j5 1 (hs4.symm ▸ h_bnd.2.2.2.2.2)]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, h5⟩
  · exact byteArray_get!_set!_one_mono l4 orb.j5 orb.j0
      (byteArray_get!_set!_one_mono l3 orb.j4 orb.j0
        (byteArray_get!_set!_one_mono l2 orb.j3 orb.j0
          (byteArray_get!_set!_one_mono l1 orb.j2 orb.j0
            (byteArray_get!_set!_one_mono l0 orb.j1 orb.j0 h0))))
  · exact byteArray_get!_set!_one_mono l4 orb.j5 orb.j1
      (byteArray_get!_set!_one_mono l3 orb.j4 orb.j1
        (byteArray_get!_set!_one_mono l2 orb.j3 orb.j1
          (byteArray_get!_set!_one_mono l1 orb.j2 orb.j1 h1)))
  · exact byteArray_get!_set!_one_mono l4 orb.j5 orb.j2
      (byteArray_get!_set!_one_mono l3 orb.j4 orb.j2
        (byteArray_get!_set!_one_mono l2 orb.j3 orb.j2 h2))
  · exact byteArray_get!_set!_one_mono l4 orb.j5 orb.j3
      (byteArray_get!_set!_one_mono l3 orb.j4 orb.j3 h3)
  · exact byteArray_get!_set!_one_mono l4 orb.j5 orb.j4 h4

theorem setOrbitLive_get!_of_not_inOrbit6 (live : ByteArray) (orb : Orbit6) (j : Nat)
    (h_not : ¬ inOrbit6 orb j) :
    (setOrbitLive live orb).get! j = live.get! j := by
  have h0 : orb.j0 ≠ j := fun h => h_not (Or.inl h.symm)
  have h1 : orb.j1 ≠ j := fun h => h_not (Or.inr (Or.inl h.symm))
  have h2 : orb.j2 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inl h.symm)))
  have h3 : orb.j3 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inl h.symm))))
  have h4 : orb.j4 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.symm)))))
  have h5 : orb.j5 ≠ j := fun h => h_not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.symm)))))
  unfold setOrbitLive
  rw [byteArray_get!_set!_ne _ orb.j5 j 1 h5,
      byteArray_get!_set!_ne _ orb.j4 j 1 h4,
      byteArray_get!_set!_ne _ orb.j3 j 1 h3,
      byteArray_get!_set!_ne _ orb.j2 j 1 h2,
      byteArray_get!_set!_ne _ orb.j1 j 1 h1,
      byteArray_get!_set!_ne _ orb.j0 j 1 h0]

/-!
### Part 2: Boolean Guard Equivalences (`orbitBoundedBool`, `orbitsDisjointBool`, `checkValidRing`)
-/

theorem orbitBoundedBool_iff (N : Nat) (orb : Orbit6) :
    orbitBoundedBool N orb = true ↔ orbitBounded N orb := by
  unfold orbitBoundedBool orbitBounded
  simp [Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem inOrbit6Bool_iff (orb : Orbit6) (j : Nat) :
    inOrbit6Bool orb j = true ↔ inOrbit6 orb j := by
  unfold inOrbit6Bool inOrbit6
  simp [Bool.or_eq_true, decide_eq_true_eq, or_assoc]

theorem inOrbit6Bool_false_iff (orb : Orbit6) (j : Nat) :
    inOrbit6Bool orb j = false ↔ ¬ inOrbit6 orb j := by
  rw [← Bool.not_eq_true, inOrbit6Bool_iff]

theorem orbitsDisjointBool_iff (o1 o2 : Orbit6) :
    orbitsDisjointBool o1 o2 = true ↔ ∀ j, inOrbit6 o1 j → ¬ inOrbit6 o2 j := by
  unfold orbitsDisjointBool
  simp only [Bool.and_eq_true, Bool.not_eq_true', inOrbit6Bool_false_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ j hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  · intro h
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · exact h o1.j0 (Or.inl rfl)
    · exact h o1.j1 (Or.inr (Or.inl rfl))
    · exact h o1.j2 (Or.inr (Or.inr (Or.inl rfl)))
    · exact h o1.j3 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact h o1.j4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    · exact h o1.j5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

theorem orbitsDisjointBool_false_iff (o1 o2 : Orbit6) :
    orbitsDisjointBool o1 o2 = false ↔ ∃ j, inOrbit6 o1 j ∧ inOrbit6 o2 j := by
  constructor
  · intro h_f
    apply Classical.byContradiction
    intro h_no
    have h_all : ∀ j, inOrbit6 o1 j → ¬ inOrbit6 o2 j :=
      fun j hj1 hj2 => h_no ⟨j, hj1, hj2⟩
    have h_t := (orbitsDisjointBool_iff o1 o2).mpr h_all
    rw [h_t] at h_f
    contradiction
  · rintro ⟨j, hj1, hj2⟩
    cases h : orbitsDisjointBool o1 o2 with
    | false => rfl
    | true =>
      exact False.elim (((orbitsDisjointBool_iff o1 o2).mp h) j hj1 hj2)

theorem orbitDisjointFromList_iff (orb : Orbit6) (orbs : List Orbit6) :
    orbitDisjointFromList orb orbs = true ↔
      ∀ o ∈ orbs, ∀ j, inOrbit6 orb j → ¬ inOrbit6 o j := by
  unfold orbitDisjointFromList
  rw [List.all_eq_true]
  constructor
  · intro h o ho
    exact (orbitsDisjointBool_iff orb o).mp (h o ho)
  · intro h o ho
    exact (orbitsDisjointBool_iff orb o).mpr (h o ho)

theorem orbitDisjointFromList_false_iff (orb : Orbit6) (orbs : List Orbit6) :
    orbitDisjointFromList orb orbs = false ↔
      ∃ o ∈ orbs, ∃ j, inOrbit6 orb j ∧ inOrbit6 o j := by
  constructor
  · intro h_f
    apply Classical.byContradiction
    intro h_no
    have h_all : ∀ o ∈ orbs, ∀ j, inOrbit6 orb j → ¬ inOrbit6 o j :=
      fun o ho j hj1 hj2 => h_no ⟨o, ho, j, hj1, hj2⟩
    have h_t := (orbitDisjointFromList_iff orb orbs).mpr h_all
    rw [h_t] at h_f
    contradiction
  · rintro ⟨o, ho, j, hj1, hj2⟩
    cases h : orbitDisjointFromList orb orbs with
    | false => rfl
    | true =>
      exact False.elim (((orbitDisjointFromList_iff orb orbs).mp h) o ho j hj1 hj2)

/-- Under `IsSoundEarlier`, `IsWellFormedEarlier`, and `IsIrreflexiveAdj`,
    `checkValidRing (rconfOfConfig c earlier) b = true` iff `IsValidBoundaryColoring c b`. -/
theorem checkValidRing_iff_isValidBoundaryColoring (c : Configuration) (earlier : Array (Array Nat))
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (b : BoundaryColoring c) :
    checkValidRing (rconfOfConfig c earlier) b = true ↔ IsValidBoundaryColoring c b := by
  unfold checkValidRing rconfOfConfig IsValidBoundaryColoring
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  have h_r_le : c.ringSize ≤ c.totalNodes := by
    dsimp [Configuration.totalNodes]; omega
  constructor
  · intro h_chk i j hi hj hadj
    by_cases hij : i = j
    · subst hij
      have h_irr := h_irrefl i (by omega)
      rw [h_irr] at hadj
      contradiction
    · by_cases h_lt : j < i
      · have hj_in : j ∈ (earlier.getD i #[]).toList :=
          h_earlier.1 i (by omega) j h_lt (Or.inl hadj)
        exact (h_chk i hi j hj_in).symm
      · have hi_lt : i < j := by omega
        have hi_in : i ∈ (earlier.getD j #[]).toList :=
          h_earlier.1 j (by omega) i hi_lt (Or.inr hadj)
        exact h_chk j hj i hi_in
  · intro h_val i hi u hu
    rcases h_wf i (by omega) u hu with ⟨hu_lt, hadj⟩
    exact (h_val i u hi (by omega) hadj).symm

/-- Every `orbit6OfColoring r b0 pow3` has `orbitBoundedBool N = true` when `N = 3 ^ r`
    and `∀ idx < r, pow3.getD idx 0 = 3 ^ idx`. -/
theorem orbitBoundedBool_orbit6OfColoring (r : Nat) (b0 : Nat → Color) (pow3 : Array Nat)
    (N : Nat) (hN : N = 3 ^ r) (h_pow : ∀ idx < r, pow3.getD idx 0 = 3 ^ idx) :
    orbitBoundedBool N (orbit6OfColoring r b0 pow3) = true := by
  rw [orbitBoundedBool_iff, hN]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact permTraceAux_permDigit_lt_pow3 ⟨0, by decide⟩ r b0 pow3 h_pow
  · exact permTraceAux_permDigit_lt_pow3 ⟨1, by decide⟩ r b0 pow3 h_pow
  · exact permTraceAux_permDigit_lt_pow3 ⟨2, by decide⟩ r b0 pow3 h_pow
  · exact permTraceAux_permDigit_lt_pow3 ⟨3, by decide⟩ r b0 pow3 h_pow
  · exact permTraceAux_permDigit_lt_pow3 ⟨4, by decide⟩ r b0 pow3 h_pow
  · exact permTraceAux_permDigit_lt_pow3 ⟨5, by decide⟩ r b0 pow3 h_pow

/-!
### Part 3: Completeness of `enumBoundaryColorings`
-/

/-- Every boundary coloring `b : Nat → Color` agrees on `< r` with some element of `enumBoundaryColorings r`. -/
theorem exists_enumBoundaryColorings_agree (r : Nat) (b : Nat → Color) :
    ∃ b0 ∈ enumBoundaryColorings r, ∀ i < r, b0 i = b i := by
  induction r with
  | zero =>
    refine ⟨fun _ => Color.c0, List.mem_singleton.mpr rfl, ?_⟩
    intro i hi; omega
  | succ v ih =>
    rcases ih with ⟨b', hb'_mem, hb'_agree⟩
    refine ⟨setColorAt b' v (b v), ?_, ?_⟩
    · dsimp [enumBoundaryColorings]
      rw [List.mem_flatMap]
      refine ⟨b', hb'_mem, ?_⟩
      cases b v <;> simp
    · intro i hi
      dsimp [setColorAt]
      by_cases hiv : i = v
      · subst hiv; rw [if_pos rfl]
      · rw [if_neg hiv]
        exact hb'_agree i (by omega)

theorem initCol_congr (c : Configuration) (b1 b2 : BoundaryColoring c)
    (h : ∀ i < c.ringSize, b1 i = b2 i) :
    initCol c b1 = initCol c b2 := by
  dsimp [initCol]
  congr 1
  funext i
  split
  · next hi => rw [h i.val hi]
  · rfl

theorem isValidBoundaryColoring_congr (c : Configuration) (b1 b2 : BoundaryColoring c)
    (h : ∀ i < c.ringSize, b1 i = b2 i) :
    IsValidBoundaryColoring c b1 ↔ IsValidBoundaryColoring c b2 := by
  constructor
  · intro hb1 i j hi hj hadj
    rw [← h i hi, ← h j hj]
    exact hb1 i j hi hj hadj
  · intro hb2 i j hi hj hadj
    rw [h i hi, h j hj]
    exact hb2 i j hi hj hadj

theorem permTraceAux_congr_coloring (p : Nat → Nat) (r : Nat) (hr : r > 0)
    (b1 b2 : Nat → Color) (h : ∀ i < r, b1 i = b2 i)
    (pow3 : Array Nat) (rem i acc : Nat) (h_le : i + rem ≤ r) :
    permTraceAux p r b1 pow3 rem i acc = permTraceAux p r b2 pow3 rem i acc := by
  induction rem generalizing i acc with
  | zero => rfl
  | succ rem ih =>
    have hi : i < r := by omega
    have hnxt : (i + 1) % r < r := Nat.mod_lt (i + 1) hr
    dsimp [permTraceAux]
    rw [h i hi, h ((i + 1) % r) hnxt]
    exact ih (i + 1) _ (by omega)

theorem boundaryTrace_congr_coloring (c : Configuration) (hr : c.ringSize > 0)
    (b1 b2 : BoundaryColoring c) (h : ∀ i < c.ringSize, b1 i = b2 i) (pow3 : Array Nat) :
    boundaryTrace c b1 pow3 = boundaryTrace c b2 pow3 := by
  rw [boundaryTrace_eq_permTraceAux_zero c b1 pow3,
      boundaryTrace_eq_permTraceAux_zero c b2 pow3]
  exact permTraceAux_congr_coloring _ c.ringSize hr b1 b2 h pow3 c.ringSize 0 0 (by omega)

/-!
### Part 4: Accumulator Invariant Across `initialLiveStep` and `initialLiveLoop`
-/

/-- Complete invariant of the `(live, orbits)` accumulator during `initialLiveLoop`. -/
structure InitAccInv (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (N : Nat) (acc : ByteArray × Array Orbit6) : Prop where
  nodup     : acc.2.toList.Nodup
  disjoint  : ∀ o₁ ∈ acc.2.toList, ∀ o₂ ∈ acc.2.toList,
                o₁ ≠ o₂ → ∀ j, inOrbit6 o₁ j → ¬ inOrbit6 o₂ j
  allLive   : ∀ o ∈ acc.2.toList, orbitAllLive acc.1 o
  bounded   : ∀ o ∈ acc.2.toList, orbitBounded N o
  liveSize  : acc.1.size = N
  binary    : ByteArrayBinary acc.1
  zero_not  : ∀ j, (∀ o ∈ acc.2.toList, ¬ inOrbit6 o j) → acc.1.get! j = 0
  orbit_src : ∀ o ∈ acc.2.toList, ∃ b0 : BoundaryColoring c,
                IsValidBoundaryColoring c b0 ∧
                (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1 = false ∧
                o = orbit6OfColoring c.ringSize b0 pow3

private theorem nodup_append_singleton_init {α : Type} {L : List α} {a : α}
    (hL : L.Nodup) (ha : a ∉ L) : (L ++ [a]).Nodup := by
  induction L with
  | nil =>
    rw [List.nil_append, List.nodup_cons]
    exact ⟨List.not_mem_nil, List.nodup_nil⟩
  | cons x xs ih =>
    rcases List.nodup_cons.mp hL with ⟨hx_not_xs, h_nodup_xs⟩
    have ha_ne_x : a ≠ x := fun h => ha (h ▸ List.mem_cons_self ..)
    have ha_not_xs : a ∉ xs := fun h => ha (List.mem_cons_of_mem x h)
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, ih h_nodup_xs ha_not_xs⟩
    rw [List.mem_append, List.mem_singleton]
    rintro (h_in_xs | h_eq)
    · exact hx_not_xs h_in_xs
    · exact ha_ne_x h_eq.symm

/-- `InitAccInv` holds at the initial accumulator `(zeros N, #[])`. -/
theorem initAccInv_empty (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (N : Nat) :
    InitAccInv c earlier pow3 N (zeros N, #[]) where
  nodup     := List.nodup_nil
  disjoint  := by intro _ h; cases h
  allLive   := by intro _ h; cases h
  bounded   := by intro _ h; cases h
  liveSize  := zeros_size N
  binary    := zeros_binary N
  zero_not  := fun j _ => zeros_get! N j
  orbit_src := by intro _ h; cases h

/-- `initialLiveStep` preserves membership in `.2.toList`. -/
theorem mem_initialLiveStep_of_mem (rc : RConf) (pow3 : Array Nat) (N : Nat)
    (b0 : Nat → Color) (acc : ByteArray × Array Orbit6) (o : Orbit6)
    (ho : o ∈ acc.2.toList) :
    o ∈ (initialLiveStep rc pow3 N b0 acc).2.toList := by
  dsimp [initialLiveStep]
  split
  · split
    · rw [Array.toList_push]
      exact List.mem_append_left _ ho
    · exact ho
  · exact ho

/-- `initialLiveLoop` preserves membership in `.2.toList`. -/
theorem mem_initialLiveLoop_of_mem (rc : RConf) (pow3 : Array Nat) (N : Nat)
    (L : List (Nat → Color)) (acc : ByteArray × Array Orbit6) (o : Orbit6)
    (ho : o ∈ acc.2.toList) :
    o ∈ (initialLiveLoop rc pow3 N L acc).2.toList := by
  induction L generalizing acc with
  | nil => exact ho
  | cons b0 rest ih =>
    dsimp [initialLiveLoop]
    exact ih _ (mem_initialLiveStep_of_mem rc pow3 N b0 acc o ho)

/-- `initialLiveStep` preserves `InitAccInv`. -/
theorem initialLiveStep_inv (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (N : Nat)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (b0 : Nat → Color) (acc : ByteArray × Array Orbit6)
    (h_inv : InitAccInv c earlier pow3 N acc) :
    InitAccInv c earlier pow3 N (initialLiveStep (rconfOfConfig c earlier) pow3 N b0 acc) := by
  dsimp [initialLiveStep]
  by_cases h_cand :
      (checkValidRing (rconfOfConfig c earlier) b0 &&
       !(FastReducer.extend (rconfOfConfig c earlier).earlier
          (rconfOfConfig c earlier).n (rconfOfConfig c earlier).r
          (initColRConf (rconfOfConfig c earlier) b0)).1) = true
  · rw [if_pos h_cand]
    let orb := orbit6OfColoring c.ringSize b0 pow3
    by_cases h_guard : (orbitBoundedBool N orb && orbitDisjointFromList orb acc.2.toList) = true
    · change InitAccInv c earlier pow3 N
        (if (orbitBoundedBool N orb && orbitDisjointFromList orb acc.2.toList) = true then
          (setOrbitLive acc.1 orb, acc.2.push orb) else acc)
      rw [if_pos h_guard]
      rcases Bool.and_eq_true_iff.mp h_cand with ⟨h_chk_val, h_not_ext_b⟩
      have hb0 : IsValidBoundaryColoring c b0 :=
        (checkValidRing_iff_isValidBoundaryColoring c earlier h_earlier h_wf h_irrefl b0).mp h_chk_val
      have h_ext_false : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1 = false := by
        change (!(FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1) = true at h_not_ext_b
        cases h : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1 with
        | false => rfl
        | true => rw [h] at h_not_ext_b; contradiction
      rcases Bool.and_eq_true_iff.mp h_guard with ⟨h_bnd_b, h_disj_b⟩
      have h_bnd_orb : orbitBounded N orb := (orbitBoundedBool_iff N orb).mp h_bnd_b
      have h_disj_orb : ∀ o ∈ acc.2.toList, ∀ j, inOrbit6 orb j → ¬ inOrbit6 o j :=
        (orbitDisjointFromList_iff orb acc.2.toList).mp h_disj_b
      have h_orb_not_mem : orb ∉ acc.2.toList := by
        intro h_mem
        exact h_disj_orb orb h_mem orb.j0 (Or.inl rfl) (Or.inl rfl)
      refine {
        nodup := ?_
        disjoint := ?_
        allLive := ?_
        bounded := ?_
        liveSize := ?_
        binary := setOrbitLive_binary acc.1 orb h_inv.binary
        zero_not := ?_
        orbit_src := ?_
      }
      · dsimp
        rw [Array.toList_push]
        exact nodup_append_singleton_init h_inv.nodup h_orb_not_mem
      · intro o1 h1 o2 h2 hne j hj1
        dsimp at h1 h2
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at h1 h2
        rcases h1 with h1_acc | rfl <;> rcases h2 with h2_acc | rfl
        · exact h_inv.disjoint o1 h1_acc o2 h2_acc hne j hj1
        · exact fun hj2 => h_disj_orb o1 h1_acc j hj2 hj1
        · exact h_disj_orb o2 h2_acc j hj1
        · exact False.elim (hne rfl)
      · intro o ho
        dsimp at ho ⊢
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at ho
        rcases ho with ho_acc | rfl
        · exact setOrbitLive_preserves_allLive acc.1 orb o (h_inv.allLive o ho_acc)
        · apply setOrbitLive_allLive acc.1 orb
          rw [h_inv.liveSize]
          exact h_bnd_orb
      · intro o ho
        dsimp at ho
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at ho
        rcases ho with ho_acc | rfl
        · exact h_inv.bounded o ho_acc
        · exact h_bnd_orb
      · dsimp
        rw [setOrbitLive_size, h_inv.liveSize]
      · intro j h_not_all
        dsimp at h_not_all ⊢
        have h_not_orb : ¬ inOrbit6 orb j := by
          apply h_not_all orb
          rw [Array.toList_push, List.mem_append, List.mem_singleton]
          exact Or.inr rfl
        have h_not_acc : ∀ o ∈ acc.2.toList, ¬ inOrbit6 o j := by
          intro o ho
          apply h_not_all o
          rw [Array.toList_push, List.mem_append]
          exact Or.inl ho
        rw [setOrbitLive_get!_of_not_inOrbit6 acc.1 orb j h_not_orb]
        exact h_inv.zero_not j h_not_acc
      · intro o ho
        dsimp at ho
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at ho
        rcases ho with ho_acc | rfl
        · exact h_inv.orbit_src o ho_acc
        · exact ⟨b0, hb0, h_ext_false, rfl⟩
    · change InitAccInv c earlier pow3 N
        (if (orbitBoundedBool N orb && orbitDisjointFromList orb acc.2.toList) = true then
          (setOrbitLive acc.1 orb, acc.2.push orb) else acc)
      rw [if_neg h_guard]
      exact h_inv
  · rw [if_neg h_cand]
    exact h_inv

/-- `initialLiveLoop` preserves `InitAccInv`. -/
theorem initialLiveLoop_inv (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (N : Nat)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (L : List (Nat → Color)) (acc : ByteArray × Array Orbit6)
    (h_inv : InitAccInv c earlier pow3 N acc) :
    InitAccInv c earlier pow3 N (initialLiveLoop (rconfOfConfig c earlier) pow3 N L acc) := by
  induction L generalizing acc with
  | nil => exact h_inv
  | cons b0 rest ih =>
    dsimp [initialLiveLoop]
    exact ih _ (initialLiveStep_inv c earlier pow3 N h_earlier h_wf h_irrefl b0 acc h_inv)

/-- When a valid non-extendable boundary coloring `b0` is processed by `initialLiveStep`,
     the resulting orbit list contains an orbit covering `boundaryTrace c b0 pow3`. -/
theorem initialLiveStep_covers_nonext (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (N : Nat)
    (hN : N = 3 ^ c.ringSize)
    (h_pow : ∀ idx < c.ringSize, pow3.getD idx 0 = 3 ^ idx)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (acc : ByteArray × Array Orbit6)
    (h_inv : InitAccInv c earlier pow3 N acc)
    (b0 : BoundaryColoring c)
    (hb0 : IsValidBoundaryColoring c b0)
    (h_ext : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1 = false) :
    ∃ orb ∈ (initialLiveStep (rconfOfConfig c earlier) pow3 N b0 acc).2.toList,
      inOrbit6 orb (boundaryTrace c b0 pow3) := by
  have h_chk_val : checkValidRing (rconfOfConfig c earlier) b0 = true :=
    (checkValidRing_iff_isValidBoundaryColoring c earlier h_earlier h_wf h_irrefl b0).mpr hb0
  have h_cand :
      (checkValidRing (rconfOfConfig c earlier) b0 &&
       !(FastReducer.extend (rconfOfConfig c earlier).earlier
          (rconfOfConfig c earlier).n (rconfOfConfig c earlier).r
          (initColRConf (rconfOfConfig c earlier) b0)).1) = true := by
    rw [Bool.and_eq_true]
    refine ⟨h_chk_val, ?_⟩
    change (!(FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1) = true
    rw [h_ext]
    rfl
  let orb := orbit6OfColoring c.ringSize b0 pow3
  have h_bnd : orbitBoundedBool N orb = true :=
    orbitBoundedBool_orbit6OfColoring c.ringSize b0 pow3 N hN h_pow
  have hj0 : inOrbit6 orb (boundaryTrace c b0 pow3) := by
    rw [boundaryTrace_eq_permTraceAux_zero c b0 pow3]
    exact Or.inl rfl
  dsimp [initialLiveStep]
  rw [if_pos h_cand]
  cases h_disj : orbitDisjointFromList orb acc.2.toList with
  | true =>
    have h_guard : (orbitBoundedBool N orb && orbitDisjointFromList orb acc.2.toList) = true := by
      rw [h_bnd, h_disj]; rfl
    change ∃ o ∈ (if (orbitBoundedBool N orb && orbitDisjointFromList orb acc.2.toList) = true then
        (setOrbitLive acc.1 orb, acc.2.push orb) else acc).2.toList,
      inOrbit6 o (boundaryTrace c b0 pow3)
    rw [if_pos h_guard]
    refine ⟨orb, ?_, hj0⟩
    dsimp
    rw [Array.toList_push, List.mem_append, List.mem_singleton]
    exact Or.inr rfl
  | false =>
    have h_guard : ¬ ((orbitBoundedBool N orb && orbitDisjointFromList orb acc.2.toList) = true) := by
      rw [h_bnd, h_disj]; decide
    change ∃ o ∈ (if (orbitBoundedBool N orb && orbitDisjointFromList orb acc.2.toList) = true then
        (setOrbitLive acc.1 orb, acc.2.push orb) else acc).2.toList,
      inOrbit6 o (boundaryTrace c b0 pow3)
    rw [if_neg h_guard]
    rcases (orbitDisjointFromList_false_iff orb acc.2.toList).mp h_disj with ⟨o, ho, j, hj_orb, hj_o⟩
    rcases h_inv.orbit_src o ho with ⟨b1, _, _, rfl⟩
    refine ⟨orbit6OfColoring c.ringSize b1 pow3, ho, ?_⟩
    exact inOrbit6_orbit6OfColoring_trans c.ringSize b0 b1 pow3 h_pow j (boundaryTrace c b0 pow3)
      hj_orb hj_o hj0

/-- If `b0 ∈ L` is a valid non-extendable boundary coloring, `initialLiveLoop` produces an orbit
    covering `boundaryTrace c b0 pow3`. -/
theorem initialLiveLoop_covers_mem (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (N : Nat)
    (hN : N = 3 ^ c.ringSize)
    (h_pow : ∀ idx < c.ringSize, pow3.getD idx 0 = 3 ^ idx)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (L : List (Nat → Color)) (acc : ByteArray × Array Orbit6)
    (h_inv : InitAccInv c earlier pow3 N acc)
    (b0 : BoundaryColoring c) (hb0_mem : b0 ∈ L)
    (hb0 : IsValidBoundaryColoring c b0)
    (h_ext : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1 = false) :
    ∃ orb ∈ (initialLiveLoop (rconfOfConfig c earlier) pow3 N L acc).2.toList,
      inOrbit6 orb (boundaryTrace c b0 pow3) := by
  induction L generalizing acc with
  | nil => contradiction
  | cons hd tl ih =>
    dsimp [initialLiveLoop]
    rcases List.mem_cons.mp hb0_mem with rfl | h_in_tl
    · rcases initialLiveStep_covers_nonext c earlier pow3 N hN h_pow h_earlier h_wf h_irrefl
        acc h_inv b0 hb0 h_ext with ⟨orb, horb, hj⟩
      exact ⟨orb, mem_initialLiveLoop_of_mem (rconfOfConfig c earlier) pow3 N tl _ orb horb, hj⟩
    · exact ih (initialLiveStep (rconfOfConfig c earlier) pow3 N hd acc)
        (initialLiveStep_inv c earlier pow3 N h_earlier h_wf h_irrefl hd acc h_inv) h_in_tl

/-!
### Part 5: Main Theorem D4.2 (`initialLiveSpec_of_wellFormed`)
-/

/-- **Main Theorem D4.2 (`initialLiveSpec_of_wellFormed`):**
    For any configuration `c` with `IsRingCycle c`, `IsSoundEarlier c earlier`,
    `IsWellFormedEarlier c earlier`, `IsIrreflexiveAdj c`, and `pow3` agreeing with `3 ^ i`
    on `0 .. c.ringSize`, `InitialLiveSpec c earlier pow3` holds unconditionally. -/
theorem initialLiveSpec_of_wellFormed (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat)
    (h_ring : IsRingCycle c)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (hN_pow : pow3.getD c.ringSize 1 = 3 ^ c.ringSize)
    (h_pow : ∀ idx < c.ringSize, pow3.getD idx 0 = 3 ^ idx) :
    InitialLiveSpec c earlier pow3 := by
  let rc := rconfOfConfig c earlier
  let N := pow3.getD rc.r 1
  have hN : N = 3 ^ c.ringSize := hN_pow
  have h_final_inv : InitAccInv c earlier pow3 N (initialLiveTotal rc pow3) :=
    initialLiveLoop_inv c earlier pow3 N h_earlier h_wf h_irrefl
      (enumBoundaryColorings rc.r) (zeros N, #[])
      (initAccInv_empty c earlier pow3 N)
  refine {
    init_inv := fun sms =>
      reducerInv_of_init_props N (initialLiveTotal rc pow3).1 (initialLiveTotal rc pow3).2 sms
        h_final_inv.nodup h_final_inv.disjoint h_final_inv.allLive h_final_inv.bounded h_final_inv.liveSize
    live_binary := h_final_inv.binary
    ext_live_zero := ?_
    nonext_in_orbit := ?_
    relabel_same_orbit := ?_
    pairing_cover_orbit := ?_
  }
  · dsimp
    intro b hb h_ext
    have h_not_in : ∀ orb ∈ (initialLiveTotal rc pow3).2.toList, ¬ inOrbit6 orb (boundaryTrace c b pow3) := by
      intro orb horb h_in
      rcases h_final_inv.orbit_src orb horb with ⟨b0, hb0, h_ext0, rfl⟩
      rcases (inOrbit6_orbit6OfColoring_digits_iff c b b0 pow3 h_pow).mp h_in with ⟨k, hk⟩
      have h_eq := extend_eq_of_edge_digits c earlier h_ring h_earlier h_wf h_irrefl b b0 hb hb0 k hk
      rw [h_ext, h_ext0] at h_eq
      contradiction
    exact ⟨h_final_inv.zero_not (boundaryTrace c b pow3) h_not_in, h_not_in⟩
  · dsimp
    intro b hb h_ext
    rcases exists_enumBoundaryColorings_agree c.ringSize b with ⟨b0, hb0_mem, hb0_agree⟩
    have hb0 : IsValidBoundaryColoring c b0 :=
      (isValidBoundaryColoring_congr c b0 b hb0_agree).mpr hb
    have h_ext0 : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1 = false := by
      rw [initCol_congr c b0 b hb0_agree]
      exact h_ext
    have hr_pos : c.ringSize > 0 := by have := h_ring.1; omega
    rw [← boundaryTrace_congr_coloring c hr_pos b0 b hb0_agree pow3]
    exact initialLiveLoop_covers_mem c earlier pow3 N hN h_pow h_earlier h_wf h_irrefl
      (enumBoundaryColorings c.ringSize) (zeros N, #[])
      (initAccInv_empty c earlier pow3 N) b0 hb0_mem hb0 h_ext0
  · dsimp
    intro b θ orb hb horb
    rcases h_final_inv.orbit_src orb horb with ⟨b0, _, _, rfl⟩
    exact relabel_same_orbit_of_orbit6OfColoring c h_ring b b0 hb pow3 h_pow θ
  · dsimp
    intro b orb hb horb h_in j_a j_b h_pair
    rcases h_final_inv.orbit_src orb horb with ⟨b0, _, _, rfl⟩
    exact pairing_cover_orbit_of_orbit6OfColoring c h_ring b b0 hb pow3 h_pow h_in j_a j_b h_pair

private theorem sharedPow3_getD_zero (i : Nat) (hi : i ≤ 15) :
    sharedPow3.getD i 0 = 3 ^ i := by
  have h := (sharedPow3_getD i hi).2
  rwa [Array.getElem!_eq_getD] at h

/-- Specialization of `initialLiveSpec_of_wellFormed` to `sharedPow3` for any configuration
    with `c.ringSize ≤ 15`. -/
theorem initialLiveSpec_sharedPow3_of_wellFormed (c : Configuration) (earlier : Array (Array Nat))
    (h_ring : IsRingCycle c)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (hr_le : c.ringSize ≤ 15) :
    InitialLiveSpec c earlier sharedPow3 :=
  initialLiveSpec_of_wellFormed c earlier sharedPow3 h_ring h_earlier h_wf h_irrefl
    (sharedPow3_getD c.ringSize hr_le).1
    (fun idx h_lt => sharedPow3_getD_zero idx (by omega))

end CheckerSoundness
end Math
