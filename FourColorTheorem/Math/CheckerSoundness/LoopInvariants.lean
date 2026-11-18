module

public import FourColorTheorem.Math.CheckerSoundness.TraceSymmetry

@[expose] public section

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false

/-!
# Stage D1: Complete State Invariants of `reducerStep` and `runReducerLoop`

This module bundles the structural invariants of `ReducerState` into `ReducerInv N st`
and proves:
1. Preservation of `ReducerInv N st` across `reducerStep` (`reducerStep_inv`) and
   `runReducerLoop` (`runReducerLoop_inv`).
2. Rank freezing for non-live traces (`dead_rank_frozen`).
3. Round decomposition (`exists_eliminating_round_decomp`) and the combined rank-decrease
   and orbit-rank-equality theorems (`eliminated_orbit_rank_eq`,
   `eliminated_orbit_sm_strict_rank_decrease`) for any orbit eliminated during `runReducerLoop`.
-/

/-- Complete invariant of `ReducerState` across `reducerStep` and `runReducerLoop`. -/
structure ReducerInv (N : Nat) (st : ReducerState) : Prop where
  nodup     : st.orbits.toList.Nodup
  disjoint  : ∀ o₁ ∈ st.orbits.toList, ∀ o₂ ∈ st.orbits.toList,
                o₁ ≠ o₂ → ∀ j, inOrbit6 o₁ j → ¬ inOrbit6 o₂ j
  allLive   : ∀ o ∈ st.orbits.toList, orbitAllLive st.live o
  bounded   : ∀ o ∈ st.orbits.toList, orbitBounded st.live.size o ∧ orbitBounded st.ranks.size o
  rankLe    : ∀ j, st.ranks.getD j 0 ≤ st.iter
  liveSize  : st.live.size = N
  ranksSize : st.ranks.size = N

private theorem nodup_append_singleton {α : Type} {L : List α} {a : α}
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

/-- `stepOrbitsList` preserves `Nodup` of the accumulated orbit list when `orbs` is `Nodup`
    and disjoint from `nextOrbits.toList`. -/
theorem stepOrbitsList_nodup (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (h_acc : nextOrbits.toList.Nodup)
    (h_orbs : orbs.Nodup)
    (h_disj : ∀ o ∈ nextOrbits.toList, o ∉ orbs) :
    (stepOrbitsList cover iter orbs nextOrbits live ranks).1.toList.Nodup := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => exact h_acc
  | cons orb0 rest ih =>
    rcases List.nodup_cons.mp h_orbs with ⟨h_not_rest, h_nodup_rest⟩
    have h_disj_rest : ∀ o ∈ nextOrbits.toList, o ∉ rest := by
      intro o ho h_in_rest
      exact h_disj o ho (List.mem_cons_of_mem orb0 h_in_rest)
    dsimp [stepOrbitsList]
    split
    · have h_orb0_not_acc : orb0 ∉ nextOrbits.toList := by
        intro h_in_acc
        exact h_disj orb0 h_in_acc (List.mem_cons_self ..)
      have h_acc' : (nextOrbits.push orb0).toList.Nodup := by
        rw [Array.toList_push]
        exact nodup_append_singleton h_acc h_orb0_not_acc
      have h_disj' : ∀ o ∈ (nextOrbits.push orb0).toList, o ∉ rest := by
        intro o ho
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at ho
        rcases ho with h_in_acc | rfl
        · exact h_disj_rest o h_in_acc
        · exact h_not_rest
      exact ih (nextOrbits.push orb0) live ranks h_acc' h_nodup_rest h_disj'
    · exact ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter)
        h_acc h_nodup_rest h_disj_rest

/-- If `orbitAllLive live o` holds and `o` is disjoint from `orb0`, then
    `orbitAllLive (clearOrbitLive live orb0) o` still holds. -/
theorem orbitAllLive_clearOrbitLive_of_disjoint (live : ByteArray) (o orb0 : Orbit6)
    (h_live : orbitAllLive live o)
    (h_disj : ∀ j, inOrbit6 o j → ¬ inOrbit6 orb0 j) :
    orbitAllLive (clearOrbitLive live orb0) o := by
  have h0 : ¬ inOrbit6 orb0 o.j0 := h_disj o.j0 (Or.inl rfl)
  have h1 : ¬ inOrbit6 orb0 o.j1 := h_disj o.j1 (Or.inr (Or.inl rfl))
  have h2 : ¬ inOrbit6 orb0 o.j2 := h_disj o.j2 (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : ¬ inOrbit6 orb0 o.j3 := h_disj o.j3 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : ¬ inOrbit6 orb0 o.j4 := h_disj o.j4 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : ¬ inOrbit6 orb0 o.j5 := h_disj o.j5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  unfold orbitAllLive at h_live ⊢
  rw [clearOrbitLive_get!_of_not_inOrbit6 live orb0 o.j0 h0,
      clearOrbitLive_get!_of_not_inOrbit6 live orb0 o.j1 h1,
      clearOrbitLive_get!_of_not_inOrbit6 live orb0 o.j2 h2,
      clearOrbitLive_get!_of_not_inOrbit6 live orb0 o.j3 h3,
      clearOrbitLive_get!_of_not_inOrbit6 live orb0 o.j4 h4,
      clearOrbitLive_get!_of_not_inOrbit6 live orb0 o.j5 h5]
  exact h_live

/-- `stepOrbitsList` preserves `orbitAllLive` for every retained orbit when all orbits in
    `nextOrbits.toList ++ orbs` are pairwise disjoint and initially `orbitAllLive`. -/
theorem stepOrbitsList_allLive (cover : ByteArray) (iter : Nat)
    (orbs : List Orbit6) (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (h_orbs_nodup : orbs.Nodup)
    (h_acc_disj : ∀ o ∈ nextOrbits.toList, o ∉ orbs)
    (h_disj : ∀ o₁ ∈ nextOrbits.toList ++ orbs, ∀ o₂ ∈ nextOrbits.toList ++ orbs,
      o₁ ≠ o₂ → ∀ j, inOrbit6 o₁ j → ¬ inOrbit6 o₂ j)
    (h_live : ∀ o ∈ nextOrbits.toList ++ orbs, orbitAllLive live o) :
    ∀ o ∈ (stepOrbitsList cover iter orbs nextOrbits live ranks).1.toList,
      orbitAllLive (stepOrbitsList cover iter orbs nextOrbits live ranks).2.1 o := by
  induction orbs generalizing nextOrbits live ranks with
  | nil =>
    intro o ho
    dsimp [stepOrbitsList] at ho ⊢
    exact h_live o (List.mem_append_left [] ho)
  | cons orb0 rest ih =>
    rcases List.nodup_cons.mp h_orbs_nodup with ⟨h_not_rest, h_nodup_rest⟩
    dsimp [stepOrbitsList]
    split
    · have h_acc_disj' : ∀ o ∈ (nextOrbits.push orb0).toList, o ∉ rest := by
        intro o ho
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at ho
        rcases ho with h_in_acc | rfl
        · intro h_in_rest
          exact h_acc_disj o h_in_acc (List.mem_cons_of_mem orb0 h_in_rest)
        · exact h_not_rest
      have h_mem_eq : ∀ o, o ∈ (nextOrbits.push orb0).toList ++ rest ↔ o ∈ nextOrbits.toList ++ orb0 :: rest := by
        intro o
        rw [Array.toList_push, List.append_assoc, List.singleton_append]
      exact ih (nextOrbits.push orb0) live ranks h_nodup_rest h_acc_disj'
        (fun o1 h1 o2 h2 => h_disj o1 ((h_mem_eq o1).mp h1) o2 ((h_mem_eq o2).mp h2))
        (fun o ho => h_live o ((h_mem_eq o).mp ho))
    · have h_acc_disj' : ∀ o ∈ nextOrbits.toList, o ∉ rest := by
        intro o ho h_in_rest
        exact h_acc_disj o ho (List.mem_cons_of_mem orb0 h_in_rest)
      have h_sub : ∀ o ∈ nextOrbits.toList ++ rest, o ∈ nextOrbits.toList ++ orb0 :: rest := by
        intro o ho
        rw [List.mem_append] at ho ⊢
        rcases ho with h_l | h_r
        · exact Or.inl h_l
        · exact Or.inr (List.mem_cons_of_mem orb0 h_r)
      have h_live' : ∀ o ∈ nextOrbits.toList ++ rest, orbitAllLive (clearOrbitLive live orb0) o := by
        intro o ho
        have ho_full : o ∈ nextOrbits.toList ++ orb0 :: rest := h_sub o ho
        have horb0_full : orb0 ∈ nextOrbits.toList ++ orb0 :: rest :=
          List.mem_append_right _ (List.mem_cons_self ..)
        have h_ne : o ≠ orb0 := by
          rintro rfl
          rw [List.mem_append] at ho
          rcases ho with h_in_acc | h_in_rest
          · exact h_acc_disj o h_in_acc (List.mem_cons_self ..)
          · exact h_not_rest h_in_rest
        exact orbitAllLive_clearOrbitLive_of_disjoint live o orb0 (h_live o ho_full)
          (h_disj o ho_full orb0 horb0_full h_ne)
      exact ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter)
        h_nodup_rest h_acc_disj'
        (fun o1 h1 o2 h2 => h_disj o1 (h_sub o1 h1) o2 (h_sub o2 h2))
        h_live'

/-- `reducerStep` preserves `ReducerInv N`. -/
theorem reducerStep_inv (N : Nat) (st : ReducerState) (h : ReducerInv N st) :
    ReducerInv N (reducerStep N st) := by
  refine {
    nodup := ?_
    disjoint := ?_
    allLive := ?_
    bounded := ?_
    rankLe := reducerStep_ranks_le_iter N st h.rankLe
    liveSize := by rw [reducerStep_live_size, h.liveSize]
    ranksSize := by rw [reducerStep_ranks_size, h.ranksSize]
  }
  · dsimp [reducerStep]
    exact stepOrbitsList_nodup _ _ st.orbits.toList (Array.mkEmpty st.orbits.size) st.live st.ranks
      List.nodup_nil h.nodup (by intro o ho; cases ho)
  · intro o1 h1 o2 h2 hne j hj
    exact h.disjoint o1 (reducerStep_orbits_sub N st o1 h1) o2 (reducerStep_orbits_sub N st o2 h2) hne j hj
  · dsimp [reducerStep]
    exact stepOrbitsList_allLive _ _ st.orbits.toList (Array.mkEmpty st.orbits.size) st.live st.ranks
      h.nodup (by intro o ho; cases ho)
      (by
        intro o1 h1 o2 h2 hne
        change o1 ∈ st.orbits.toList at h1
        change o2 ∈ st.orbits.toList at h2
        exact h.disjoint o1 h1 o2 h2 hne)
      (by
        intro o ho
        change o ∈ st.orbits.toList at ho
        exact h.allLive o ho)
  · intro o ho
    rw [reducerStep_live_size, reducerStep_ranks_size]
    exact h.bounded o (reducerStep_orbits_sub N st o ho)

/-- `runReducerLoop` preserves `ReducerInv N`. -/
theorem runReducerLoop_inv (N fuel : Nat) (st : ReducerState) (h : ReducerInv N st) :
    ReducerInv N (runReducerLoop N fuel st) := by
  induction fuel generalizing st with
  | zero => exact h
  | succ fuel ih =>
    dsimp [runReducerLoop]
    split
    · exact ih (reducerStep N st) (reducerStep_inv N st h)
    · exact h

/-- Any trace `j` that is not live at state `st` (under `ReducerInv N st`) has its rank
    frozen across `runReducerLoop N fuel st`, and that final rank is `≤ st.iter`. -/
theorem dead_rank_frozen (N fuel : Nat) (st : ReducerState)
    (h_inv : ReducerInv N st) (j : Nat) (h_dead : (st.live.get! j == 1) = false) :
    (runReducerLoop N fuel st).ranks.getD j 0 = st.ranks.getD j 0 ∧
    (runReducerLoop N fuel st).ranks.getD j 0 ≤ st.iter := by
  have h_not_in : ∀ orb ∈ st.orbits.toList, ¬ inOrbit6 orb j :=
    fun orb h_mem => not_inOrbit6_of_not_live st.live orb j (h_inv.allLive orb h_mem) h_dead
  have h_eq := runReducerLoop_ranks_preserves_of_not_in_orbits N fuel st j h_not_in
  exact ⟨h_eq, h_eq ▸ h_inv.rankLe j⟩

/-- **Exact Round Decomposition for Eliminated Orbits:**
    If `orb ∈ st.orbits.toList`, `orb ∉ (runReducerLoop N fuel st).orbits.toList`, and `ReducerInv N st`,
    then there exist a round state `st_k` and remaining fuel `rem` such that:
    1. `runReducerLoop N fuel st = runReducerLoop N rem (reducerStep N st_k)`
    2. `ReducerInv N st_k`
    3. `orb ∈ st_k.orbits.toList`
    4. `orb` is uncovered at `st_k`
    5. Every `sm ∈ st.activeSM.toList` satisfies the active-SM invariant at `st_k`. -/
theorem exists_eliminating_round_decomp (N fuel : Nat) (st : ReducerState)
    (h_inv : ReducerInv N st)
    (orb : Orbit6) (horb : orb ∈ st.orbits.toList)
    (h_not_mem : orb ∉ (runReducerLoop N fuel st).orbits.toList) :
    ∃ (st_k : ReducerState) (rem : Nat),
      runReducerLoop N fuel st = runReducerLoop N rem (reducerStep N st_k) ∧
      ReducerInv N st_k ∧
      orb ∈ st_k.orbits.toList ∧
      (let cov := (stepSMList st_k.live st_k.activeSM.toList (zeros N) (Array.mkEmpty st_k.activeSM.size)).1
       orbitCovered cov orb = false) ∧
      (∀ sm ∈ st.activeSM.toList,
        sm ∈ st_k.activeSM.toList ∨ ∃ t < 1 <<< sm.p, (st_k.live.get! (smFitIndex sm t) == 1) = false) ∧
      (∀ j, (st.live.get! j == 1) = false → (st_k.live.get! j == 1) = false) := by
  induction fuel generalizing st with
  | zero =>
    dsimp [runReducerLoop] at h_not_mem
    exact False.elim (h_not_mem horb)
  | succ fuel ih =>
    dsimp [runReducerLoop] at h_not_mem ⊢
    by_cases h_cond : (st.changed && !st.orbits.isEmpty) = true
    · rw [if_pos h_cond] at h_not_mem ⊢
      rcases stepOrbitsList_retained_or_uncovered
          (stepSMList st.live st.activeSM.toList (zeros N) (Array.mkEmpty st.activeSM.size)).1
          (st.iter + 1) st.orbits.toList (Array.mkEmpty st.orbits.size) st.live st.ranks
          orb horb with h_ret | h_uncov
      · rcases ih (reducerStep N st) (reducerStep_inv N st h_inv) h_ret h_not_mem with
          ⟨st_k, rem, h_loop_eq, h_inv_k, horb_k, h_uncov_k, h_sm_k, h_mono_k⟩
        refine ⟨st_k, rem, h_loop_eq, h_inv_k, horb_k, h_uncov_k, ?_, ?_⟩
        · intro sm hsm
          rcases retained_or_not_live_of_reducerStep N st sm hsm with h_sm_ret | ⟨t, ht, h_dead⟩
          · exact h_sm_k sm h_sm_ret
          · right
            exact ⟨t, ht, h_mono_k (smFitIndex sm t) h_dead⟩
        · intro j hj
          exact h_mono_k j (reducerStep_not_live_mono N st j hj)
      · exact ⟨st, fuel, rfl, h_inv, horb, h_uncov, fun sm hsm => Or.inl hsm, fun _ hj => hj⟩
    · rw [if_neg h_cond] at h_not_mem
      exact False.elim (h_not_mem horb)

/-- **Corollary 1 (Uniform Orbit Final Rank & S₃-Invariance on Eliminated Orbits):**
    Under `ReducerInv N st`, if `orb ∈ st.orbits.toList` is not in `(runReducerLoop N fuel st).orbits.toList`,
    then all 6 trace indices `j1, j2` of `orb` receive the exact same positive final rank
    in `(runReducerLoop N fuel st).ranks`. -/
theorem eliminated_orbit_rank_eq (N fuel : Nat) (st : ReducerState)
    (h_inv : ReducerInv N st)
    (orb : Orbit6) (horb : orb ∈ st.orbits.toList)
    (h_not_mem : orb ∉ (runReducerLoop N fuel st).orbits.toList)
    (j1 j2 : Nat) (hj1 : inOrbit6 orb j1) (hj2 : inOrbit6 orb j2) :
    (runReducerLoop N fuel st).ranks.getD j1 0 = (runReducerLoop N fuel st).ranks.getD j2 0 ∧
    (runReducerLoop N fuel st).ranks.getD j1 0 > 0 := by
  rcases exists_eliminating_round_decomp N fuel st h_inv orb horb h_not_mem with
    ⟨st_k, rem, h_loop_eq, h_inv_k, horb_k, h_uncov_k, _, _⟩
  have h_bnd := h_inv_k.bounded orb horb_k
  have hr1 := (eliminated_orb_final_rank_and_live N rem st_k orb horb_k
    h_inv_k.nodup h_inv_k.disjoint h_bnd.2 h_bnd.1 h_uncov_k j1 hj1).1
  have hr2 := (eliminated_orb_final_rank_and_live N rem st_k orb horb_k
    h_inv_k.nodup h_inv_k.disjoint h_bnd.2 h_bnd.1 h_uncov_k j2 hj2).1
  rw [h_loop_eq, hr1, hr2]
  exact ⟨rfl, by omega⟩

/-- If `a.isEmpty = true`, then no element belongs to `a.toList`. -/
theorem not_mem_toList_of_isEmpty {α : Type} (a : Array α) (h_empty : a.isEmpty = true) (x : α) :
    x ∉ a.toList := by
  intro hx
  rw [not_isEmpty_of_mem_toList a x hx] at h_empty
  contradiction

/-- When `(runReducerLoop N fuel st).orbits.isEmpty = true` and `ReducerInv N st`,
    any two indices `j1, j2` belonging to the same initial orbit `orb ∈ st.orbits.toList`
    receive equal positive final rank in `(runReducerLoop N fuel st).ranks`. -/
theorem orbits_empty_rank_eq_of_same_orbit (N fuel : Nat) (st : ReducerState)
    (h_inv : ReducerInv N st)
    (h_empty : (runReducerLoop N fuel st).orbits.isEmpty = true)
    (orb : Orbit6) (horb : orb ∈ st.orbits.toList)
    (j1 j2 : Nat) (hj1 : inOrbit6 orb j1) (hj2 : inOrbit6 orb j2) :
    (runReducerLoop N fuel st).ranks.getD j1 0 = (runReducerLoop N fuel st).ranks.getD j2 0 ∧
    (runReducerLoop N fuel st).ranks.getD j1 0 > 0 :=
  eliminated_orbit_rank_eq N fuel st h_inv orb horb
    (not_mem_toList_of_isEmpty (runReducerLoop N fuel st).orbits h_empty orb)
    j1 j2 hj1 hj2

/-- When `st.ranks` is initially all zero (`∀ j, st.ranks.getD j 0 = 0`), any trace `j` not belonging
    to any orbit in `st.orbits.toList` has final rank `0` after `runReducerLoop N fuel st`. -/
theorem rank_zero_of_not_in_orbits (N fuel : Nat) (st : ReducerState)
    (h_zero : ∀ j, st.ranks.getD j 0 = 0)
    (j : Nat) (h_not : ∀ orb ∈ st.orbits.toList, ¬ inOrbit6 orb j) :
    (runReducerLoop N fuel st).ranks.getD j 0 = 0 := by
  rw [runReducerLoop_ranks_preserves_of_not_in_orbits N fuel st j h_not]
  exact h_zero j

end CheckerSoundness
end Math
