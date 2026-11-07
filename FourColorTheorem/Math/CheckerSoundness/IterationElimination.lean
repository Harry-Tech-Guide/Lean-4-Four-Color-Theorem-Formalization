import FourColorTheorem.Math.CheckerSoundness.InitialLive

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false

/-!
# Stage D3: Reducing `LiveZeroIterationEliminationHypothesis` and `IterationEliminationHypothesis` to `InitialLiveSpec`

This module combines the loop invariants from `LoopInvariants.lean` (Stage D1) and the initial-state
specification `InitialLiveSpec` from `InitialLive.lean` (Stage D2) to prove:

1. **`liveZeroIterationElimination_of_initialLiveSpec`:** Reduces
   `LiveZeroIterationEliminationHypothesis c earlier sms pow3` (used by C-reducibility in `CReduce.lean`)
   to `InitialLiveSpec` and the structural `earlier`/`adj` predicates.
2. **`all_valid_liveZero_of_checkFastTotal`:** When `checkFastTotal (rconfOfConfig c earlier) sms pow3 = true`,
   every valid boundary coloring `b` satisfies `LiveZero` in the final state under `InitialLiveSpec`.
3. **`iterationElimination_of_checkFastTotal`:** Reduces `IterationEliminationHypothesis c earlier sms pow3`
   (used by D-reducibility in `DReduce.lean`) to `InitialLiveSpec` and `checkFastTotal = true`.
4. **`fast_d_sound_of_initialLiveSpec` & `fast_c_sound_of_initialLiveSpec`:** D- and C-reducibility
   theorems replacing `IterationEliminationHypothesis` and `LiveZeroIterationEliminationHypothesis`
   with `InitialLiveSpec` (`InitialLiveSpec` is itself an open obligation for Stage D4).
-/

/-- If `live.get! j = 0`, then `(live.get! j == 1) = false`. -/
theorem beq_one_false_of_eq_zero {b : UInt8} (h : b = 0) : (b == 1) = false := by
  subst h; rfl

/-- If `live.get! j = 0` and all orbits in `orbs` satisfy `orbitAllLive live`, then `j`
    does not belong to any orbit in `orbs`. -/
theorem not_in_orbits_of_live_zero (live : ByteArray) (orbs : List Orbit6)
    (h_allLive : ∀ o ∈ orbs, orbitAllLive live o)
    (j : Nat) (hj_zero : live.get! j = 0) :
    ∀ o ∈ orbs, ¬ inOrbit6 o j := by
  intro o ho
  exact not_inOrbit6_of_not_live live o j (h_allLive o ho) (beq_one_false_of_eq_zero hj_zero)

/-- Under `InitialLiveSpec`, if `orb ∈ orbits0.toList` is not in `(computeFinalState rc sms pow3).orbits.toList`,
    then every member `j` of `orb` has `(computeFinalState rc sms pow3).live.get! j = 0`. -/
theorem final_live_zero_of_orbit_eliminated (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_init : InitialLiveSpec c earlier sms pow3)
    (orb : Orbit6)
    (horb : orb ∈ (initialLiveFast (rconfOfConfig c earlier) pow3).2.toList)
    (h_not_mem : orb ∉ (computeFinalState (rconfOfConfig c earlier) sms pow3).orbits.toList)
    (j : Nat) (hj : inOrbit6 orb j) :
    (computeFinalState (rconfOfConfig c earlier) sms pow3).live.get! j = 0 := by
  let rc := rconfOfConfig c earlier
  let N := pow3.getD rc.r 1
  let initSt : ReducerState := {
    live := (initialLiveFast rc pow3).1
    orbits := (initialLiveFast rc pow3).2
    activeSM := sms
    ranks := Array.replicate N 0
    iter := 0
    changed := true
  }
  change orb ∉ (runReducerLoop N ((initialLiveFast rc pow3).2.size + 1) initSt).orbits.toList at h_not_mem
  change (runReducerLoop N ((initialLiveFast rc pow3).2.size + 1) initSt).live.get! j = 0
  rcases exists_eliminating_round_decomp N ((initialLiveFast rc pow3).2.size + 1) initSt h_init.init_inv
      orb horb h_not_mem with ⟨st_k, rem, h_loop_eq, h_inv_k, horb_k, h_uncov_k, _, _⟩
  have h_bnd := h_inv_k.bounded orb horb_k
  rw [h_loop_eq]
  exact (eliminated_orb_final_rank_and_live N rem st_k orb horb_k
    h_inv_k.nodup h_inv_k.disjoint h_bnd.2 h_bnd.1 h_uncov_k j hj).2

/-- **S₃-Invariance of Final `LiveZero` and `computeEliminationRanks` on Valid Boundary Colorings:**
    If `b'` is a valid boundary coloring whose `θ`-relabelled trace `boundaryTraceTheta c b' θ pow3`
    has `finalSt.live.get! = 0`, then `b'` itself satisfies `LiveZero` (`finalSt.live.get! (boundaryTrace c b' pow3) = 0`)
    and `boundaryTrace c b' pow3` has the exact same final rank in `computeEliminationRanks` as
    `boundaryTraceTheta c b' θ pow3`. -/
theorem relabelBoundary_ranks_eq_and_liveZero (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_init : InitialLiveSpec c earlier sms pow3)
    (b' : BoundaryColoring c) (hb' : IsValidBoundaryColoring c b')
    (θ : ColorPairing)
    (h_lz_theta : (computeFinalState (rconfOfConfig c earlier) sms pow3).live.get! (boundaryTraceTheta c b' θ pow3) = 0) :
    LiveZero c pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live b' ∧
    (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b' pow3) 0 =
      (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTraceTheta c b' θ pow3) 0 := by
  let rc := rconfOfConfig c earlier
  let N := pow3.getD rc.r 1
  let initSt : ReducerState := {
    live := (initialLiveFast rc pow3).1
    orbits := (initialLiveFast rc pow3).2
    activeSM := sms
    ranks := Array.replicate N 0
    iter := 0
    changed := true
  }
  have h_final_inv : ReducerInv N (computeFinalState rc sms pow3) :=
    runReducerLoop_inv N ((initialLiveFast rc pow3).2.size + 1) initSt h_init.init_inv
  cases h_ext : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b')).1 with
  | true =>
    have hb'_theta : IsValidBoundaryColoring c (relabelBoundary θ b') :=
      relabelBoundary_valid c b' θ hb'
    have h_ext_theta : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c (relabelBoundary θ b'))).1 = true := by
      rw [extend_relabelBoundary_eq c earlier h_earlier h_wf h_irrefl b' hb' θ]
      exact h_ext
    have h_ext0 := h_init.ext_live_zero b' hb' h_ext
    have h_ext0_theta := h_init.ext_live_zero (relabelBoundary θ b') hb'_theta h_ext_theta
    have h_lz_b' : LiveZero c pow3 (computeFinalState rc sms pow3).live b' := by
      unfold LiveZero computeFinalState
      exact runReducerLoop_preserves_zero N ((initialLiveFast rc pow3).2.size + 1) initSt
        (boundaryTrace c b' pow3) h_ext0.1
    have h_zero_init : ∀ j, initSt.ranks.getD j 0 = 0 := fun j => array_replicate_zero_getD N j
    have hr1 : (computeEliminationRanks rc sms pow3).getD (boundaryTrace c b' pow3) 0 = 0 :=
      rank_zero_of_not_in_orbits N ((initialLiveFast rc pow3).2.size + 1) initSt
        h_zero_init (boundaryTrace c b' pow3) h_ext0.2
    have hr2 : (computeEliminationRanks rc sms pow3).getD (boundaryTraceTheta c b' θ pow3) 0 = 0 :=
      rank_zero_of_not_in_orbits N ((initialLiveFast rc pow3).2.size + 1) initSt
        h_zero_init (boundaryTraceTheta c b' θ pow3) h_ext0_theta.2
    exact ⟨h_lz_b', hr1.trans hr2.symm⟩
  | false =>
    rcases h_init.nonext_in_orbit b' hb' h_ext with ⟨orb', horb', hj1⟩
    have hj2 : inOrbit6 orb' (boundaryTraceTheta c b' θ pow3) :=
      (h_init.relabel_same_orbit b' θ orb' hb' horb').mp hj1
    have h_not_mem : orb' ∉ (computeFinalState rc sms pow3).orbits.toList := by
      intro h_in_final
      exact not_in_orbits_of_live_zero (computeFinalState rc sms pow3).live
        (computeFinalState rc sms pow3).orbits.toList h_final_inv.allLive
        (boundaryTraceTheta c b' θ pow3) h_lz_theta orb' h_in_final hj2
    have h_lz_b' : LiveZero c pow3 (computeFinalState rc sms pow3).live b' :=
      final_live_zero_of_orbit_eliminated c earlier sms pow3 h_init orb' horb' h_not_mem
        (boundaryTrace c b' pow3) hj1
    have h_rank_eq := (eliminated_orbit_rank_eq N ((initialLiveFast rc pow3).2.size + 1) initSt
      h_init.init_inv orb' horb' h_not_mem
      (boundaryTrace c b' pow3) (boundaryTraceTheta c b' θ pow3) hj1 hj2).1
    exact ⟨h_lz_b', h_rank_eq⟩

theorem eq_zero_of_beq_one_false_of_binary {a : ByteArray} (h_bin : ByteArrayBinary a)
    {j : Nat} (h_false : (a.get! j == 1) = false) :
    a.get! j = 0 := by
  rcases h_bin j with h0 | h1
  · exact h0
  · rw [h1] at h_false
    contradiction

theorem byteArray_set!_zero_binary (a : ByteArray) (i : Nat) (h_bin : ByteArrayBinary a) :
    ByteArrayBinary (a.set! i 0) := by
  intro j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i < a.size
    · left
      exact byteArray_get!_set!_self a i 0 hi
    · left
      change (a.data.set! i 0)[i]! = 0
      simp [hi]
      rfl
  · rw [byteArray_get!_set!_ne a i j 0 hij]
    exact h_bin j

theorem clearOrbitLive_binary (live : ByteArray) (orb : Orbit6) (h_bin : ByteArrayBinary live) :
    ByteArrayBinary (clearOrbitLive live orb) := by
  unfold clearOrbitLive
  exact byteArray_set!_zero_binary _ orb.j5
    (byteArray_set!_zero_binary _ orb.j4
      (byteArray_set!_zero_binary _ orb.j3
        (byteArray_set!_zero_binary _ orb.j2
          (byteArray_set!_zero_binary _ orb.j1
            (byteArray_set!_zero_binary _ orb.j0 h_bin)))))

theorem stepOrbitsList_binary (cover : ByteArray) (iter : Nat) (orbs : List Orbit6)
    (nextOrbits : Array Orbit6) (live : ByteArray) (ranks : Array Nat)
    (h_bin : ByteArrayBinary live) :
    ByteArrayBinary (stepOrbitsList cover iter orbs nextOrbits live ranks).2.1 := by
  induction orbs generalizing nextOrbits live ranks with
  | nil => exact h_bin
  | cons orb0 rest ih =>
    dsimp [stepOrbitsList]
    split
    · exact ih (nextOrbits.push orb0) live ranks h_bin
    · exact ih nextOrbits (clearOrbitLive live orb0) (setOrbitRanks ranks orb0 iter)
        (clearOrbitLive_binary live orb0 h_bin)

theorem reducerStep_binary (N : Nat) (st : ReducerState) (h_bin : ByteArrayBinary st.live) :
    ByteArrayBinary (reducerStep N st).live := by
  dsimp [reducerStep]
  exact stepOrbitsList_binary _ _ _ _ _ _ h_bin

theorem runReducerLoop_binary (N fuel : Nat) (st : ReducerState) (h_bin : ByteArrayBinary st.live) :
    ByteArrayBinary (runReducerLoop N fuel st).live := by
  induction fuel generalizing st with
  | zero => exact h_bin
  | succ fuel ih =>
    dsimp [runReducerLoop]
    split
    · exact ih (reducerStep N st) (reducerStep_binary N st h_bin)
    · exact h_bin

/-- **Main Theorem D3.1 (`liveZeroIterationElimination_of_initialLiveSpec`):**
    Under `IsSoundEarlier`, `IsWellFormedEarlier`, `IsIrreflexiveAdj`, and `InitialLiveSpec`,
    `LiveZeroIterationEliminationHypothesis` holds. `InitialLiveSpec` is itself an
    open obligation (Stage D4). -/
theorem liveZeroIterationElimination_of_initialLiveSpec (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_init : InitialLiveSpec c earlier sms pow3) :
    LiveZeroIterationEliminationHypothesis c earlier sms pow3 := by
  let rc := rconfOfConfig c earlier
  let N := pow3.getD rc.r 1
  let initSt : ReducerState := {
    live := (initialLiveFast rc pow3).1
    orbits := (initialLiveFast rc pow3).2
    activeSM := sms
    ranks := Array.replicate N 0
    iter := 0
    changed := true
  }
  have h_final_inv : ReducerInv N (computeFinalState rc sms pow3) :=
    runReducerLoop_inv N ((initialLiveFast rc pow3).2.size + 1) initSt h_init.init_inv
  have h_final_bin : ByteArrayBinary (computeFinalState rc sms pow3).live :=
    runReducerLoop_binary N ((initialLiveFast rc pow3).2.size + 1) initSt h_init.live_binary
  intro b hb h_lz hr_pos
  have h_not_ext : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = false := by
    cases h : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 with
    | true =>
      dsimp [constructedRank] at hr_pos
      rw [h] at hr_pos
      contradiction
    | false => rfl
  rcases h_init.nonext_in_orbit b hb h_not_ext with ⟨orb, horb, hj_b⟩
  have h_not_mem : orb ∉ (computeFinalState rc sms pow3).orbits.toList := by
    intro h_in_final
    exact not_in_orbits_of_live_zero (computeFinalState rc sms pow3).live
      (computeFinalState rc sms pow3).orbits.toList h_final_inv.allLive
      (boundaryTrace c b pow3) h_lz orb h_in_final hj_b
  rcases exists_eliminating_round_decomp N ((initialLiveFast rc pow3).2.size + 1) initSt h_init.init_inv
      orb horb h_not_mem with ⟨st_k, rem, h_loop_eq, h_inv_k, horb_k, h_uncov_k, h_sm_k, _⟩
  have h_bnd := h_inv_k.bounded orb horb_k
  have hj_rank : (computeEliminationRanks rc sms pow3).getD (boundaryTrace c b pow3) 0 = st_k.iter + 1 := by
    change (runReducerLoop N ((initialLiveFast rc pow3).2.size + 1) initSt).ranks.getD (boundaryTrace c b pow3) 0 = st_k.iter + 1
    rw [h_loop_eq]
    exact (eliminated_orb_final_rank_and_live N rem st_k orb horb_k
      h_inv_k.nodup h_inv_k.disjoint h_bnd.2 h_bnd.1 h_uncov_k (boundaryTrace c b pow3) hj_b).1
  have h_bnd_N : orbitBounded N orb := by
    rw [← h_inv_k.liveSize]
    exact h_bnd.1
  let cov := (stepSMList st_k.live st_k.activeSM.toList (zeros N) (Array.mkEmpty st_k.activeSM.size)).1
  have h_pair := uncovered_pairing_of_not_covered cov orb h_uncov_k
  have h_j_theta_ex : ∃ j_θ : Nat, (j_θ = orb.j0 ∨ j_θ = orb.j2 ∨ j_θ = orb.j5) ∧
      j_θ < N ∧ (cov.get! j_θ == 1) = false := by
    rcases h_pair with h0 | h2 | h5
    · exact ⟨orb.j0, Or.inl rfl, h_bnd_N.1, h0⟩
    · exact ⟨orb.j2, Or.inr (Or.inl rfl), h_bnd_N.2.2.1, h2⟩
    · exact ⟨orb.j5, Or.inr (Or.inr rfl), h_bnd_N.2.2.2.2.2, h5⟩
  rcases h_j_theta_ex with ⟨j_θ, hj_θ_cases, hj_θ_lt, hj_θ_uncov⟩
  rcases h_init.pairing_cover_sm b orb hb horb hj_b j_θ hj_θ_cases with ⟨θ, hθ_cover⟩
  refine ⟨θ, ?_⟩
  intro sm hsm h_fit0
  have h_fit_or : smFitIndex sm 0 = j_θ ∨ smFitIndex (swapSM sm) 0 = j_θ :=
    hθ_cover sm hsm h_fit0
  have h_dead_ex : ∃ t < 1 <<< sm.p, (st_k.live.get! (smFitIndex sm t) == 1) = false := by
    rcases h_sm_k sm hsm with h_active | ⟨t, ht, h_dead⟩
    · rcases h_fit_or with h_f0 | h_f_dual
      · exact exists_not_live_of_uncovered_in_round N st_k j_θ hj_θ_lt hj_θ_uncov sm (Or.inl h_active) h_f0
      · have h_tree_dual : smFitTree (swapSM sm) sm.p 0 0 0 = j_θ := by
          have := smFitTree_eq_smFitIndex (swapSM sm) 0
          dsimp [swapSM] at this ⊢
          rw [this]
          exact h_f_dual
        have hj_zeros : j_θ < (zeros N).size := by
          rw [zeros_size]
          exact hj_θ_lt
        rcases uncovered_of_stepSMList_swapSM st_k.live st_k.activeSM.toList (zeros N)
            (Array.mkEmpty st_k.activeSM.size) j_θ hj_zeros hj_θ_uncov sm h_active h_tree_dual with
          ⟨t, ht, h_dead⟩
        rw [smFitTree_eq_smFitIndex] at h_dead
        exact ⟨t, ht, h_dead⟩
    · exact ⟨t, ht, h_dead⟩
  rcases h_dead_ex with ⟨t, ht, h_dead⟩
  have h_not_in_k : ∀ orb' ∈ st_k.orbits.toList, ¬ inOrbit6 orb' (smFitIndex sm t) :=
    fun orb' h_mem => not_inOrbit6_of_not_live st_k.live orb' (smFitIndex sm t) (h_inv_k.allLive orb' h_mem) h_dead
  have h_not_in_step : ∀ orb' ∈ (reducerStep N st_k).orbits.toList, ¬ inOrbit6 orb' (smFitIndex sm t) :=
    fun orb' h_mem => h_not_in_k orb' (reducerStep_orbits_sub N st_k orb' h_mem)
  have h_rank_t : (computeEliminationRanks rc sms pow3).getD (smFitIndex sm t) 0 =
      st_k.ranks.getD (smFitIndex sm t) 0 := by
    change (runReducerLoop N ((initialLiveFast rc pow3).2.size + 1) initSt).ranks.getD (smFitIndex sm t) 0 =
      st_k.ranks.getD (smFitIndex sm t) 0
    rw [h_loop_eq,
        runReducerLoop_ranks_preserves_of_not_in_orbits N rem (reducerStep N st_k) (smFitIndex sm t) h_not_in_step,
        reducerStep_ranks_preserves_of_not_in_orbits N st_k (smFitIndex sm t) h_not_in_k]
  have h_le_k := h_inv_k.rankLe (smFitIndex sm t)
  have h_final_dead : ((computeFinalState rc sms pow3).live.get! (smFitIndex sm t) == 1) = false := by
    change ((runReducerLoop N ((initialLiveFast rc pow3).2.size + 1) initSt).live.get! (smFitIndex sm t) == 1) = false
    rw [h_loop_eq]
    exact runReducerLoop_not_live_mono N rem (reducerStep N st_k) (smFitIndex sm t)
      (reducerStep_not_live_mono N st_k (smFitIndex sm t) h_dead)
  have h_final_zero : (computeFinalState rc sms pow3).live.get! (smFitIndex sm t) = 0 :=
    eq_zero_of_beq_one_false_of_binary h_final_bin h_final_dead
  refine ⟨t, ht, ?_, ?_⟩
  · rw [h_rank_t, hj_rank]
    omega
  · intro b' hb' h_tr'
    have h_lz_theta : (computeFinalState rc sms pow3).live.get! (boundaryTraceTheta c b' θ pow3) = 0 := by
      rw [h_tr']
      exact h_final_zero
    have h_both := relabelBoundary_ranks_eq_and_liveZero c earlier sms pow3
      h_earlier h_wf h_irrefl h_init b' hb' θ h_lz_theta
    refine ⟨h_both.1, ?_⟩
    rw [h_both.2, h_tr']

/-- When `checkFastTotal (rconfOfConfig c earlier) sms pow3 = true`, every valid boundary coloring `b`
    satisfies `LiveZero` in `computeFinalState`. -/
theorem all_valid_liveZero_of_checkFastTotal (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_check : checkFastTotal (rconfOfConfig c earlier) sms pow3 = true)
    (h_init : InitialLiveSpec c earlier sms pow3) :
    ∀ b, IsValidBoundaryColoring c b →
      LiveZero c pow3 (computeFinalState (rconfOfConfig c earlier) sms pow3).live b := by
  let rc := rconfOfConfig c earlier
  let N := pow3.getD rc.r 1
  let initSt : ReducerState := {
    live := (initialLiveFast rc pow3).1
    orbits := (initialLiveFast rc pow3).2
    activeSM := sms
    ranks := Array.replicate N 0
    iter := 0
    changed := true
  }
  intro b hb
  cases h_ext : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 with
  | true =>
    have h_ext0 := h_init.ext_live_zero b hb h_ext
    unfold LiveZero computeFinalState
    exact runReducerLoop_preserves_zero N ((initialLiveFast rc pow3).2.size + 1) initSt
      (boundaryTrace c b pow3) h_ext0.1
  | false =>
    rcases h_init.nonext_in_orbit b hb h_ext with ⟨orb, horb, hj_b⟩
    have h_not_mem : orb ∉ (computeFinalState rc sms pow3).orbits.toList :=
      not_mem_toList_of_isEmpty (computeFinalState rc sms pow3).orbits h_check orb
    exact final_live_zero_of_orbit_eliminated c earlier sms pow3 h_init orb horb h_not_mem
      (boundaryTrace c b pow3) hj_b

/-- **Main Theorem D3.2 (`iterationElimination_of_checkFastTotal`):**
    When `checkFastTotal (rconfOfConfig c earlier) sms pow3 = true`, `IterationEliminationHypothesis`
    holds under `IsSoundEarlier`, `IsWellFormedEarlier`, `IsIrreflexiveAdj`,
    and `InitialLiveSpec` (`InitialLiveSpec` is itself an open obligation for Stage D4). -/
theorem iterationElimination_of_checkFastTotal (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_check : checkFastTotal (rconfOfConfig c earlier) sms pow3 = true)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_init : InitialLiveSpec c earlier sms pow3) :
    IterationEliminationHypothesis c earlier sms pow3 :=
  iteration_elimination_of_live_zero_all c earlier sms pow3
    (all_valid_liveZero_of_checkFastTotal c earlier sms pow3 h_check h_init)
    (liveZeroIterationElimination_of_initialLiveSpec c earlier sms pow3 h_earlier h_wf h_irrefl h_init)

/-- D-reducibility theorem reducing `IterationEliminationHypothesis` to `InitialLiveSpec`. -/
theorem fast_d_sound_of_initialLiveSpec (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_check : checkFastTotal (rconfOfConfig c earlier) sms pow3 = true)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_init : InitialLiveSpec c earlier sms pow3) :
    IsDReducible c :=
  fast_d_sound'' c earlier sms pow3 h_check h_earlier h_irrefl h_rep
    (iterationElimination_of_checkFastTotal c earlier sms pow3 h_check h_earlier h_wf h_irrefl h_init)

/-- C-reducibility theorem reducing `LiveZeroIterationEliminationHypothesis` to `InitialLiveSpec`. -/
theorem fast_c_sound_of_initialLiveSpec (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_contract : c.contractEdges ≠ [])
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_init : InitialLiveSpec c earlier sms pow3)
    (h_csound_chk : ContractCheckSoundnessHypothesis c earlier pow3
      (computeFinalState (rconfOfConfig c earlier) sms pow3).live)
    (h_run : runContractCheckTotal (rconfOfConfig c earlier) pow3
      (computeFinalState (rconfOfConfig c earlier) sms pow3).live = true) :
    IsCReducible c :=
  fast_c_sound_of_live_zero c earlier sms pow3 h_contract h_earlier h_irrefl h_rep
    (liveZeroIterationElimination_of_initialLiveSpec c earlier sms pow3 h_earlier h_wf h_irrefl h_init)
    h_csound_chk h_run

end CheckerSoundness
end Math