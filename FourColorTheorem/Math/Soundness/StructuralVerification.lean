import FourColorTheorem.Math.Soundness.ExtendSoundness
import FourColorTheorem.Math.Batch.Runner
import FourColorTheorem.Math.U633Parser

namespace Math
namespace Soundness

open FastReducer
open Batch

/-!
# Structural Adjacency and Earlier Properties Verification

This module establishes the structural properties of the Robertson-Sanders-Seymour-Thomas (RSST)
633 unavoidable configurations:
1. `IsIrreflexiveAdj c`: No vertex in configuration `c` is adjacent to itself.
2. `IsSoundEarlier c earlier`: The `earlier` neighbor table contains all earlier-indexed neighbors
   in the adjacency graph, and ring earlier-neighbors are adjacent in `c`.
-/

/-- Boolean check that no vertex in `c` is adjacent to itself. -/
def checkIrreflexiveAdj (c : Configuration) : Bool :=
  (List.range c.totalNodes).all (fun i => !c.adj i i)

/-- Soundness of `checkIrreflexiveAdj`: if the check passes, `c` has irreflexive adjacency. -/
theorem irreflexive_of_check (c : Configuration) (h : checkIrreflexiveAdj c = true) :
    IsIrreflexiveAdj c := by
  intro i hi
  have hMem : i ∈ List.range c.totalNodes := List.mem_range.mpr hi
  have h_all := List.all_eq_true.mp h i hMem
  cases hc : c.adj i i with
  | false => rfl
  | true =>
    rw [hc] at h_all
    contradiction

/-- Boolean check that `earlier` contains all earlier neighbors for each vertex,
    and ring earlier neighbors are adjacent in `c`. -/
def checkSoundEarlier (c : Configuration) (earlier : Array (Array Nat)) : Bool :=
  let part1 := (List.range c.totalNodes).all (fun v =>
    (List.range v).all (fun u =>
      if c.adj v u || c.adj u v then
        (earlier.getD v #[]).toList.contains u
      else true))
  let part2 := (List.range c.ringSize).all (fun i =>
    (earlier.getD i #[]).toList.all (fun u =>
      if u < i then
        c.adj i u || c.adj u i
      else true))
  part1 && part2

/-- Soundness of `checkSoundEarlier`: if the check passes, `earlier` is sound for `c`. -/
theorem sound_earlier_of_check (c : Configuration) (earlier : Array (Array Nat))
    (h : checkSoundEarlier c earlier = true) :
    IsSoundEarlier c earlier := by
  dsimp [checkSoundEarlier] at h
  rw [Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩
  constructor
  · intro v hv u hu h_adj
    have hv_mem : v ∈ List.range c.totalNodes := List.mem_range.mpr hv
    have h_v := List.all_eq_true.mp h1 v hv_mem
    have hu_mem : u ∈ List.range v := List.mem_range.mpr hu
    have h_u := List.all_eq_true.mp h_v u hu_mem
    have h_or : (c.adj v u || c.adj u v) = true := by
      cases h_adj with
      | inl h_vu => rw [h_vu]; rfl
      | inr h_uv => rw [h_uv, Bool.or_true]
    rw [if_pos h_or] at h_u
    change (earlier.getD v #[]).toList.elem u = true at h_u
    exact List.elem_iff.mp h_u
  · intro i hi u hu hu_lt
    have hi_mem : i ∈ List.range c.ringSize := List.mem_range.mpr hi
    have h_i := List.all_eq_true.mp h2 i hi_mem
    have h_u := List.all_eq_true.mp h_i u hu
    rw [if_pos hu_lt] at h_u
    cases hc : c.adj i u with
    | true => exact Or.inl rfl
    | false =>
      rw [hc] at h_u
      exact Or.inr h_u

/-- Universal theorem: every configuration constructed via `configOfRConf` has irreflexive adjacency. -/
theorem configOfRConf_is_irreflexive (rc : RConf) :
    IsIrreflexiveAdj (configOfRConf rc) := by
  intro i _hi
  dsimp [configOfRConf, symAdj]
  have h_not_lt : ¬ (i < i) := Nat.lt_irrefl i
  rw [if_neg h_not_lt, if_neg h_not_lt]

/-- Universal theorem: every configuration constructed via `configOfRConf` has sound earlier adjacency. -/
theorem configOfRConf_is_sound_earlier (rc : RConf) :
    IsSoundEarlier (configOfRConf rc) rc.earlier := by
  constructor
  · intro v _hv u hu h_adj
    dsimp [configOfRConf, symAdj] at h_adj
    have h_not_vu : ¬ (v < u) := by omega
    rw [if_neg h_not_vu, if_pos hu, if_pos hu] at h_adj
    cases h_adj with
    | inl h => exact List.elem_iff.mp h
    | inr h => exact List.elem_iff.mp h
  · intro i _hi u hu hu_lt
    dsimp [configOfRConf, symAdj]
    have h_not_iu : ¬ (i < u) := by omega
    rw [if_neg h_not_iu, if_pos hu_lt]
    exact Or.inl (List.elem_iff.mpr hu)

/-- Pointwise theorem: any canonical RSST configuration index `idx < 633` has irreflexive adjacency. -/
theorem unavoidable_is_irreflexive (idx : Nat) (h_lt : idx < 633) :
    IsIrreflexiveAdj theUnavoidableSet[idx]! := by
  rw [theUnavoidableSet_getElem! idx h_lt]
  exact configOfRConf_is_irreflexive sharedCfgs[idx]!

/-- Pointwise theorem: any canonical RSST configuration index `idx < 633` has sound earlier adjacency. -/
theorem unavoidable_is_sound_earlier (idx : Nat) (h_lt : idx < 633) :
    IsSoundEarlier theUnavoidableSet[idx]! sharedCfgs[idx]!.earlier := by
  rw [theUnavoidableSet_getElem! idx h_lt]
  exact configOfRConf_is_sound_earlier sharedCfgs[idx]!

end Soundness
end Math
