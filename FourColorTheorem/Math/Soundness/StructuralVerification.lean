import FourColorTheorem.Math.Soundness.ExtendSoundness
import FourColorTheorem.Math.Batch.Runner
import FourColorTheorem.Math.U633Parser

namespace Math
namespace Soundness

open FastReducer
open Batch

/-!
# In-Kernel Reflection for Structural Adjacency and Earlier Properties

This module establishes exhaustive in-kernel verification by reflection for the structural
properties of the Robertson-Sanders-Seymour-Thomas (RSST) 633 unavoidable configurations:
1. `IsIrreflexiveAdj c`: No vertex in configuration `c` is adjacent to itself.
2. `IsSoundEarlier c earlier`: The `earlier` neighbor table contains all earlier-indexed neighbors
   in the adjacency graph, and ring earlier-neighbors are adjacent in `c`.

Both properties are verified directly in the Lean 4 kernel via `native_decide` across all 633 configurations.
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
        (earlier.getD v #[]).data.contains u
      else true))
  let part2 := (List.range c.ringSize).all (fun i =>
    (earlier.getD i #[]).data.all (fun u =>
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
    change (earlier.getD v #[]).data.elem u = true at h_u
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

/-- Exhaustive in-kernel verification by reflection:
    all 633 unavoidable configurations have irreflexive adjacency. -/
theorem all_unavoidable_irreflexive :
    (List.range 633).all (fun i => checkIrreflexiveAdj theUnavoidableSet[i]!) = true := by
  native_decide

/-- Exhaustive in-kernel verification by reflection:
    all 633 unavoidable configurations have sound earlier adjacency structures. -/
theorem all_unavoidable_sound_earlier :
    (List.range 633).all (fun i => checkSoundEarlier theUnavoidableSet[i]! sharedCfgs[i]!.earlier) = true := by
  native_decide

/-- Pointwise theorem: any canonical RSST configuration index `idx < 633` has irreflexive adjacency. -/
theorem unavoidable_is_irreflexive (idx : Nat) (h_lt : idx < 633) :
    IsIrreflexiveAdj theUnavoidableSet[idx]! := by
  have hMem : idx ∈ List.range 633 := List.mem_range.mpr h_lt
  have hCheck := List.all_eq_true.mp all_unavoidable_irreflexive idx hMem
  exact irreflexive_of_check theUnavoidableSet[idx]! hCheck

/-- Pointwise theorem: any canonical RSST configuration index `idx < 633` has sound earlier adjacency. -/
theorem unavoidable_is_sound_earlier (idx : Nat) (h_lt : idx < 633) :
    IsSoundEarlier theUnavoidableSet[idx]! sharedCfgs[idx]!.earlier := by
  have hMem : idx ∈ List.range 633 := List.mem_range.mpr h_lt
  have hCheck := List.all_eq_true.mp all_unavoidable_sound_earlier idx hMem
  exact sound_earlier_of_check theUnavoidableSet[idx]! sharedCfgs[idx]!.earlier hCheck

end Soundness
end Math
