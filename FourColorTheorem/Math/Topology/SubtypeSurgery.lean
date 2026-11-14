/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Topology.Surgery
import FourColorTheorem.Math.Topology.OrbitLemmas

/-!
# Subtype-Based Hypermap Disk Excision (`exciseSubtype`)

This module resolves the fixed-carrier completeness bug in `Surgery.exciseFixed`:
because `exciseFixed` retains the original carrier `H.Dart`, any dart `d ∈ removed` remains
an inhabitant of `H.Dart` even after being removed from `eraseAllDarts darts removed`, making
`IsCompleteDarts (exciseFixed H c f) (eraseAllDarts darts removed)` uninhabited whenever
`removed` intersects `darts`.

Here we restrict both the carrier type (`{ d : H.Dart // d ∉ removed }`) and the dart list
(`subDarts darts removed`), proving:
1. `mem_removed_iff_of_fixed_on`: any permutation fixing `removed` pointwise restricts
   bijectively to `{ d : D // d ∉ removed }`.
2. `exciseSubtype` and `exciseSubtypeOfFixed`: subtype-restricted `Hypermap` construction.
3. `exciseSubtype_complete` and `exciseSubtype_strictly_smaller`: completeness (`Nodup`,
   exhaustive, non-empty) and strict dart-count decrease.
4. `twoEdgeSphere_excise_witness`: concrete kernel-verified finite hypermap witness proving
   non-vacuity of subtype excision.
-/

namespace Hypermap

section SubtypeRestriction

/-- Any permutation that fixes every dart in `removed` preserves membership in `removed`. -/
theorem mem_removed_iff_of_fixed_on {D : Type} (p : Perm D) (removed : List D)
    (h_fix : ∀ r ∈ removed, p.f r = r) (d : D) :
    d ∈ removed ↔ p.f d ∈ removed := by
  constructor
  · intro hd
    rwa [h_fix d hd]
  · intro hpd
    have hfix : p.f (p.f d) = p.f d := h_fix (p.f d) hpd
    have hinj : p.f d = d := by
      have h1 := congrArg p.inv hfix
      rwa [p.left_inv, p.left_inv] at h1
    rwa [← hinj]

/-- Restrict a permutation `p : Perm D` to the subtype `{ d : D // d ∉ removed }`
    whenever `p.f` preserves membership in `removed`. -/
def restrictPerm {D : Type} (p : Perm D) (removed : List D)
    (h_inv : ∀ d, d ∈ removed ↔ p.f d ∈ removed) : Perm { d : D // d ∉ removed } where
  f x := ⟨p.f x.1, fun hm => x.2 ((h_inv x.1).mpr hm)⟩
  inv x :=
    ⟨p.inv x.1, fun hm =>
      x.2 (by
        have hmem := (h_inv (p.inv x.1)).mp hm
        rwa [p.right_inv] at hmem)⟩
  left_inv x := Subtype.ext (p.left_inv x.1)
  right_inv x := Subtype.ext (p.right_inv x.1)

/-- If `e'`, `n'`, `f'` satisfy `e' ∘ n' ∘ f' = id` and `e'`, `n'` preserve `removed`,
    then `f'` automatically preserves `removed`. -/
theorem face_mem_removed_iff_of_edge_node {D : Type} (removed : List D) (e' n' f' : Perm D)
    (h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_edge : ∀ d, d ∈ removed ↔ e'.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ n'.f d ∈ removed)
    (d : D) :
    d ∈ removed ↔ f'.f d ∈ removed := by
  have h1 := (h_node (f'.f d)).symm
  have h2 := (h_edge (n'.f (f'.f d))).symm
  rw [h_enf d] at h2
  exact h2.trans h1

/-- Construct a hypermap on the subtype `{ d : H.Dart // d ∉ removed }` from modified
    permutations `(e', n', f')` whose fixed/invariant removed set is closed under `e'` and `n'`. -/
def exciseSubtype (H : Hypermap) (removed : List H.Dart) (e' n' f' : Perm H.Dart)
    (h_e_inv : ∀ d, e'.f (e'.f d) = d)
    (h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_edge : ∀ d, d ∈ removed ↔ e'.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ n'.f d ∈ removed) : Hypermap where
  Dart := { d : H.Dart // d ∉ removed }
  edge := restrictPerm e' removed h_edge
  node := restrictPerm n' removed h_node
  face := restrictPerm f' removed (face_mem_removed_iff_of_edge_node removed e' n' f' h_enf h_edge h_node)
  edge_involution x := Subtype.ext (h_e_inv x.1)
  edge_node_face_id x := Subtype.ext (h_enf x.1)

/-- Convenience constructor when `e'` and `n'` fix every dart of `removed` pointwise. -/
def exciseSubtypeOfFixed (H : Hypermap) (removed : List H.Dart) (e' n' f' : Perm H.Dart)
    (h_e_inv : ∀ d, e'.f (e'.f d) = d)
    (h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_e_fix : ∀ r ∈ removed, e'.f r = r)
    (h_n_fix : ∀ r ∈ removed, n'.f r = r) : Hypermap :=
  exciseSubtype H removed e' n' f' h_e_inv h_enf
    (mem_removed_iff_of_fixed_on e' removed h_e_fix)
    (mem_removed_iff_of_fixed_on n' removed h_n_fix)

end SubtypeRestriction

section SubDartsCompleteness

/-- Filter a list of darts into the subtype `{ d : D // d ∉ removed }`. -/
def subDarts {D : Type} [DecidableEq D] (darts removed : List D) :
    List { d : D // d ∉ removed } :=
  match darts with
  | [] => []
  | d :: ds =>
    if h : d ∈ removed then subDarts ds removed
    else ⟨d, h⟩ :: subDarts ds removed

/-- Membership characterization of `subDarts`. -/
theorem mem_subDarts {D : Type} [DecidableEq D] (darts removed : List D)
    (x : { d : D // d ∉ removed }) :
    x ∈ subDarts darts removed ↔ x.1 ∈ darts := by
  induction darts with
  | nil =>
    simp [subDarts]
  | cons d ds ih =>
    dsimp [subDarts]
    by_cases h : d ∈ removed
    · rw [dif_pos h, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (hxd | hds)
        · exact False.elim (x.2 (hxd ▸ h))
        · exact hds
    · rw [dif_neg h, List.mem_cons, List.mem_cons, ih]
      constructor
      · rintro (rfl | hds)
        · exact Or.inl rfl
        · exact Or.inr hds
      · rintro (hxd | hds)
        · exact Or.inl (Subtype.ext hxd)
        · exact Or.inr hds

/-- `subDarts` preserves duplicate-freedom (`Nodup`). -/
theorem subDarts_nodup {D : Type} [DecidableEq D] (darts removed : List D)
    (h_nodup : darts.Nodup) :
    (subDarts darts removed).Nodup := by
  induction darts with
  | nil =>
    exact List.nodup_nil
  | cons d ds ih =>
    have hd_not : d ∉ ds := (List.nodup_cons.mp h_nodup).1
    have hds_nodup : ds.Nodup := (List.nodup_cons.mp h_nodup).2
    dsimp [subDarts]
    by_cases h : d ∈ removed
    · rw [dif_pos h]
      exact ih hds_nodup
    · rw [dif_neg h, List.nodup_cons]
      refine ⟨?_, ih hds_nodup⟩
      intro hm
      rw [mem_subDarts] at hm
      exact hd_not hm

/-- `subDarts` does not increase list length. -/
theorem subDarts_length_le {D : Type} [DecidableEq D] (darts removed : List D) :
    (subDarts darts removed).length ≤ darts.length := by
  induction darts with
  | nil =>
    exact Nat.le_refl 0
  | cons d ds ih =>
    dsimp [subDarts]
    by_cases h : d ∈ removed
    · rw [dif_pos h]
      exact Nat.le_trans ih (Nat.le_succ _)
    · rw [dif_neg h]
      exact Nat.succ_le_succ ih

/-- If at least one dart of `darts` is removed, `subDarts darts removed` is strictly shorter. -/
theorem exciseSubtype_strictly_smaller {D : Type} [DecidableEq D] (darts removed : List D)
    (h_rem : ∃ d ∈ darts, d ∈ removed) :
    (subDarts darts removed).length < darts.length := by
  obtain ⟨r, hr_in, hr_rem⟩ := h_rem
  induction darts with
  | nil =>
    cases hr_in
  | cons d ds ih =>
    dsimp [subDarts]
    by_cases h : d ∈ removed
    · rw [dif_pos h]
      exact Nat.lt_succ_of_le (subDarts_length_le ds removed)
    · rw [dif_neg h]
      have hr_ds : r ∈ ds := by
        rcases List.mem_cons.mp hr_in with rfl | htail
        · exact False.elim (h hr_rem)
        · exact htail
      exact Nat.succ_lt_succ (ih hr_ds)

/-- If at least one dart of `darts` survives removal, `subDarts darts removed` is non-empty. -/
theorem subDarts_nonempty {D : Type} [DecidableEq D] (darts removed : List D)
    (h_surv : ∃ d ∈ darts, d ∉ removed) :
    subDarts darts removed ≠ [] := by
  obtain ⟨d, hd_in, hd_not⟩ := h_surv
  intro hnil
  have hmem : (⟨d, hd_not⟩ : { x : D // x ∉ removed }) ∈ subDarts darts removed :=
    (mem_subDarts darts removed ⟨d, hd_not⟩).mpr hd_in
  rw [hnil] at hmem
  cases hmem

/-- **Completeness of Subtype Excision (`exciseSubtype`):**
    Restricting a complete dart list `darts` (`Nodup`, exhaustive, non-empty survivor)
    produces a complete dart list for `exciseSubtype` (`Nodup`, exhaustive, non-empty). -/
theorem exciseSubtype_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts removed : List H.Dart) (e' n' f' : Perm H.Dart)
    (h_e_inv : ∀ d, e'.f (e'.f d) = d)
    (h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_edge : ∀ d, d ∈ removed ↔ e'.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ n'.f d ∈ removed)
    (h_nodup : darts.Nodup)
    (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_surv : ∃ d ∈ darts, d ∉ removed) :
    let H' := exciseSubtype H removed e' n' f' h_e_inv h_enf h_edge h_node
    let darts' := subDarts darts removed
    darts'.Nodup ∧ (∀ d : H'.Dart, d ∈ darts') ∧ darts' ≠ [] := by
  refine ⟨subDarts_nodup darts removed h_nodup, ?_, subDarts_nonempty darts removed h_surv⟩
  intro x
  exact (mem_subDarts darts removed x).mpr (h_all x.1)

end SubDartsCompleteness

section NonVacuityWitness

private theorem fin4_all {P : Fin 4 → Prop}
    (h0 : P ⟨0, by decide⟩) (h1 : P ⟨1, by decide⟩)
    (h2 : P ⟨2, by decide⟩) (h3 : P ⟨3, by decide⟩) : ∀ x : Fin 4, P x
  | ⟨0, _⟩ => h0
  | ⟨1, _⟩ => h1
  | ⟨2, _⟩ => h2
  | ⟨3, _⟩ => h3

private def swap01Perm : Perm (Fin 4) where
  f
    | ⟨0, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => ⟨0, by decide⟩
    | ⟨2, _⟩ => ⟨2, by decide⟩
    | ⟨3, _⟩ => ⟨3, by decide⟩
  inv
    | ⟨0, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => ⟨0, by decide⟩
    | ⟨2, _⟩ => ⟨2, by decide⟩
    | ⟨3, _⟩ => ⟨3, by decide⟩
  left_inv := fin4_all rfl rfl rfl rfl
  right_inv := fin4_all rfl rfl rfl rfl

private def twoEdgeSphereEdge : Perm (Fin 4) where
  f
    | ⟨0, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => ⟨0, by decide⟩
    | ⟨2, _⟩ => ⟨3, by decide⟩
    | ⟨3, _⟩ => ⟨2, by decide⟩
  inv
    | ⟨0, _⟩ => ⟨1, by decide⟩
    | ⟨1, _⟩ => ⟨0, by decide⟩
    | ⟨2, _⟩ => ⟨3, by decide⟩
    | ⟨3, _⟩ => ⟨2, by decide⟩
  left_inv := fin4_all rfl rfl rfl rfl
  right_inv := fin4_all rfl rfl rfl rfl

private def twoEdgeSphereNode : Perm (Fin 4) where
  f
    | ⟨0, _⟩ => ⟨2, by decide⟩
    | ⟨1, _⟩ => ⟨3, by decide⟩
    | ⟨2, _⟩ => ⟨0, by decide⟩
    | ⟨3, _⟩ => ⟨1, by decide⟩
  inv
    | ⟨0, _⟩ => ⟨2, by decide⟩
    | ⟨1, _⟩ => ⟨3, by decide⟩
    | ⟨2, _⟩ => ⟨0, by decide⟩
    | ⟨3, _⟩ => ⟨1, by decide⟩
  left_inv := fin4_all rfl rfl rfl rfl
  right_inv := fin4_all rfl rfl rfl rfl

private def twoEdgeSphereFace : Perm (Fin 4) where
  f
    | ⟨0, _⟩ => ⟨3, by decide⟩
    | ⟨1, _⟩ => ⟨2, by decide⟩
    | ⟨2, _⟩ => ⟨1, by decide⟩
    | ⟨3, _⟩ => ⟨0, by decide⟩
  inv
    | ⟨0, _⟩ => ⟨3, by decide⟩
    | ⟨1, _⟩ => ⟨2, by decide⟩
    | ⟨2, _⟩ => ⟨1, by decide⟩
    | ⟨3, _⟩ => ⟨0, by decide⟩
  left_inv := fin4_all rfl rfl rfl rfl
  right_inv := fin4_all rfl rfl rfl rfl

/-- Concrete 4-dart spherical 2-edge map (`V=2, E=2, F=2`) used to certify non-vacuity of
    `exciseSubtype` and `subDarts`. -/
def twoEdgeSphere : Hypermap where
  Dart := Fin 4
  edge := twoEdgeSphereEdge
  node := twoEdgeSphereNode
  face := twoEdgeSphereFace
  edge_involution := fin4_all rfl rfl rfl rfl
  edge_node_face_id := fin4_all rfl rfl rfl rfl

/-- **Constructive Non-Vacuity Witness for `exciseSubtype`:**
    Excising edge `{2, 3}` from `twoEdgeSphere` produces a complete, strictly smaller,
    non-empty subtype hypermap with `2 < 4` darts. -/
theorem twoEdgeSphere_excise_witness :
    let darts : List (Fin 4) := [0, 1, 2, 3]
    let removed : List (Fin 4) := [2, 3]
    let e' := swap01Perm
    let n' := (Perm.one : Perm (Fin 4))
    let f' := swap01Perm
    let h_e_inv : ∀ d, e'.f (e'.f d) = d := fin4_all rfl rfl rfl rfl
    let h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d := fin4_all rfl rfl rfl rfl
    let h_e_fix : ∀ r ∈ removed, e'.f r = r := by decide
    let h_n_fix : ∀ r ∈ removed, n'.f r = r := by decide
    let H' := exciseSubtypeOfFixed twoEdgeSphere removed e' n' f' h_e_inv h_enf h_e_fix h_n_fix
    let darts' := subDarts darts removed
    darts'.Nodup ∧ (∀ d : H'.Dart, d ∈ darts') ∧ darts' ≠ [] ∧ darts'.length < darts.length := by
  intro darts removed e' n' f' h_e_inv h_enf h_e_fix h_n_fix H' darts'
  letI : DecidableEq twoEdgeSphere.Dart := inferInstanceAs (DecidableEq (Fin 4))
  have h_nodup : darts.Nodup := by decide
  have h_all : ∀ d : Fin 4, d ∈ darts := fin4_all (by decide) (by decide) (by decide) (by decide)
  have h_surv : ∃ d ∈ darts, d ∉ removed := ⟨0, by decide, by decide⟩
  have h_rem : ∃ d ∈ darts, d ∈ removed := ⟨2, by decide, by decide⟩
  have h_comp := exciseSubtype_complete twoEdgeSphere darts removed e' n' f'
    h_e_inv h_enf
    (mem_removed_iff_of_fixed_on e' removed h_e_fix)
    (mem_removed_iff_of_fixed_on n' removed h_n_fix)
    h_nodup h_all h_surv
  exact ⟨h_comp.1, h_comp.2.1, h_comp.2.2, exciseSubtype_strictly_smaller darts removed h_rem⟩

end NonVacuityWitness

end Hypermap
