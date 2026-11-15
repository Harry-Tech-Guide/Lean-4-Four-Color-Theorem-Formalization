/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Topology.Genus
import FourColorTheorem.Math.Topology.PlanarKempe
import FourColorTheorem.Math.Topology.CubicGirth5
import FourColorTheorem.Math.Unavoidability.FreeCompletionProjection

/-!
# Stage U.5: Capped-Ring Disk Excision & Unconditional D-Reduction (`DiskExcision`)

This module formalizes projection-safe capped-ring disk excision on the dual triangulation
`H.dual` of a planar, bridgeless minimal counterexample `H` containing a matched unavoidable
configuration `rc = parsedRConfList[h]` (`h < 633`), eliminating all 249 D-reducible
configurations unconditionally and preparing `restrictModColoringToCap` for Stage V C-reduction:

1. **`Hypermap.mirror` & `orientedDual`:** Orientation-reversing involution `(e, n⁻¹, e ∘ f⁻¹ ∘ e)`
   preserving planarity (`isPlanar_mirror`), vertex orbits, and bridgelessness while normalizing
   `RingFanProjectionConsistent`'s `nodePermOriented H.dual p.emb.orient` into a single canonical
   forward node direction `(orientedDual H p.emb.orient).node`.
2. **Multi-Edge Subtype Excision (`deleteEdgesSubtype`):** Generalizes 1-edge `deleteEdgeSubtype`
   to an arbitrary `H.edge`-closed list `removed` via `BypassValid` orbit-jump invariants,
   preserving planarity (`exciseSubtype_isPlanar_of_perm`), dart completeness, exact vertex-orbit
   equivalence on surviving darts (`deleteEdgesSubtype_sameOrbit_node_iff`), and dual
   bridgelessness (`deleteEdgesSubtype_dual_isBridgeless`).
3. **Capped-Ring Excision (`CappedRingWitness`):** Excises all darts incident to the `m ≥ 4`
   interior vertices `p.emb.rep u` (`c.ringSize ≤ u < c.totalNodes`), leaving the `r` canonical
   ring darts `capRingDart x` strictly distinct (via interior-fan apex recovery, requiring zero
   ring-injectivity assumptions), strictly fewer surviving darts (`capDarts.length < darts.length`),
   an exact `r`-cycle `H_cap.dual.face.f (capRingDart x) = capRingDart ((x + 1) % r)`, and
   `CyclicOrder4` along the excised ring boundary.
4. **Gluing, Contract Restriction & Unconditional D-Reduction:**
   - `glue_capped_and_interior`: glues any `H_cap.FaceColoring` and interior valid config coloring
     agreeing on `capRingDart` into a global `H.FaceColoring`.
   - `restrictModColoringToCap`: restricts any `VertexColoringMod H.dual (mappedContractDarts p.emb)`
     onto `H_cap.FaceColoring`.
   - `d_reducible_matched_impossible`: unconditionally discharges every D-reducible configuration.
   - `c_reducible_matched_impossible_of_mod_coloring`: discharges any C-reducible configuration once
     the contracted coloring `VertexColoringMod H.dual (mappedContractDarts p.emb)` exists.
-/

namespace Hypermap

open Math Math.Discharging Math.Unavoidability
open Math.Hypermap (sameVertex faceDegree)

private theorem list_length_pos_of_ne_nil {α : Type} {l : List α} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact False.elim (h rfl)
  | cons _ _ => exact Nat.succ_pos _

section MirrorAndOrientedDual

private theorem instBEqOfDecidableEq_eq_de {α : Type} (d1 d2 : DecidableEq α) :
    @instBEqOfDecidableEq α d1 = @instBEqOfDecidableEq α d2 := by
  apply beq_eq_of_pointwise
  intro x y
  change @decide (x = y) (d1 x y) = @decide (x = y) (d2 x y)
  by_cases h : x = y
  · rw [@decide_eq_true (x = y) (d1 x y) h, @decide_eq_true (x = y) (d2 x y) h]
  · rw [@decide_eq_false (x = y) (d1 x y) h, @decide_eq_false (x = y) (d2 x y) h]

private theorem perm_f_inj_de {D : Type} (p : Perm D) {x y : D} (h : p.f x = p.f y) : x = y := by
  calc
    x = p.inv (p.f x) := (p.left_inv x).symm
    _ = p.inv (p.f y) := congrArg p.inv h
    _ = y := p.left_inv y

private theorem perm_iter_succ_shift {D : Type} (p : Perm D) :
    ∀ (n : Nat) (x : D), Perm.iter p (n + 1) x = Perm.iter p n (p.f x)
  | 0, _ => rfl
  | n + 1, x => by
    change p.f (Perm.iter p (n + 1) x) = p.f (Perm.iter p n (p.f x))
    rw [perm_iter_succ_shift p n x]

private theorem iter_perm_symm_iff_rev {D : Type} (p : Perm D) :
    ∀ x y : D, SameOrbit p.symm x y ↔ SameOrbit p y x :=
  fun _ _ => sameOrbit_symm_perm p

/-- Orientation-reversing mirror involution `(e, n⁻¹, e ∘ f⁻¹ ∘ e)` on hypermaps. -/
def mirror (H : Hypermap) : Hypermap where
  Dart := H.Dart
  edge := H.edge
  node := Perm.symm H.node
  face :=
    { f := fun d => H.edge.f (H.face.inv (H.edge.f d))
      inv := fun d => H.edge.f (H.face.f (H.edge.f d))
      left_inv := fun d => by
        rw [H.edge_involution, H.face.right_inv, H.edge_involution]
      right_inv := fun d => by
        rw [H.edge_involution, H.face.left_inv, H.edge_involution] }
  edge_involution := H.edge_involution
  edge_node_face_id := fun d => by
    have h := H.face_edge_node_id (H.node.inv (H.edge.f d))
    have h1 := H.face_edge_node_id (H.edge.f d)
    have h2 : H.edge.f (H.node.f (H.edge.f d)) = H.face.inv (H.edge.f d) := by
      have h3 := congrArg H.face.inv h1
      rwa [H.face.left_inv] at h3
    change H.edge.f (H.node.inv (H.edge.f (H.face.inv (H.edge.f d)))) = d
    rw [← h2, H.edge_involution, H.node.left_inv, H.edge_involution]

theorem mirror_face_iter (H : Hypermap) :
    ∀ (k : Nat) (d : H.Dart),
      Perm.iter H.mirror.face k d = H.edge.f (Perm.iter H.face.symm k (H.edge.f d))
  | 0, d => by simp [Perm.iter, H.edge_involution]
  | k + 1, d => by
    rw [Perm.iter_succ, Perm.iter_succ, mirror_face_iter H k d]
    change H.edge.f (H.face.inv (H.edge.f (H.edge.f (Perm.iter H.face.symm k (H.edge.f d))))) =
      H.edge.f (H.face.inv (Perm.iter H.face.symm k (H.edge.f d)))
    rw [H.edge_involution]

theorem mirror_face_cube (H : Hypermap)
    (h_tri : ∀ d : H.Dart, H.face.f (H.face.f (H.face.f d)) = d) (d : H.Dart) :
    H.mirror.face.f (H.mirror.face.f (H.mirror.face.f d)) = d := by
  have h1 := h_tri (H.face.inv (H.face.inv (H.face.inv (H.edge.f d))))
  rw [H.face.right_inv, H.face.right_inv, H.face.right_inv] at h1
  change H.edge.f (H.face.inv (H.edge.f (H.edge.f (H.face.inv (H.edge.f (H.edge.f (H.face.inv (H.edge.f d)))))))) = d
  rw [H.edge_involution, H.edge_involution, ← h1, H.edge_involution]

theorem sameOrbit_mirror_node_iff (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts) (x y : H.Dart) :
    SameOrbit H.mirror.node x y ↔ SameOrbit H.node x y := by
  change SameOrbit H.node.symm x y ↔ SameOrbit H.node x y
  exact (sameOrbit_symm_perm H.node).trans
    ⟨fun h => sameOrbit_symm_of_complete H.node darts h_all h,
     fun h => sameOrbit_symm_of_complete H.node darts h_all h⟩

theorem sameOrbit_mirror_face_iff (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts) (x y : H.Dart) :
    SameOrbit H.mirror.face (H.edge.f x) (H.edge.f y) ↔ SameOrbit H.face x y := by
  have hf_iff : SameOrbit H.mirror.face (H.edge.f x) (H.edge.f y) ↔ SameOrbit H.face.symm x y := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [mirror_face_iter, H.edge_involution] at hk
      exact perm_f_inj_de H.edge hk
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [mirror_face_iter, H.edge_involution, hk]⟩
  exact hf_iff.trans ((sameOrbit_symm_perm H.face).trans
    ⟨fun h => sameOrbit_symm_of_complete H.face darts h_all h,
     fun h => sameOrbit_symm_of_complete H.face darts h_all h⟩)

private theorem countRelClasses_map_congr_aux {D : Type} (φ : D → D) (hφ_inv : ∀ x, φ (φ x) = x)
    (R1 R2 : D → D → Prop) [DecidableRel R1] [DecidableRel R2]
    (h_iff : ∀ x y : D, R1 (φ x) (φ y) ↔ R2 x y) :
    ∀ (n : Nat) (l : List D), l.length ≤ n → countRelClasses R1 (l.map φ) = countRelClasses R2 l
  | 0, l, h => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    subst hnil; simp [countRelClasses_nil]
  | _ + 1, [], _ => by simp [countRelClasses_nil]
  | n + 1, d :: ds, h => by
    have h_len : ds.length ≤ n := by dsimp at h; omega
    rw [List.map_cons, countRelClasses_cons, countRelClasses_cons]
    have h_flt1 : (ds.map φ).filter (fun y => !decide (R1 (φ d) y)) =
        (ds.filter (fun x => !decide (R2 d x))).map φ := by
      rw [List.filter_map]
      congr 1
      apply filter_ext_of_mem
      intro x _
      dsimp only [Function.comp_def]
      by_cases hR : R2 d x
      · have hR1 : R1 (φ d) (φ x) := (h_iff d x).mpr hR
        simp [hR, hR1]
      · have hR1 : ¬ R1 (φ d) (φ x) := fun h1 => hR ((h_iff d x).mp h1)
        simp [hR, hR1]
    rw [h_flt1]
    have h_sub_len : (ds.filter (fun x => !decide (R2 d x))).length ≤ n :=
      Nat.le_trans (List.length_filter_le _ ds) h_len
    rw [countRelClasses_map_congr_aux φ hφ_inv R1 R2 h_iff n _ h_sub_len]

theorem reachEN_mirror_iff (H : Hypermap) (x y : H.Dart) :
    ReachEN H.mirror.edge H.mirror.node x y ↔ ReachEN H.edge H.node x y := by
  change ReachEN H.edge H.node.symm x y ↔ ReachEN H.edge H.node x y
  constructor
  · rintro ⟨w⟩
    induction w with
    | refl => exact reachEN_refl _ _ _
    | step s _ ih =>
      refine reachEN_trans _ _ ?_ ih
      cases s with
      | e_fwd => exact ⟨.step (.e_fwd _) (.refl _)⟩
      | e_bwd => exact ⟨.step (.e_bwd _) (.refl _)⟩
      | n_fwd => exact ⟨.step (.n_bwd _) (.refl _)⟩
      | n_bwd => exact ⟨.step (.n_fwd _) (.refl _)⟩
  · rintro ⟨w⟩
    induction w with
    | refl => exact reachEN_refl _ _ _
    | step s _ ih =>
      refine reachEN_trans _ _ ?_ ih
      cases s with
      | e_fwd => exact ⟨.step (.e_fwd _) (.refl _)⟩
      | e_bwd => exact ⟨.step (.e_bwd _) (.refl _)⟩
      | n_fwd => exact ⟨.step (.n_bwd _) (.refl _)⟩
      | n_bwd => exact ⟨.step (.n_fwd _) (.refl _)⟩

theorem genusDeficit_mirror_eq (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {fuel : Nat} (h_len : darts.length ≤ fuel) :
    genusDeficit H.mirror.hypermapToTriple fuel darts = genusDeficit H.hypermapToTriple fuel darts := by
  classical
  dsimp only [genusDeficit, hypermapToTriple]
  have hcomp : countRelClasses (ReachEN H.mirror.edge H.mirror.node) darts =
      countRelClasses (ReachEN H.edge H.node) darts :=
    countRelClasses_eq_of_iff (ReachEN H.mirror.edge H.mirror.node) (ReachEN H.edge H.node)
      (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
      (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
      (reachEN_mirror_iff H) darts
  have hedge : countOrbits H.mirror.edge fuel darts = countOrbits H.edge fuel darts := rfl
  have hnode : countOrbits H.mirror.node fuel darts = countOrbits H.node fuel darts :=
    countOrbits_eq_of_sameOrbit_iff H.mirror.node H.node darts h_all h_len h_len
      (sameOrbit_mirror_node_iff H darts h_all) darts
  have hface_mem : ∀ z : H.Dart, z ∈ darts ↔ z ∈ darts.map H.edge.f := fun z => by
    constructor
    · intro _
      exact List.mem_map.mpr ⟨H.edge.f z, h_all _, H.edge_involution z⟩
    · intro _
      exact h_all z
  have hface_rel : countOrbits H.mirror.face fuel darts = countOrbits H.face fuel darts := by
    rw [countOrbits_eq_countRelClasses H.mirror.face darts h_all h_len darts,
        countOrbits_eq_countRelClasses H.face darts h_all h_len darts]
    rw [countRelClasses_eq_of_iff_mem (SameOrbit H.mirror.face)
      (sameOrbit_refl _) (sameOrbit_symm_of_complete _ darts h_all) (sameOrbit_trans _)
      darts (darts.map H.edge.f) hface_mem]
    exact countRelClasses_map_congr_aux H.edge.f H.edge_involution
      (SameOrbit H.mirror.face) (SameOrbit H.face)
      (sameOrbit_mirror_face_iff H darts h_all) darts.length darts (Nat.le_refl _)
  rw [hcomp, hedge, hnode, hface_rel]

theorem isPlanar_mirror (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) :
    H.mirror.isPlanar fuel darts = H.isPlanar fuel darts := by
  rw [Bool.eq_iff_iff]
  have hm := (eulerChar_le_two_mul_numComponents H.mirror darts h_nodup h_all h_len).2
  have hp := (eulerChar_le_two_mul_numComponents H darts h_nodup h_all h_len).2
  rw [hm, hp, genusDeficit_mirror_eq H darts h_all h_len]
  rfl

/-- Canonical orientation-normalized dual triangulation for a matched embedding:
    equals `H.dual` when `orient = false` and `H.dual.mirror` when `orient = true`,
    so `(orientedDual H orient).node = nodePermOriented H.dual orient`. -/
def orientedDual (H : Hypermap) (orient : Bool) : Hypermap where
  Dart := H.Dart
  edge := H.edge
  node := nodePermOriented H.dual orient
  face := if orient then H.dual.mirror.face else H.dual.face
  edge_involution := H.edge_involution
  edge_node_face_id := fun d => by
    cases orient
    · exact H.dual.edge_node_face_id d
    · exact H.dual.mirror.edge_node_face_id d

theorem orientedDual_edge (H : Hypermap) (orient : Bool) :
    (orientedDual H orient).edge = H.edge := rfl

theorem orientedDual_node_eq (H : Hypermap) (orient : Bool) :
    (orientedDual H orient).node = nodePermOriented H.dual orient := rfl

theorem orientedDual_sameOrbit_node_iff (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts) (orient : Bool) (x y : H.Dart) :
    SameOrbit (orientedDual H orient).node x y ↔ SameOrbit H.face x y := by
  have hdual : ∀ a b, SameOrbit H.dual.node a b ↔ SameOrbit H.face a b := fun a b =>
    (sameOrbit_symm_perm H.face).trans
      ⟨fun h => sameOrbit_symm_of_complete H.face darts h_all h,
       fun h => sameOrbit_symm_of_complete H.face darts h_all h⟩
  cases orient
  · exact hdual x y
  · change SameOrbit H.dual.mirror.node x y ↔ SameOrbit H.face x y
    exact (sameOrbit_mirror_node_iff H.dual darts h_all x y).trans (hdual x y)

theorem orientedDual_isPlanar (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (orient : Bool) :
    (orientedDual H orient).isPlanar fuel darts = H.isPlanar fuel darts := by
  cases orient
  · exact isPlanar_dual H darts h_nodup h_all h_len
  · change H.dual.mirror.isPlanar fuel darts = H.isPlanar fuel darts
    rw [isPlanar_mirror H.dual darts h_nodup h_all h_len, isPlanar_dual H darts h_nodup h_all h_len]

theorem orientedDual_face_cube (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_tri : ∀ d : H.Dart, d ∈ darts → faceDegree H.dual d darts.length = 3)
    (orient : Bool) (d : H.Dart) :
    (orientedDual H orient).face.f ((orientedDual H orient).face.f ((orientedDual H orient).face.f d)) = d := by
  have htri_dual : ∀ z : H.Dart, H.dual.face.f (H.dual.face.f (H.dual.face.f z)) = z := by
    intro z
    have h3 : (getOrbit H.dual.face darts.length z).length = 3 := h_tri z (h_all z)
    have hper := perm_iter_length_getOrbit_eq_self_of_complete
      H.dual.face darts h_all (Nat.le_refl darts.length) z
    rw [h3] at hper
    simpa [Perm.iter] using hper
  cases orient
  · exact htri_dual d
  · exact mirror_face_cube H.dual htri_dual d

end MirrorAndOrientedDual

section MultiEdgeExcision

/-- Jump invariant relating original permutation `p0` and bypassed permutation `p` on active set `A`:
    deleted darts (`¬ A z`) are fixed points of `p`, and surviving darts (`A z`) jump forward along
    `p0` to their first active iterate (`m ≥ 1`). -/
def BypassValid {D : Type} (p0 p : Perm D) (A : D → Prop) : Prop :=
  ∀ z, (¬ A z → p.f z = z) ∧
       (A z → ∃ m, 1 ≤ m ∧ p.f z = Perm.iter p0 m z ∧ ∀ j, 1 ≤ j → j < m → ¬ A (Perm.iter p0 j z))

theorem bypassValid_self {D : Type} (p0 : Perm D) :
    BypassValid p0 p0 (fun _ => True) := by
  intro z
  refine ⟨fun h => False.elim (h trivial), fun _ => ?_⟩
  exact ⟨1, Nat.le_refl 1, rfl, fun j hj1 hjm => by omega⟩

theorem bypassValid_step {D : Type} [DecidableEq D]
    (p0 p : Perm D) (A : D → Prop) (h : BypassValid p0 p A) (a : D) :
    BypassValid p0 (bypass p a) (fun z => A z ∧ z ≠ a) := by
  intro z
  constructor
  · intro hz
    by_cases hza : z = a
    · subst hza; simp [bypass]
    · have hnAz : ¬ A z := fun hAz => hz ⟨hAz, hza⟩
      have hpz : p.f z = z := (h z).1 hnAz
      dsimp [bypass]
      rw [if_neg hza, if_neg (by rw [hpz]; exact hza), hpz]
  · intro ⟨hAz, hza⟩
    obtain ⟨m1, hm1_ge, hm1_eq, hm1_skip⟩ := (h z).2 hAz
    by_cases hpa : p.f z = a
    · have hp_ne_a : p.f a ≠ a := fun hpa_eq => by
        have hz_eq := perm_f_inj_de p (hpa.trans hpa_eq.symm)
        exact hza hz_eq
      have hAa : A a := Classical.byContradiction fun hnAa =>
        hp_ne_a ((h a).1 hnAa)
      obtain ⟨m2, hm2_ge, hm2_eq, hm2_skip⟩ := (h a).2 hAa
      have h_byp : (bypass p a).f z = Perm.iter p0 (m1 + m2) z := by
        dsimp [bypass]
        rw [if_neg hza, if_pos hpa, hm2_eq, ← hpa, hm1_eq, ← Perm.iter_add, Nat.add_comm]
      refine ⟨m1 + m2, by omega, h_byp, fun j hj1 hjlt => ?_⟩
      by_cases hjm1 : j < m1
      · intro ⟨hAj, _⟩
        exact hm1_skip j hj1 hjm1 hAj
      · by_cases hjeq : j = m1
        · intro ⟨_, hjne⟩
          have hiter_a : Perm.iter p0 j z = a := by rw [hjeq, ← hm1_eq, hpa]
          exact hjne hiter_a
        · have hjgt : m1 < j := by omega
          intro ⟨hAj, _⟩
          have hj_diff : Perm.iter p0 j z = Perm.iter p0 (j - m1) a := by
            rw [← hpa, hm1_eq, ← Perm.iter_add, Nat.sub_add_cancel (Nat.le_of_lt hjgt)]
          rw [hj_diff] at hAj
          exact hm2_skip (j - m1) (by omega) (by omega) hAj
    · have h_byp : (bypass p a).f z = Perm.iter p0 m1 z := by
        dsimp [bypass]
        rw [if_neg hza, if_neg hpa, hm1_eq]
      exact ⟨m1, hm1_ge, h_byp, fun j hj1 hjlt ⟨hAj, _⟩ => hm1_skip j hj1 hjlt hAj⟩

theorem bypassValid_jump {D : Type} {p0 p : Perm D} {S : D → Prop}
    (hbv : BypassValid p0 p S) {x : D} (hx : S x)
    {k : Nat} (hk1 : 1 ≤ k) (hSk : S (Perm.iter p0 k x))
    (hskip : ∀ j, 1 ≤ j → j < k → ¬ S (Perm.iter p0 j x)) :
    p.f x = Perm.iter p0 k x := by
  obtain ⟨m, hm1, hmeq, hmskip⟩ := (hbv x).2 hx
  have hmk : m = k := Classical.byContradiction fun hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hskip m hm1 hlt (by
        rw [← hmeq]
        exact Classical.byContradiction fun hns => by
          have hfx_fix : p.f (p.f x) = p.f x := (hbv (p.f x)).1 hns
          have hx_fix : p.f x = x := perm_f_inj_de p hfx_fix
          rw [hx_fix] at hns
          exact hns hx)
    · exact hmskip k hk1 hgt hSk
  rw [hmeq, hmk]

theorem bypassValid_sameOrbit_iff {D : Type} {p0 p : Perm D} {S : D → Prop}
    (hbv : BypassValid p0 p S) {x y : D} (hx : S x) (hy : S y) :
    SameOrbit p x y ↔ SameOrbit p0 x y := by
  constructor
  · rintro ⟨n, hn⟩
    have hstep : ∀ z, SameOrbit p0 z (p.f z) := by
      intro z
      by_cases hSz : S z
      · obtain ⟨m, _, hmeq, _⟩ := (hbv z).2 hSz
        exact ⟨m, hmeq.symm⟩
      · exact ⟨0, ((hbv z).1 hSz).symm⟩
    have h_iter : ∀ m z, SameOrbit p0 z (Perm.iter p m z) := by
      intro m
      induction m with
      | zero => intro z; exact sameOrbit_refl p0 z
      | succ m ih =>
        intro z
        rw [Perm.iter_succ]
        exact sameOrbit_trans p0 (ih z) (hstep _)
    rw [← hn]
    exact h_iter n x
  · rintro ⟨n, hn⟩
    induction n using Nat.strongRecOn generalizing x with
    | _ n ih =>
      cases n with
      | zero => exact ⟨0, hn⟩
      | succ n' =>
        obtain ⟨m, hm1, hmeq, hmskip⟩ := (hbv x).2 hx
        have hmn : m ≤ n' + 1 := Classical.byContradiction fun hgt => by
          have hlt : n' + 1 < m := Nat.lt_of_not_le hgt
          have hbad := hmskip (n' + 1) (Nat.succ_pos n') hlt
          rw [hn] at hbad
          exact hbad hy
        have hSpx : S (p.f x) := Classical.byContradiction fun hns => by
          have hfix := perm_f_inj_de p ((hbv (p.f x)).1 hns)
          rw [hfix] at hns
          exact hns hx
        have hsub : n' + 1 - m < n' + 1 := by omega
        have hrem : Perm.iter p0 (n' + 1 - m) (p.f x) = y := by
          rw [hmeq, ← Perm.iter_add, Nat.sub_add_cancel hmn, hn]
        exact sameOrbit_trans p (sameOrbit_step p rfl) (ih (n' + 1 - m) hsub hSpx hrem)

private theorem uncoupleEdge_e_inv {D : Type} [DecidableEq D] (T : PermTriple D)
    (h_inv : ∀ x, T.e.f (T.e.f x) = x) (d : D) :
    let b := T.e.f d
    ∀ x, (uncoupleEdge T d b).e.f ((uncoupleEdge T d b).e.f x) = x := by
  intro b x
  have hb : T.e.f b = d := h_inv d
  by_cases hxd : x = d
  · subst hxd
    dsimp [uncoupleEdge, swapCompLeft]
    rw [swapFun_right, swapFun_right]
  · by_cases hxb : x = b
    · subst hxb
      dsimp [uncoupleEdge, swapCompLeft]
      change swapFun d b (T.e.f (swapFun d b (T.e.f b))) = b
      rw [hb, swapFun_left, hb, swapFun_left]
    · have hex_ne_d : T.e.f x ≠ d := fun heq => hxb (by dsimp [b]; rw [← heq, h_inv x])
      have hex_ne_b : T.e.f x ≠ b := fun heq => hxd (by
        calc x = T.e.f (T.e.f x) := (h_inv x).symm
        _ = T.e.f b := by rw [heq]
        _ = d := hb)
      dsimp [uncoupleEdge, swapCompLeft]
      change swapFun d b (T.e.f (swapFun d b (T.e.f x))) = x
      rw [swapFun_of_ne hex_ne_d hex_ne_b, h_inv x, swapFun_of_ne hxd hxb]

/-- Single-step edge deletion on a permutation triple with involution `e`. -/
def deleteEdgeStepTriple {D : Type} [DecidableEq D] (T : PermTriple D)
    (h_inv : ∀ x, T.e.f (T.e.f x) = x) (d : D) :
    { T' : PermTriple D // ∀ x, T'.e.f (T'.e.f x) = x } :=
  if _ : T.e.f d = d then ⟨T, h_inv⟩
  else
    let b := T.e.f d
    let T1 := uncoupleEdge T d b
    have h1d : T1.e.f d = d := by
      dsimp [T1, uncoupleEdge, swapCompLeft]
      exact swapFun_right d b
    let T2 := isolateFixed T1 d h1d
    have h2b : T2.e.f b = b := by
      dsimp [T2, isolateFixed, T1, uncoupleEdge, swapCompLeft]
      rw [h_inv d]
      exact swapFun_left d b
    ⟨isolateFixed T2 b h2b, uncoupleEdge_e_inv T h_inv d⟩

/-- Fold `deleteEdgeStepTriple` over a list of edge representatives `xs`. -/
def deleteEdgesFold {D : Type} [DecidableEq D]
    (T : { T' : PermTriple D // ∀ x, T'.e.f (T'.e.f x) = x }) :
    List D → { T' : PermTriple D // ∀ x, T'.e.f (T'.e.f x) = x }
  | [] => T
  | d :: ds => deleteEdgesFold (deleteEdgeStepTriple T.1 T.2 d) ds

theorem deleteEdgesFold_genusDeficit_le {D : Type} [DecidableEq D]
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_len : darts.length ≤ fuel) :
    ∀ (xs : List D) (T : { T' : PermTriple D // ∀ x, T'.e.f (T'.e.f x) = x }),
      genusDeficit (deleteEdgesFold T xs).1 fuel darts ≤ genusDeficit T.1 fuel darts
  | [], _ => Int.le_refl _
  | d :: ds, T => by
    dsimp [deleteEdgesFold]
    have h_ih := deleteEdgesFold_genusDeficit_le darts h_all h_len ds (deleteEdgeStepTriple T.1 T.2 d)
    have h_step : genusDeficit (deleteEdgeStepTriple T.1 T.2 d).1 fuel darts ≤
        genusDeficit T.1 fuel darts := by
      dsimp [deleteEdgeStepTriple]
      split
      · exact Int.le_refl _
      · rename_i hne
        let b := T.1.e.f d
        let T1 := uncoupleEdge T.1 d b
        have h1d : T1.e.f d = d := by
          dsimp [T1, uncoupleEdge, swapCompLeft]; exact swapFun_right d b
        let T2 := isolateFixed T1 d h1d
        have h2b : T2.e.f b = b := by
          dsimp [T2, isolateFixed, T1, uncoupleEdge, swapCompLeft]
          rw [T.2 d]; exact swapFun_left d b
        have hgd1 : genusDeficit T1 fuel darts ≤ genusDeficit T.1 fuel darts :=
          genusDeficit_uncoupleEdge_le T.1 darts h_all h_len hne
        have hgd2 : genusDeficit T2 fuel darts = genusDeficit T1 fuel darts :=
          genusDeficit_isolateFixed_eq T1 d h1d darts h_all h_len
        have hgd3 : genusDeficit (isolateFixed T2 b h2b) fuel darts = genusDeficit T2 fuel darts :=
          genusDeficit_isolateFixed_eq T2 b h2b darts h_all h_len
        change genusDeficit (isolateFixed T2 b h2b) fuel darts ≤ genusDeficit T.1 fuel darts
        omega
    exact Int.le_trans h_ih h_step

private structure EdgeDelInv {D : Type} (T0 : PermTriple D) (removed done : List D)
    (T : PermTriple D) (A : D → Prop) : Prop where
  he_out : ∀ z, T.e.f z = T0.e.f z ∨ T.e.f z = z
  he_orig : ∀ z, z ∉ removed → T.e.f z = T0.e.f z
  he_done : ∀ z ∈ done, T.e.f z = z
  hbv : BypassValid T0.n T.n A
  he_fix : ∀ z, T.e.f z = z ↔ ¬ A z

private theorem deleteEdgeStepTriple_inv {D : Type} [DecidableEq D]
    (T0 : PermTriple D) (removed done : List D)
    (h_closed : ∀ z, z ∈ removed ↔ T0.e.f z ∈ removed)
    {T : { T' : PermTriple D // ∀ x, T'.e.f (T'.e.f x) = x }} {A : D → Prop}
    (hinv : EdgeDelInv T0 removed done T.1 A)
    {d : D} (hd_mem : d ∈ removed) :
    ∃ A', EdgeDelInv T0 removed (d :: done) (deleteEdgeStepTriple T.1 T.2 d).1 A' := by
  dsimp [deleteEdgeStepTriple]
  by_cases hfix : T.1.e.f d = d
  · rw [if_pos hfix]
    refine ⟨A, hinv.he_out, hinv.he_orig, ?_, hinv.hbv, hinv.he_fix⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hzd
    · exact hfix
    · exact hinv.he_done z hzd
  · rw [if_neg hfix]
    let b := T.1.e.f d
    have hb_eq : b = T0.e.f d := by
      rcases hinv.he_out d with h1 | h2
      · exact h1
      · exact False.elim (hfix h2)
    have hb_mem : b ∈ removed := by rw [hb_eq]; exact (h_closed d).mp hd_mem
    have hbd : b ≠ d := hfix
    have hTbd : T.1.e.f b = d := T.2 d
    refine ⟨fun z => A z ∧ z ≠ d ∧ z ≠ b, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      by_cases hzd : z = d
      · right; subst hzd; dsimp [isolateFixed, uncoupleEdge, swapCompLeft]; exact swapFun_right _ _
      · by_cases hzb : z = b
        · right; subst hzb
          dsimp [isolateFixed, uncoupleEdge, swapCompLeft]; rw [hTbd]; exact swapFun_left d b
        · have hez_d : T.1.e.f z ≠ d := fun h => hzb (by dsimp [b]; rw [← h, T.2 z])
          have hez_b : T.1.e.f z ≠ b := fun h => hzd (by dsimp [b] at h; exact perm_f_inj_de T.1.e h)
          change swapFun d b (T.1.e.f z) = T0.e.f z ∨ swapFun d b (T.1.e.f z) = z
          rw [swapFun_of_ne hez_d hez_b]
          exact hinv.he_out z
    · intro z hz
      have hzd : z ≠ d := fun h => hz (h ▸ hd_mem)
      have hzb : z ≠ b := fun h => hz (h ▸ hb_mem)
      have hez_d : T.1.e.f z ≠ d := fun h => hzb (by dsimp [b]; rw [← h, T.2 z])
      have hez_b : T.1.e.f z ≠ b := fun h => hzd (by dsimp [b] at h; exact perm_f_inj_de T.1.e h)
      change swapFun d b (T.1.e.f z) = T0.e.f z
      rw [swapFun_of_ne hez_d hez_b]
      exact hinv.he_orig z hz
    · intro z hz
      by_cases hzd : z = d
      · subst hzd; dsimp [isolateFixed, uncoupleEdge, swapCompLeft]; exact swapFun_right _ _
      · by_cases hzb : z = b
        · subst hzb; dsimp [isolateFixed, uncoupleEdge, swapCompLeft]; rw [hTbd]; exact swapFun_left d b
        · rcases List.mem_cons.mp hz with rfl | hzd_mem
          · exact False.elim (hzd rfl)
          · have hfz : T.1.e.f z = z := hinv.he_done z hzd_mem
            change swapFun d b (T.1.e.f z) = z
            rw [hfz, swapFun_of_ne hzd hzb]
    · have h1 := bypassValid_step T0.n T.1.n A hinv.hbv d
      have h2 := bypassValid_step T0.n (bypass T.1.n d) _ h1 b
      change BypassValid T0.n (bypass (bypass T.1.n d) b) _
      refine fun z => ⟨fun hna => (h2 z).1 (fun ⟨⟨hAz, hzd⟩, hzb⟩ => hna ⟨hAz, hzd, hzb⟩),
        fun ⟨hAz, hzd, hzb⟩ => ?_⟩
      obtain ⟨m, hm1, hmeq, hmskip⟩ := (h2 z).2 ⟨⟨hAz, hzd⟩, hzb⟩
      exact ⟨m, hm1, hmeq, fun j hj1 hjlt ⟨hAj, hjd, hjb⟩ => hmskip j hj1 hjlt ⟨⟨hAj, hjd⟩, hjb⟩⟩
    · intro z
      by_cases hzd : z = d
      · subst hzd
        have hfix' : swapFun z b (T.1.e.f z) = z := swapFun_right _ _
        change swapFun z b (T.1.e.f z) = z ↔ ¬ (A z ∧ z ≠ z ∧ z ≠ b)
        simp [hfix']
      · by_cases hzb : z = b
        · have hfix' : swapFun d b (T.1.e.f z) = z := by rw [hzb, hTbd]; exact swapFun_left d b
          change swapFun d b (T.1.e.f z) = z ↔ ¬ (A z ∧ z ≠ d ∧ z ≠ b)
          rw [hfix']; simp [hzb]
        · have hez_d : T.1.e.f z ≠ d := fun h => hzb (by dsimp [b]; rw [← h, T.2 z])
          have hez_b : T.1.e.f z ≠ b := fun h => hzd (by dsimp [b] at h; exact perm_f_inj_de T.1.e h)
          change swapFun d b (T.1.e.f z) = z ↔ ¬ (A z ∧ z ≠ d ∧ z ≠ b)
          rw [swapFun_of_ne hez_d hez_b, hinv.he_fix z]
          simp [hzd, hzb]

private theorem deleteEdgesFold_inv {D : Type} [DecidableEq D]
    (T0 : PermTriple D) (removed : List D)
    (h_closed : ∀ z, z ∈ removed ↔ T0.e.f z ∈ removed) :
    ∀ (xs done : List D) (T : { T' : PermTriple D // ∀ x, T'.e.f (T'.e.f x) = x })
      (A : D → Prop),
      EdgeDelInv T0 removed done T.1 A →
      (∀ d ∈ xs, d ∈ removed) →
      ∃ A', EdgeDelInv T0 removed (xs ++ done) (deleteEdgesFold T xs).1 A'
  | [], done, _, A, hinv, _ => ⟨A, hinv⟩
  | d :: ds, done, T, A, hinv, hxs => by
    obtain ⟨A1, hinv1⟩ := deleteEdgeStepTriple_inv T0 removed done h_closed hinv
      (hxs d List.mem_cons_self)
    obtain ⟨A2, hinv2⟩ := deleteEdgesFold_inv T0 removed h_closed ds (d :: done)
      (deleteEdgeStepTriple T.1 T.2 d) A1 hinv1
      (fun x hx => hxs x (List.mem_cons_of_mem d hx))
    refine ⟨A2, hinv2.he_out, hinv2.he_orig, ?_, hinv2.hbv, hinv2.he_fix⟩
    intro z hz
    apply hinv2.he_done z
    simp only [List.mem_append, List.mem_cons] at hz ⊢
    rcases hz with (rfl | hzd) | hzdone
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hzd
    · exact Or.inr (Or.inr hzdone)

private theorem deleteEdgesFold_final_bv {D : Type} [DecidableEq D]
    (T0 : PermTriple D) (h_inv0 : ∀ x, T0.e.f (T0.e.f x) = x)
    (h_free : ∀ x : D, T0.e.f x ≠ x)
    (removed : List D) (h_closed : ∀ z, z ∈ removed ↔ T0.e.f z ∈ removed) :
    let Tf := (deleteEdgesFold ⟨T0, h_inv0⟩ removed).1
    (∀ z, z ∈ removed ↔ Tf.e.f z ∈ removed) ∧
    (∀ z, z ∈ removed ↔ Tf.n.f z ∈ removed) ∧
    (∀ z, z ∉ removed → Tf.e.f z = T0.e.f z) ∧
    BypassValid T0.n Tf.n (fun z => z ∉ removed) := by
  have hinit : EdgeDelInv T0 removed [] T0 (fun _ => True) :=
    { he_out := fun _ => Or.inl rfl
      he_orig := fun _ _ => rfl
      he_done := fun _ h => by cases h
      hbv := bypassValid_self T0.n
      he_fix := fun z => ⟨fun h => False.elim (h_free z h), fun h => False.elim (h trivial)⟩ }
  obtain ⟨Af, hinv⟩ :=
    deleteEdgesFold_inv T0 removed h_closed removed [] ⟨T0, h_inv0⟩ (fun _ => True) hinit
      (fun _ hd => hd)
  dsimp only
  let Tf := (deleteEdgesFold ⟨T0, h_inv0⟩ removed).1
  have hAf_iff : ∀ z, Af z ↔ z ∉ removed := by
    intro z
    by_cases hz : z ∈ removed
    · have hfix : Tf.e.f z = z := hinv.he_done z (List.mem_append.mpr (Or.inl hz))
      have hnA : ¬ Af z := (hinv.he_fix z).mp hfix
      exact ⟨fun h => False.elim (hnA h), fun h => False.elim (h hz)⟩
    · have hne : Tf.e.f z ≠ z := by
        rw [hinv.he_orig z hz]
        exact h_free z
      have hA : Af z := Classical.byContradiction fun hna =>
        hne ((hinv.he_fix z).mpr hna)
      exact ⟨fun _ => hz, fun _ => hA⟩
  have hbv : BypassValid T0.n Tf.n (fun z => z ∉ removed) := by
    intro z
    constructor
    · intro hnz
      exact (hinv.hbv z).1 (fun hAz => hnz ((hAf_iff z).mp hAz))
    · intro hnz
      obtain ⟨m, hm1, hmeq, hmskip⟩ := (hinv.hbv z).2 ((hAf_iff z).mpr hnz)
      exact ⟨m, hm1, hmeq, fun j hj1 hjlt hj => hmskip j hj1 hjlt ((hAf_iff _).mpr hj)⟩
  have he_fix_rem : ∀ z ∈ removed, Tf.e.f z = z := fun z hz =>
    hinv.he_done z (List.mem_append.mpr (Or.inl hz))
  have hn_fix_rem : ∀ z ∈ removed, Tf.n.f z = z := fun z hz =>
    (hbv z).1 (fun h => h hz)
  exact ⟨mem_removed_iff_of_fixed_on Tf.e removed he_fix_rem,
    mem_removed_iff_of_fixed_on Tf.n removed hn_fix_rem,
    hinv.he_orig, hbv⟩

/-- Construct the multi-edge-deleted subtype hypermap removing all darts in an `H.edge`-closed
    list `removed`, assuming `H` has no self-paired darts (`∀ d, H.edge.f d ≠ d`). -/
def deleteEdgesSubtype (H : Hypermap) [DecidableEq H.Dart]
    (removed : List H.Dart) (h_closed : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d) : Hypermap :=
  let Tf := (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).1
  have hspec := deleteEdgesFold_final_bv H.hypermapToTriple H.edge_involution h_free removed h_closed
  H.exciseSubtype removed Tf.e Tf.n Tf.f
    (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).2 Tf.enf_id
    hspec.1 hspec.2.1

instance instDecidableEqDeleteEdgesSubtype (H : Hypermap) [DecidableEq H.Dart]
    (removed : List H.Dart) (h_closed : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d) :
    DecidableEq (deleteEdgesSubtype H removed h_closed h_free).Dart := by
  dsimp only [deleteEdgesSubtype, Hypermap.exciseSubtype]
  exact Subtype.instDecidableEq

theorem deleteEdgesSubtype_isPlanar (H : Hypermap) [DecidableEq H.Dart]
    (darts removed : List H.Dart) (h_closed : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d)
    (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel fuel' : Nat} (h_fuel : darts.length ≤ fuel)
    (h_planar : H.isPlanar fuel darts = true)
    (darts' : List (deleteEdgesSubtype H removed h_closed h_free).Dart)
    (h_nodup' : darts'.Nodup)
    (h_comp' : ∀ x : (deleteEdgesSubtype H removed h_closed h_free).Dart, x ∈ darts')
    (h_fuel' : darts'.length ≤ fuel') :
    @Hypermap.isPlanar (deleteEdgesSubtype H removed h_closed h_free)
      (@instBEqOfDecidableEq _ inferInstance) fuel' darts' = true := by
  have hgd_le := deleteEdgesFold_genusDeficit_le darts h_all h_fuel removed
    ⟨H.hypermapToTriple, H.edge_involution⟩
  have hspec := deleteEdgesFold_final_bv H.hypermapToTriple H.edge_involution h_free removed h_closed
  have hfree' : ∀ d : H.Dart, ¬ d ∈ removed →
      (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).1.e.f d ≠ d := by
    intro d hd
    rw [hspec.2.2.1 d hd]
    exact h_free d
  let H' := deleteEdgesSubtype H removed h_closed h_free
  have hres := exciseSubtype_isPlanar_of_perm H darts removed _ _ _
    (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).2
    (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).1.enf_id
    hspec.1 hspec.2.1 h_nodup h_all h_fuel h_planar hgd_le hfree' darts' h_nodup' h_comp' h_fuel'
  dsimp only [deleteEdgesSubtype]
  rwa [instBEqOfDecidableEq_eq_de inferInstance
    (H.instDecidableEqExciseDart removed _ _ _
      (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).2
      (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).1.enf_id
      hspec.1 hspec.2.1)]

theorem deleteEdgesSubtype_edge_val (H : Hypermap) [DecidableEq H.Dart]
    (removed : List H.Dart) (h_closed : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d)
    (x : (deleteEdgesSubtype H removed h_closed h_free).Dart) :
    ((deleteEdgesSubtype H removed h_closed h_free).edge.f x).val = H.edge.f x.val :=
  (deleteEdgesFold_final_bv H.hypermapToTriple H.edge_involution h_free removed h_closed).2.2.1
    x.val x.property

theorem deleteEdgesSubtype_node_jump (H : Hypermap) [DecidableEq H.Dart]
    (removed : List H.Dart) (h_closed : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d)
    (x : (deleteEdgesSubtype H removed h_closed h_free).Dart)
    {k : Nat} (hk1 : 1 ≤ k) (hSk : Perm.iter H.node k x.val ∉ removed)
    (hskip : ∀ j, 1 ≤ j → j < k → Perm.iter H.node j x.val ∈ removed) :
    ((deleteEdgesSubtype H removed h_closed h_free).node.f x).val = Perm.iter H.node k x.val :=
  bypassValid_jump
    (deleteEdgesFold_final_bv H.hypermapToTriple H.edge_involution h_free removed h_closed).2.2.2
    x.property hk1 hSk (fun j hj1 hjlt => Classical.not_not.mpr (hskip j hj1 hjlt))

theorem deleteEdgesSubtype_sameOrbit_node_iff (H : Hypermap) [DecidableEq H.Dart]
    (removed : List H.Dart) (h_closed : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d)
    (x y : (deleteEdgesSubtype H removed h_closed h_free).Dart) :
    SameOrbit (deleteEdgesSubtype H removed h_closed h_free).node x y ↔
      SameOrbit H.node x.val y.val := by
  let H' := deleteEdgesSubtype H removed h_closed h_free
  have hiter : ∀ m (z : H'.Dart), (Perm.iter H'.node m z).val =
      Perm.iter (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).1.n m z.val := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro z
      rw [Perm.iter_succ, Perm.iter_succ]
      change (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).1.n.f
          (Perm.iter H'.node m z).val = _
      rw [ih z]
  have hiff1 : SameOrbit H'.node x y ↔
      SameOrbit (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ removed).1.n x.val y.val := by
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, by rw [← hiter m x, hm]⟩
    · rintro ⟨m, hm⟩
      refine ⟨m, Subtype.ext ?_⟩
      rw [hiter m x, hm]
  exact hiff1.trans (bypassValid_sameOrbit_iff
    (deleteEdgesFold_final_bv H.hypermapToTriple H.edge_involution h_free removed h_closed).2.2.2
    x.property y.property)

instance instDecidableEqDeleteEdgesSubtypeDual (H : Hypermap) [DecidableEq H.Dart]
    (removed : List H.Dart) (h_closed : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d) :
    DecidableEq (deleteEdgesSubtype H removed h_closed h_free).dual.Dart := by
  dsimp only [Hypermap.dual]
  exact instDecidableEqDeleteEdgesSubtype H removed h_closed h_free

theorem deleteEdgesSubtype_dual_isBridgeless
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_bridge : Math.Hypermap.isBridgeless H darts darts.length)
    (orient : Bool) (removed : List H.Dart)
    (h_closed : ∀ d, d ∈ removed ↔ (orientedDual H orient).edge.f d ∈ removed)
    (h_free : ∀ d : H.Dart, (orientedDual H orient).edge.f d ≠ d)
    (darts' : List (deleteEdgesSubtype (orientedDual H orient) removed h_closed h_free).dual.Dart) :
    Math.Hypermap.isBridgeless (deleteEdgesSubtype (orientedDual H orient) removed h_closed h_free).dual
      darts' darts'.length := by
  let T0 := orientedDual H orient
  let T' := deleteEdgesSubtype T0 removed h_closed h_free
  intro d' hd'
  refine Classical.byContradiction fun hbr => ?_
  have hbr' : (getOrbit T'.dual.face darts'.length d').contains (T'.dual.edge.f d') = true := by
    cases hb : Math.Hypermap.isBridge T'.dual d' darts'.length <;> simp_all [Math.Hypermap.isBridge, Math.Hypermap.sameFace]
    exact hb hbr
  rw [List.contains_iff_mem] at hbr'
  obtain ⟨k, _, hk⟩ := mem_getOrbit_imp_exists_iter T'.dual.face darts'.length d' (T'.dual.edge.f d') hbr'
  have hso_f : SameOrbit T'.dual.face d' (T'.dual.edge.f d') := ⟨k, hk.symm⟩
  change SameOrbit T'.node.symm d' (T'.edge.f d') at hso_f
  have hso_n : SameOrbit T'.node (T'.edge.f d') d' := (sameOrbit_symm_perm T'.node).mp hso_f
  have hso_T0 : SameOrbit T0.node (T'.edge.f d').val d'.val :=
    (deleteEdgesSubtype_sameOrbit_node_iff T0 removed h_closed h_free (T'.edge.f d') d').mp hso_n
  have he_val : (T'.edge.f d').val = H.edge.f d'.val := by
    have := deleteEdgesSubtype_edge_val T0 removed h_closed h_free d'
    rwa [orientedDual_edge] at this
  rw [he_val] at hso_T0
  have hso_H : SameOrbit H.face (H.edge.f d'.val) d'.val :=
    (orientedDual_sameOrbit_node_iff H darts h_all orient _ _).mp hso_T0
  have hso_H_sym : SameOrbit H.face d'.val (H.edge.f d'.val) :=
    sameOrbit_symm_of_complete H.face darts h_all hso_H
  obtain ⟨m, hm⟩ := hso_H_sym
  have hcloses := orbitClosesWithin_mono H.face d'.val d'.val
    (orbitClosesWithin_of_complete H.face darts h_all d'.val) (Nat.le_refl darts.length)
  have hmem := iter_mem_getOrbit_of_closes H.face darts.length d'.val hcloses m
  rw [hm] at hmem
  have hb_orig := h_bridge d'.val (h_all d'.val)
  change (getOrbit H.face darts.length d'.val).contains (H.edge.f d'.val) = false at hb_orig
  rw [List.contains_iff_mem.mpr hmem] at hb_orig
  exact Bool.false_ne_true hb_orig.symm

end MultiEdgeExcision

section ConfigurationDiskExcision

private theorem mem_of_mem_dropLast_de {α : Type} {x : α} :
    ∀ {l : List α}, x ∈ l.dropLast → x ∈ l
  | [], h => by cases h
  | [_], h => by cases h
  | a :: b :: t, h => by
    change x ∈ a :: (b :: t).dropLast at h
    rcases List.mem_cons.mp h with rfl | ht
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (mem_of_mem_dropLast_de ht))

/-- Decidable check for whether dart `d` lies on some interior vertex `p.emb.rep u`
    (`c.ringSize ≤ u < c.totalNodes`) of the configuration embedding in `H.dual`. -/
def isIntVertBool (c : Configuration) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (rep : Nat → T.Dart) (d : T.Dart) : Bool :=
  (List.range c.interiorSize).any fun k => sameVertex T d (rep (c.ringSize + k)) darts.length

theorem isIntVertBool_eq_true_iff (c : Configuration) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (rep : Nat → T.Dart) (d : T.Dart) :
    isIntVertBool c T darts rep d = true ↔
      ∃ u, c.ringSize ≤ u ∧ u < c.totalNodes ∧ sameVertex T d (rep u) darts.length = true := by
  simp only [isIntVertBool, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨k, hk, hsv⟩
    exact ⟨c.ringSize + k, Nat.le_add_right _ _, by dsimp [Configuration.totalNodes]; omega, hsv⟩
  · rintro ⟨u, hur, hun, hsv⟩
    refine ⟨u - c.ringSize, ?_, ?_⟩
    · dsimp [Configuration.totalNodes] at hun; omega
    · rw [show c.ringSize + (u - c.ringSize) = u by omega]; exact hsv

/-- Decidable interior-edge-incident dart filter: `d` is deleted iff `d` or `H.edge.f d`
    belongs to an interior vertex `p.emb.rep u` (`c.ringSize ≤ u < c.totalNodes`). -/
def isIntDartBool (c : Configuration) (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (rep : Nat → H.Dart) (d : H.Dart) : Bool :=
  isIntVertBool c H.dual darts rep d || isIntVertBool c H.dual darts rep (H.edge.f d)

/-- List of all darts incident to at least one interior configuration vertex. -/
def removedIntDarts (c : Configuration) (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (rep : Nat → H.Dart) : List H.Dart :=
  darts.filter (isIntDartBool c H darts rep)

theorem removedIntDarts_mem_iff (c : Configuration) (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (rep : Nat → H.Dart) (d : H.Dart) :
    d ∈ removedIntDarts c H darts rep ↔
      isIntVertBool c H.dual darts rep d = true ∨
        isIntVertBool c H.dual darts rep (H.edge.f d) = true := by
  simp [removedIntDarts, List.mem_filter, h_all d, isIntDartBool, Bool.or_eq_true]

theorem removedIntDarts_edge_closed (c : Configuration) (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (rep : Nat → H.Dart) (orient : Bool) :
    ∀ d : H.Dart, d ∈ removedIntDarts c H darts rep ↔
      (orientedDual H orient).edge.f d ∈ removedIntDarts c H darts rep := by
  intro d
  rw [orientedDual_edge, removedIntDarts_mem_iff c H darts h_all rep d,
      removedIntDarts_mem_iff c H darts h_all rep (H.edge.f d), H.edge_involution]
  exact or_comm

private theorem mc_dual_tri {H : Hypermap} [DecidableEq H.Dart] {darts : List H.Dart}
    (h_mc : PrimalMinimalCounterexample H darts) :
    ∀ d : H.Dart, d ∈ darts → faceDegree H.dual d darts.length = 3 := by
  intro d _
  rw [faceDegree_dual_eq_nodeDegree_of_complete H darts h_mc.complete (Nat.le_refl _) d]
  exact mc_nodeDegree_eq_three H darts h_mc d

private theorem mc_dual_loopless {H : Hypermap} [DecidableEq H.Dart] {darts : List H.Dart}
    (h_mc : PrimalMinimalCounterexample H darts) :
    ∀ d : H.Dart, sameVertex H.dual d (H.dual.edge.f d) darts.length = false := by
  intro d
  exact dual_sameVertex_edge_eq_false_of_isBridgeless H darts h_mc.complete
    (Nat.le_refl _) (Nat.le_refl _) h_mc.is_bridgeless d

private theorem mc_oriented_edge_free {H : Hypermap} [DecidableEq H.Dart] {darts : List H.Dart}
    (h_mc : PrimalMinimalCounterexample H darts) (orient : Bool) :
    ∀ d : H.Dart, (orientedDual H orient).edge.f d ≠ d := by
  intro d
  rw [orientedDual_edge]
  exact mc_edge_ne_self H darts h_mc d

private theorem fanHead_spec (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (T : Hypermap) [DecidableEq T.Dart] (darts : List T.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) T darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) T darts p.emb)
    (x : Nat) (hx : x < (parsedRConfList[h]'hlen).r) :
    ∃ (hx_adj : x < (parsedRConfList[h]'hlen).adj.size),
      let fans := (((parsedRConfList[h]'hlen).adj[x]'hx_adj).toList.drop 1).dropLast
      ∃ hf0 : 0 < fans.length,
        let f0 := fans[0]'hf0
        let c := configOfRConf (parsedRConfList[h]'hlen)
        c.ringSize ≤ f0 ∧ f0 < c.totalNodes ∧ c.adj f0 x = true := by
  have hhdr := fastConf_equiv_header h hh
  have hring := fastConf_equiv_ring_and_fans h hh
  have hadj := fastConf_equiv_adj h hh
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  have hx_c : x < c.ringSize := hhdr.2.2.1 ▸ hx
  have hx_tot : x < c.totalNodes := Nat.lt_of_lt_of_le hx_c (Nat.le_add_right _ _)
  have hx_adj : x < rc.adj.size := by rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; exact hx_tot
  have hrf := hfan x hx hx_adj
  have hf0 : 0 < (((rc.adj[x]'hx_adj).toList.drop 1).dropLast).length :=
    list_length_pos_of_ne_nil hrf.1
  let fans := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast
  let f0 := fans[0]'hf0
  have hf0_mem : f0 ∈ fans := List.getElem_mem _
  have hf0_r : c.ringSize ≤ f0 := (hring.2 x hx_c).2.2.2.1 f0 hf0_mem
  have hf0_adj_mem : f0 ∈ (rc.adj[x]'hx_adj).toList := List.mem_of_mem_drop (mem_of_mem_dropLast_de hf0_mem)
  have hf0_spec := (hadj.1 x hx_tot).2 f0 hf0_adj_mem
  have hadj_xf : c.adj x f0 = true :=
    (hadj.2.1 x hx_tot f0 hf0_spec.1).trans (List.contains_iff_mem.mpr hf0_adj_mem)
  have hadj_sym : c.adj f0 x = true := by
    rw [p.adj_symm f0 x hf0_spec.1 hx_tot]; exact hadj_xf
  exact ⟨hx_adj, hf0, hf0_r, hf0_spec.1, hadj_sym⟩

/-- Canonical raw ring dart in `H.Dart` at boundary index `x < rc.r`, constructed as
    `(orientedDual H p.emb.orient).face.f (p.emb.dart (fans[0]) x)`. -/
def capRingRawDart (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (x : Nat) (hx : x < (parsedRConfList[h]'hlen).r) : H.Dart :=
  have hhdr := fastConf_equiv_header h hh
  let rc := parsedRConfList[h]'hlen
  have hx_adj : x < rc.adj.size := by
    have h1 : rc.adj.size = (configOfRConf rc).totalNodes := hhdr.2.2.2.2.2.2.2.2.2.2.2.1
    have h2 : (configOfRConf rc).ringSize = rc.r := hhdr.2.2.1
    have h3 : (configOfRConf rc).totalNodes = (configOfRConf rc).ringSize + (configOfRConf rc).interiorSize := rfl
    rw [h1, h3, h2]
    exact Nat.lt_of_lt_of_le hx (Nat.le_add_right _ _)
  have hrf := hfan x hx hx_adj
  have hf0 : 0 < (((rc.adj[x]'hx_adj).toList.drop 1).dropLast).length :=
    list_length_pos_of_ne_nil hrf.1
  let f0 := (((rc.adj[x]'hx_adj).toList.drop 1).dropLast)[0]'hf0
  (orientedDual H p.emb.orient).face.f (p.emb.dart f0 x)

private theorem capRingRawDart_equations (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (x : Nat) (hx : x < (parsedRConfList[h]'hlen).r) :
    let rc := parsedRConfList[h]'hlen
    let T0 := orientedDual H p.emb.orient
    let hx_adj : x < rc.adj.size := by
      have h1 : rc.adj.size = (configOfRConf rc).totalNodes :=
        (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
      have h2 : (configOfRConf rc).ringSize = rc.r := (fastConf_equiv_header h hh).2.2.1
      have h3 : (configOfRConf rc).totalNodes = (configOfRConf rc).ringSize + (configOfRConf rc).interiorSize := rfl
      rw [h1, h3, h2]
      exact Nat.lt_of_lt_of_le hx (Nat.le_add_right _ _)
    let fans := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast
    let f0 := fans[0]'(list_length_pos_of_ne_nil (hfan x hx hx_adj).1)
    let dx := capRingRawDart h hh hlen H darts p hfan x hx
    T0.node.f dx = H.edge.f (p.emb.dart f0 x) ∧
    H.edge.f dx = T0.node.f (H.edge.f (p.emb.dart f0 ((x + 1) % rc.r))) := by
  intro rc T0 hx_adj fans f0 dx
  have h_edge_eq : T0.edge = H.edge := orientedDual_edge H p.emb.orient
  have h_node_eq : T0.node = nodePermOriented H.dual p.emb.orient := orientedDual_node_eq H p.emb.orient
  have h_tri0 : ∀ z : H.Dart, T0.face.f (T0.face.f (T0.face.f z)) = z :=
    orientedDual_face_cube H darts h_mc.complete (mc_dual_tri h_mc) p.emb.orient
  have h1 : T0.node.f dx = H.edge.f (p.emb.dart f0 x) := by
    have h_id := T0.edge_node_face_id (p.emb.dart f0 x)
    have h_e := congrArg T0.edge.f h_id
    rw [T0.edge_involution] at h_e
    change T0.node.f dx = T0.edge.f (p.emb.dart f0 x) at h_e
    rwa [h_edge_eq] at h_e
  have h2 : H.edge.f dx = T0.node.f (H.edge.f (p.emb.dart f0 ((x + 1) % rc.r))) := by
    have hrf := hfan x hx hx_adj
    have hf0 : 0 < fans.length := list_length_pos_of_ne_nil hrf.1
    have hturn := hrf.2.2.1 hf0
    change p.emb.dart f0 ((x + 1) % rc.r) = T0.node.f (p.emb.dart f0 x) at hturn
    have h_fen := T0.face_edge_node_id (p.emb.dart f0 x)
    rw [← hturn] at h_fen
    have h_f2 := congrArg T0.face.f h_fen
    change T0.face.f (T0.face.f (T0.edge.f (p.emb.dart f0 ((x + 1) % rc.r)))) = dx at h_f2
    have h_f3 := congrArg T0.face.f h_f2
    rw [h_tri0] at h_f3
    have h_id := T0.edge_node_face_id dx
    have h_e := congrArg T0.edge.f h_id
    rw [T0.edge_involution, ← h_f3, h_edge_eq] at h_e
    exact h_e.symm
  exact ⟨h1, h2⟩

theorem capRingRawDart_vertex (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (x : Nat) (hx : x < (parsedRConfList[h]'hlen).r) :
    sameVertex H.dual (capRingRawDart h hh hlen H darts p hfan x hx) (p.emb.rep x) darts.length = true := by
  have heq := capRingRawDart_equations h hh hlen H darts h_mc p hfan x hx
  obtain ⟨hx_adj, hf0, hf0_r, hf0_tot, hadj⟩ := fanHead_spec h hh hlen H.dual darts p hfan x hx
  have hhdr := fastConf_equiv_header h hh
  have hx_tot : x < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by
    have : (configOfRConf (parsedRConfList[h]'hlen)).ringSize = (parsedRConfList[h]'hlen).r := hhdr.2.2.1
    change _ < (configOfRConf (parsedRConfList[h]'hlen)).ringSize + _
    omega
  have hsv_edge : sameVertex H.dual (H.edge.f (p.emb.dart _ x)) (p.emb.rep x) darts.length = true :=
    p.emb.dart_edge_same_vertex_rep _ hf0_r hf0_tot x hx_tot hadj
  have h_node_eq : (orientedDual H p.emb.orient).node = nodePermOriented H.dual p.emb.orient :=
    orientedDual_node_eq H p.emb.orient
  have hsv_step := sameVertex_permOriented_f H.dual darts h_mc.complete (Nat.le_refl _) p.emb.orient
    (capRingRawDart h hh hlen H darts p hfan x hx)
  rw [← h_node_eq] at hsv_step
  have h_sym : sameVertex H.dual (capRingRawDart h hh hlen H darts p hfan x hx)
      ((orientedDual H p.emb.orient).node.f (capRingRawDart h hh hlen H darts p hfan x hx)) darts.length = true := by
    rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]
    exact hsv_step
  rw [heq.1] at h_sym
  exact sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _) h_sym hsv_edge

theorem capRingRawDart_edge_vertex (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (x : Nat) (hx : x < (parsedRConfList[h]'hlen).r) :
    let rc := parsedRConfList[h]'hlen
    sameVertex H.dual (H.edge.f (capRingRawDart h hh hlen H darts p hfan x hx))
      (p.emb.rep ((x + 1) % rc.r)) darts.length = true := by
  intro rc
  have heq := capRingRawDart_equations h hh hlen H darts h_mc p hfan x hx
  have hhdr := fastConf_equiv_header h hh
  have hring := fastConf_equiv_ring_and_fans h hh
  have hadj_cert := fastConf_equiv_adj h hh
  let c := configOfRConf rc
  have hr6 : 6 ≤ c.ringSize := hhdr.2.2.2.2.2.1
  have hr_eq : c.ringSize = rc.r := hhdr.2.2.1
  have hnext_r : (x + 1) % rc.r < rc.r := Nat.mod_lt _ (by omega)
  have hnext_c : (x + 1) % rc.r < c.ringSize := hr_eq ▸ hnext_r
  have hnext_tot : (x + 1) % rc.r < c.totalNodes := Nat.lt_of_lt_of_le hnext_c (Nat.le_add_right _ _)
  obtain ⟨hx_adj, hf0, hf0_r, hf0_tot, _⟩ := fanHead_spec h hh hlen H.dual darts p hfan x hx
  have hnext_adj : (x + 1) % rc.r < rc.adj.size := by
    rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]
    exact hnext_tot
  have hlast := (hfan x hx hx_adj).2.2.2.1 hnext_adj hf0
  have hf0_in_next : ((rc.adj[x]'hx_adj).toList.drop 1).dropLast[0]'hf0 ∈
      ((rc.adj[(x + 1) % rc.r]'hnext_adj).toList.drop 1).dropLast :=
    List.mem_of_getLast? hlast
  have hf0_in_next_adj : ((rc.adj[x]'hx_adj).toList.drop 1).dropLast[0]'hf0 ∈
      (rc.adj[(x + 1) % rc.r]'hnext_adj).toList :=
    List.mem_of_mem_drop (mem_of_mem_dropLast_de hf0_in_next)
  let f0 := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast[0]'hf0
  have hf0_lt_from_next : f0 < c.totalNodes :=
    ((hadj_cert.1 ((x + 1) % rc.r) hnext_tot).2 f0 hf0_in_next_adj).1
  have hadj_nf : c.adj ((x + 1) % rc.r) f0 = true :=
    (hadj_cert.2.1 ((x + 1) % rc.r) hnext_tot f0 hf0_lt_from_next).trans
      (List.contains_iff_mem.mpr hf0_in_next_adj)
  have hadj_fn : c.adj f0 ((x + 1) % rc.r) = true := by
    rw [p.adj_symm f0 ((x + 1) % rc.r) hf0_tot hnext_tot]; exact hadj_nf
  have hsv_edge : sameVertex H.dual (H.edge.f (p.emb.dart f0 ((x + 1) % rc.r)))
      (p.emb.rep ((x + 1) % rc.r)) darts.length = true :=
    p.emb.dart_edge_same_vertex_rep f0 hf0_r hf0_tot ((x + 1) % rc.r) hnext_tot hadj_fn
  have h_node_eq : (orientedDual H p.emb.orient).node = nodePermOriented H.dual p.emb.orient :=
    orientedDual_node_eq H p.emb.orient
  have hsv_step := sameVertex_permOriented_f H.dual darts h_mc.complete (Nat.le_refl _) p.emb.orient
    (H.edge.f (p.emb.dart f0 ((x + 1) % rc.r)))
  rw [← h_node_eq, ← heq.2] at hsv_step
  exact sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _) hsv_step hsv_edge

theorem capRingRawDart_not_mem_removed (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (x : Nat) (hx : x < (parsedRConfList[h]'hlen).r) :
    capRingRawDart h hh hlen H darts p hfan x hx ∉
      removedIntDarts (configOfRConf (parsedRConfList[h]'hlen)) H darts p.emb.rep := by
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  have hhdr := fastConf_equiv_header h hh
  have hr_eq : c.ringSize = rc.r := hhdr.2.2.1
  have hr6 : 6 ≤ c.ringSize := hhdr.2.2.2.2.2.1
  have no_int : ∀ z (ridx : Nat), ridx < c.ringSize →
      sameVertex H.dual z (p.emb.rep ridx) darts.length = true →
      isIntVertBool c H.dual darts p.emb.rep z = false := by
    intro z ridx hridx hsv_zr
    rw [Bool.eq_false_iff]
    intro hint
    obtain ⟨u, hur, hun, hsv_zu⟩ := (isIntVertBool_eq_true_iff c H.dual darts p.emb.rep z).mp hint
    have hsv_rz : sameVertex H.dual (p.emb.rep ridx) z darts.length = true := by
      rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]
      exact hsv_zr
    have hsv_ur := sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _)
      (by rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]; exact hsv_zu) hsv_zr
    have hf := p.emb.int_ring_distinct u ridx hur hun hridx
    rw [hsv_ur] at hf
    cases hf
  rw [removedIntDarts_mem_iff c H darts h_mc.complete p.emb.rep]
  have h1 := no_int (capRingRawDart h hh hlen H darts p hfan x hx) x (hr_eq ▸ hx)
    (capRingRawDart_vertex h hh hlen H darts h_mc p hfan x hx)
  have hnext : (x + 1) % rc.r < c.ringSize := hr_eq ▸ Nat.mod_lt _ (by omega)
  have h2 := no_int (H.edge.f (capRingRawDart h hh hlen H darts p hfan x hx)) ((x + 1) % rc.r) hnext
    (capRingRawDart_edge_vertex h hh hlen H darts h_mc p hfan x hx)
  rintro (ht1 | ht2)
  · rw [h1] at ht1; cases ht1
  · rw [h2] at ht2; cases ht2

theorem capRingRawDart_inj (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {x y : Nat} (hx : x < (parsedRConfList[h]'hlen).r) (hy : y < (parsedRConfList[h]'hlen).r)
    (heq : capRingRawDart h hh hlen H darts p hfan x hx =
           capRingRawDart h hh hlen H darts p hfan y hy) : x = y := by
  let T0 := orientedDual H p.emb.orient
  have hinj_f := congrArg T0.face.inv heq
  dsimp only [capRingRawDart] at hinj_f
  rw [T0.face.left_inv, T0.face.left_inv] at hinj_f
  obtain ⟨hx_adj, hf0x, hfx_r, hfx_tot, hadjx⟩ := fanHead_spec h hh hlen H.dual darts p hfan x hx
  obtain ⟨hy_adj, hf0y, hfy_r, hfy_tot, hadjy⟩ := fanHead_spec h hh hlen H.dual darts p hfan y hy
  let fx := (((parsedRConfList[h]'hlen).adj[x]'hx_adj).toList.drop 1).dropLast[0]'hf0x
  let fy := (((parsedRConfList[h]'hlen).adj[y]'hy_adj).toList.drop 1).dropLast[0]'hf0y
  have hhdr := fastConf_equiv_header h hh
  have hr_eq : (configOfRConf (parsedRConfList[h]'hlen)).ringSize = (parsedRConfList[h]'hlen).r :=
    hhdr.2.2.1
  have hx_tot : x < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes :=
    Nat.lt_of_lt_of_le (hr_eq ▸ hx) (Nat.le_add_right _ _)
  have hy_tot : y < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes :=
    Nat.lt_of_lt_of_le (hr_eq ▸ hy) (Nat.le_add_right _ _)
  have hsv_fx := p.emb.dart_same_vertex_rep fx hfx_r hfx_tot x hx_tot hadjx
  have hsv_fy := p.emb.dart_same_vertex_rep fy hfy_r hfy_tot y hy_tot hadjy
  change p.emb.dart fx x = p.emb.dart fy y at hinj_f
  rw [hinj_f] at hsv_fx
  have hsv_repx : sameVertex H.dual (p.emb.rep fx) (p.emb.dart fy y) darts.length = true := by
    rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]
    exact hsv_fx
  have hsv_fxy : sameVertex H.dual (p.emb.rep fx) (p.emb.rep fy) darts.length = true :=
    sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _) hsv_repx hsv_fy
  have hfeq : fx = fy := Classical.byContradiction fun hne => by
    have hf := p.emb.int_distinct fx fy hfx_r hfx_tot hfy_r hfy_tot hne
    rw [hsv_fxy] at hf; cases hf
  exact Classical.byContradiction fun hxy_ne => by
    change (configOfRConf (parsedRConfList[h]'hlen)).adj fx x = true at hadjx
    rw [hfeq] at hadjx hinj_f
    exact p.emb.int_inj_neighbor fy hfy_r hfy_tot x y hx_tot hy_tot hadjx hadjy hxy_ne hinj_f

/-- Surviving dual triangulation obtained from `orientedDual H p.emb.orient` by excising all
    darts incident to interior vertices of `c`. -/
def capTriangulation (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    Hypermap :=
  let _ := hh
  deleteEdgesSubtype (orientedDual H p.emb.orient)
    (removedIntDarts (configOfRConf (parsedRConfList[h]'hlen)) H darts p.emb.rep)
    (removedIntDarts_edge_closed _ H darts h_mc.complete p.emb.rep p.emb.orient)
    (mc_oriented_edge_free h_mc p.emb.orient)

/-- Primal capped-ring hypermap `H_cap := capTriangulation.dual`. -/
def capHypermap (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    Hypermap :=
  (capTriangulation h hh hlen H darts h_mc p).dual

instance instDecidableEqCapTriangulation (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    DecidableEq (capTriangulation h hh hlen H darts h_mc p).Dart :=
  instDecidableEqDeleteEdgesSubtype (orientedDual H p.emb.orient)
    (removedIntDarts (configOfRConf (parsedRConfList[h]'hlen)) H darts p.emb.rep)
    (removedIntDarts_edge_closed _ H darts h_mc.complete p.emb.rep p.emb.orient)
    (mc_oriented_edge_free h_mc p.emb.orient)

instance instDecidableEqCapTriangulationDual (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    DecidableEq (capTriangulation h hh hlen H darts h_mc p).dual.Dart := by
  dsimp only [Hypermap.dual]
  exact instDecidableEqCapTriangulation h hh hlen H darts h_mc p

instance instDecidableEqCapHypermap (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    DecidableEq (capHypermap h hh hlen H darts h_mc p).Dart :=
  instDecidableEqCapTriangulationDual h hh hlen H darts h_mc p

/-- Surviving complete dart list `subDarts darts removedIntDarts` for `capHypermap`. -/
def capDarts (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    List (capHypermap h hh hlen H darts h_mc p).Dart :=
  subDarts darts (removedIntDarts (configOfRConf (parsedRConfList[h]'hlen)) H darts p.emb.rep)

/-- Canonical surviving ring dart in `capHypermap.Dart` indexed by `x < rc.r`. -/
def capRingDart (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (x : Nat) (hx : x < (parsedRConfList[h]'hlen).r) :
    (capHypermap h hh hlen H darts h_mc p).Dart :=
  ⟨capRingRawDart h hh hlen H darts p hfan x hx,
   capRingRawDart_not_mem_removed h hh hlen H darts h_mc p hfan x hx⟩

private theorem capRingDart_eq_of_eq (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {x y : Nat} (hx : x < (parsedRConfList[h]'hlen).r)
    (hy : y < (parsedRConfList[h]'hlen).r) (hxy : x = y) :
    capRingDart h hh hlen H darts h_mc p hfan x hx =
      capRingDart h hh hlen H darts h_mc p hfan y hy := by
  subst hxy; rfl

theorem capDarts_nodup (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    (capDarts h hh hlen H darts h_mc p).Nodup :=
  subDarts_nodup darts _ h_mc.nodup

theorem capDarts_complete (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    ∀ x : (capHypermap h hh hlen H darts h_mc p).Dart, x ∈ capDarts h hh hlen H darts h_mc p := by
  intro x
  exact (mem_subDarts darts _ x).mpr (h_mc.complete x.val)

theorem capDarts_nonempty (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb) :
    capDarts h hh hlen H darts h_mc p ≠ [] := by
  have hhdr := fastConf_equiv_header h hh
  have hr6 : 6 ≤ (configOfRConf (parsedRConfList[h]'hlen)).ringSize := hhdr.2.2.2.2.2.1
  have hr_eq : (configOfRConf (parsedRConfList[h]'hlen)).ringSize = (parsedRConfList[h]'hlen).r :=
    hhdr.2.2.1
  have h0_lt : 0 < (parsedRConfList[h]'hlen).r := by omega
  have hmem := capDarts_complete h hh hlen H darts h_mc p
    (capRingDart h hh hlen H darts h_mc p hfan 0 h0_lt)
  intro hnil
  rw [hnil] at hmem
  cases hmem

theorem capDarts_length_lt (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    (capDarts h hh hlen H darts h_mc p).length < darts.length := by
  have hhdr := fastConf_equiv_header h hh
  let c := configOfRConf (parsedRConfList[h]'hlen)
  have hi4 : 4 ≤ c.interiorSize := hhdr.2.2.2.2.2.2.2.1
  have hu_lt : c.ringSize < c.totalNodes := by dsimp [Configuration.totalNodes]; omega
  obtain ⟨v, hv_lt, hadj⟩ := p.emb.int_nonempty c.ringSize (Nat.le_refl _) hu_lt
  have hsv := p.emb.dart_same_vertex_rep c.ringSize (Nat.le_refl _) hu_lt v hv_lt hadj
  have hd_mem : p.emb.dart c.ringSize v ∈
      removedIntDarts c H darts p.emb.rep := by
    rw [removedIntDarts_mem_iff c H darts h_mc.complete p.emb.rep]
    left
    exact (isIntVertBool_eq_true_iff c H.dual darts p.emb.rep _).mpr
      ⟨c.ringSize, Nat.le_refl _, hu_lt, hsv⟩
  exact exciseSubtype_strictly_smaller darts _ ⟨p.emb.dart c.ringSize v, h_mc.complete _, hd_mem⟩

theorem capHypermap_isPlanar (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    let H_cap := capHypermap h hh hlen H darts h_mc p
    let darts_cap := capDarts h hh hlen H darts h_mc p
    @Hypermap.isPlanar H_cap (@instBEqOfDecidableEq H_cap.Dart inferInstance)
      darts_cap.length darts_cap = true := by
  intro H_cap darts_cap
  let T0 := orientedDual H p.emb.orient
  have hT0_plan : T0.isPlanar darts.length darts = true := by
    rw [orientedDual_isPlanar H darts h_mc.nodup h_mc.complete (Nat.le_refl _) p.emb.orient]
    exact h_mc.is_planar
  have hText_plan := deleteEdgesSubtype_isPlanar T0 darts
    (removedIntDarts _ H darts p.emb.rep)
    (removedIntDarts_edge_closed _ H darts h_mc.complete p.emb.rep p.emb.orient)
    (mc_oriented_edge_free h_mc p.emb.orient)
    h_mc.nodup h_mc.complete (Nat.le_refl _) hT0_plan
    darts_cap (capDarts_nodup h hh hlen H darts h_mc p)
    (capDarts_complete h hh hlen H darts h_mc p) (Nat.le_refl _)
  change @Hypermap.isPlanar (capTriangulation h hh hlen H darts h_mc p).dual
    (@instBEqOfDecidableEq _ inferInstance) darts_cap.length darts_cap = true
  rw [isPlanar_dual (capTriangulation h hh hlen H darts h_mc p) darts_cap
    (capDarts_nodup h hh hlen H darts h_mc p) (capDarts_complete h hh hlen H darts h_mc p)
    (Nat.le_refl _)]
  exact hText_plan

theorem capHypermap_isBridgeless (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts) :
    Math.Hypermap.isBridgeless (capHypermap h hh hlen H darts h_mc p)
      (capDarts h hh hlen H darts h_mc p) (capDarts h hh hlen H darts h_mc p).length :=
  deleteEdgesSubtype_dual_isBridgeless H darts h_mc.complete h_mc.is_bridgeless p.emb.orient
    (removedIntDarts _ H darts p.emb.rep)
    (removedIntDarts_edge_closed _ H darts h_mc.complete p.emb.rep p.emb.orient)
    (mc_oriented_edge_free h_mc p.emb.orient)
    (capDarts h hh hlen H darts h_mc p)

theorem capHypermap_dual_face_ring (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (x : Nat) (hx : x < (parsedRConfList[h]'hlen).r) :
    let rc := parsedRConfList[h]'hlen
    have hr6 : 6 ≤ rc.r := by
      have h1 := (fastConf_equiv_header h hh).2.2.2.2.2.1
      have h2 : (configOfRConf rc).ringSize = rc.r := (fastConf_equiv_header h hh).2.2.1
      rw [← h2]; exact h1
    have hnext : (x + 1) % rc.r < rc.r := Nat.mod_lt _ (by omega)
    (capHypermap h hh hlen H darts h_mc p).dual.face.f
      (capRingDart h hh hlen H darts h_mc p hfan x hx) =
      capRingDart h hh hlen H darts h_mc p hfan ((x + 1) % rc.r) hnext := by
  intro rc hr6 hnext
  let c := configOfRConf rc
  let T0 := orientedDual H p.emb.orient
  let rem := removedIntDarts c H darts p.emb.rep
  let y := (x + 1) % rc.r
  have hy : y < rc.r := hnext
  have hprev_eq : (y + rc.r - 1) % rc.r = x := by
    rw [show y = (x + 1) % rc.r from rfl]
    by_cases hx1 : x + 1 < rc.r
    · rw [Nat.mod_eq_of_lt hx1, show x + 1 + rc.r - 1 = x + rc.r from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hx]
    · have hxeq : x + 1 = rc.r := by dsimp only [rc] at *; omega
      rw [hxeq, Nat.mod_self, Nat.zero_add, show rc.r - 1 = x from by dsimp only [rc] at *; omega, Nat.mod_eq_of_lt hx]
  have hhdr := fastConf_equiv_header h hh
  have hr_eq : c.ringSize = rc.r := hhdr.2.2.1
  have hring := fastConf_equiv_ring_and_fans h hh
  have hadj_cert := fastConf_equiv_adj h hh
  have hx_tot : x < c.totalNodes := Nat.lt_of_lt_of_le (hr_eq ▸ hx) (Nat.le_add_right _ _)
  have hy_tot : y < c.totalNodes := Nat.lt_of_lt_of_le (hr_eq ▸ hy) (Nat.le_add_right _ _)
  have hy_adj : y < rc.adj.size := by
    rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; exact hy_tot
  have hx_adj : x < rc.adj.size := by
    rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; exact hx_tot
  let fansY := ((rc.adj[y]'hy_adj).toList.drop 1).dropLast
  let fansX := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast
  have hrfY := hfan y hy hy_adj
  have hrfX := hfan x hx hx_adj
  have hfanY_ne : fansY ≠ [] := hrfY.1
  have hfanX_ne : fansX ≠ [] := hrfX.1
  let s := fansY.length
  have hs_pos : 0 < s := list_length_pos_of_ne_nil hfanY_ne
  have hnode_eq : T0.node = nodePermOriented H.dual p.emb.orient := orientedDual_node_eq H p.emb.orient
  have h_chain : ∀ k (hk : k < s),
      Perm.iter T0.node (k + 1) (capRingRawDart h hh hlen H darts p hfan y hy) =
        H.edge.f (p.emb.dart (fansY[k]'hk) y) := by
    intro k
    induction k with
    | zero =>
      intro _
      change T0.node.f (capRingRawDart h hh hlen H darts p hfan y hy) = _
      exact (capRingRawDart_equations h hh hlen H darts h_mc p hfan y hy).1
    | succ k ih =>
      intro hk
      have hk_lt : k < s := Nat.lt_of_succ_lt hk
      rw [Perm.iter_succ, ih hk_lt]
      have hturn := hrfY.2.1 k hk
      change H.dual.edge.f (p.emb.dart (fansY[k + 1]'hk) y) =
        (nodePermOriented H.dual p.emb.orient).f (H.dual.edge.f (p.emb.dart (fansY[k]'hk_lt) y)) at hturn
      rw [← hnode_eq] at hturn
      exact hturn.symm
  have h_last_eq : fansY[s - 1]'(by omega) = fansX[0]'(list_length_pos_of_ne_nil hfanX_ne) := by
    have hlast_y := hrfX.2.2.2.1 hy_adj (list_length_pos_of_ne_nil hfanX_ne)
    change fansY.getLast? = some (fansX[0]'_) at hlast_y
    rw [List.getLast?_eq_some_getLast hfanY_ne, Option.some.injEq] at hlast_y
    rw [← List.getLast_eq_getElem hfanY_ne]
    exact hlast_y
  have h_jump_target :
      Perm.iter T0.node (s + 1) (capRingRawDart h hh hlen H darts p hfan y hy) =
        H.edge.f (capRingRawDart h hh hlen H darts p hfan x hx) := by
    rw [Perm.iter_succ, show s = (s - 1) + 1 from (Nat.sub_add_cancel hs_pos).symm,
        h_chain (s - 1) (by omega), h_last_eq]
    have heqx := (capRingRawDart_equations h hh hlen H darts h_mc p hfan x hx).2
    change H.edge.f (capRingRawDart h hh hlen H darts p hfan x hx) =
      T0.node.f (H.edge.f (p.emb.dart _ y)) at heqx
    exact heqx.symm
  have h_skip : ∀ j, 1 ≤ j → j < s + 1 →
      Perm.iter T0.node j (capRingRawDart h hh hlen H darts p hfan y hy) ∈ rem := by
    intro j hj1 hjlt
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : k < s := by omega
    rw [h_chain k hk]
    have hfk_mem : fansY[k]'hk ∈ fansY := List.getElem_mem _
    have hfk_r : c.ringSize ≤ fansY[k]'hk := (hring.2 y (hr_eq ▸ hy)).2.2.2.1 _ hfk_mem
    have hfk_adj_mem : fansY[k]'hk ∈ (rc.adj[y]'hy_adj).toList :=
      List.mem_of_mem_drop (mem_of_mem_dropLast_de hfk_mem)
    have hfk_spec := (hadj_cert.1 y hy_tot).2 _ hfk_adj_mem
    have hadj_yf : c.adj y (fansY[k]'hk) = true :=
      (hadj_cert.2.1 y hy_tot _ hfk_spec.1).trans (List.contains_iff_mem.mpr hfk_adj_mem)
    have hadj_sym : c.adj (fansY[k]'hk) y = true := by
      rw [p.adj_symm _ y hfk_spec.1 hy_tot]; exact hadj_yf
    have hsv_fk := p.emb.dart_same_vertex_rep _ hfk_r hfk_spec.1 y hy_tot hadj_sym
    rw [removedIntDarts_mem_iff c H darts h_mc.complete p.emb.rep]
    right
    rw [H.edge_involution]
    exact (isIntVertBool_eq_true_iff c H.dual darts p.emb.rep _).mpr
      ⟨fansY[k]'hk, hfk_r, hfk_spec.1, hsv_fk⟩
  have h_target_surv :
      Perm.iter T0.node (s + 1) (capRingRawDart h hh hlen H darts p hfan y hy) ∉ rem := by
    rw [h_jump_target]
    intro hmem
    have := (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient _).mpr
      (by rwa [orientedDual_edge])
    exact capRingRawDart_not_mem_removed h hh hlen H darts h_mc p hfan x hx this
  let dx_cap := capRingDart h hh hlen H darts h_mc p hfan x hx
  let dy_cap := capRingDart h hh hlen H darts h_mc p hfan y hy
  have hnode_cap : ((capTriangulation h hh hlen H darts h_mc p).node.f dy_cap).val =
      ((capTriangulation h hh hlen H darts h_mc p).edge.f dx_cap).val := by
    change ((T0.deleteEdgesSubtype rem
      (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient)
      (mc_oriented_edge_free h_mc p.emb.orient)).node.f dy_cap).val =
      ((T0.deleteEdgesSubtype rem
      (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient)
      (mc_oriented_edge_free h_mc p.emb.orient)).edge.f dx_cap).val
    rw [deleteEdgesSubtype_node_jump T0 rem
          (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient)
          (mc_oriented_edge_free h_mc p.emb.orient) dy_cap (by omega) h_target_surv h_skip,
        show dy_cap.val = capRingRawDart h hh hlen H darts p hfan y hy from rfl,
        h_jump_target, deleteEdgesSubtype_edge_val, orientedDual_edge]
    rfl
  have hnode_ext : (capTriangulation h hh hlen H darts h_mc p).node.f dy_cap =
      (capTriangulation h hh hlen H darts h_mc p).edge.f dx_cap := Subtype.ext hnode_cap
  have hface_id := (capTriangulation h hh hlen H darts h_mc p).face_edge_node_id dy_cap
  rw [hnode_ext, (capTriangulation h hh hlen H darts h_mc p).edge_involution] at hface_id
  exact hface_id

theorem capRingDart_cyc4 (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {i j l m : Nat} (hij : i < j) (hjl : j < l) (hlm : l < m)
    (hm : m < (configOfRConf (parsedRConfList[h]'hlen)).ringSize) :
    let rc := parsedRConfList[h]'hlen
    let H_cap := capHypermap h hh hlen H darts h_mc p
    let rd : Nat → H_cap.Dart := fun idx =>
      if hidx : idx < rc.r then capRingDart h hh hlen H darts h_mc p hfan idx hidx
      else capRingDart h hh hlen H darts h_mc p hfan 0 (by
        have hhdr := fastConf_equiv_header h hh; have := hhdr.2.2.1; have := hhdr.2.2.2.2.2.1; omega)
    ∃ L, Nonempty (CyclicOrder4 H_cap.dual.face L (rd i) (rd j) (rd l) (rd m)) := by
  intro rc H_cap rd
  have hhdr := fastConf_equiv_header h hh
  have hr_eq : (configOfRConf rc).ringSize = rc.r := hhdr.2.2.1
  have hr6 : 6 ≤ rc.r := hr_eq ▸ hhdr.2.2.2.2.2.1
  have hm_r : m < rc.r := hr_eq ▸ hm
  have h_rd_eq : ∀ z (hz : z < rc.r), rd z = capRingDart h hh hlen H darts h_mc p hfan z hz :=
    fun z hz => dif_pos hz
  have h_iter : ∀ k a (ha : a < rc.r),
      Perm.iter H_cap.dual.face k (rd a) =
        capRingDart h hh hlen H darts h_mc p hfan ((a + k) % rc.r) (Nat.mod_lt _ (by omega)) := by
    intro k
    induction k with
    | zero =>
      intro a ha
      refine Eq.trans (h_rd_eq a ha) ?_
      exact capRingDart_eq_of_eq h hh hlen H darts h_mc p hfan ha _
        (by rw [Nat.add_zero, Nat.mod_eq_of_lt ha])
    | succ k ih =>
      intro a ha
      rw [Perm.iter_succ, ih a ha]
      refine Eq.trans (capHypermap_dual_face_ring h hh hlen H darts h_mc p hfan _ _) ?_
      exact capRingDart_eq_of_eq h hh hlen H darts h_mc p hfan _ _ (by
        change ((a + k) % rc.r + 1) % rc.r = (a + (k + 1)) % rc.r
        rw [Nat.mod_add_mod, Nat.add_assoc])
  refine ⟨rc.r, ⟨?_⟩⟩
  exact
    { inj_lt := fun a b ha hb heq => by
        rw [h_iter a i (by omega), h_iter b i (by omega)] at heq
        have hval := congrArg Subtype.val heq
        have hmod := capRingRawDart_inj h hh hlen H darts h_mc p hfan
          (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) hval
        by_cases hia : i + a < rc.r <;> by_cases hib : i + b < rc.r
        · rw [Nat.mod_eq_of_lt hia, Nat.mod_eq_of_lt hib] at hmod; omega
        · rw [Nat.mod_eq_of_lt hia,
              show (i + b) % rc.r = i + b - rc.r by
                have : i + b < 2 * rc.r := by omega
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]] at hmod
          omega
        · rw [Nat.mod_eq_of_lt hib,
              show (i + a) % rc.r = i + a - rc.r by
                have : i + a < 2 * rc.r := by omega
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]] at hmod
          omega
        · rw [show (i + a) % rc.r = i + a - rc.r by
                have : i + a < 2 * rc.r := by omega
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)],
              show (i + b) % rc.r = i + b - rc.r by
                have : i + b < 2 * rc.r := by omega
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]] at hmod
          omega
      period := by
        refine Eq.trans (h_iter rc.r i (by omega)) ?_
        refine Eq.trans (capRingDart_eq_of_eq h hh hlen H darts h_mc p hfan _ (by omega : i < rc.r)
          (by rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)])) ?_
        exact (h_rd_eq i (by omega)).symm
      k1 := j - i
      k2 := l - j
      k3 := m - l
      k4 := rc.r - (m - i)
      hk1 := by omega
      hk2 := by omega
      hk3 := by omega
      hk4 := by omega
      hsum := by omega
      hd1 := by
        refine Eq.trans (h_iter (j - i) i (by omega)) ?_
        refine Eq.trans (capRingDart_eq_of_eq h hh hlen H darts h_mc p hfan _ (by omega : j < rc.r)
          (by rw [show i + (j - i) = j by omega, Nat.mod_eq_of_lt (by omega)])) ?_
        exact (h_rd_eq j (by omega)).symm
      hd2 := by
        refine Eq.trans (h_iter (j - i + (l - j)) i (by omega)) ?_
        refine Eq.trans (capRingDart_eq_of_eq h hh hlen H darts h_mc p hfan _ (by omega : l < rc.r)
          (by rw [show i + (j - i + (l - j)) = l by omega, Nat.mod_eq_of_lt (by omega)])) ?_
        exact (h_rd_eq l (by omega)).symm
      hd3 := by
        refine Eq.trans (h_iter (j - i + (l - j) + (m - l)) i (by omega)) ?_
        refine Eq.trans (capRingDart_eq_of_eq h hh hlen H darts h_mc p hfan _ hm_r
          (by rw [show i + (j - i + (l - j) + (m - l)) = m by omega, Nat.mod_eq_of_lt hm_r])) ?_
        exact (h_rd_eq m hm_r).symm }

theorem capRingDart_adj (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (i j : Nat) (hi : i < (configOfRConf (parsedRConfList[h]'hlen)).ringSize)
    (hj : j < (configOfRConf (parsedRConfList[h]'hlen)).ringSize)
    (hadj : (configOfRConf (parsedRConfList[h]'hlen)).adj i j = true) :
    let rc := parsedRConfList[h]'hlen
    let H_cap := capHypermap h hh hlen H darts h_mc p
    let rd : Nat → H_cap.Dart := fun idx =>
      if hidx : idx < rc.r then capRingDart h hh hlen H darts h_mc p hfan idx hidx
      else capRingDart h hh hlen H darts h_mc p hfan 0 (by
        have hhdr := fastConf_equiv_header h hh; have := hhdr.2.2.1; have := hhdr.2.2.2.2.2.1; omega)
    ∃ u v : H_cap.Dart, SameOrbit H_cap.face (rd i) u ∧ SameOrbit H_cap.face (rd j) v ∧
      H_cap.edge.f u = v := by
  intro rc H_cap rd
  have hhdr := fastConf_equiv_header h hh
  have hr_eq : (configOfRConf rc).ringSize = rc.r := hhdr.2.2.1
  have hr6 : 6 ≤ rc.r := hr_eq ▸ hhdr.2.2.2.2.2.1
  have hring := (fastConf_equiv_ring_and_fans h hh).1 i hi j hj
  rw [hring] at hadj
  have hstep_adj : ∀ a (ha : a < rc.r),
      let b := (a + 1) % rc.r
      ∃ hb : b < rc.r,
        ∃ u v : H_cap.Dart,
          SameOrbit H_cap.face (capRingDart h hh hlen H darts h_mc p hfan a ha) u ∧
          SameOrbit H_cap.face (capRingDart h hh hlen H darts h_mc p hfan b hb) v ∧
          H_cap.edge.f u = v := by
    intro a ha b
    have hb : b < rc.r := Nat.mod_lt _ (by omega)
    refine ⟨hb, capRingDart h hh hlen H darts h_mc p hfan a ha,
      H_cap.edge.f (capRingDart h hh hlen H darts h_mc p hfan a ha),
      sameOrbit_refl H_cap.face _, ?_, rfl⟩
    have hdual_face := capHypermap_dual_face_ring h hh hlen H darts h_mc p hfan a ha
    have h_en : (capTriangulation h hh hlen H darts h_mc p).edge.f
        ((capTriangulation h hh hlen H darts h_mc p).node.f
          (capRingDart h hh hlen H darts h_mc p hfan b hb)) =
        (capRingDart h hh hlen H darts h_mc p hfan a ha) := by
      have hsub : (capTriangulation h hh hlen H darts h_mc p).face.f
          (capRingDart h hh hlen H darts h_mc p hfan a ha) =
          capRingDart h hh hlen H darts h_mc p hfan b hb := hdual_face
      have hid := (capTriangulation h hh hlen H darts h_mc p).edge_node_face_id
        (capRingDart h hh hlen H darts h_mc p hfan a ha)
      rw [hsub] at hid
      exact hid
    have h_inv_node : (capTriangulation h hh hlen H darts h_mc p).node.f
        (capRingDart h hh hlen H darts h_mc p hfan b hb) =
        H_cap.edge.f (capRingDart h hh hlen H darts h_mc p hfan a ha) := by
      have := congrArg (capTriangulation h hh hlen H darts h_mc p).edge.f h_en
      rwa [(capTriangulation h hh hlen H darts h_mc p).edge_involution] at this
    have h_sym := congrArg (capTriangulation h hh hlen H darts h_mc p).node.inv h_inv_node
    rw [(capTriangulation h hh hlen H darts h_mc p).node.left_inv] at h_sym
    exact sameOrbit_symm_of_complete H_cap.face (capDarts h hh hlen H darts h_mc p)
      (capDarts_complete h hh hlen H darts h_mc p) ⟨1, by
        dsimp only [H_cap, capHypermap]
        change (capTriangulation h hh hlen H darts h_mc p).node.inv _ = _
        exact h_sym.symm⟩
  rcases hadj with h_prev | h_next
  · have h_ji : i = (j + 1) % rc.r := by
      rw [hr_eq] at h_prev
      have hj_r : j < rc.r := hr_eq ▸ hj
      have hi_r : i < rc.r := hr_eq ▸ hi
      by_cases hi0 : i = 0
      · have hjval : j = rc.r - 1 := by
          rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : rc.r - 1 < rc.r)] at h_prev
          exact h_prev
        rw [hjval, show rc.r - 1 + 1 = rc.r by omega, Nat.mod_self, hi0]
      · have hjval : j = i - 1 := by
          rw [show i + rc.r - 1 = (i - 1) + rc.r by omega, Nat.add_mod_right,
              Nat.mod_eq_of_lt (by omega)] at h_prev
          exact h_prev
        rw [hjval, show i - 1 + 1 = i by omega, Nat.mod_eq_of_lt hi_r]
    obtain ⟨hb, u, v, hu, hv, huv⟩ := hstep_adj j (hr_eq ▸ hj)
    refine ⟨v, u, ?_, ?_, ?_⟩
    · dsimp only [rd]
      rw [dif_pos (hr_eq ▸ hi), capRingDart_eq_of_eq h hh hlen H darts h_mc p hfan (hr_eq ▸ hi) hb h_ji]
      exact hv
    · dsimp only [rd]
      rw [dif_pos (hr_eq ▸ hj)]
      exact hu
    · rw [← huv, H_cap.edge_involution]
  · obtain ⟨hb, u, v, hu, hv, huv⟩ := hstep_adj i (hr_eq ▸ hi)
    have hbj : (i + 1) % rc.r = j := by rw [h_next, hr_eq]
    refine ⟨u, v, ?_, ?_, huv⟩
    · dsimp only [rd]
      rw [dif_pos (hr_eq ▸ hi)]
      exact hu
    · dsimp only [rd]
      rw [dif_pos (hr_eq ▸ hj), capRingDart_eq_of_eq h hh hlen H darts h_mc p hfan (hr_eq ▸ hj) hb hbj.symm]
      exact hv

/-- Capped-ring topological witness packaging `H_cap`, its cyclic boundary ring darts,
    and global 4-coloring gluing. -/
structure CappedRingWitness (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (c : Configuration) where
  H_cap : Hypermap
  dec_cap : DecidableEq H_cap.Dart
  darts_cap : List H_cap.Dart
  nodup_cap : darts_cap.Nodup
  complete_cap : ∀ d, d ∈ darts_cap
  nonempty_cap : darts_cap ≠ []
  smaller : darts_cap.length < darts.length
  planar_cap : @Hypermap.isPlanar H_cap (@instBEqOfDecidableEq H_cap.Dart dec_cap)
    darts_cap.length darts_cap = true
  bridgeless_cap : Math.Hypermap.isBridgeless H_cap darts_cap darts_cap.length
  ringDart : Nat → H_cap.Dart
  ring_cyc : ∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
    ∃ L, Nonempty (CyclicOrder4 H_cap.dual.face L (ringDart i) (ringDart j) (ringDart l) (ringDart m))
  ring_adj : ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true →
    ∃ u v, SameOrbit H_cap.face (ringDart i) u ∧ SameOrbit H_cap.face (ringDart j) v ∧
      H_cap.edge.f u = v
  glue : ∀ (col_cap : H_cap.FaceColoring) (ext : Nat → Color),
    (∀ i < c.ringSize, ext i = col_cap.color (ringDart i)) →
    Math.IsValidConfigColoring c ext →
    H.FaceColoring

end ConfigurationDiskExcision

section GluingAndReducibilityDischarge

private theorem face_invariant_sameOrbit {H : Hypermap} (col : H.FaceColoring) :
    ∀ {x y : H.Dart}, SameOrbit H.face x y → col.color y = col.color x := by
  intro x y ⟨k, hk⟩
  rw [← hk]
  clear y hk
  induction k with
  | zero => rfl
  | succ k ih => rw [Perm.iter_succ, col.face_invariant, ih]

private theorem node_invariant_sameOrbit {T : Hypermap} (col : T.Dart → Color)
    (h_inv : ∀ d, col (T.node.f d) = col d) :
    ∀ {x y : T.Dart}, SameOrbit T.node x y → col y = col x := by
  intro x y ⟨k, hk⟩
  rw [← hk]
  clear y hk
  induction k with
  | zero => rfl
  | succ k ih => rw [Perm.iter_succ, h_inv, ih]

private theorem dual_face_color_sameOrbit_node {T : Hypermap} (col : T.dual.FaceColoring)
    {x y : T.Dart} (hso : SameOrbit T.node x y) : col.color y = col.color x := by
  have hso_sym : SameOrbit T.node.symm y x := (sameOrbit_symm_perm T.node).mpr hso
  exact (face_invariant_sameOrbit col hso_sym).symm

/-- Glue a 4-coloring `col_cap` of the capped outer map `capHypermap` and a valid 4-coloring
    `ext` of `c` agreeing on the ring darts into a global `H.FaceColoring`. -/
noncomputable def glue_capped_and_interior (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (col_cap : (capHypermap h hh hlen H darts h_mc p).FaceColoring)
    (ext : Nat → Color)
    (h_match : ∀ i (hi : i < (parsedRConfList[h]'hlen).r),
      ext i = col_cap.color (capRingDart h hh hlen H darts h_mc p hfan i hi))
    (h_val : Math.IsValidConfigColoring (configOfRConf (parsedRConfList[h]'hlen)) ext) :
    H.FaceColoring := by
  classical
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  let T0 := orientedDual H p.emb.orient
  let rem := removedIntDarts c H darts p.emb.rep
  let T_cap := capTriangulation h hh hlen H darts h_mc p
  let H_cap := capHypermap h hh hlen H darts h_mc p
  have hhdr := fastConf_equiv_header h hh
  have hr_eq : c.ringSize = rc.r := hhdr.2.2.1
  have h_all_surv : ∀ d : H.Dart,
      (∀ u, c.ringSize ≤ u → u < c.totalNodes →
        sameVertex H.dual d (p.emb.rep u) darts.length = false) →
      ∃ w : T_cap.Dart, sameVertex H.dual d w.val darts.length = true := by
    intro d hnotint
    by_cases hdr : d ∈ rem
    · rw [removedIntDarts_mem_iff c H darts h_mc.complete p.emb.rep] at hdr
      rcases hdr with h1 | h2
      · obtain ⟨u, hur, hun, hsv⟩ := (isIntVertBool_eq_true_iff c H.dual darts p.emb.rep d).mp h1
        rw [hnotint u hur hun] at hsv; cases hsv
      · obtain ⟨u, hur, hun, hsv⟩ := (isIntVertBool_eq_true_iff c H.dual darts p.emb.rep _).mp h2
        have hsv_rev : sameVertex H.dual (p.emb.rep u) (H.edge.f d) darts.length = true := by
          rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]; exact hsv
        obtain ⟨v, hv_lt, hadj_uv, hdart_uv⟩ :=
          p.int_dart_bij u hur hun (H.edge.f d) hsv
        have h_ed := congrArg H.edge.f hdart_uv.symm
        change H.edge.f (H.edge.f d) = H.edge.f (p.emb.dart u v) at h_ed
        rw [H.edge_involution] at h_ed
        have hsv_dv : sameVertex H.dual d (p.emb.rep v) darts.length = true := by
          rw [h_ed]; exact p.emb.dart_edge_same_vertex_rep u hur hun v hv_lt hadj_uv
        have hv_r : v < c.ringSize := Classical.byContradiction fun hge => by
          have hge' : c.ringSize ≤ v := Nat.le_of_not_lt hge
          rw [hnotint v hge' hv_lt] at hsv_dv; cases hsv_dv
        let rx := capRingDart h hh hlen H darts h_mc p hfan v (hr_eq ▸ hv_r)
        have h_vr : sameVertex H.dual (p.emb.rep v) rx.val darts.length = true := by
          rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]
          exact capRingRawDart_vertex h hh hlen H darts h_mc p hfan v (hr_eq ▸ hv_r)
        exact ⟨rx, sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _) hsv_dv h_vr⟩
    · exact ⟨⟨d, hdr⟩, sameVertex_refl H.dual darts.length d⟩
  let col_fn : H.Dart → Color := fun d =>
    if hd : ∃ u, c.ringSize ≤ u ∧ u < c.totalNodes ∧
        sameVertex H.dual d (p.emb.rep u) darts.length = true then
      ext (Classical.choose hd)
    else
      col_cap.color (Classical.choose (h_all_surv d (fun u hur hun =>
        Classical.byContradiction fun hne =>
          hd ⟨u, hur, hun, by cases h : sameVertex H.dual d (p.emb.rep u) darts.length <;> simp_all⟩)))
  have h_sameVertex_sameOrbit : ∀ {a b : H.Dart},
      sameVertex H.dual a b darts.length = true ↔ SameOrbit H.dual.node a b := by
    intro a b
    rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _),
        sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _) a b]
    constructor
    · intro hmem
      obtain ⟨k, _, hk⟩ := mem_getOrbit_imp_exists_iter H.dual.node darts.length a b hmem
      exact ⟨k, hk.symm⟩
    · rintro ⟨k, hk⟩
      have hcl := orbitClosesWithin_mono H.dual.node a a
        (orbitClosesWithin_of_complete H.dual.node darts h_mc.complete a) (Nat.le_refl _)
      have := iter_mem_getOrbit_of_closes H.dual.node darts.length a hcl k
      rwa [hk] at this
  have h_surv_eq : ∀ {w1 w2 : T_cap.Dart},
      sameVertex H.dual w1.val w2.val darts.length = true →
      col_cap.color w1 = col_cap.color w2 := by
    intro w1 w2 hsv
    have hso_T0 : SameOrbit T0.node w1.val w2.val :=
      (orientedDual_sameOrbit_node_iff H darts h_mc.complete p.emb.orient w1.val w2.val).mpr
        (sameOrbit_symm_of_complete H.face darts h_mc.complete
          ((sameOrbit_symm_perm H.face).mp (h_sameVertex_sameOrbit.mp hsv)))
    have hso_cap : SameOrbit T_cap.node w1 w2 := by
      change SameOrbit (T0.deleteEdgesSubtype rem
        (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient)
        (mc_oriented_edge_free h_mc p.emb.orient)).node w1 w2
      exact (deleteEdgesSubtype_sameOrbit_node_iff T0 rem
        (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient)
        (mc_oriented_edge_free h_mc p.emb.orient) w1 w2).mpr hso_T0
    exact (dual_face_color_sameOrbit_node col_cap hso_cap).symm
  have h_col_int : ∀ d u, c.ringSize ≤ u → u < c.totalNodes →
      sameVertex H.dual d (p.emb.rep u) darts.length = true → col_fn d = ext u := by
    intro d u hur hun hsv
    have hd : ∃ u', c.ringSize ≤ u' ∧ u' < c.totalNodes ∧
        sameVertex H.dual d (p.emb.rep u') darts.length = true := ⟨u, hur, hun, hsv⟩
    dsimp only [col_fn]
    rw [dif_pos hd]
    obtain ⟨u_c_r, hu_c_n, hsv_c⟩ := Classical.choose_spec hd
    have heq_u : Classical.choose hd = u := Classical.byContradiction fun hne => by
      have hsv_cu := sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _)
        (by rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]; exact hsv_c) hsv
      have hf := p.emb.int_distinct _ u u_c_r hu_c_n hur hun hne
      rw [hsv_cu] at hf; cases hf
    rw [heq_u]
  have h_col_ext_surv : ∀ (d : H.Dart) (w : T_cap.Dart),
      (∀ u, c.ringSize ≤ u → u < c.totalNodes →
        sameVertex H.dual d (p.emb.rep u) darts.length = false) →
      sameVertex H.dual d w.val darts.length = true →
      col_fn d = col_cap.color w := by
    intro d w hnotint hdw
    have hd : ¬ ∃ u, c.ringSize ≤ u ∧ u < c.totalNodes ∧
        sameVertex H.dual d (p.emb.rep u) darts.length = true := by
      rintro ⟨u, hur, hun, hsv⟩
      rw [hnotint u hur hun] at hsv; cases hsv
    dsimp only [col_fn]
    rw [dif_neg hd]
    have hwc := Classical.choose_spec (h_all_surv d hnotint)
    have hsv_ww : sameVertex H.dual (Classical.choose (h_all_surv d hnotint)).val w.val darts.length = true :=
      sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _)
        (by rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]; exact hwc) hdw
    exact h_surv_eq hsv_ww
  have h_col_ring : ∀ d i, i < c.ringSize →
      sameVertex H.dual d (p.emb.rep i) darts.length = true → col_fn d = ext i := by
    intro d i hi hsv_di
    have hnotint : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
        sameVertex H.dual d (p.emb.rep u) darts.length = false := fun u hur hun =>
      Classical.byContradiction fun hne => by
        have hsv_du : sameVertex H.dual d (p.emb.rep u) darts.length = true := by
          cases h : sameVertex H.dual d (p.emb.rep u) darts.length <;> simp_all
        have hsv_ui := sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _)
          (by rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]; exact hsv_du) hsv_di
        have hf := p.emb.int_ring_distinct u i hur hun hi
        rw [hsv_ui] at hf; cases hf
    let rx := capRingDart h hh hlen H darts h_mc p hfan i (hr_eq ▸ hi)
    have h_drx : sameVertex H.dual d rx.val darts.length = true :=
      sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _) hsv_di
        (by rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]
            exact capRingRawDart_vertex h hh hlen H darts h_mc p hfan i (hr_eq ▸ hi))
    rw [h_col_ext_surv d rx hnotint h_drx, ← h_match i (hr_eq ▸ hi)]
  have h_node_inv : ∀ d, col_fn (H.dual.node.f d) = col_fn d := by
    intro d
    have h_sv : ∀ u, sameVertex H.dual (H.dual.node.f d) (p.emb.rep u) darts.length =
        sameVertex H.dual d (p.emb.rep u) darts.length := fun u => by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hs
        exact sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _)
          (by rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]
              exact sameVertex_node_f H.dual darts h_mc.complete (Nat.le_refl _) d) hs
      · intro hs
        exact sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _)
          (sameVertex_node_f H.dual darts h_mc.complete (Nat.le_refl _) d) hs
    by_cases h_int : ∃ u, c.ringSize ≤ u ∧ u < c.totalNodes ∧
        sameVertex H.dual d (p.emb.rep u) darts.length = true
    · obtain ⟨u, hur, hun, hsv⟩ := h_int
      rw [h_col_int (H.dual.node.f d) u hur hun (by rw [h_sv u]; exact hsv),
          h_col_int d u hur hun hsv]
    · have hnot : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
          sameVertex H.dual d (p.emb.rep u) darts.length = false := fun u hur hun =>
        Classical.byContradiction fun hne =>
          h_int ⟨u, hur, hun, by cases h : sameVertex H.dual d (p.emb.rep u) darts.length <;> simp_all⟩
      have hnot_f : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
          sameVertex H.dual (H.dual.node.f d) (p.emb.rep u) darts.length = false := fun u hur hun => by
        rw [h_sv u]; exact hnot u hur hun
      obtain ⟨w, hdw⟩ := h_all_surv d hnot
      have hfdw : sameVertex H.dual (H.dual.node.f d) w.val darts.length = true :=
        sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _)
          (sameVertex_node_f H.dual darts h_mc.complete (Nat.le_refl _) d) hdw
      rw [h_col_ext_surv (H.dual.node.f d) w hnot_f hfdw, h_col_ext_surv d w hnot hdw]
  have h_edge_prop : ∀ d, col_fn (H.edge.f d) ≠ col_fn d := by
    intro d
    have handle_int : ∀ z u, c.ringSize ≤ u → u < c.totalNodes →
        sameVertex H.dual z (p.emb.rep u) darts.length = true →
        col_fn (H.edge.f z) ≠ col_fn z := by
      intro z u hur hun hsv_z
      obtain ⟨v, hv_lt, hadj_uv, hdz⟩ := p.int_dart_bij u hur hun z hsv_z
      have hsv_ez : sameVertex H.dual (H.edge.f z) (p.emb.rep v) darts.length = true := by
        rw [← hdz]; exact p.emb.dart_edge_same_vertex_rep u hur hun v hv_lt hadj_uv
      have h_col_z : col_fn z = ext u := h_col_int z u hur hun hsv_z
      have h_col_ez : col_fn (H.edge.f z) = ext v := by
        by_cases hvr : c.ringSize ≤ v
        · exact h_col_int (H.edge.f z) v hvr hv_lt hsv_ez
        · exact h_col_ring (H.edge.f z) v (Nat.lt_of_not_le hvr) hsv_ez
      rw [h_col_z, h_col_ez]
      exact h_val v u hv_lt (by dsimp [Configuration.totalNodes] at *; omega)
        (by rw [p.adj_symm v u hv_lt (by omega)]; exact hadj_uv)
    by_cases h1 : ∃ u, c.ringSize ≤ u ∧ u < c.totalNodes ∧
        sameVertex H.dual d (p.emb.rep u) darts.length = true
    · obtain ⟨u, hur, hun, hsv⟩ := h1
      exact handle_int d u hur hun hsv
    · by_cases h2 : ∃ u, c.ringSize ≤ u ∧ u < c.totalNodes ∧
          sameVertex H.dual (H.edge.f d) (p.emb.rep u) darts.length = true
      · obtain ⟨u, hur, hun, hsv⟩ := h2
        have hne := handle_int (H.edge.f d) u hur hun hsv
        rw [H.edge_involution] at hne
        exact hne.symm
      · have hd_surv : d ∉ rem := by
          rw [removedIntDarts_mem_iff c H darts h_mc.complete p.emb.rep]
          rintro (ht1 | ht2)
          · obtain ⟨u, hur, hun, hsv⟩ := (isIntVertBool_eq_true_iff c H.dual darts p.emb.rep d).mp ht1
            exact h1 ⟨u, hur, hun, hsv⟩
          · obtain ⟨u, hur, hun, hsv⟩ := (isIntVertBool_eq_true_iff c H.dual darts p.emb.rep _).mp ht2
            exact h2 ⟨u, hur, hun, hsv⟩
        have hed_surv : H.edge.f d ∉ rem := by
          rw [← orientedDual_edge H p.emb.orient]
          exact fun hm => hd_surv ((removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient d).mpr hm)
        let w : T_cap.Dart := ⟨d, hd_surv⟩
        have hew : H_cap.edge.f w = ⟨H.edge.f d, hed_surv⟩ := by
          apply Subtype.ext
          change ((deleteEdgesSubtype T0 rem
            (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient)
            (mc_oriented_edge_free h_mc p.emb.orient)).edge.f w).val = H.edge.f d
          rw [deleteEdgesSubtype_edge_val, orientedDual_edge]
        have hnot1 : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
            sameVertex H.dual d (p.emb.rep u) darts.length = false := fun u hur hun =>
          Classical.byContradiction fun hne =>
            h1 ⟨u, hur, hun, by cases h : sameVertex H.dual d (p.emb.rep u) darts.length <;> simp_all⟩
        have hnot2 : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
            sameVertex H.dual (H.edge.f d) (p.emb.rep u) darts.length = false := fun u hur hun =>
          Classical.byContradiction fun hne =>
            h2 ⟨u, hur, hun, by cases h : sameVertex H.dual (H.edge.f d) (p.emb.rep u) darts.length <;> simp_all⟩
        rw [h_col_ext_surv d w hnot1 (sameVertex_refl H.dual darts.length d),
            h_col_ext_surv (H.edge.f d) (H_cap.edge.f w) hnot2 (by rw [hew]; exact sameVertex_refl _ _ _)]
        exact col_cap.edge_proper w
  exact H.vertexColoringOfDualToFaceColoring
    { color := col_fn
      node_invariant := h_node_inv
      edge_proper := h_edge_prop }

/-- Build a full `CappedRingWitness` for any matched embedding `h < 633`. -/
noncomputable def build_cappedRingWitness (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb) :
    CappedRingWitness H darts (configOfRConf (parsedRConfList[h]'hlen)) :=
  let rc := parsedRConfList[h]'hlen
  let H_cap := capHypermap h hh hlen H darts h_mc p
  let darts_cap := capDarts h hh hlen H darts h_mc p
  let rd : Nat → H_cap.Dart := fun idx =>
    if hidx : idx < rc.r then capRingDart h hh hlen H darts h_mc p hfan idx hidx
    else capRingDart h hh hlen H darts h_mc p hfan 0 (by
      have hhdr := fastConf_equiv_header h hh; have := hhdr.2.2.1; have := hhdr.2.2.2.2.2.1; omega)
  { H_cap := H_cap
    dec_cap := inferInstance
    darts_cap := darts_cap
    nodup_cap := capDarts_nodup h hh hlen H darts h_mc p
    complete_cap := capDarts_complete h hh hlen H darts h_mc p
    nonempty_cap := capDarts_nonempty h hh hlen H darts h_mc p hfan
    smaller := capDarts_length_lt h hh hlen H darts h_mc p
    planar_cap := capHypermap_isPlanar h hh hlen H darts h_mc p
    bridgeless_cap := capHypermap_isBridgeless h hh hlen H darts h_mc p
    ringDart := rd
    ring_cyc := fun i j l m hij hjl hlm hm => capRingDart_cyc4 h hh hlen H darts h_mc p hfan hij hjl hlm hm
    ring_adj := fun i j hi hj hadj => capRingDart_adj h hh hlen H darts h_mc p hfan i j hi hj hadj
    glue := fun col_cap ext h_match h_val =>
      glue_capped_and_interior h hh hlen H darts h_mc p hfan col_cap ext
        (fun i hi => by
          have := h_match i (by rw [(fastConf_equiv_header h hh).2.2.1]; exact hi)
          dsimp only [rd] at this
          rw [dif_pos hi] at this
          exact this) h_val }

/-- Restrict any contracted 4-coloring `VertexColoringMod H.dual (mappedContractDarts p.emb)`
    to a valid `FaceColoring` on `capHypermap` (since `mappedContractDarts p.emb ⊆ removedIntDarts`). -/
def restrictModColoringToCap (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (col_mod : VertexColoringMod H.dual (mappedContractDarts p.emb)) :
    (capHypermap h hh hlen H darts h_mc p).FaceColoring :=
  let c := configOfRConf (parsedRConfList[h]'hlen)
  let T0 := orientedDual H p.emb.orient
  let rem := removedIntDarts c H darts p.emb.rep
  let T_cap := capTriangulation h hh hlen H darts h_mc p
  let not_mem_contract : ∀ d : H.Dart, d ∉ rem → d ∉ mappedContractDarts p.emb := by
    intro d hdr hm
    rw [mappedContractDarts, List.mem_map] at hm
    obtain ⟨q, hq_mem, rfl⟩ := hm
    obtain ⟨qA, qB, hqAr, hqAn, hqBn, hqAdj, _, hq_d⟩ := contractEdgeDart_canon p hq_mem
    rw [hq_d] at hdr
    have hsv := p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
    apply hdr
    rw [removedIntDarts_mem_iff c H darts h_mc.complete p.emb.rep]
    left
    exact (isIntVertBool_eq_true_iff c H.dual darts p.emb.rep _).mpr ⟨qA, hqAr, hqAn, hsv⟩
  { color := fun x => col_mod.color x.val
    face_invariant := fun x => by
      change col_mod.color (T_cap.node.inv x).val = col_mod.color x.val
      have hso_cap : SameOrbit T_cap.node (T_cap.node.inv x) x :=
        ⟨1, by simp [Perm.iter, T_cap.node.right_inv]⟩
      have hso_T0 : SameOrbit T0.node (T_cap.node.inv x).val x.val :=
        (deleteEdgesSubtype_sameOrbit_node_iff T0 rem
          (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient)
          (mc_oriented_edge_free h_mc p.emb.orient) (T_cap.node.inv x) x).mp
          (by dsimp only [T_cap, capTriangulation, T0, rem, c] at hso_cap ⊢; exact hso_cap)
      have hso_dual : SameOrbit H.dual.node (T_cap.node.inv x).val x.val := by
        have hf := (orientedDual_sameOrbit_node_iff H darts h_mc.complete p.emb.orient _ _).mp hso_T0
        exact (sameOrbit_symm_perm H.face).mpr (sameOrbit_symm_of_complete H.face darts h_mc.complete hf)
      exact (node_invariant_sameOrbit col_mod.color col_mod.node_invariant hso_dual).symm
    edge_proper := fun x => by
      have he_val : ((capHypermap h hh hlen H darts h_mc p).edge.f x).val = H.edge.f x.val := by
        change ((deleteEdgesSubtype T0 rem
          (removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient)
          (mc_oriented_edge_free h_mc p.emb.orient)).edge.f x).val = H.edge.f x.val
        rw [deleteEdgesSubtype_edge_val, orientedDual_edge]
      change col_mod.color ((capHypermap h hh hlen H darts h_mc p).edge.f x).val ≠ col_mod.color x.val
      rw [he_val]
      have hx_not_M : x.val ∉ mappedContractDarts p.emb := not_mem_contract x.val x.property
      have hex_not_rem : H.edge.f x.val ∉ rem := by
        rw [← orientedDual_edge H p.emb.orient]
        intro hm
        exact x.property ((removedIntDarts_edge_closed c H darts h_mc.complete p.emb.rep p.emb.orient x.val).mpr hm)
      have hex_not_M : H.edge.f x.val ∉ mappedContractDarts p.emb := not_mem_contract (H.edge.f x.val) hex_not_rem
      exact col_mod.edge_proper x.val hx_not_M hex_not_M }

theorem restrictModColoringToCap_ring_eq (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (col_mod : VertexColoringMod H.dual (mappedContractDarts p.emb))
    (i : Nat) (hi : i < (parsedRConfList[h]'hlen).r) :
    (restrictModColoringToCap h hh hlen H darts h_mc p col_mod).color
      (capRingDart h hh hlen H darts h_mc p hfan i hi) = col_mod.color (p.emb.rep i) := by
  have hsv := capRingRawDart_vertex h hh hlen H darts h_mc p hfan i hi
  exact node_invariant_sameVertex_eq H.dual darts h_mc.complete (Nat.le_refl _)
    col_mod.color col_mod.node_invariant hsv

private theorem validBoundaryColoring_of_ring_adj {H_cap : Hypermap} {c : Configuration}
    (ringDart : Nat → H_cap.Dart)
    (h_ring_adj : ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true →
      ∃ u v, SameOrbit H_cap.face (ringDart i) u ∧ SameOrbit H_cap.face (ringDart j) v ∧
        H_cap.edge.f u = v)
    (col : H_cap.FaceColoring) :
    Math.IsValidBoundaryColoring c (fun i => col.color (ringDart i)) := by
  intro i j hi hj hadj heq
  obtain ⟨u, v, hui, hvj, huv⟩ := h_ring_adj i j hi hj hadj
  have h1 : col.color u = col.color (ringDart i) := face_invariant_sameOrbit col hui
  have h2 : col.color v = col.color (ringDart j) := face_invariant_sameOrbit col hvj
  have hprop := col.edge_proper u
  rw [huv, h1, h2] at hprop
  exact hprop heq.symm

/-- **Unconditional D-Reducibility Contradiction Theorem:**
    Discharges all 249 D-reducible configurations (`h < 633` with `IsDReducible`) in any
    minimal counterexample `H`, without any `RSSTStandardizationBridge`. -/
theorem d_reducible_matched_impossible (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (hD : Math.IsDReducible (configOfRConf (parsedRConfList[h]'hlen))) :
    False := by
  let _ := hmc
  let c := configOfRConf (parsedRConfList[h]'hlen)
  let w := build_cappedRingWitness h hh hlen H darts h_mc p hfan
  have hNonempty := @PrimalMinimalCounterexample.is_minimal H _ darts h_mc w.H_cap w.dec_cap
    w.darts_cap w.nodup_cap w.complete_cap w.nonempty_cap w.smaller w.planar_cap w.bridgeless_cap
  rcases hNonempty with ⟨col_cap⟩
  let bnd : Math.BoundaryColoring c := fun i => col_cap.color (w.ringDart i)
  have hbnd_val := validBoundaryColoring_of_ring_adj w.ringDart w.ring_adj col_cap
  have hElim : Math.Eliminated c bnd := hD bnd hbnd_val
  obtain ⟨col_cap', ext, h_match, h_val⟩ := @Math.kempe_pullback_of_cappedRing w.H_cap w.dec_cap
    w.darts_cap w.nodup_cap w.complete_cap w.planar_cap c w.ringDart w.ring_cyc w.ring_adj
    (fun col i => col.color (w.ringDart i)) (fun _ _ _ => rfl) col_cap hElim
  exact h_mc.not_colorable (w.glue col_cap' ext h_match h_val)

/-- **Conditional C-Reducibility Contradiction Theorem:**
    Discharges any C-reducible configuration (`h < 633` with `IsCReducible`) in a minimal
    counterexample once a contracted coloring `VertexColoringMod H.dual (mappedContractDarts p.emb)`
    is supplied (used with `restrictModColoringToCap` in Stage V). -/
theorem c_reducible_matched_impossible_of_mod_coloring (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : PrimalMinimalCounterexample H darts)
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (hfan : RingFanProjectionConsistent (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (hC : Math.IsCReducible (configOfRConf (parsedRConfList[h]'hlen)))
    (col_mod : VertexColoringMod H.dual (mappedContractDarts p.emb)) :
    False := by
  let _ := hmc
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  let w := build_cappedRingWitness h hh hlen H darts h_mc p hfan
  let col_cap : w.H_cap.FaceColoring := restrictModColoringToCap h hh hlen H darts h_mc p col_mod
  let bnd : Math.BoundaryColoring c := fun i => col_cap.color (w.ringDart i)
  have hbnd_val := validBoundaryColoring_of_ring_adj w.ringDart w.ring_adj col_cap
  have h_pull := pullback_mod_coloring_extendsToContracted c H.dual darts h_mc.complete p col_mod
  have h_bnd_eq : ∀ i, i < c.ringSize → col_mod.color (p.emb.rep i) = bnd i := by
    intro i hi
    have hi_r : i < rc.r := by rw [← (fastConf_equiv_header h hh).2.2.1]; exact hi
    dsimp only [bnd, col_cap, w, build_cappedRingWitness]
    rw [dif_pos hi_r]
    exact (restrictModColoringToCap_ring_eq h hh hlen H darts h_mc p hfan col_mod i hi_r).symm
  have hbnd_sat : Math.extendsToContracted c bnd := by
    obtain ⟨full, hfull_ring, hfull_val⟩ := h_pull
    exact ⟨full, fun i hi => (hfull_ring i hi).trans (h_bnd_eq i hi), hfull_val⟩
  have hElim : Math.Eliminated c bnd := hC.2 bnd hbnd_val hbnd_sat
  obtain ⟨col_cap', ext, h_match, h_val⟩ := @Math.kempe_pullback_of_cappedRing w.H_cap w.dec_cap
    w.darts_cap w.nodup_cap w.complete_cap w.planar_cap c w.ringDart w.ring_cyc w.ring_adj
    (fun col i => col.color (w.ringDart i)) (fun _ _ _ => rfl) col_cap hElim
  exact h_mc.not_colorable (w.glue col_cap' ext h_match h_val)

end GluingAndReducibilityDischarge

end Hypermap
