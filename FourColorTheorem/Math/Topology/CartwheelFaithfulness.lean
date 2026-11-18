module

public import FourColorTheorem.Math.Topology.Birkhoff5Ring
public import FourColorTheorem.Math.Unavoidability.CheckIsoSoundness

@[expose] public section

/-!
# Faithfulness of Small-Degree Cartwheels in a Minimal Counterexample

This module proves unconditionally (`mc_cartwheelEmbedded_dual`) that in the dual triangulation
`H.dual` of any minimal counterexample `H : Hypermap` (`H.PrimalMinimalCounterexample darts`),
every hub dart `d0` of degree `5 ≤ nodeDegree H.dual d0 darts.length ≤ 11` satisfies
`Math.Unavoidability.CartwheelEmbedded H.dual darts.length refl d0` for both `refl = false`
and `refl = true`.
-/

namespace Hypermap

open Math.Hypermap
open Math.Discharging
open Math.Unavoidability

section DualCycleHelpers

private theorem sameOrbit_node_of_node_f {H : Hypermap} (x : H.Dart) :
    SameOrbit H.node x (H.node.f x) :=
  ⟨1, rfl⟩

private theorem sameOrbit_refl' {D : Type} (p : Perm D) (x : D) : SameOrbit p x x :=
  ⟨0, rfl⟩

private theorem sameOrbit_trans' {D : Type} (p : Perm D) {x y z : D}
    (hxy : SameOrbit p x y) (hyz : SameOrbit p y z) : SameOrbit p x z := by
  rcases hxy with ⟨k1, rfl⟩
  rcases hyz with ⟨k2, rfl⟩
  exact ⟨k2 + k1, Perm.iter_add p k2 k1 x⟩

private theorem sameOrbit_face_of_sameVertex_dual {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : sameVertex H.dual x y darts.length = true) : SameOrbit H.face x y := by
  rw [sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _)] at h
  have hsym := (mem_getOrbit_node_iff_mem_symm H.dual darts h_mc.complete (Nat.le_refl _) y x).mp h
  have hcl := orbitClosesWithin_of_complete H.face darts h_mc.complete y
  have hex := (mem_getOrbit_iff_exists_iter H.face darts.length y x hcl).mp hsym
  rcases hex with ⟨k, hk⟩
  exact sameOrbit_face_symm darts h_mc ⟨k, hk.symm⟩

private theorem sameVertex_dual_of_sameOrbit_face {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : SameOrbit H.face x y) : sameVertex H.dual x y darts.length = true := by
  rcases sameOrbit_face_symm darts h_mc h with ⟨k, hk⟩
  have hcl := orbitClosesWithin_of_complete H.face darts h_mc.complete y
  have hmem := (mem_getOrbit_iff_exists_iter H.face darts.length y x hcl).mpr ⟨k, hk.symm⟩
  have hsym := (mem_getOrbit_node_iff_mem_symm H.dual darts h_mc.complete (Nat.le_refl _) y x).mpr hmem
  exact (sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _) y x).mpr hsym

private theorem sameOrbit_face_iff_sameVertex_dual {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (x y : H.Dart) :
    SameOrbit H.face x y ↔ sameVertex H.dual x y darts.length = true :=
  ⟨sameVertex_dual_of_sameOrbit_face darts h_mc, sameOrbit_face_of_sameVertex_dual darts h_mc⟩

private theorem dual_sameVertex_symm {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : sameVertex H.dual x y darts.length = true) :
    sameVertex H.dual y x darts.length = true := by
  rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _) y x]; exact h

private theorem dual_sameVertex_trans {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y z : H.Dart}
    (h1 : sameVertex H.dual x y darts.length = true)
    (h2 : sameVertex H.dual y z darts.length = true) :
    sameVertex H.dual x z darts.length = true :=
  sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _) h1 h2

private theorem mc_dual_no_self_loop {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (x : H.Dart) :
    sameVertex H.dual x (H.edge.f x) darts.length = false :=
  dual_sameVertex_edge_eq_false_of_isBridgeless H darts h_mc.complete (Nat.le_refl _)
    (Nat.le_refl _) h_mc.is_bridgeless x

private theorem mc_node_cube {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (x : H.Dart) :
    H.node.f (H.node.f (H.node.f x)) = x := by
  have hlen : (getOrbit H.node darts.length x).length = 3 :=
    mc_nodeDegree_eq_three H darts h_mc x
  have hc := perm_iter_length_getOrbit_eq_self_of_complete H.node darts h_mc.complete
    (Nat.le_refl _) x
  rw [hlen] at hc
  exact hc

private theorem mc_dual_tri {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (x : H.dual.Dart) :
    H.dual.face.f (H.dual.face.f (H.dual.face.f x)) = x := by
  change H.node.inv (H.node.inv (H.node.inv x)) = x
  have hcube := mc_node_cube darts h_mc (H.node.inv (H.node.inv (H.node.inv x)))
  rw [H.node.right_inv, H.node.right_inv, H.node.right_inv] at hcube
  exact hcube.symm

private theorem mc_dual_nodeDegree_ge_five {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (x : H.Dart) :
    5 ≤ nodeDegree H.dual x darts.length := by
  rw [nodeDegree_dual_eq_faceDegree_of_complete H darts h_mc.complete (Nat.le_refl _) x]
  exact mc_faceDegree_ge_five H darts h_mc x

private theorem mc_dual_no_parallel {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {d1 d2 : H.Dart}
    (h1 : sameVertex H.dual d1 d2 darts.length = true)
    (h2 : sameVertex H.dual (H.edge.f d1) (H.edge.f d2) darts.length = true) :
    d1 = d2 := by
  by_cases hne : d1 = d2
  · exact hne
  · exact False.elim (mc_no_parallel_edges_of_two_darts H darts h_mc hne
      (sameOrbit_face_of_sameVertex_dual darts h_mc h1)
      (sameOrbit_face_of_sameVertex_dual darts h_mc h2))

private theorem adj_ne_vertex {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {u v : H.Dart}
    (hadj : areAdjacentVertices H.dual u v darts.length = true) :
    sameVertex H.dual u v darts.length = false := by
  cases h : sameVertex H.dual u v darts.length
  · rfl
  · exfalso
    have hirr := areAdjacentVertices_irrefl H.dual darts h_mc.complete (Nat.le_refl _)
      (mc_dual_no_self_loop darts h_mc) u
    have hcongr := areAdjacentVertices_congr H.dual darts h_mc.complete (Nat.le_refl _)
      (sameVertex_refl H.dual darts.length u) h
    have hadj2 : areAdjacentVertices H.dual u u darts.length = true := hcongr.trans hadj
    rw [hadj2] at hirr
    exact Bool.false_ne_true hirr.symm

private theorem faceCycleCut_disj_edge_of {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {k : Nat} (hk3 : 3 ≤ k) (rf cd : Fin k → H.Dart)
    (h_diff : ∀ i j : Fin k, i ≠ j → ¬SameOrbit H.face (rf i) (rf j))
    (h_a : ∀ i : Fin k, SameOrbit H.face (rf i) (cd i))
    (h_b : ∀ i : Fin k, SameOrbit H.face (rf ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) (H.edge.f (cd i))) :
    ∀ i j : Fin k, H.edge.f (cd i) ≠ cd j := by
  intro i j heq
  have hbj := h_b i
  rw [heq] at hbj
  have hs1 : SameOrbit H.face (rf ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) (rf j) :=
    sameOrbit_trans' H.face hbj (sameOrbit_face_symm darts h_mc (h_a j))
  have hj_eq : j = ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ :=
    Classical.byContradiction fun hne => h_diff _ _ (fun h => hne h.symm) hs1
  have heq2 : H.edge.f (cd j) = cd i := by rw [← heq, H.edge_edge]
  have hbj2 := h_b j
  rw [heq2] at hbj2
  have hs2 : SameOrbit H.face (rf ⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩) (rf i) :=
    sameOrbit_trans' H.face hbj2 (sameOrbit_face_symm darts h_mc (h_a i))
  have hi_eq : (⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = i :=
    Classical.byContradiction fun hne => h_diff _ _ hne hs2
  have hv := congrArg Fin.val hi_eq
  dsimp at hv
  rw [hj_eq] at hv
  dsimp at hv
  have hi_lt := i.isLt
  by_cases h1 : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : i.val + 2 < k
    · rw [show i.val + 1 + 1 = i.val + 2 by omega, Nat.mod_eq_of_lt h2] at hv; omega
    · have hk2 : i.val + 1 + 1 = k := by omega
      rw [hk2, Nat.mod_self] at hv; omega
  · have hk1 : i.val + 1 = k := by omega
    rw [hk1, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hv; omega

private theorem sameOrbit_node_cases {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : SameOrbit H.node x y) :
    y = x ∨ y = H.node.f x ∨ H.node.f y = x := by
  rcases h with ⟨k, rfl⟩
  have hcube : ∀ z : H.Dart, H.node.f (H.node.f (H.node.f z)) = z := mc_node_cube darts h_mc
  have h3 : ∀ m : Nat, Perm.iter H.node (m + 3) x = Perm.iter H.node m x := fun m =>
    hcube (Perm.iter H.node m x)
  have h_red : ∀ q r : Nat, Perm.iter H.node (3 * q + r) x = Perm.iter H.node r x := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show 3 * (q + 1) + r = (3 * q + r) + 3 by omega, h3, ih r]
  have hmod : Perm.iter H.node k x = Perm.iter H.node (k % 3) x := by
    have h1 := h_red (k / 3) (k % 3)
    rw [Nat.div_add_mod k 3] at h1
    exact h1
  rw [hmod]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · rw [h0]; exact Or.inl rfl
  · rw [h1]; exact Or.inr (Or.inl rfl)
  · rw [h2]; exact Or.inr (Or.inr (by simpa [Perm.iter] using hcube x))

private theorem mc_three_cycle_consecutive {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (refl : Bool)
    {A B C d_AB d_AC : H.Dart}
    (hAB : sameVertex H.dual A B darts.length = false)
    (hBC : sameVertex H.dual B C darts.length = false)
    (hCA : sameVertex H.dual C A darts.length = false)
    (h1A : sameVertex H.dual d_AB A darts.length = true)
    (h1B : sameVertex H.dual (H.edge.f d_AB) B darts.length = true)
    (h2A : sameVertex H.dual d_AC A darts.length = true)
    (h2C : sameVertex H.dual (H.edge.f d_AC) C darts.length = true)
    (hadjBC : areAdjacentVertices H.dual B C darts.length = true) :
    (nodePermOriented H.dual refl).f d_AB = d_AC ∨
      (nodePermOriented H.dual refl).inv d_AB = d_AC := by
  have hBC_iff := (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) B C).mp hadjBC
  rcases hBC_iff with ⟨d_BC, hd_BCB, hd_BCC⟩
  let rf : Fin 3 → H.Dart := fun i =>
    match i.val with
    | 0 => A
    | 1 => B
    | _ => C
  let cd : Fin 3 → H.Dart := fun i =>
    match i.val with
    | 0 => d_AB
    | 1 => d_BC
    | _ => H.edge.f d_AC
  have h_diff : ∀ i j : Fin 3, i ≠ j → ¬SameOrbit H.face (rf i) (rf j) := by
    rintro ⟨iv, hiv⟩ ⟨jv, hjv⟩ hij hs
    have hsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2) with rfl | rfl | rfl <;>
    rcases (by omega : jv = 0 ∨ jv = 1 ∨ jv = 2) with rfl | rfl | rfl <;>
    simp only [rf] at hsv
    · exact hij rfl
    · rw [hAB] at hsv; exact Bool.false_ne_true hsv
    · rw [dual_sameVertex_symm darts h_mc hsv] at hCA; exact Bool.false_ne_true hCA.symm
    · rw [dual_sameVertex_symm darts h_mc hsv] at hAB; exact Bool.false_ne_true hAB.symm
    · exact hij rfl
    · rw [hBC] at hsv; exact Bool.false_ne_true hsv
    · rw [hCA] at hsv; exact Bool.false_ne_true hsv
    · rw [dual_sameVertex_symm darts h_mc hsv] at hBC; exact Bool.false_ne_true hBC.symm
    · exact hij rfl
  have h_a : ∀ i : Fin 3, SameOrbit H.face (rf i) (cd i) := by
    rintro ⟨iv, hiv⟩
    apply sameOrbit_face_of_sameVertex_dual darts h_mc
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2) with rfl | rfl | rfl <;> dsimp [rf, cd]
    · exact dual_sameVertex_symm darts h_mc h1A
    · exact dual_sameVertex_symm darts h_mc hd_BCB
    · exact dual_sameVertex_symm darts h_mc h2C
  have h_b : ∀ i : Fin 3, SameOrbit H.face (rf ⟨(i.val + 1) % 3, Nat.mod_lt _ (by omega)⟩) (H.edge.f (cd i)) := by
    rintro ⟨iv, hiv⟩
    apply sameOrbit_face_of_sameVertex_dual darts h_mc
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2) with rfl | rfl | rfl <;> simp only [rf, cd]
    · exact dual_sameVertex_symm darts h_mc h1B
    · exact dual_sameVertex_symm darts h_mc hd_BCC
    · rw [H.edge_edge]; exact dual_sameVertex_symm darts h_mc h2A
  let cut : H.FaceCycleCut 3 :=
    { hk := by decide
      ringFace := rf
      cutDart := cd
      h_diff := h_diff
      h_a := h_a
      h_b := h_b
      h_disj_edge := faceCycleCut_disj_edge_of darts h_mc (by decide) rf cd h_diff h_a h_b }
  have hres : H.dual.node.f d_AB = d_AC ∨ H.dual.node.inv d_AB = d_AC := by
    rcases mc_three_cycle_is_facial_dual H darts h_mc cut with h3L | h3R
    · have horb := (mc_three_cycle_facial_orbits_dual H darts h_mc cut h3L).2.2 ⟨0, by decide⟩ ⟨2, by decide⟩
      simp only [cut, cd] at horb
      rcases sameOrbit_node_cases darts h_mc horb with h0 | h1 | h2
      · exfalso
        have heq : H.edge.f d_AB = d_AC := by rw [← h0, H.edge_edge]
        rw [heq] at h1B
        have hAB' := dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc h2A) h1B
        rw [hAB'] at hAB; exact Bool.false_ne_true hAB.symm
      · left
        change H.face.inv d_AB = d_AC
        rw [face_inv_eq_edge_node, ← h1, H.edge_edge]
      · exfalso
        have hfnode : H.face.inv (H.edge.f d_AC) = H.edge.f d_AB := by
          rw [face_inv_eq_edge_node, h2]
        have hCB : sameVertex H.dual C B darts.length = true := by
          have hs1 : SameOrbit H.face (H.edge.f d_AC) (H.face.inv (H.edge.f d_AC)) :=
            sameOrbit_face_symm darts h_mc ⟨1, H.face.right_inv (H.edge.f d_AC)⟩
          rw [hfnode] at hs1
          have hhsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs1
          exact dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc h2C)
            (dual_sameVertex_trans darts h_mc hhsv h1B)
        rw [dual_sameVertex_symm darts h_mc hCB] at hBC
        exact Bool.false_ne_true hBC.symm
    · have horb := (mc_three_cycle_facial_orbits_dual H darts h_mc cut.rev h3R).2.2 ⟨2, by decide⟩ ⟨0, by decide⟩
      have hcutR0 : cut.rev.cutDart ⟨0, by decide⟩ = H.edge.f (cd ⟨2, by decide⟩) := by
        dsimp [FaceCycleCut.rev]
      have hcutR2 : cut.rev.cutDart ⟨2, by decide⟩ = H.edge.f (cd ⟨0, by decide⟩) := by
        dsimp [FaceCycleCut.rev]
      rw [hcutR0, hcutR2] at horb
      simp only [cd] at horb
      rw [H.edge_edge] at horb
      rcases sameOrbit_node_cases darts h_mc horb with h0 | h1 | h2
      · exfalso
        have hAB' : sameVertex H.dual A B darts.length = true := by
          rw [← h0] at h1B
          exact dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc h2A) h1B
        rw [hAB'] at hAB; exact Bool.false_ne_true hAB.symm
      · exfalso
        have hfnode : H.face.inv (H.edge.f d_AB) = H.edge.f d_AC := by
          rw [face_inv_eq_edge_node, ← h1]
        have hBC' : sameVertex H.dual B C darts.length = true := by
          have hs1 : SameOrbit H.face (H.edge.f d_AB) (H.face.inv (H.edge.f d_AB)) :=
            sameOrbit_face_symm darts h_mc ⟨1, H.face.right_inv (H.edge.f d_AB)⟩
          rw [hfnode] at hs1
          have hhsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs1
          exact dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc h1B)
            (dual_sameVertex_trans darts h_mc hhsv h2C)
        rw [hBC'] at hBC; exact Bool.false_ne_true hBC.symm
      · right
        have hinv : H.face.inv d_AC = d_AB := by
          rw [face_inv_eq_edge_node, h2, H.edge_edge]
        change H.face.f d_AB = d_AC
        rw [← hinv, H.face.right_inv]
  cases refl
  · exact hres
  · simp only [nodePermOriented, Perm.symm]
    exact hres.symm

private theorem mc_four_cycle_diag_of_adj {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {v0 v1 v2 v3 : H.Dart}
    (h01 : sameVertex H.dual v0 v1 darts.length = false)
    (h02 : sameVertex H.dual v0 v2 darts.length = false)
    (h03 : sameVertex H.dual v0 v3 darts.length = false)
    (h12 : sameVertex H.dual v1 v2 darts.length = false)
    (h13 : sameVertex H.dual v1 v3 darts.length = false)
    (h23 : sameVertex H.dual v2 v3 darts.length = false)
    (ha01 : areAdjacentVertices H.dual v0 v1 darts.length = true)
    (ha12 : areAdjacentVertices H.dual v1 v2 darts.length = true)
    (ha23 : areAdjacentVertices H.dual v2 v3 darts.length = true)
    (ha30 : areAdjacentVertices H.dual v3 v0 darts.length = true) :
    areAdjacentVertices H.dual v0 v2 darts.length = true ∨
      areAdjacentVertices H.dual v1 v3 darts.length = true := by
  rcases (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) v0 v1).mp ha01 with ⟨d0, hd0a, hd0b⟩
  rcases (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) v1 v2).mp ha12 with ⟨d1, hd1a, hd1b⟩
  rcases (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) v2 v3).mp ha23 with ⟨d2, hd2a, hd2b⟩
  rcases (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) v3 v0).mp ha30 with ⟨d3, hd3a, hd3b⟩
  let rf : Fin 4 → H.Dart := fun i =>
    match i.val with
    | 0 => v0
    | 1 => v1
    | 2 => v2
    | _ => v3
  let cd : Fin 4 → H.Dart := fun i =>
    match i.val with
    | 0 => d0
    | 1 => d1
    | 2 => d2
    | _ => d3
  have h_diff : ∀ i j : Fin 4, i ≠ j → ¬SameOrbit H.face (rf i) (rf j) := by
    rintro ⟨iv, hiv⟩ ⟨jv, hjv⟩ hij hs
    have hsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : jv = 0 ∨ jv = 1 ∨ jv = 2 ∨ jv = 3) with rfl | rfl | rfl | rfl <;>
    simp only [rf] at hsv
    · exact hij rfl
    · rw [h01] at hsv; exact Bool.false_ne_true hsv
    · rw [h02] at hsv; exact Bool.false_ne_true hsv
    · rw [h03] at hsv; exact Bool.false_ne_true hsv
    · rw [dual_sameVertex_symm darts h_mc hsv] at h01; exact Bool.false_ne_true h01.symm
    · exact hij rfl
    · rw [h12] at hsv; exact Bool.false_ne_true hsv
    · rw [h13] at hsv; exact Bool.false_ne_true hsv
    · rw [dual_sameVertex_symm darts h_mc hsv] at h02; exact Bool.false_ne_true h02.symm
    · rw [dual_sameVertex_symm darts h_mc hsv] at h12; exact Bool.false_ne_true h12.symm
    · exact hij rfl
    · rw [h23] at hsv; exact Bool.false_ne_true hsv
    · rw [dual_sameVertex_symm darts h_mc hsv] at h03; exact Bool.false_ne_true h03.symm
    · rw [dual_sameVertex_symm darts h_mc hsv] at h13; exact Bool.false_ne_true h13.symm
    · rw [dual_sameVertex_symm darts h_mc hsv] at h23; exact Bool.false_ne_true h23.symm
    · exact hij rfl
  have h_a : ∀ i : Fin 4, SameOrbit H.face (rf i) (cd i) := by
    rintro ⟨iv, hiv⟩
    apply sameOrbit_face_of_sameVertex_dual darts h_mc
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3) with rfl | rfl | rfl | rfl <;> dsimp [rf, cd]
    · exact dual_sameVertex_symm darts h_mc hd0a
    · exact dual_sameVertex_symm darts h_mc hd1a
    · exact dual_sameVertex_symm darts h_mc hd2a
    · exact dual_sameVertex_symm darts h_mc hd3a
  have h_b : ∀ i : Fin 4, SameOrbit H.face (rf ⟨(i.val + 1) % 4, Nat.mod_lt _ (by omega)⟩) (H.edge.f (cd i)) := by
    rintro ⟨iv, hiv⟩
    apply sameOrbit_face_of_sameVertex_dual darts h_mc
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3) with rfl | rfl | rfl | rfl <;> dsimp [rf, cd]
    · exact dual_sameVertex_symm darts h_mc hd0b
    · exact dual_sameVertex_symm darts h_mc hd1b
    · exact dual_sameVertex_symm darts h_mc hd2b
    · exact dual_sameVertex_symm darts h_mc hd3b
  let cut : H.FaceCycleCut 4 :=
    { hk := by decide
      ringFace := rf
      cutDart := cd
      h_diff := h_diff
      h_a := h_a
      h_b := h_b
      h_disj_edge := faceCycleCut_disj_edge_of darts h_mc (by decide) rf cd h_diff h_a h_b }
  rcases mc_four_cycle_has_diag_edge_dual H darts h_mc cut with ⟨u, hu0, hu2⟩ | ⟨u, hu1, hu3⟩
  · left
    exact areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _)
      (dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc hu0))
      (dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc hu2))
  · right
    exact areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _)
      (dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc hu1))
      (dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc hu3))

private theorem mc_five_cycle_common_neighbor_of_chordless {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (rf : Fin 5 → H.Dart)
    (h_diff : ∀ i j : Fin 5, i ≠ j → sameVertex H.dual (rf i) (rf j) darts.length = false)
    (h_cyc : ∀ i : Fin 5,
      areAdjacentVertices H.dual (rf i) (rf ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) darts.length = true)
    (h_non : ∀ i j : Fin 5, i ≠ j → j.val ≠ (i.val + 1) % 5 → i.val ≠ (j.val + 1) % 5 →
      areAdjacentVertices H.dual (rf i) (rf j) darts.length = false) :
    ∃ w : H.Dart, ∀ m : Fin 5, areAdjacentVertices H.dual w (rf m) darts.length = true := by
  have hadj : ∀ i : Fin 5, ∃ d, sameVertex H.dual d (rf i) darts.length = true ∧
      sameVertex H.dual (H.edge.f d) (rf ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) darts.length = true :=
    fun i => (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) _ _).mp (h_cyc i)
  let cd : Fin 5 → H.Dart := fun i => Classical.choose (hadj i)
  have h_a : ∀ i : Fin 5, SameOrbit H.face (rf i) (cd i) := fun i =>
    sameOrbit_face_of_sameVertex_dual darts h_mc
      (dual_sameVertex_symm darts h_mc (Classical.choose_spec (hadj i)).1)
  have h_b : ∀ i : Fin 5, SameOrbit H.face (rf ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) (H.edge.f (cd i)) :=
    fun i => sameOrbit_face_of_sameVertex_dual darts h_mc
      (dual_sameVertex_symm darts h_mc (Classical.choose_spec (hadj i)).2)
  have h_diff_so : ∀ i j : Fin 5, i ≠ j → ¬SameOrbit H.face (rf i) (rf j) := fun i j hij hs => by
    have hsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs
    rw [h_diff i j hij] at hsv
    exact Bool.false_ne_true hsv
  let cut : H.FaceCycleCut 5 :=
    { hk := by decide
      ringFace := rf
      cutDart := cd
      h_diff := h_diff_so
      h_a := h_a
      h_b := h_b
      h_disj_edge := faceCycleCut_disj_edge_of darts h_mc (by decide) rf cd h_diff_so h_a h_b }
  have h_chord : Chordless5 cut := by
    intro i j hij h1 h2 u hu hv
    have htrue : areAdjacentVertices H.dual (rf i) (rf j) darts.length = true :=
      areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _)
        (dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc hu))
        (dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc hv))
    rw [h_non i j hij h1 h2] at htrue
    exact Bool.false_ne_true htrue
  rcases mc_birkhoff_five_ring_encloses_single_vertex_dual darts h_mc cut h_chord with
      ⟨w, _, _, _, h_edges⟩ | ⟨w, _, _, _, h_edges⟩
  · refine ⟨w, fun m => ?_⟩
    have hm := h_edges m
    have hsw : sameVertex H.dual (Perm.iter H.face ((5 - m.val) % 5) w) w darts.length = true :=
      dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc ⟨(5 - m.val) % 5, rfl⟩)
    have hsm : sameVertex H.dual (H.edge.f (Perm.iter H.face ((5 - m.val) % 5) w)) (rf m) darts.length = true :=
      dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc hm)
    exact areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _) hsw hsm
  · refine ⟨w, fun m => ?_⟩
    let k : Fin 5 := ⟨(5 - m.val) % 5, Nat.mod_lt _ (by decide)⟩
    have hm := h_edges k
    have hrf : cut.rev.ringFace k = rf m := by
      dsimp [FaceCycleCut.rev, k, cut]
      congr 1
      ext
      rcases (by have := m.isLt; omega :
        m.val = 0 ∨ m.val = 1 ∨ m.val = 2 ∨ m.val = 3 ∨ m.val = 4) with h | h | h | h | h <;>
        simp [h]
    rw [hrf] at hm
    have hsw : sameVertex H.dual (Perm.iter H.face ((5 - k.val) % 5) w) w darts.length = true :=
      dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc ⟨(5 - k.val) % 5, rfl⟩)
    have hsm : sameVertex H.dual (H.edge.f (Perm.iter H.face ((5 - k.val) % 5) w)) (rf m) darts.length = true :=
      dual_sameVertex_symm darts h_mc (sameVertex_dual_of_sameOrbit_face darts h_mc hm)
    exact areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _) hsw hsm

end DualCycleHelpers

section CartwheelProofHelpers

private def nextDeg (deg i : Nat) : Nat :=
  if i = deg then 1 else i + 1

private def prevDeg (deg i : Nat) : Nat :=
  if i = 1 then deg else i - 1

private theorem nextDeg_ge_one {deg i : Nat} : 1 ≤ nextDeg deg i := by
  unfold nextDeg
  split <;> omega

private theorem nextDeg_le {deg i : Nat} (hdeg : 1 ≤ deg) (hi : i ≤ deg) :
    nextDeg deg i ≤ deg := by
  unfold nextDeg
  split <;> omega

private theorem prevDeg_ge_one {deg i : Nat} (hdeg : 1 ≤ deg) (hi1 : 1 ≤ i) :
    1 ≤ prevDeg deg i := by
  unfold prevDeg
  split <;> omega

private theorem prevDeg_le {deg i : Nat} (hi : i ≤ deg) : prevDeg deg i ≤ deg := by
  unfold prevDeg
  split <;> omega

private theorem nextDeg_ne_self {deg i : Nat} (hdeg : 2 ≤ deg) :
    nextDeg deg i ≠ i := by
  unfold nextDeg
  split <;> omega

private theorem prevDeg_ne_self {deg i : Nat} (hdeg : 2 ≤ deg) (hi1 : 1 ≤ i) :
    prevDeg deg i ≠ i := by
  unfold prevDeg
  split <;> omega

private theorem nextDeg_prevDeg {deg i : Nat} (hi1 : 1 ≤ i) (hi : i ≤ deg) :
    nextDeg deg (prevDeg deg i) = i := by
  unfold nextDeg prevDeg
  split <;> split <;> omega

private theorem prevDeg_nextDeg {deg i : Nat} (hi1 : 1 ≤ i) (_hi : i ≤ deg) :
    prevDeg deg (nextDeg deg i) = i := by
  unfold nextDeg prevDeg
  split <;> split <;> omega

private theorem nextDeg_nextDeg_ne_prevDeg {deg i : Nat} (hdeg : 5 ≤ deg) (hi1 : 1 ≤ i) (_hi : i ≤ deg) :
    nextDeg deg (nextDeg deg i) ≠ prevDeg deg i := by
  unfold nextDeg prevDeg
  repeat' split
  all_goals omega

private theorem iter_succ_eq {D : Type} (p : Perm D) (n : Nat) (x : D) :
    p.f (Perm.iter p n x) = Perm.iter p (n + 1) x := by
  rw [show n + 1 = 1 + n by omega, Perm.iter_add]
  rfl

private theorem dual_edge_f (H : Hypermap) (x : H.Dart) : H.dual.edge.f x = H.edge.f x := rfl

private theorem div_mod_spoke (deg r i : Nat) (hdeg : 0 < deg) (hi1 : 1 ≤ i) (hi : i ≤ deg) :
    (r * deg + i - 1) / deg = r ∧ (r * deg + i - 1) % deg + 1 = i := by
  have h1 : r * deg + i - 1 = deg * r + (i - 1) := by rw [Nat.mul_comm r deg]; omega
  constructor
  · rw [h1, Nat.mul_add_div hdeg, Nat.div_eq_of_lt (by omega : i - 1 < deg), Nat.add_zero]
  · have h2 : r * deg + i - 1 = (i - 1) + deg * r := by rw [Nat.mul_comm r deg]; omega
    rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : i - 1 < deg)]
    omega

private theorem spokeDart_eq_iter (T : Hypermap) (refl : Bool) (d0 : T.Dart) (i : Nat) :
    spokeDartOriented T refl d0 i = Perm.iter (nodePermOriented T refl) (i - 1) d0 := by
  unfold spokeDartOriented nodePermOriented
  cases refl <;> rfl

private theorem sameVertex_spokeDart {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    sameVertex H.dual (spokeDartOriented H.dual refl d0 i) d0 darts.length = true := by
  rw [spokeDart_eq_iter]
  have hmem : Perm.iter (nodePermOriented H.dual refl) (i - 1) d0 ∈ getOrbit H.dual.node darts.length d0 :=
    (mem_getOrbit_nodePermOriented_iff H.dual darts h_mc.complete (Nat.le_refl _) refl d0 _).mpr
      ⟨i - 1, by omega, rfl⟩
  exact (sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _) d0 _).mpr hmem

private theorem spokeDart_next {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    (nodePermOriented H.dual refl).f (spokeDartOriented H.dual refl d0 i) =
      spokeDartOriented H.dual refl d0 (nextDeg (nodeDegree H.dual d0 darts.length) i) := by
  rw [spokeDart_eq_iter, spokeDart_eq_iter]
  unfold nextDeg
  by_cases hid : i = nodeDegree H.dual d0 darts.length
  · subst hid
    simp only [if_true, Nat.sub_self, Perm.iter]
    rw [iter_succ_eq, show nodeDegree H.dual d0 darts.length - 1 + 1 = nodeDegree H.dual d0 darts.length by omega]
    exact Math.Unavoidability.perm_iter_nodePermOriented_deg_eq_self H.dual darts h_mc.complete
      (Nat.le_refl _) refl d0
  · simp only [hid, if_false]
    rw [iter_succ_eq, show (i + 1) - 1 = (i - 1) + 1 by omega]

private theorem spokeDart_prev {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hdeg : 1 ≤ nodeDegree H.dual d0 darts.length)
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    (nodePermOriented H.dual refl).inv (spokeDartOriented H.dual refl d0 i) =
      spokeDartOriented H.dual refl d0 (prevDeg (nodeDegree H.dual d0 darts.length) i) := by
  have hp1 := prevDeg_ge_one hdeg hi1
  have hp2 := prevDeg_le hi
  have hnext := spokeDart_next darts h_mc refl d0 hp1 hp2
  rw [nextDeg_prevDeg hi1 hi] at hnext
  rw [← hnext]
  exact (nodePermOriented H.dual refl).left_inv _

private def spokeRay (H : Hypermap) (refl : Bool) (d0 : H.Dart) (i m : Nat) : H.Dart :=
  Perm.iter (nodePermOriented H.dual refl) m (H.edge.f (spokeDartOriented H.dual refl d0 i))

private theorem cartDart_zero (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart) :
    cartDartOriented T deg refl d0 0 = d0 := by
  unfold cartDartOriented
  rfl

private theorem cartDart_spoke_eq (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ deg) :
    cartDartOriented T deg refl d0 i = T.edge.f (spokeDartOriented T refl d0 i) :=
  cartDartOriented_spoke T deg refl d0 hi1 hi

private theorem cartDart_hat_eq (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ deg) :
    cartDartOriented T deg refl d0 (deg + i) =
      T.edge.f ((nodePermOriented T refl).inv ((nodePermOriented T refl).inv
        (T.edge.f (spokeDartOriented T refl d0 i)))) := by
  unfold cartDartOriented
  have hne : deg + i ≠ 0 := by omega
  have hdm := div_mod_spoke deg 1 i (by omega) hi1 hi
  rw [show 1 * deg + i = deg + i by omega] at hdm
  simp only [beq_iff_eq, hne, if_false, hdm.1, hdm.2, if_true]
  unfold ruleVertexDart ruleRot nodePermOriented
  cases refl <;> rfl

private theorem cartDart_fan_eq (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart) {r i : Nat}
    (hr : r = 2 ∨ r = 3 ∨ r = 4) (hi1 : 1 ≤ i) (hi : i ≤ deg) :
    cartDartOriented T deg refl d0 (r * deg + i) =
      T.edge.f (Perm.iter (nodePermOriented T refl) (r + 1)
        (T.edge.f (spokeDartOriented T refl d0 i))) := by
  unfold cartDartOriented
  have hne : r * deg + i ≠ 0 := by rcases hr with rfl | rfl | rfl <;> omega
  have hdm := div_mod_spoke deg r i (by omega) hi1 hi
  simp only [beq_iff_eq, hne, if_false, hdm.1, hdm.2]
  rcases hr with rfl | rfl | rfl
  · simp only [if_true, show ¬(2 = 0) by omega, show ¬(2 = 1) by omega, if_false]
    unfold ruleVertexDart ruleRotInv nodePermOriented
    cases refl <;> rfl
  · simp only [if_true, show ¬(3 = 0) by omega, show ¬(3 = 1) by omega, show ¬(3 = 2) by omega, if_false]
    unfold ruleVertexDart ruleRotInv nodePermOriented
    cases refl <;> rfl
  · simp only [show ¬(4 = 0) by omega, show ¬(4 = 1) by omega, show ¬(4 = 2) by omega,
      show ¬(4 = 3) by omega, if_false]
    unfold nodePermOriented Perm.symm Perm.iter
    cases refl <;> rfl

private theorem sameVertex_spokeRay {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat} (m : Nat)
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length)
    (hm : m < nodeDegree H.dual (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length) :
    sameVertex H.dual (spokeRay H refl d0 i m)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length = true := by
  rw [cartDart_spoke_eq _ _ _ _ hi1 hi] at hm ⊢
  unfold spokeRay
  have hmem := (mem_getOrbit_nodePermOriented_iff H.dual darts h_mc.complete (Nat.le_refl _) refl
    (H.edge.f (spokeDartOriented H.dual refl d0 i)) _).mpr ⟨m, hm, rfl⟩
  exact (sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _)
    (H.edge.f (spokeDartOriented H.dual refl d0 i)) _).mpr hmem

private theorem dual_neighbor_of_hub {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 w : H.Dart)
    (hadj : areAdjacentVertices H.dual d0 w darts.length = true) :
    ∃ u, 1 ≤ u ∧ u ≤ nodeDegree H.dual d0 darts.length ∧
      sameVertex H.dual w
        (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 u) darts.length = true := by
  rcases (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) d0 w).mp hadj with ⟨d, hd0, hdw⟩
  have hmem := (sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _) d0 d).mp hd0
  rcases (mem_getOrbit_nodePermOriented_iff H.dual darts h_mc.complete (Nat.le_refl _) refl d0 d).mp hmem with
    ⟨m, hm, rfl⟩
  refine ⟨m + 1, by omega, by omega, ?_⟩
  rw [cartDart_spoke_eq _ _ _ _ (by omega : 1 ≤ m + 1) (by omega)]
  have hsd : spokeDartOriented H.dual refl d0 (m + 1) = Perm.iter (nodePermOriented H.dual refl) m d0 := by
    rw [spokeDart_eq_iter]; rfl
  rw [hsd]
  exact dual_sameVertex_symm darts h_mc hdw

private theorem dual_neighbor_of_spoke {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length)
    (w : H.Dart)
    (hadj : areAdjacentVertices H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) w darts.length = true) :
    ∃ m, m < nodeDegree H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length ∧
      sameVertex H.dual (H.edge.f (spokeRay H refl d0 i m)) w darts.length = true := by
  let ci := cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i
  rcases (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) ci w).mp hadj with ⟨d, hdc, hdw⟩
  have hmem := (sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _) ci d).mp hdc
  rcases (mem_getOrbit_nodePermOriented_iff H.dual darts h_mc.complete (Nat.le_refl _) refl ci d).mp hmem with
    ⟨m, hm, rfl⟩
  refine ⟨m, hm, ?_⟩
  have hci : ci = H.edge.f (spokeDartOriented H.dual refl d0 i) :=
    cartDart_spoke_eq _ _ _ _ hi1 hi
  rw [hci] at hdw
  unfold spokeRay
  exact hdw

private theorem sameVertex_inv_self {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (x : H.Dart) :
    sameVertex H.dual ((nodePermOriented H.dual refl).inv x) x darts.length = true := by
  let cdx := nodeDegree H.dual x darts.length
  have hcd1 : 1 ≤ cdx := by have := mc_dual_nodeDegree_ge_five darts h_mc x; omega
  have hcyc := Math.Unavoidability.perm_iter_nodePermOriented_deg_eq_self H.dual darts h_mc.complete
    (Nat.le_refl _) refl x
  have hinv : (nodePermOriented H.dual refl).inv x = Perm.iter (nodePermOriented H.dual refl) (cdx - 1) x := by
    have hf : (nodePermOriented H.dual refl).f (Perm.iter (nodePermOriented H.dual refl) (cdx - 1) x) = x := by
      rw [iter_succ_eq, show cdx - 1 + 1 = cdx by omega]
      exact hcyc
    calc
      (nodePermOriented H.dual refl).inv x
          = (nodePermOriented H.dual refl).inv ((nodePermOriented H.dual refl).f
              (Perm.iter (nodePermOriented H.dual refl) (cdx - 1) x)) := by rw [hf]
      _ = Perm.iter (nodePermOriented H.dual refl) (cdx - 1) x :=
        (nodePermOriented H.dual refl).left_inv _
  rw [hinv]
  have hmem := (mem_getOrbit_nodePermOriented_iff H.dual darts h_mc.complete (Nat.le_refl _) refl x _).mpr
    ⟨cdx - 1, by omega, rfl⟩
  exact (sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _) x _).mpr hmem

private theorem sameVertex_f_self {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (x : H.Dart) :
    sameVertex H.dual ((nodePermOriented H.dual refl).f x) x darts.length = true := by
  have hmem := (mem_getOrbit_nodePermOriented_iff H.dual darts h_mc.complete (Nat.le_refl _) refl x _).mpr
    ⟨1, by have := mc_dual_nodeDegree_ge_five darts h_mc x; omega, rfl⟩
  exact (sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _) x _).mpr hmem

private theorem cartDegOriented_eq (T : Hypermap) [DecidableEq T.Dart]
    (fuel deg : Nat) (refl : Bool) (d0 : T.Dart) (u : Nat) :
    cartDegOriented T fuel deg refl d0 u =
      nodeDegree T (cartDartOriented T deg refl d0 u) fuel :=
  rfl

private theorem spokeRay_zero_edge (H : Hypermap) (refl : Bool) (d0 : H.Dart) (i : Nat) :
    H.edge.f (spokeRay H refl d0 i 0) = spokeDartOriented H.dual refl d0 i := by
  unfold spokeRay
  exact H.edge_edge _

private theorem spokeRay_one_edge {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hdeg : 1 ≤ nodeDegree H.dual d0 darts.length)
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    H.edge.f (spokeRay H refl d0 i 1) =
      (nodePermOriented H.dual refl).inv
        (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0
          (prevDeg (nodeDegree H.dual d0 darts.length) i)) := by
  let deg := nodeDegree H.dual d0 darts.length
  have hp1 := prevDeg_ge_one hdeg hi1
  have hp2 := prevDeg_le hi
  rw [cartDart_spoke_eq _ _ _ _ hp1 hp2]
  have hnext := spokeDart_next darts h_mc refl d0 hp1 hp2
  rw [nextDeg_prevDeg hi1 hi] at hnext
  have htri := tri_fan_turn_edge H.dual (mc_dual_tri darts h_mc) refl (spokeDartOriented H.dual refl d0 (prevDeg deg i))
  rw [hnext] at htri
  exact htri

private theorem spokeRay_sub_one_eq_inv {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    spokeRay H refl d0 i (nodeDegree H.dual (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length - 1) =
      (nodePermOriented H.dual refl).inv (H.edge.f (spokeDartOriented H.dual refl d0 i)) := by
  let x := H.edge.f (spokeDartOriented H.dual refl d0 i)
  let cd := nodeDegree H.dual (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length
  have hcd1 : 1 ≤ cd := by
    have := mc_dual_nodeDegree_ge_five darts h_mc (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i)
    omega
  have hdeg_eq : cd = nodeDegree H.dual x darts.length := by
    dsimp [cd]
    rw [cartDart_spoke_eq _ _ _ _ hi1 hi, dual_edge_f]
  have hcyc := Math.Unavoidability.perm_iter_nodePermOriented_deg_eq_self H.dual darts h_mc.complete
    (Nat.le_refl _) refl x
  rw [← hdeg_eq, ← show cd - 1 + 1 = cd by omega, ← iter_succ_eq] at hcyc
  calc
    spokeRay H refl d0 i (cd - 1)
        = (nodePermOriented H.dual refl).inv ((nodePermOriented H.dual refl).f (spokeRay H refl d0 i (cd - 1))) :=
      ((nodePermOriented H.dual refl).left_inv _).symm
    _ = (nodePermOriented H.dual refl).inv x := by
      change (nodePermOriented H.dual refl).inv
        ((nodePermOriented H.dual refl).f (Perm.iter (nodePermOriented H.dual refl) (cd - 1) x)) = _
      rw [hcyc]

private theorem spokeRay_pred_edge {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hdeg : 1 ≤ nodeDegree H.dual d0 darts.length)
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    H.edge.f (spokeRay H refl d0 i
      (nodeDegree H.dual (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length - 1)) =
      (nodePermOriented H.dual refl).f
        (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0
          (nextDeg (nodeDegree H.dual d0 darts.length) i)) := by
  let deg := nodeDegree H.dual d0 darts.length
  have hn1 := nextDeg_ge_one (deg := deg) (i := i)
  have hn2 := nextDeg_le hdeg hi
  rw [cartDart_spoke_eq _ _ _ _ hn1 hn2, spokeRay_sub_one_eq_inv darts h_mc refl d0 hi1 hi]
  have htri := tri_fan_turn H.dual (mc_dual_tri darts h_mc) refl (spokeDartOriented H.dual refl d0 i)
  rw [spokeDart_next darts h_mc refl d0 hi1 hi] at htri
  exact htri

private theorem spokeRay_sub_two_eq_inv2 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    spokeRay H refl d0 i (nodeDegree H.dual (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length - 2) =
      (nodePermOriented H.dual refl).inv ((nodePermOriented H.dual refl).inv (H.edge.f (spokeDartOriented H.dual refl d0 i))) := by
  let x := H.edge.f (spokeDartOriented H.dual refl d0 i)
  let cd := nodeDegree H.dual (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length
  have hcd2 : 2 ≤ cd := by
    have := mc_dual_nodeDegree_ge_five darts h_mc (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i)
    omega
  have hstep : (nodePermOriented H.dual refl).f (Perm.iter (nodePermOriented H.dual refl) (cd - 2) x) =
      Perm.iter (nodePermOriented H.dual refl) (cd - 1) x := by
    rw [iter_succ_eq, show cd - 2 + 1 = cd - 1 by omega]
  calc
    spokeRay H refl d0 i (cd - 2)
        = (nodePermOriented H.dual refl).inv ((nodePermOriented H.dual refl).f (spokeRay H refl d0 i (cd - 2))) :=
      ((nodePermOriented H.dual refl).left_inv _).symm
    _ = (nodePermOriented H.dual refl).inv (spokeRay H refl d0 i (cd - 1)) := by
      change (nodePermOriented H.dual refl).inv
        ((nodePermOriented H.dual refl).f (Perm.iter (nodePermOriented H.dual refl) (cd - 2) x)) = _
      rw [hstep]
      rfl
    _ = (nodePermOriented H.dual refl).inv ((nodePermOriented H.dual refl).inv x) := by
      rw [spokeRay_sub_one_eq_inv darts h_mc refl d0 hi1 hi]

private theorem spokeRay_pred2_edge {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    H.edge.f (spokeRay H refl d0 i
      (nodeDegree H.dual (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length - 2)) =
      cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0
        (nodeDegree H.dual d0 darts.length + i) := by
  rw [spokeRay_sub_two_eq_inv2 darts h_mc refl d0 hi1 hi, cartDart_hat_eq _ _ _ _ hi1 hi]

private theorem spokeRay_two_edge {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hdeg : 1 ≤ nodeDegree H.dual d0 darts.length)
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    H.edge.f (spokeRay H refl d0 i 2) =
      (nodePermOriented H.dual refl).inv
        (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0
          (nodeDegree H.dual d0 darts.length + prevDeg (nodeDegree H.dual d0 darts.length) i)) := by
  let deg := nodeDegree H.dual d0 darts.length
  let ρ := nodePermOriented H.dual refl
  have hp1 := prevDeg_ge_one hdeg hi1
  have hp2 := prevDeg_le hi
  let s_prev := spokeDartOriented H.dual refl d0 (prevDeg deg i)
  let y := ρ.inv (H.edge.f s_prev)
  let z := ρ.inv y
  have hy_edge : H.edge.f y = ρ.f (H.edge.f (spokeDartOriented H.dual refl d0 i)) := by
    have htri := tri_fan_turn H.dual (mc_dual_tri darts h_mc) refl s_prev
    have hnext := spokeDart_next darts h_mc refl d0 hp1 hp2
    rw [nextDeg_prevDeg hi1 hi] at hnext
    rw [hnext] at htri
    exact htri
  have hfz : ρ.f z = y := ρ.right_inv y
  have htri_z := tri_fan_turn_edge H.dual (mc_dual_tri darts h_mc) refl z
  change H.edge.f (ρ.f (H.edge.f (ρ.f z))) = ρ.inv (H.edge.f z) at htri_z
  rw [hfz, hy_edge] at htri_z
  have hez : H.edge.f z = cartDartOriented H.dual deg refl d0 (deg + prevDeg deg i) := by
    rw [cartDart_hat_eq _ _ _ _ hp1 hp2]
  rw [hez] at htri_z
  exact htri_z

private theorem spokeRay_fan_edge (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {r i : Nat}
    (hr : r = 2 ∨ r = 3 ∨ r = 4) (hi1 : 1 ≤ i) (hi : i ≤ deg) :
    H.edge.f (spokeRay H refl d0 i (r + 1)) =
      cartDartOriented H.dual deg refl d0 (r * deg + i) := by
  rw [cartDart_fan_eq H.dual deg refl d0 hr hi1 hi]
  rfl

private theorem hub_ne_spoke {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    sameVertex H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 0)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length = false := by
  cases h : sameVertex H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 0)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length
  · rfl
  · exfalso
    rw [cartDart_zero, cartDart_spoke_eq _ _ _ _ hi1 hi, dual_edge_f] at h
    have hs := sameVertex_spokeDart darts h_mc refl d0 hi1 hi
    have hself := dual_sameVertex_trans darts h_mc hs h
    have hirr := mc_dual_no_self_loop darts h_mc (spokeDartOriented H.dual refl d0 i)
    rw [hself] at hirr
    exact Bool.false_ne_true hirr.symm

private theorem spoke_ne_spoke {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i j : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length)
    (hj1 : 1 ≤ j) (hj : j ≤ nodeDegree H.dual d0 darts.length) (hne : i ≠ j) :
    sameVertex H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 j) darts.length = false := by
  cases h : sameVertex H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 j) darts.length
  · rfl
  · exfalso
    rw [cartDart_spoke_eq _ _ _ _ hi1 hi, cartDart_spoke_eq _ _ _ _ hj1 hj] at h
    have hsi := sameVertex_spokeDart darts h_mc refl d0 hi1 hi
    have hsj := sameVertex_spokeDart darts h_mc refl d0 hj1 hj
    have hsij := dual_sameVertex_trans darts h_mc hsi (dual_sameVertex_symm darts h_mc hsj)
    have heq := mc_dual_no_parallel darts h_mc hsij h
    rw [spokeDart_eq_iter, spokeDart_eq_iter] at heq
    have hinj := perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _)
      refl d0 (by omega : i - 1 < nodeDegree H.dual d0 darts.length)
      (by omega : j - 1 < nodeDegree H.dual d0 darts.length) heq
    exact hne (by omega)

private def activeL2Pos (deg : Nat) (cartDeg : Nat → Nat) (p : Nat) : Prop :=
  (deg + 1 ≤ p ∧ p ≤ 2 * deg) ∨
    ∃ i r, 1 ≤ i ∧ i ≤ deg ∧ (r = 2 ∨ r = 3 ∨ r = 4) ∧ p = r * deg + i ∧ r + 4 ≤ cartDeg i ∧ cartDeg i ≤ 8

private def isAttachedSpoke (deg : Nat) (cartDeg : Nat → Nat) (u p : Nat) : Prop :=
  1 ≤ u ∧ u ≤ deg ∧
    (p = deg + u ∨ p = deg + prevDeg deg u ∨
      ∃ r, (r = 2 ∨ r = 3 ∨ r = 4) ∧ p = r * deg + u ∧ r + 4 ≤ cartDeg u ∧ cartDeg u ≤ 8)

private def spokeFanIdx (deg : Nat) (cartDeg : Nat → Nat) (u p : Nat) : Nat :=
  if p = deg + prevDeg deg u then 2
  else if p = deg + u then cartDeg u - 2
  else (p - 1) / deg + 1

private theorem l2_has_attached_spoke {deg : Nat} {cartDeg : Nat → Nat} (_hdeg : 1 ≤ deg)
    {p : Nat} (hp : activeL2Pos deg cartDeg p) :
    ∃ u, isAttachedSpoke deg cartDeg u p := by
  rcases hp with ⟨hp1, hp2⟩ | ⟨i, r, hi1, hi, hr, rfl, hrc, hc8⟩
  · refine ⟨p - deg, by omega, by omega, Or.inl (by omega)⟩
  · exact ⟨i, hi1, hi, Or.inr (Or.inr ⟨r, hr, rfl, hrc, hc8⟩)⟩

private theorem spokeFanIdx_spec {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    {u p : Nat}
    (hatt : isAttachedSpoke (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) u p) :
    let deg := nodeDegree H.dual d0 darts.length
    let cartDeg := cartDegOriented H.dual darts.length deg refl d0
    let m := spokeFanIdx deg cartDeg u p
    2 ≤ m ∧ m ≤ cartDeg u - 2 ∧
      sameVertex H.dual (H.edge.f (spokeRay H refl d0 u m))
        (cartDartOriented H.dual deg refl d0 p) darts.length = true ∧
      areAdjacentVertices H.dual
        (cartDartOriented H.dual deg refl d0 u)
        (cartDartOriented H.dual deg refl d0 p) darts.length = true := by
  dsimp only
  let deg := nodeDegree H.dual d0 darts.length
  let cartDeg := cartDegOriented H.dual darts.length deg refl d0
  rcases hatt with ⟨hu1, hu, hcases⟩
  have hcd_eq : cartDeg u = nodeDegree H.dual (cartDartOriented H.dual deg refl d0 u) darts.length := rfl
  have hcd5 : 5 ≤ cartDeg u := by
    rw [hcd_eq]; exact mc_dual_nodeDegree_ge_five darts h_mc _
  have hstep : ∀ m, 2 ≤ m → m ≤ cartDeg u - 2 →
      sameVertex H.dual (H.edge.f (spokeRay H refl d0 u m))
        (cartDartOriented H.dual deg refl d0 p) darts.length = true →
      2 ≤ m ∧ m ≤ cartDeg u - 2 ∧
        sameVertex H.dual (H.edge.f (spokeRay H refl d0 u m))
          (cartDartOriented H.dual deg refl d0 p) darts.length = true ∧
        areAdjacentVertices H.dual
          (cartDartOriented H.dual deg refl d0 u)
          (cartDartOriented H.dual deg refl d0 p) darts.length = true := by
    intro m hm2 hmcd hsm
    refine ⟨hm2, hmcd, hsm, ?_⟩
    exact areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _)
      (sameVertex_spokeRay darts h_mc refl d0 m hu1 hu
        (by rw [← hcd_eq]; exact Nat.lt_of_le_of_lt hmcd (by omega))) hsm
  rcases hcases with rfl | rfl | ⟨r, hr, rfl, hrc, hc8⟩
  · have hprev_ne : prevDeg deg u ≠ u := prevDeg_ne_self (by omega) hu1
    have hpre_le : prevDeg deg u ≤ deg := prevDeg_le hu
    have hm_eq : spokeFanIdx deg cartDeg u (deg + u) = cartDeg u - 2 := by
      unfold spokeFanIdx
      rw [if_neg (by omega), if_pos rfl]
    rw [hm_eq]
    refine hstep (cartDeg u - 2) (by omega) (Nat.le_refl _) ?_
    rw [hcd_eq, spokeRay_pred2_edge darts h_mc refl d0 hu1 hu]
    exact sameVertex_refl H.dual darts.length _
  · have hm_eq : spokeFanIdx deg cartDeg u (deg + prevDeg deg u) = 2 := by
      unfold spokeFanIdx
      rw [if_pos rfl]
    rw [hm_eq]
    refine hstep 2 (Nat.le_refl _) (by omega) ?_
    rw [spokeRay_two_edge darts h_mc refl d0 (by omega) hu1 hu]
    exact sameVertex_inv_self darts h_mc refl _
  · have hq := (div_mod_spoke deg r u (by omega) hu1 hu).1
    have hpre_le : prevDeg deg u ≤ deg := prevDeg_le hu
    have hcd_ge_r : r + 4 ≤ cartDeg u := hrc
    have hm_eq : spokeFanIdx deg cartDeg u (r * deg + u) = r + 1 := by
      unfold spokeFanIdx
      rw [if_neg (by rcases hr with rfl | rfl | rfl <;> omega),
          if_neg (by rcases hr with rfl | rfl | rfl <;> omega), hq]
    rw [hm_eq]
    refine hstep (r + 1) (by rcases hr with rfl | rfl | rfl <;> omega) (by omega) ?_
    rw [spokeRay_fan_edge H deg refl d0 hr hu1 hu]
    exact sameVertex_refl H.dual darts.length _

private theorem spokeFanIdx_inj {deg : Nat} {cartDeg : Nat → Nat} (hdeg5 : 5 ≤ deg)
    {u p q : Nat}
    (hp : isAttachedSpoke deg cartDeg u p) (hq : isAttachedSpoke deg cartDeg u q) (hne : p ≠ q)
    (hcd5 : 5 ≤ cartDeg u) :
    spokeFanIdx deg cartDeg u p ≠ spokeFanIdx deg cartDeg u q := by
  have hu1 := hp.1
  have hu := hp.2.1
  have hp' := hp.2.2
  have hq' := hq.2.2
  have hpre_ge : 1 ≤ prevDeg deg u := prevDeg_ge_one (by omega) hp.1
  have hpre_le : prevDeg deg u ≤ deg := prevDeg_le hp.2.1
  have hpre_ne : prevDeg deg u ≠ u := prevDeg_ne_self (by omega) hp.1
  have hr_eq : ∀ r : Nat, r = 2 ∨ r = 3 ∨ r = 4 →
      spokeFanIdx deg cartDeg u (r * deg + u) = r + 1 := fun r hr => by
    unfold spokeFanIdx
    have hqdiv := (div_mod_spoke deg r u (by omega) hu1 hu).1
    rw [if_neg (by rcases hr with rfl | rfl | rfl <;> omega),
        if_neg (by rcases hr with rfl | rfl | rfl <;> omega), hqdiv]
  have h1_eq : spokeFanIdx deg cartDeg u (deg + prevDeg deg u) = 2 := by
    unfold spokeFanIdx; rw [if_pos rfl]
  have h2_eq : spokeFanIdx deg cartDeg u (deg + u) = cartDeg u - 2 := by
    unfold spokeFanIdx; rw [if_neg (by omega), if_pos rfl]
  rcases hp' with rfl | rfl | ⟨rp, hrp, rfl, hrcp, hc8p⟩ <;>
  rcases hq' with hq1 | hq2 | ⟨rq, hrq, hq3, hrcq, hc8q⟩
  · exact False.elim (hne hq1.symm)
  · rw [hq2, h2_eq, h1_eq]; omega
  · rw [hq3, h2_eq, hr_eq rq hrq]; rcases hrq with rfl | rfl | rfl <;> omega
  · rw [hq1, h1_eq, h2_eq]; omega
  · exact False.elim (hne hq2.symm)
  · rw [hq3, h1_eq, hr_eq rq hrq]; rcases hrq with rfl | rfl | rfl <;> omega
  · rw [hq1, hr_eq rp hrp, h2_eq]; rcases hrp with rfl | rfl | rfl <;> omega
  · rw [hq2, hr_eq rp hrp, h1_eq]; rcases hrp with rfl | rfl | rfl <;> omega
  · rw [hq3, hr_eq rp hrp, hr_eq rq hrq]
    intro heq
    apply hne
    have : rp = rq := by omega
    subst this; exact hq3.symm

private theorem l2_ne_hub {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    {p : Nat} (hp : activeL2Pos (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) p) :
    sameVertex H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 0)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p) darts.length = false := by
  let deg := nodeDegree H.dual d0 darts.length
  let cartDeg := cartDegOriented H.dual darts.length deg refl d0
  rcases l2_has_attached_spoke (by omega) hp with ⟨u, hu⟩
  rcases spokeFanIdx_spec darts h_mc refl d0 hdeg5 hu with ⟨hm2, hmcd, hsm, _⟩
  have hcd_eq : cartDeg u = nodeDegree H.dual (cartDartOriented H.dual deg refl d0 u) darts.length := rfl
  have hcd5 : 5 ≤ cartDeg u := by rw [hcd_eq]; exact mc_dual_nodeDegree_ge_five darts h_mc _
  cases h : sameVertex H.dual (cartDartOriented H.dual deg refl d0 0) (cartDartOriented H.dual deg refl d0 p) darts.length
  · rfl
  · exfalso
    have h0 : sameVertex H.dual (spokeRay H refl d0 u 0) (spokeRay H refl d0 u (spokeFanIdx deg cartDeg u p)) darts.length = true := by
      have s0 := sameVertex_spokeRay darts h_mc refl d0 0 hu.1 hu.2.1 (by dsimp only [deg, cartDeg] at hcd_eq ⊢; rw [← hcd_eq]; omega)
      have sm := sameVertex_spokeRay darts h_mc refl d0 (spokeFanIdx deg cartDeg u p) hu.1 hu.2.1 (by dsimp only [deg, cartDeg] at hcd_eq ⊢; rw [← hcd_eq]; omega)
      exact dual_sameVertex_trans darts h_mc s0 (dual_sameVertex_symm darts h_mc sm)
    have he : sameVertex H.dual (H.edge.f (spokeRay H refl d0 u 0))
        (H.edge.f (spokeRay H refl d0 u (spokeFanIdx deg cartDeg u p))) darts.length = true := by
      rw [spokeRay_zero_edge]
      have hs0 := sameVertex_spokeDart darts h_mc refl d0 hu.1 hu.2.1
      rw [← cartDart_zero H.dual deg refl d0] at hs0
      exact dual_sameVertex_trans darts h_mc hs0 (dual_sameVertex_trans darts h_mc h (dual_sameVertex_symm darts h_mc hsm))
    have heq := mc_dual_no_parallel darts h_mc h0 he
    unfold spokeRay at heq
    have hcd_raw : nodeDegree H.dual (H.edge.f (spokeDartOriented H.dual refl d0 u)) darts.length = cartDeg u := by
      rw [hcd_eq]; dsimp only [deg]; rw [cartDart_spoke_eq _ _ _ _ hu.1 hu.2.1, dual_edge_f]
    have hinj := perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl
      (H.edge.f (spokeDartOriented H.dual refl d0 u))
      (by rw [hcd_raw]; dsimp only [deg, cartDeg]; omega)
      (by rw [hcd_raw]; dsimp only [deg, cartDeg]; omega)
      heq
    dsimp only [deg, cartDeg] at *
    omega

private theorem spoke_adj_iff {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    {i j : Nat} (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length)
    (hj1 : 1 ≤ j) (hj : j ≤ nodeDegree H.dual d0 darts.length) (hne : i ≠ j) :
    areAdjacentVertices H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 j) darts.length = true ↔
      j = nextDeg (nodeDegree H.dual d0 darts.length) i ∨
        j = prevDeg (nodeDegree H.dual d0 darts.length) i := by
  let deg := nodeDegree H.dual d0 darts.length
  constructor
  · intro hadj
    have h0i := hub_ne_spoke darts h_mc refl d0 hi1 hi
    have hij := spoke_ne_spoke darts h_mc refl d0 hi1 hi hj1 hj hne
    have hj0' : sameVertex H.dual (cartDartOriented H.dual deg refl d0 j) (cartDartOriented H.dual deg refl d0 0) darts.length = false := by
      cases hc : sameVertex H.dual (cartDartOriented H.dual deg refl d0 j) (cartDartOriented H.dual deg refl d0 0) darts.length
      · rfl
      · exfalso
        have hc' := dual_sameVertex_symm darts h_mc hc
        rw [hub_ne_spoke darts h_mc refl d0 hj1 hj] at hc'
        exact Bool.false_ne_true hc'
    have hsi : sameVertex H.dual (spokeDartOriented H.dual refl (cartDartOriented H.dual deg refl d0 0) i)
        (cartDartOriented H.dual deg refl d0 0) darts.length = true := by
      rw [cartDart_zero]; exact sameVertex_spokeDart darts h_mc refl d0 hi1 hi
    have hsj : sameVertex H.dual (spokeDartOriented H.dual refl (cartDartOriented H.dual deg refl d0 0) j)
        (cartDartOriented H.dual deg refl d0 0) darts.length = true := by
      rw [cartDart_zero]; exact sameVertex_spokeDart darts h_mc refl d0 hj1 hj
    have hei : sameVertex H.dual (H.edge.f (spokeDartOriented H.dual refl d0 i))
        (cartDartOriented H.dual deg refl d0 i) darts.length = true := by
      rw [cartDart_spoke_eq _ _ _ _ hi1 hi]; exact sameVertex_refl _ _ _
    have hej : sameVertex H.dual (H.edge.f (spokeDartOriented H.dual refl d0 j))
        (cartDartOriented H.dual deg refl d0 j) darts.length = true := by
      rw [cartDart_spoke_eq _ _ _ _ hj1 hj]; exact sameVertex_refl _ _ _
    have hcon := mc_three_cycle_consecutive darts h_mc refl h0i hij hj0' hsi hei hsj hej hadj
    rcases hcon with hfwd | hinv
    · left
      rw [cartDart_zero] at hfwd
      rw [spokeDart_next darts h_mc refl d0 hi1 hi, spokeDart_eq_iter, spokeDart_eq_iter] at hfwd
      have hn1 := nextDeg_ge_one (deg := deg) (i := i)
      have hn2 := nextDeg_le (deg := nodeDegree H.dual d0 darts.length) (by omega) hi
      have h_j_lt : j - 1 < nodeDegree H.dual d0 darts.length := by omega
      have h_n_lt : nextDeg (nodeDegree H.dual d0 darts.length) i - 1 < nodeDegree H.dual d0 darts.length := by
        dsimp only [deg] at *; omega
      have hinj := perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl d0
        h_n_lt h_j_lt hfwd
      dsimp only [deg] at *
      omega
    · right
      rw [cartDart_zero] at hinv
      rw [spokeDart_prev darts h_mc refl d0 (by omega) hi1 hi, spokeDart_eq_iter, spokeDart_eq_iter] at hinv
      have hp1 := prevDeg_ge_one (deg := deg) (i := i) (by dsimp only [deg]; omega) hi1
      have hp2 := prevDeg_le (deg := nodeDegree H.dual d0 darts.length) hi
      have h_j_lt : j - 1 < nodeDegree H.dual d0 darts.length := by omega
      have h_p_lt : prevDeg (nodeDegree H.dual d0 darts.length) i - 1 < nodeDegree H.dual d0 darts.length := by
        dsimp only [deg] at *; omega
      have hinj := perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl d0
        h_p_lt h_j_lt hinv
      dsimp only [deg] at *
      omega
  · intro hcases
    rcases hcases with rfl | rfl
    · have hcd_ge := mc_dual_nodeDegree_ge_five darts h_mc (cartDartOriented H.dual deg refl d0 i)
      have hp : sameVertex H.dual (spokeRay H refl d0 i (nodeDegree H.dual (cartDartOriented H.dual deg refl d0 i) darts.length - 1))
          (cartDartOriented H.dual deg refl d0 i) darts.length = true :=
        sameVertex_spokeRay darts h_mc refl d0 (nodeDegree H.dual (cartDartOriented H.dual deg refl d0 i) darts.length - 1)
          hi1 hi (by dsimp only [deg] at hcd_ge ⊢; omega)
      have hq : sameVertex H.dual (H.edge.f (spokeRay H refl d0 i (nodeDegree H.dual (cartDartOriented H.dual deg refl d0 i) darts.length - 1)))
          (cartDartOriented H.dual deg refl d0 (nextDeg deg i)) darts.length = true := by
        rw [spokeRay_pred_edge darts h_mc refl d0 (by omega) hi1 hi]
        exact sameVertex_f_self darts h_mc refl _
      exact areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _) hp hq
    · have hcd_ge := mc_dual_nodeDegree_ge_five darts h_mc (cartDartOriented H.dual deg refl d0 i)
      have hp : sameVertex H.dual (spokeRay H refl d0 i 1)
          (cartDartOriented H.dual deg refl d0 i) darts.length = true :=
        sameVertex_spokeRay darts h_mc refl d0 1 hi1 hi (by dsimp only [deg] at hcd_ge ⊢; omega)
      have hq : sameVertex H.dual (H.edge.f (spokeRay H refl d0 i 1))
          (cartDartOriented H.dual deg refl d0 (prevDeg deg i)) darts.length = true := by
        rw [spokeRay_one_edge darts h_mc refl d0 (by omega) hi1 hi]
        exact sameVertex_inv_self darts h_mc refl _
      exact areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _) hp hq

private theorem l2_ne_spoke {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    {u p : Nat} (hu1 : 1 ≤ u) (hu : u ≤ nodeDegree H.dual d0 darts.length)
    (hp : activeL2Pos (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) p) :
    sameVertex H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 u)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p) darts.length = false := by
  let deg := nodeDegree H.dual d0 darts.length
  let cartDeg := cartDegOriented H.dual darts.length deg refl d0
  rcases l2_has_attached_spoke (by omega) hp with ⟨i, hi⟩
  rcases spokeFanIdx_spec darts h_mc refl d0 hdeg5 hi with ⟨hm2, hmcd, hsm, hadj_ip⟩
  cases h : sameVertex H.dual (cartDartOriented H.dual deg refl d0 u) (cartDartOriented H.dual deg refl d0 p) darts.length
  · rfl
  · exfalso
    have hadj_iu : areAdjacentVertices H.dual (cartDartOriented H.dual deg refl d0 i)
        (cartDartOriented H.dual deg refl d0 u) darts.length = true := by
      have hcongr := areAdjacentVertices_congr H.dual darts h_mc.complete (Nat.le_refl _)
        (sameVertex_refl H.dual darts.length (cartDartOriented H.dual deg refl d0 i))
        (dual_sameVertex_symm darts h_mc h)
      rw [← hcongr]
      exact hadj_ip
    have hne : i ≠ u := by
      intro heq; subst heq
      exact Bool.false_ne_true ((adj_ne_vertex darts h_mc hadj_iu).symm.trans (sameVertex_refl _ _ _))
    have hnext_or_prev := (spoke_adj_iff darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hu1 hu hne).mp hadj_iu
    let cdi := cartDeg i
    have hcd_eq : cdi = nodeDegree H.dual (cartDartOriented H.dual deg refl d0 i) darts.length := rfl
    have hcd5 : 5 ≤ cdi := by rw [hcd_eq]; exact mc_dual_nodeDegree_ge_five darts h_mc _
    have hcd_raw : nodeDegree H.dual (H.edge.f (spokeDartOriented H.dual refl d0 i)) darts.length = cdi := by
      rw [hcd_eq]; dsimp only [deg]; rw [cartDart_spoke_eq _ _ _ _ hi.1 hi.2.1, dual_edge_f]
    have hm_sp_lt : spokeFanIdx deg cartDeg i p < cdi := by
      dsimp only [cdi, deg, cartDeg] at *; omega
    have contra_ray : ∀ m, m < cdi →
        sameVertex H.dual (H.edge.f (spokeRay H refl d0 i m)) (cartDartOriented H.dual deg refl d0 p) darts.length = true →
        (m = 1 ∨ m = cdi - 1) → False := by
      intro m hm hmp hcase
      have hsame : sameVertex H.dual (spokeRay H refl d0 i m)
          (spokeRay H refl d0 i (spokeFanIdx deg cartDeg i p)) darts.length = true :=
        dual_sameVertex_trans darts h_mc
          (sameVertex_spokeRay darts h_mc refl d0 m hi.1 hi.2.1 (by dsimp only [deg] at hcd_eq ⊢; rw [← hcd_eq]; exact hm))
          (dual_sameVertex_symm darts h_mc
            (sameVertex_spokeRay darts h_mc refl d0 (spokeFanIdx deg cartDeg i p) hi.1 hi.2.1 (by dsimp only [deg] at hcd_eq ⊢; rw [← hcd_eq]; exact hm_sp_lt)))
      have he : sameVertex H.dual (H.edge.f (spokeRay H refl d0 i m))
          (H.edge.f (spokeRay H refl d0 i (spokeFanIdx deg cartDeg i p))) darts.length = true :=
        dual_sameVertex_trans darts h_mc hmp (dual_sameVertex_symm darts h_mc hsm)
      have heq := mc_dual_no_parallel darts h_mc hsame he
      unfold spokeRay at heq
      have hinj := perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl
        (H.edge.f (spokeDartOriented H.dual refl d0 i))
        (by rw [hcd_raw]; exact hm)
        (by rw [hcd_raw]; exact hm_sp_lt)
        heq
      dsimp only [cdi, deg, cartDeg] at *
      omega
    rcases hnext_or_prev with rfl | rfl
    · apply contra_ray (cdi - 1) (by omega) _ (Or.inr rfl)
      have hed : sameVertex H.dual (H.edge.f (spokeRay H refl d0 i (cdi - 1)))
          (cartDartOriented H.dual deg refl d0 (nextDeg deg i)) darts.length = true := by
        rw [hcd_eq, spokeRay_pred_edge darts h_mc refl d0 (by omega) hi.1 hi.2.1]
        exact sameVertex_f_self darts h_mc refl _
      exact dual_sameVertex_trans darts h_mc hed h
    · apply contra_ray 1 (by omega) _ (Or.inl rfl)
      have hed : sameVertex H.dual (H.edge.f (spokeRay H refl d0 i 1))
          (cartDartOriented H.dual deg refl d0 (prevDeg deg i)) darts.length = true := by
        rw [spokeRay_one_edge darts h_mc refl d0 (by omega) hi.1 hi.2.1]
        exact sameVertex_inv_self darts h_mc refl _
      exact dual_sameVertex_trans darts h_mc hed h

private theorem hub_not_adj_l2 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    {p : Nat} (hp : activeL2Pos (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) p) :
    areAdjacentVertices H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 0)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p) darts.length = false := by
  cases h : areAdjacentVertices H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 0)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p) darts.length
  · rfl
  · exfalso
    rw [cartDart_zero] at h
    rcases dual_neighbor_of_hub darts h_mc refl d0 _ h with ⟨u, hu1, hu, hsame⟩
    have hne := l2_ne_spoke darts h_mc refl d0 hdeg5 hu1 hu hp
    have hsame' := dual_sameVertex_symm darts h_mc hsame
    rw [hne] at hsame'
    exact Bool.false_ne_true hsame'

private theorem hub_adj_spoke {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi : i ≤ nodeDegree H.dual d0 darts.length) :
    areAdjacentVertices H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 0)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 i) darts.length = true := by
  rw [cartDart_zero, cartDart_spoke_eq _ _ _ _ hi1 hi]
  exact areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _)
    (sameVertex_spokeDart darts h_mc refl d0 hi1 hi)
    (sameVertex_refl H.dual darts.length _)

private theorem spoke_adj_l2_iff {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    {u p : Nat} (hu1 : 1 ≤ u) (hu : u ≤ nodeDegree H.dual d0 darts.length)
    (hp : activeL2Pos (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) p)
    (hadj : areAdjacentVertices H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 u)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p) darts.length = true) :
    isAttachedSpoke (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) u p := by
  let deg := nodeDegree H.dual d0 darts.length
  let cartDeg := cartDegOriented H.dual darts.length deg refl d0
  let c := fun k => cartDartOriented H.dual deg refl d0 k
  have adj_symm : ∀ a b, areAdjacentVertices H.dual a b darts.length = true →
      areAdjacentVertices H.dual b a darts.length = true := fun a b hab => by
    rw [areAdjacentVertices_symm H.dual darts h_mc.complete (Nat.le_refl _) a b] at hab
    exact hab
  have ne_symm : ∀ a b, sameVertex H.dual a b darts.length = false →
      sameVertex H.dual b a darts.length = false := fun a b hab => by
    cases hc : sameVertex H.dual b a darts.length
    · rfl
    · exfalso; have := dual_sameVertex_symm darts h_mc hc; rw [hab] at this; exact Bool.false_ne_true this
  rcases hp with ⟨hp1, hp2⟩ | ⟨i, r, hi1, hi, hr, rfl, hrc, hc8⟩
  · let a := p - deg
    have ha1 : 1 ≤ a := by omega
    have ha : a ≤ deg := by omega
    have hp_a : p = deg + a := by omega
    by_cases hau : u = a ∨ u = nextDeg deg a
    · rcases hau with rfl | rfl
      · exact ⟨hu1, hu, Or.inl hp_a⟩
      · exact ⟨hu1, hu, Or.inr (Or.inl (by rw [hp_a, prevDeg_nextDeg ha1 ha]))⟩
    · exfalso
      have hna1 : 1 ≤ nextDeg deg a := nextDeg_ge_one
      have hna : nextDeg deg a ≤ deg := nextDeg_le (by omega) ha
      have ha_att : isAttachedSpoke deg cartDeg a p := ⟨ha1, ha, Or.inl hp_a⟩
      have hna_att : isAttachedSpoke deg cartDeg (nextDeg deg a) p :=
        ⟨hna1, hna, Or.inr (Or.inl (by rw [hp_a, prevDeg_nextDeg ha1 ha]))⟩
      have hadj_ap := (spokeFanIdx_spec darts h_mc refl d0 hdeg5 ha_att).2.2.2
      have hadj_nap := (spokeFanIdx_spec darts h_mc refl d0 hdeg5 hna_att).2.2.2
      have hadj_au : areAdjacentVertices H.dual (c a) (c u) darts.length = true := by
        have hdiag := mc_four_cycle_diag_of_adj darts h_mc
          (hub_ne_spoke darts h_mc refl d0 ha1 ha)
          (l2_ne_hub darts h_mc refl d0 hdeg5 (Or.inl ⟨hp1, hp2⟩))
          (hub_ne_spoke darts h_mc refl d0 hu1 hu)
          (l2_ne_spoke darts h_mc refl d0 hdeg5 ha1 ha (Or.inl ⟨hp1, hp2⟩))
          (spoke_ne_spoke darts h_mc refl d0 ha1 ha hu1 hu (fun heq => hau (Or.inl heq.symm)))
          (ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hu1 hu (Or.inl ⟨hp1, hp2⟩)))
          (hub_adj_spoke darts h_mc refl d0 ha1 ha)
          hadj_ap
          (adj_symm _ _ hadj)
          (adj_symm _ _ (hub_adj_spoke darts h_mc refl d0 hu1 hu))
        rcases hdiag with h0p | hau'
        · rw [hub_not_adj_l2 darts h_mc refl d0 hdeg5 (Or.inl ⟨hp1, hp2⟩)] at h0p
          exact False.elim (Bool.false_ne_true h0p)
        · exact hau'
      have hadj_nau : areAdjacentVertices H.dual (c (nextDeg deg a)) (c u) darts.length = true := by
        have hdiag := mc_four_cycle_diag_of_adj darts h_mc
          (hub_ne_spoke darts h_mc refl d0 hna1 hna)
          (l2_ne_hub darts h_mc refl d0 hdeg5 (Or.inl ⟨hp1, hp2⟩))
          (hub_ne_spoke darts h_mc refl d0 hu1 hu)
          (l2_ne_spoke darts h_mc refl d0 hdeg5 hna1 hna (Or.inl ⟨hp1, hp2⟩))
          (spoke_ne_spoke darts h_mc refl d0 hna1 hna hu1 hu (fun heq => hau (Or.inr heq.symm)))
          (ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hu1 hu (Or.inl ⟨hp1, hp2⟩)))
          (hub_adj_spoke darts h_mc refl d0 hna1 hna)
          hadj_nap
          (adj_symm _ _ hadj)
          (adj_symm _ _ (hub_adj_spoke darts h_mc refl d0 hu1 hu))
        rcases hdiag with h0p | hnau'
        · rw [hub_not_adj_l2 darts h_mc refl d0 hdeg5 (Or.inl ⟨hp1, hp2⟩)] at h0p
          exact False.elim (Bool.false_ne_true h0p)
        · exact hnau'
      have hu_cases := (spoke_adj_iff darts h_mc refl d0 hdeg5 ha1 ha hu1 hu
        (fun heq => hau (Or.inl heq.symm))).mp hadj_au
      have hu_prev : u = prevDeg deg a := by
        rcases hu_cases with hnext | hprev
        · exact False.elim (hau (Or.inr hnext))
        · exact hprev
      have hna_cases := (spoke_adj_iff darts h_mc refl d0 hdeg5 hna1 hna hu1 hu
        (fun heq => hau (Or.inr heq.symm))).mp hadj_nau
      rw [hu_prev] at hna_cases
      rcases hna_cases with hnn | hnp
      · exact nextDeg_nextDeg_ne_prevDeg hdeg5 ha1 ha hnn.symm
      · rw [prevDeg_nextDeg ha1 ha] at hnp
        exact prevDeg_ne_self (by omega) ha1 hnp
  · by_cases hui : u = i
    · subst hui
      exact ⟨hu1, hu, Or.inr (Or.inr ⟨r, hr, rfl, hrc, hc8⟩)⟩
    · exfalso
      have hp_act : activeL2Pos deg cartDeg (r * deg + i) :=
        Or.inr ⟨i, r, hi1, hi, hr, rfl, hrc, hc8⟩
      have hi_att : isAttachedSpoke deg cartDeg i (r * deg + i) :=
        ⟨hi1, hi, Or.inr (Or.inr ⟨r, hr, rfl, hrc, hc8⟩)⟩
      have hadj_ip := (spokeFanIdx_spec darts h_mc refl d0 hdeg5 hi_att).2.2.2
      have hdiag := mc_four_cycle_diag_of_adj darts h_mc
        (hub_ne_spoke darts h_mc refl d0 hi1 hi)
        (l2_ne_hub darts h_mc refl d0 hdeg5 hp_act)
        (hub_ne_spoke darts h_mc refl d0 hu1 hu)
        (l2_ne_spoke darts h_mc refl d0 hdeg5 hi1 hi hp_act)
        (spoke_ne_spoke darts h_mc refl d0 hi1 hi hu1 hu (fun heq => hui heq.symm))
        (ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hu1 hu hp_act))
        (hub_adj_spoke darts h_mc refl d0 hi1 hi)
        hadj_ip
        (adj_symm _ _ hadj)
        (adj_symm _ _ (hub_adj_spoke darts h_mc refl d0 hu1 hu))
      have hadj_iu : areAdjacentVertices H.dual (c i) (c u) darts.length = true := by
        rcases hdiag with h0p | hiu
        · rw [hub_not_adj_l2 darts h_mc refl d0 hdeg5 hp_act] at h0p
          exact False.elim (Bool.false_ne_true h0p)
        · exact hiu
      have hu_cases := (spoke_adj_iff darts h_mc refl d0 hdeg5 hi1 hi hu1 hu (fun heq => hui heq.symm)).mp hadj_iu
      let cdi := cartDeg i
      have hcd_eq : cdi = nodeDegree H.dual (c i) darts.length := rfl
      have hcd5 : 5 ≤ cdi := by rw [hcd_eq]; exact mc_dual_nodeDegree_ge_five darts h_mc _
      have hcd_raw : nodeDegree H.dual (H.edge.f (spokeDartOriented H.dual refl d0 i)) darts.length = cdi := by
        rw [hcd_eq]; dsimp only [c, deg]; rw [cartDart_spoke_eq _ _ _ _ hi1 hi, dual_edge_f]
      let m_u := if u = prevDeg deg i then 1 else cdi - 1
      have hmu_lt : m_u < cdi := by
        dsimp [m_u]; split <;> omega
      have hmu_same : sameVertex H.dual (H.edge.f (spokeRay H refl d0 i m_u)) (c u) darts.length = true := by
        rcases hu_cases with rfl | rfl
        · have hne_pn : nextDeg deg i ≠ prevDeg deg i := by
            unfold nextDeg prevDeg
            repeat' split
            all_goals (dsimp only [deg] at *; omega)
          have hm_eq : m_u = cdi - 1 := by dsimp [m_u]; rw [if_neg hne_pn]
          rw [hm_eq, hcd_eq, spokeRay_pred_edge darts h_mc refl d0 (by omega) hi1 hi]
          exact sameVertex_f_self darts h_mc refl _
        · have hm_eq : m_u = 1 := by dsimp [m_u]; rw [if_pos rfl]
          rw [hm_eq, spokeRay_one_edge darts h_mc refl d0 (by omega) hi1 hi]
          exact sameVertex_inv_self darts h_mc refl _
      have hcd_ge_r : r + 4 ≤ cdi := hrc
      have hcon := mc_three_cycle_consecutive darts h_mc refl
        (l2_ne_spoke darts h_mc refl d0 hdeg5 hi1 hi hp_act)
        (ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hu1 hu hp_act))
        (ne_symm _ _ (spoke_ne_spoke darts h_mc refl d0 hi1 hi hu1 hu (fun heq => hui heq.symm)))
        (sameVertex_spokeRay darts h_mc refl d0 (r + 1) hi1 hi
          (by rw [← hcd_eq]; dsimp only [cdi, deg, cartDeg] at *; omega))
        (by rw [spokeRay_fan_edge H deg refl d0 hr hi1 hi]; exact sameVertex_refl _ _ _)
        (sameVertex_spokeRay darts h_mc refl d0 m_u hi1 hi (by rw [← hcd_eq]; exact hmu_lt))
        hmu_same
        (adj_symm _ _ hadj)
      have hcon' : r + 2 = m_u ∨ r = m_u := by
        rcases hcon with hfwd | hinv
        · left
          unfold spokeRay at hfwd
          rw [iter_succ_eq] at hfwd
          exact perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl
            (H.edge.f (spokeDartOriented H.dual refl d0 i))
            (by rw [hcd_raw]; dsimp only [cdi, deg, cartDeg] at *; omega)
            (by rw [hcd_raw]; exact hmu_lt)
            hfwd
        · right
          have hf : spokeRay H refl d0 i (r + 1) =
              (nodePermOriented H.dual refl).f (spokeRay H refl d0 i r) := by
            unfold spokeRay
            rw [iter_succ_eq]
          rw [hf, (nodePermOriented H.dual refl).left_inv] at hinv
          unfold spokeRay at hinv
          exact perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl
            (H.edge.f (spokeDartOriented H.dual refl d0 i))
            (by rw [hcd_raw]; dsimp only [cdi, deg, cartDeg] at *; omega)
            (by rw [hcd_raw]; exact hmu_lt)
            hinv
      dsimp [m_u] at hcon'
      split at hcon' <;> rcases hr with rfl | rfl | rfl <;> omega

private theorem ite_ne_63 {r s : Nat} (hs : s ≠ 63) :
    (if (r != 63) = true then r else s) ≠ 63 := by
  by_cases h : r = 63 <;> simp [h, hs]

private theorem ite_ne_63_left {a b : Nat} (ha : a ≠ 63) :
    (if (a != 63) = true then a else b) ≠ 63 := by
  simp [ha]

private theorem pureTriAdj_edge {x y z p q : Nat} (hx : x < 63) (hy : y < 63) (hz : z < 63)
    (hp : p = x ∨ p = y ∨ p = z) (hq : q = x ∨ q = y ∨ q = z) (hne : p ≠ q) :
    pureTriAdj x y z p q ≠ 63 ∨ pureTriAdj x y z q p ≠ 63 := by
  unfold pureTriAdj
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact False.elim (hne rfl)
  · left; simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]; omega
  · right; simp only [beq_iff_eq, Bool.and_eq_true]
    split
    · omega
    · split
      · omega
      · split
        · omega
        · exfalso; simp_all
  · right; simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]; omega
  · exact False.elim (hne rfl)
  · left; simp only [beq_iff_eq, Bool.and_eq_true]
    split
    · omega
    · split
      · omega
      · exfalso; simp_all
  · left; simp only [beq_iff_eq, Bool.and_eq_true]
    split
    · omega
    · split
      · omega
      · split
        · omega
        · exfalso; simp_all
  · right; simp only [beq_iff_eq, Bool.and_eq_true]
    split
    · omega
    · split
      · omega
      · exfalso; simp_all
  · exact False.elim (hne rfl)

private theorem pureSpokeAdj_of_tri1 {deg cdi i p q : Nat} (hdeg11 : deg ≤ 11) (_hi1 : 1 ≤ i) (hi : i ≤ deg)
    (hp : p = 0 ∨ p = prevDeg deg i ∨ p = i)
    (hq : q = 0 ∨ q = prevDeg deg i ∨ q = i) (hne : p ≠ q) :
    pureSpokeAdj deg i cdi p q ≠ 63 ∨ pureSpokeAdj deg i cdi q p ≠ 63 := by
  have hpre_le := prevDeg_le hi
  have hedge := pureTriAdj_edge (x := 0) (y := prevDeg deg i) (z := i)
    (by omega) (by omega) (by omega) hp hq hne
  unfold pureSpokeAdj
  have heq : (if (i == 1) = true then deg else i - 1) = prevDeg deg i := by
    unfold prevDeg; simp only [beq_iff_eq]
  rcases hedge with h1 | h2
  · left; dsimp only; rw [heq]; exact ite_ne_63_left h1
  · right; dsimp only; rw [heq]; exact ite_ne_63_left h2

private theorem pureSpokeAdj_of_tri2 {deg cdi i p q : Nat} (hdeg11 : deg ≤ 11) (_hi1 : 1 ≤ i) (hi : i ≤ deg)
    (hp : p = i ∨ p = prevDeg deg i ∨ p = deg + prevDeg deg i)
    (hq : q = i ∨ q = prevDeg deg i ∨ q = deg + prevDeg deg i) (hne : p ≠ q) :
    pureSpokeAdj deg i cdi p q ≠ 63 ∨ pureSpokeAdj deg i cdi q p ≠ 63 := by
  have hpre_le := prevDeg_le hi
  have hedge := pureTriAdj_edge (x := i) (y := prevDeg deg i) (z := deg + prevDeg deg i)
    (by omega) (by omega) (by omega) hp hq hne
  unfold pureSpokeAdj
  have heq : (if (i == 1) = true then deg else i - 1) = prevDeg deg i := by
    unfold prevDeg; simp only [beq_iff_eq]
  rcases hedge with h1 | h2
  · left; dsimp only; rw [heq]; exact ite_ne_63 (ite_ne_63_left h1)
  · right; dsimp only; rw [heq]; exact ite_ne_63 (ite_ne_63_left h2)

private theorem pureSpokeAdj_of_fanTri {deg cdi i p q : Nat}
    (hdeg11 : deg ≤ 11) (_hi1 : 1 ≤ i) (hi : i ≤ deg) (_hcd5 : 5 ≤ cdi) (_hcd8 : cdi ≤ 8)
    (h1 : p ≠ q)
    (htri :
      (cdi = 5 ∧ (p = i ∨ p = deg + prevDeg deg i ∨ p = deg + i) ∧
                 (q = i ∨ q = deg + prevDeg deg i ∨ q = deg + i)) ∨
      (cdi = 6 ∧ (((p = i ∨ p = deg + prevDeg deg i ∨ p = 2 * deg + i) ∧
                   (q = i ∨ q = deg + prevDeg deg i ∨ q = 2 * deg + i)) ∨
                  ((p = i ∨ p = 2 * deg + i ∨ p = deg + i) ∧
                   (q = i ∨ q = 2 * deg + i ∨ q = deg + i)))) ∨
      (cdi = 7 ∧ (((p = i ∨ p = deg + prevDeg deg i ∨ p = 2 * deg + i) ∧
                   (q = i ∨ q = deg + prevDeg deg i ∨ q = 2 * deg + i)) ∨
                  ((p = i ∨ p = 2 * deg + i ∨ p = 3 * deg + i) ∧
                   (q = i ∨ q = 2 * deg + i ∨ q = 3 * deg + i)) ∨
                  ((p = i ∨ p = 3 * deg + i ∨ p = deg + i) ∧
                   (q = i ∨ q = 3 * deg + i ∨ q = deg + i)))) ∨
      (cdi = 8 ∧ (((p = i ∨ p = deg + prevDeg deg i ∨ p = 2 * deg + i) ∧
                   (q = i ∨ q = deg + prevDeg deg i ∨ q = 2 * deg + i)) ∨
                  ((p = i ∨ p = 2 * deg + i ∨ p = 3 * deg + i) ∧
                   (q = i ∨ q = 2 * deg + i ∨ q = 3 * deg + i)) ∨
                  ((p = i ∨ p = 3 * deg + i ∨ p = 4 * deg + i) ∧
                   (q = i ∨ q = 3 * deg + i ∨ q = 4 * deg + i)) ∨
                  ((p = i ∨ p = 4 * deg + i ∨ p = deg + i) ∧
                   (q = i ∨ q = 4 * deg + i ∨ q = deg + i))))) :
    pureSpokeAdj deg i cdi p q ≠ 63 ∨ pureSpokeAdj deg i cdi q p ≠ 63 := by
  have hpre_le := prevDeg_le hi
  have heq : (if (i == 1) = true then deg else i - 1) = prevDeg deg i := by
    unfold prevDeg; simp only [beq_iff_eq]
  rcases htri with ⟨rfl, hp, hq⟩ | ⟨rfl, h6⟩ | ⟨rfl, h7⟩ | ⟨rfl, h8⟩
  · have hedge := pureTriAdj_edge (x := i) (y := deg + prevDeg deg i) (z := deg + i)
      (by omega) (by omega) (by omega) hp hq h1
    rcases hedge with ha | hb
    · left; unfold pureSpokeAdj; dsimp only; rw [heq]
      exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, ↓reduceIte]; exact ha))
    · right; unfold pureSpokeAdj; dsimp only; rw [heq]
      exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, ↓reduceIte]; exact hb))
  · rcases h6 with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have hedge := pureTriAdj_edge (x := i) (y := deg + prevDeg deg i) (z := 2 * deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(6 = 5) by omega, if_true, if_false]; exact ite_ne_63_left ha))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(6 = 5) by omega, if_true, if_false]; exact ite_ne_63_left hb))
    · have hedge := pureTriAdj_edge (x := i) (y := 2 * deg + i) (z := deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(6 = 5) by omega, if_true, if_false]; exact ite_ne_63 ha))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(6 = 5) by omega, if_true, if_false]; exact ite_ne_63 hb))
  · rcases h7 with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have hedge := pureTriAdj_edge (x := i) (y := deg + prevDeg deg i) (z := 2 * deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(7 = 5) by omega, show ¬(7 = 6) by omega, if_true, if_false]; exact ite_ne_63_left ha))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(7 = 5) by omega, show ¬(7 = 6) by omega, if_true, if_false]; exact ite_ne_63_left hb))
    · have hedge := pureTriAdj_edge (x := i) (y := 2 * deg + i) (z := 3 * deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(7 = 5) by omega, show ¬(7 = 6) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63_left ha)))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(7 = 5) by omega, show ¬(7 = 6) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63_left hb)))
    · have hedge := pureTriAdj_edge (x := i) (y := 3 * deg + i) (z := deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(7 = 5) by omega, show ¬(7 = 6) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63 ha)))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(7 = 5) by omega, show ¬(7 = 6) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63 hb)))
  · rcases h8 with ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have hedge := pureTriAdj_edge (x := i) (y := deg + prevDeg deg i) (z := 2 * deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(8 = 5) by omega, show ¬(8 = 6) by omega, show ¬(8 = 7) by omega, if_true, if_false]; exact ite_ne_63_left ha))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(8 = 5) by omega, show ¬(8 = 6) by omega, show ¬(8 = 7) by omega, if_true, if_false]; exact ite_ne_63_left hb))
    · have hedge := pureTriAdj_edge (x := i) (y := 2 * deg + i) (z := 3 * deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(8 = 5) by omega, show ¬(8 = 6) by omega, show ¬(8 = 7) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63_left ha)))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(8 = 5) by omega, show ¬(8 = 6) by omega, show ¬(8 = 7) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63_left hb)))
    · have hedge := pureTriAdj_edge (x := i) (y := 3 * deg + i) (z := 4 * deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(8 = 5) by omega, show ¬(8 = 6) by omega, show ¬(8 = 7) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63 (ite_ne_63_left ha))))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(8 = 5) by omega, show ¬(8 = 6) by omega, show ¬(8 = 7) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63 (ite_ne_63_left hb))))
    · have hedge := pureTriAdj_edge (x := i) (y := 4 * deg + i) (z := deg + i)
        (by omega) (by omega) (by omega) hp hq h1
      rcases hedge with ha | hb
      · left; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(8 = 5) by omega, show ¬(8 = 6) by omega, show ¬(8 = 7) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63 (ite_ne_63 ha))))
      · right; unfold pureSpokeAdj; dsimp only; rw [heq]
        exact ite_ne_63 (ite_ne_63 (by simp only [beq_iff_eq, show ¬(8 = 5) by omega, show ¬(8 = 6) by omega, show ¬(8 = 7) by omega, if_true, if_false]; exact ite_ne_63 (ite_ne_63 (ite_ne_63 hb))))

private theorem pureSpokeAdj_of_sameSpoke_consecutive {deg cdi i p q : Nat}
    (hdeg5 : 5 ≤ deg) (hdeg11 : deg ≤ 11) (hi1 : 1 ≤ i) (hi : i ≤ deg) (hcd5 : 5 ≤ cdi)
    (hp : p = deg + i ∨ p = deg + prevDeg deg i ∨ ∃ r, (r = 2 ∨ r = 3 ∨ r = 4) ∧ p = r * deg + i ∧ r + 4 ≤ cdi ∧ cdi ≤ 8)
    (hq : q = deg + i ∨ q = deg + prevDeg deg i ∨ ∃ r, (r = 2 ∨ r = 3 ∨ r = 4) ∧ q = r * deg + i ∧ r + 4 ≤ cdi ∧ cdi ≤ 8)
    (hpq : p ≠ q)
    (hm_adj : ∀ mp mq,
      (p = deg + prevDeg deg i → mp = 2) →
      (p = deg + i → mp = cdi - 2) →
      (∀ r, p = r * deg + i → (r = 2 ∨ r = 3 ∨ r = 4) → mp = r + 1) →
      (q = deg + prevDeg deg i → mq = 2) →
      (q = deg + i → mq = cdi - 2) →
      (∀ r, q = r * deg + i → (r = 2 ∨ r = 3 ∨ r = 4) → mq = r + 1) →
      mp = mq + 1 ∨ mq = mp + 1) :
    pureSpokeAdj deg i cdi p q ≠ 63 ∨ pureSpokeAdj deg i cdi q p ≠ 63 := by
  have hpre_ge := prevDeg_ge_one (deg := deg) (i := i) (by omega) hi1
  have hpre_le := prevDeg_le hi
  have hpre_ne : prevDeg deg i ≠ i := prevDeg_ne_self (by omega) hi1
  have getM : ∀ x, (x = deg + i ∨ x = deg + prevDeg deg i ∨ ∃ r, (r = 2 ∨ r = 3 ∨ r = 4) ∧ x = r * deg + i ∧ r + 4 ≤ cdi ∧ cdi ≤ 8) →
      ∃ mx, (x = deg + prevDeg deg i → mx = 2) ∧
            (x = deg + i → mx = cdi - 2) ∧
            (∀ r, x = r * deg + i → (r = 2 ∨ r = 3 ∨ r = 4) → mx = r + 1) := by
    intro x hx
    rcases hx with rfl | rfl | ⟨r, hr, rfl, _, _⟩
    · exact ⟨cdi - 2, fun h => by omega, fun _ => rfl, fun r heq hr => by rcases hr with rfl | rfl | rfl <;> omega⟩
    · exact ⟨2, fun _ => rfl, fun h => by omega, fun r heq hr => by rcases hr with rfl | rfl | rfl <;> omega⟩
    · exact ⟨r + 1, fun h => by rcases hr with rfl | rfl | rfl <;> omega,
        fun h => by rcases hr with rfl | rfl | rfl <;> omega,
        fun r' heq hr' => by
          have : r = r' := by rcases hr with rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl <;> omega
          subst this; rfl⟩
  rcases getM p hp with ⟨mp, hmp1, hmp2, hmp3⟩
  rcases getM q hq with ⟨mq, hmq1, hmq2, hmq3⟩
  have hdiff := hm_adj mp mq hmp1 hmp2 hmp3 hmq1 hmq2 hmq3
  rcases hp with rfl | rfl | ⟨rp, hrp, rfl, hrcp, hc8p⟩ <;>
  rcases hq with hq1 | hq2 | ⟨rq, hrq, hq3, hrcq, hc8q⟩
  · exact False.elim (hpq hq1.symm)
  · subst hq2
    have emp := hmp2 rfl; have emq := hmq1 rfl
    have hcd5' : cdi = 5 := by omega
    subst hcd5'
    exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
      (Or.inl ⟨rfl, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩)
  · subst hq3
    have emp := hmp2 rfl; have emq := hmq3 rq rfl hrq
    have hcd_le : cdi ≤ 8 := hc8q
    rcases hrq with rfl | rfl | rfl
    · have hcd6 : cdi = 6 := by omega
      subst hcd6
      exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inl ⟨rfl, Or.inr ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩⟩))
    · have hcd7 : cdi = 7 := by omega
      subst hcd7
      exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩)⟩)))
    · have hcd8 : cdi = 8 := by omega
      subst hcd8
      exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩))⟩)))
  · subst hq1
    have emp := hmp1 rfl; have emq := hmq2 rfl
    have hcd5' : cdi = 5 := by omega
    subst hcd5'
    exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
      (Or.inl ⟨rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩)
  · exact False.elim (hpq hq2.symm)
  · subst hq3
    have emp := hmp1 rfl; have emq := hmq3 rq rfl hrq
    have hrq2 : rq = 2 := by rcases hrq with rfl | rfl | rfl <;> omega
    subst hrq2
    rcases (by omega : cdi = 6 ∨ cdi = 7 ∨ cdi = 8) with rfl | rfl | rfl
    · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inl ⟨rfl, Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩⟩))
    · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩⟩)))
    · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩⟩)))
  · subst hq1
    have emp := hmp3 rp rfl hrp; have emq := hmq2 rfl
    rcases hrp with rfl | rfl | rfl
    · have hcd6 : cdi = 6 := by omega
      subst hcd6
      exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inl ⟨rfl, Or.inr ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩⟩))
    · have hcd7 : cdi = 7 := by omega
      subst hcd7
      exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩)⟩)))
    · have hcd8 : cdi = 8 := by omega
      subst hcd8
      exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩))⟩)))
  · subst hq2
    have emp := hmp3 rp rfl hrp; have emq := hmq1 rfl
    have hrp2 : rp = 2 := by rcases hrp with rfl | rfl | rfl <;> omega
    subst hrp2
    rcases (by omega : cdi = 6 ∨ cdi = 7 ∨ cdi = 8) with rfl | rfl | rfl
    · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inl ⟨rfl, Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩⟩))
    · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩⟩)))
    · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩⟩)))
  · subst hq3
    have emp := hmp3 rp rfl hrp; have emq := hmq3 rq rfl hrq
    rcases hrp with rfl | rfl | rfl <;> rcases hrq with rfl | rfl | rfl <;> try omega
    · rcases (by omega : cdi = 7 ∨ cdi = 8) with rfl | rfl
      · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
          (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩)⟩)))
      · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
          (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩)⟩)))
    · rcases (by omega : cdi = 7 ∨ cdi = 8) with rfl | rfl
      · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
          (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩)⟩)))
      · exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
          (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩)⟩)))
    · have hcd8 : cdi = 8 := by omega
      subst hcd8
      exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩))⟩)))
    · have hcd8 : cdi = 8 := by omega
      subst hcd8
      exact pureSpokeAdj_of_fanTri hdeg11 hi1 hi (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩))⟩)))

private theorem l2_same_spoke_ne_and_adj {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart)
    (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    (hdeg11 : nodeDegree H.dual d0 darts.length ≤ 11)
    {u p q : Nat}
    (hp : isAttachedSpoke (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) u p)
    (hq : isAttachedSpoke (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) u q)
    (hpq : p ≠ q) :
    sameVertex H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 q) darts.length = false ∧
    (areAdjacentVertices H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 q) darts.length = true →
      pureSpokeAdj (nodeDegree H.dual d0 darts.length) u
        (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0 u) p q ≠ 63 ∨
      pureSpokeAdj (nodeDegree H.dual d0 darts.length) u
        (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0 u) q p ≠ 63) := by
  let deg := nodeDegree H.dual d0 darts.length
  let cartDeg := cartDegOriented H.dual darts.length deg refl d0
  let c := fun k => cartDartOriented H.dual deg refl d0 k
  have hu1 := hp.1
  have hu := hp.2.1
  have hcd_eq : cartDeg u = nodeDegree H.dual (c u) darts.length := rfl
  have hcd5 : 5 ≤ cartDeg u := by rw [hcd_eq]; exact mc_dual_nodeDegree_ge_five darts h_mc _
  have hcd_raw : nodeDegree H.dual (H.edge.f (spokeDartOriented H.dual refl d0 u)) darts.length = cartDeg u := by
    rw [hcd_eq]; dsimp only [c, deg]; rw [cartDart_spoke_eq _ _ _ _ hu1 hu, dual_edge_f]
  rcases spokeFanIdx_spec darts h_mc refl d0 hdeg5 hp with ⟨hmp2, hmp_le, hsmp, _⟩
  rcases spokeFanIdx_spec darts h_mc refl d0 hdeg5 hq with ⟨hmq2, hmq_le, hsmq, _⟩
  have hm_ne := spokeFanIdx_inj hdeg5 hp hq hpq hcd5
  have hmp_lt : spokeFanIdx deg cartDeg u p < nodeDegree H.dual (c u) darts.length := by
    dsimp only [deg, cartDeg] at hcd_eq ⊢; rw [← hcd_eq]; omega
  have hmq_lt : spokeFanIdx deg cartDeg u q < nodeDegree H.dual (c u) darts.length := by
    dsimp only [deg, cartDeg] at hcd_eq ⊢; rw [← hcd_eq]; omega
  have hmp_raw : spokeFanIdx deg cartDeg u p < nodeDegree H.dual (H.edge.f (spokeDartOriented H.dual refl d0 u)) darts.length := by
    rw [hcd_raw]; dsimp only [deg, cartDeg]; omega
  have hmq_raw : spokeFanIdx deg cartDeg u q < nodeDegree H.dual (H.edge.f (spokeDartOriented H.dual refl d0 u)) darts.length := by
    rw [hcd_raw]; dsimp only [deg, cartDeg]; omega
  have hne_pq : sameVertex H.dual (c p) (c q) darts.length = false := by
    cases h : sameVertex H.dual (c p) (c q) darts.length
    · rfl
    · exfalso
      have hs := dual_sameVertex_trans darts h_mc
        (sameVertex_spokeRay darts h_mc refl d0 (spokeFanIdx deg cartDeg u p) hu1 hu hmp_lt)
        (dual_sameVertex_symm darts h_mc (sameVertex_spokeRay darts h_mc refl d0 (spokeFanIdx deg cartDeg u q) hu1 hu hmq_lt))
      have he := dual_sameVertex_trans darts h_mc hsmp
        (dual_sameVertex_trans darts h_mc h (dual_sameVertex_symm darts h_mc hsmq))
      have heq := mc_dual_no_parallel darts h_mc hs he
      unfold spokeRay at heq
      exact hm_ne (perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl
        (H.edge.f (spokeDartOriented H.dual refl d0 u)) hmp_raw hmq_raw heq)
  refine ⟨hne_pq, fun hadj => ?_⟩
  have act_of_att : ∀ x, isAttachedSpoke deg cartDeg u x → activeL2Pos deg cartDeg x := by
    intro x hx
    rcases hx.2.2 with rfl | rfl | ⟨r, hr, rfl, hrc, hc8⟩
    · exact Or.inl ⟨by omega, by omega⟩
    · have h1 := prevDeg_ge_one (deg := nodeDegree H.dual d0 darts.length) (by omega) hu1
      have h2 := prevDeg_le (deg := nodeDegree H.dual d0 darts.length) hu
      exact Or.inl ⟨by dsimp only [deg] at *; omega, by dsimp only [deg] at *; omega⟩
    · exact Or.inr ⟨u, r, hu1, hu, hr, rfl, hrc, hc8⟩
  have hne_symm : ∀ a b, sameVertex H.dual a b darts.length = false → sameVertex H.dual b a darts.length = false :=
    fun a b hab => by
      cases hc : sameVertex H.dual b a darts.length
      · rfl
      · exfalso; have := dual_sameVertex_symm darts h_mc hc; rw [hab] at this; exact Bool.false_ne_true this
  have hcon := mc_three_cycle_consecutive darts h_mc refl
    (l2_ne_spoke darts h_mc refl d0 hdeg5 hu1 hu (act_of_att p hp))
    hne_pq
    (hne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hu1 hu (act_of_att q hq)))
    (sameVertex_spokeRay darts h_mc refl d0 (spokeFanIdx deg cartDeg u p) hu1 hu hmp_lt)
    hsmp
    (sameVertex_spokeRay darts h_mc refl d0 (spokeFanIdx deg cartDeg u q) hu1 hu hmq_lt)
    hsmq
    hadj
  have hm_con : spokeFanIdx deg cartDeg u p = spokeFanIdx deg cartDeg u q + 1 ∨
      spokeFanIdx deg cartDeg u q = spokeFanIdx deg cartDeg u p + 1 := by
    rcases hcon with hfwd | hinv
    · right
      unfold spokeRay at hfwd
      rw [iter_succ_eq] at hfwd
      exact (perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl
        (H.edge.f (spokeDartOriented H.dual refl d0 u))
        (by rw [hcd_raw]; dsimp only [deg, cartDeg]; omega) hmq_raw hfwd).symm
    · left
      let mp := spokeFanIdx deg cartDeg u p
      have hmp_ge : 2 ≤ mp := hmp2
      have hmp_lt_cd : mp ≤ cartDeg u - 2 := hmp_le
      have hf : spokeRay H refl d0 u mp =
          (nodePermOriented H.dual refl).f (spokeRay H refl d0 u (mp - 1)) := by
        unfold spokeRay
        rw [iter_succ_eq, show mp - 1 + 1 = mp by omega]
      rw [hf, (nodePermOriented H.dual refl).left_inv] at hinv
      unfold spokeRay at hinv
      have hinj := perm_iter_nodePermOriented_inj_lt_deg H.dual darts h_mc.complete (Nat.le_refl _) refl
        (H.edge.f (spokeDartOriented H.dual refl d0 u))
        (by rw [hcd_raw]; dsimp only [deg, cartDeg] at *; omega) hmq_raw hinv
      omega
  apply pureSpokeAdj_of_sameSpoke_consecutive hdeg5 hdeg11 hu1 hu hcd5 hp.2.2 hq.2.2 hpq
  intro mp mq h1 h2 h3 g1 g2 g3
  have eqp : mp = spokeFanIdx deg cartDeg u p := by
    unfold spokeFanIdx
    by_cases ca : p = deg + prevDeg deg u
    · rw [if_pos ca]; exact h1 ca
    · by_cases cb : p = deg + u
      · rw [if_neg ca, if_pos cb]; exact h2 cb
      · rw [if_neg ca, if_neg cb]
        rcases hp.2.2 with rfl | rfl | ⟨r, hr, rfl, _, _⟩
        · exact False.elim (cb rfl)
        · exact False.elim (ca rfl)
        · rw [(div_mod_spoke deg r u (by omega) hu1 hu).1]; exact h3 r rfl hr
  have eqq : mq = spokeFanIdx deg cartDeg u q := by
    unfold spokeFanIdx
    by_cases ca : q = deg + prevDeg deg u
    · rw [if_pos ca]; exact g1 ca
    · by_cases cb : q = deg + u
      · rw [if_neg ca, if_pos cb]; exact g2 cb
      · rw [if_neg ca, if_neg cb]
        rcases hq.2.2 with rfl | rfl | ⟨r, hr, rfl, _, _⟩
        · exact False.elim (cb rfl)
        · exact False.elim (ca rfl)
        · rw [(div_mod_spoke deg r u (by omega) hu1 hu).1]; exact g3 r rfl hr
  rw [eqp, eqq]
  exact hm_con

private theorem l2_disjoint_spokes_ne_and_not_adj {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart) (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    {p q : Nat}
    (hp : activeL2Pos (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) p)
    (hq : activeL2Pos (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) q)
    (hdisj : ¬∃ u, isAttachedSpoke (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) u p ∧
      isAttachedSpoke (nodeDegree H.dual d0 darts.length)
      (cartDegOriented H.dual darts.length (nodeDegree H.dual d0 darts.length) refl d0) u q) :
    sameVertex H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 q) darts.length = false ∧
    areAdjacentVertices H.dual
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 p)
      (cartDartOriented H.dual (nodeDegree H.dual d0 darts.length) refl d0 q) darts.length = false := by
  let deg := nodeDegree H.dual d0 darts.length
  let cartDeg := cartDegOriented H.dual darts.length deg refl d0
  let c := fun k => cartDartOriented H.dual deg refl d0 k
  rcases l2_has_attached_spoke (by omega) hp with ⟨i, hi⟩
  rcases l2_has_attached_spoke (by omega) hq with ⟨j, hj⟩
  have hij_ne : i ≠ j := by
    intro h; subst h; exact hdisj ⟨i, hi, hj⟩
  have hne_pq : sameVertex H.dual (c p) (c q) darts.length = false := by
    cases h : sameVertex H.dual (c p) (c q) darts.length
    · rfl
    · exfalso
      have hadj_ip := (spokeFanIdx_spec darts h_mc refl d0 hdeg5 hi).2.2.2
      have hcongr := areAdjacentVertices_congr H.dual darts h_mc.complete (Nat.le_refl _)
        (sameVertex_refl H.dual darts.length (c i)) h
      have hadj_iq : areAdjacentVertices H.dual (c i) (c q) darts.length = true := by
        rw [← hcongr]; exact hadj_ip
      exact hdisj ⟨i, hi, spoke_adj_l2_iff darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hq hadj_iq⟩
  refine ⟨hne_pq, ?_⟩
  cases hadj : areAdjacentVertices H.dual (c p) (c q) darts.length
  · rfl
  · exfalso
    have adj_symm : ∀ a b, areAdjacentVertices H.dual a b darts.length = true →
        areAdjacentVertices H.dual b a darts.length = true := fun a b hab => by
      rw [areAdjacentVertices_symm H.dual darts h_mc.complete (Nat.le_refl _) a b] at hab; exact hab
    have ne_symm : ∀ a b, sameVertex H.dual a b darts.length = false →
        sameVertex H.dual b a darts.length = false := fun a b hab => by
      cases hc : sameVertex H.dual b a darts.length
      · rfl
      · exfalso; have := dual_sameVertex_symm darts h_mc hc; rw [hab] at this; exact Bool.false_ne_true this
    have hadj_iq_false : areAdjacentVertices H.dual (c i) (c q) darts.length = false := by
      cases h : areAdjacentVertices H.dual (c i) (c q) darts.length
      · rfl
      · exfalso; exact hdisj ⟨i, hi, spoke_adj_l2_iff darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hq h⟩
    have hadj_jp_false : areAdjacentVertices H.dual (c j) (c p) darts.length = false := by
      cases h : areAdjacentVertices H.dual (c j) (c p) darts.length
      · rfl
      · exfalso; exact hdisj ⟨j, spoke_adj_l2_iff darts h_mc refl d0 hdeg5 hj.1 hj.2.1 hp h, hj⟩
    have hadj_ip := (spokeFanIdx_spec darts h_mc refl d0 hdeg5 hi).2.2.2
    have hadj_jq := (spokeFanIdx_spec darts h_mc refl d0 hdeg5 hj).2.2.2
    cases hij_adj : areAdjacentVertices H.dual (c i) (c j) darts.length
    · -- Case chordless 5-cycle: (c 0, c i, c p, c q, c j)
      let rf : Fin 5 → H.Dart := fun m =>
        match m.val with
        | 0 => c 0
        | 1 => c i
        | 2 => c p
        | 3 => c q
        | _ => c j
      have h_diff : ∀ a b : Fin 5, a ≠ b → sameVertex H.dual (rf a) (rf b) darts.length = false := by
        rintro ⟨av, hav⟩ ⟨bv, hbv⟩ hab
        rcases (by omega : av = 0 ∨ av = 1 ∨ av = 2 ∨ av = 3 ∨ av = 4) with rfl | rfl | rfl | rfl | rfl <;>
        rcases (by omega : bv = 0 ∨ bv = 1 ∨ bv = 2 ∨ bv = 3 ∨ bv = 4) with rfl | rfl | rfl | rfl | rfl <;>
        dsimp [rf]
        · exact False.elim (hab rfl)
        · exact hub_ne_spoke darts h_mc refl d0 hi.1 hi.2.1
        · exact l2_ne_hub darts h_mc refl d0 hdeg5 hp
        · exact l2_ne_hub darts h_mc refl d0 hdeg5 hq
        · exact hub_ne_spoke darts h_mc refl d0 hj.1 hj.2.1
        · exact ne_symm _ _ (hub_ne_spoke darts h_mc refl d0 hi.1 hi.2.1)
        · exact False.elim (hab rfl)
        · exact l2_ne_spoke darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hp
        · exact l2_ne_spoke darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hq
        · exact spoke_ne_spoke darts h_mc refl d0 hi.1 hi.2.1 hj.1 hj.2.1 hij_ne
        · exact ne_symm _ _ (l2_ne_hub darts h_mc refl d0 hdeg5 hp)
        · exact ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hp)
        · exact False.elim (hab rfl)
        · exact hne_pq
        · exact ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hj.1 hj.2.1 hp)
        · exact ne_symm _ _ (l2_ne_hub darts h_mc refl d0 hdeg5 hq)
        · exact ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hq)
        · exact ne_symm _ _ hne_pq
        · exact False.elim (hab rfl)
        · exact ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hj.1 hj.2.1 hq)
        · exact ne_symm _ _ (hub_ne_spoke darts h_mc refl d0 hj.1 hj.2.1)
        · exact ne_symm _ _ (spoke_ne_spoke darts h_mc refl d0 hi.1 hi.2.1 hj.1 hj.2.1 hij_ne)
        · exact l2_ne_spoke darts h_mc refl d0 hdeg5 hj.1 hj.2.1 hp
        · exact l2_ne_spoke darts h_mc refl d0 hdeg5 hj.1 hj.2.1 hq
        · exact False.elim (hab rfl)
      have h_cyc : ∀ a : Fin 5,
          areAdjacentVertices H.dual (rf a) (rf ⟨(a.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) darts.length = true := by
        rintro ⟨av, hav⟩
        rcases (by omega : av = 0 ∨ av = 1 ∨ av = 2 ∨ av = 3 ∨ av = 4) with rfl | rfl | rfl | rfl | rfl <;>
        dsimp [rf]
        · exact hub_adj_spoke darts h_mc refl d0 hi.1 hi.2.1
        · exact hadj_ip
        · exact hadj
        · exact adj_symm _ _ hadj_jq
        · exact adj_symm _ _ (hub_adj_spoke darts h_mc refl d0 hj.1 hj.2.1)
      have hadj_symm_false : ∀ a b, areAdjacentVertices H.dual a b darts.length = false →
          areAdjacentVertices H.dual b a darts.length = false := fun a b hab => by
        rw [areAdjacentVertices_symm H.dual darts h_mc.complete (Nat.le_refl _) b a]; exact hab
      have h_non : ∀ a b : Fin 5, a ≠ b → b.val ≠ (a.val + 1) % 5 → a.val ≠ (b.val + 1) % 5 →
          areAdjacentVertices H.dual (rf a) (rf b) darts.length = false := by
        rintro ⟨av, hav⟩ ⟨bv, hbv⟩ hab h1 h2
        rcases (by omega : av = 0 ∨ av = 1 ∨ av = 2 ∨ av = 3 ∨ av = 4) with rfl | rfl | rfl | rfl | rfl <;>
        rcases (by omega : bv = 0 ∨ bv = 1 ∨ bv = 2 ∨ bv = 3 ∨ bv = 4) with rfl | rfl | rfl | rfl | rfl <;>
        dsimp only [rf] at * <;>
        (try exact False.elim (hab (Fin.ext rfl))) <;>
        (try exact False.elim (h1 (by decide))) <;>
        (try exact False.elim (h2 (by decide)))
        · exact hub_not_adj_l2 darts h_mc refl d0 hdeg5 hp
        · exact hub_not_adj_l2 darts h_mc refl d0 hdeg5 hq
        · exact hadj_iq_false
        · exact hij_adj
        · exact hadj_symm_false _ _ (hub_not_adj_l2 darts h_mc refl d0 hdeg5 hp)
        · exact hadj_symm_false _ _ hadj_jp_false
        · exact hadj_symm_false _ _ (hub_not_adj_l2 darts h_mc refl d0 hdeg5 hq)
        · exact hadj_symm_false _ _ hadj_iq_false
        · exact hadj_symm_false _ _ hij_adj
        · exact hadj_jp_false
      rcases mc_five_cycle_common_neighbor_of_chordless darts h_mc rf h_diff h_cyc h_non with ⟨w, hw⟩
      have hw0' := hw ⟨0, by decide⟩
      dsimp only [rf] at hw0'
      have hw0 : areAdjacentVertices H.dual (c 0) w darts.length = true := adj_symm _ _ hw0'
      rw [show c 0 = d0 from cartDart_zero _ _ _ _] at hw0
      rcases dual_neighbor_of_hub darts h_mc refl d0 w hw0 with ⟨u, hu1, hu, hwu⟩
      have hup : areAdjacentVertices H.dual (c u) (c p) darts.length = true := by
        have hcongr := areAdjacentVertices_congr H.dual darts h_mc.complete (Nat.le_refl _)
          hwu (sameVertex_refl H.dual darts.length (c p))
        rw [← hcongr]
        exact hw ⟨2, by decide⟩
      have huq : areAdjacentVertices H.dual (c u) (c q) darts.length = true := by
        have hcongr := areAdjacentVertices_congr H.dual darts h_mc.complete (Nat.le_refl _)
          hwu (sameVertex_refl H.dual darts.length (c q))
        rw [← hcongr]
        exact hw ⟨3, by decide⟩
      exact hdisj ⟨u, spoke_adj_l2_iff darts h_mc refl d0 hdeg5 hu1 hu hp hup,
                      spoke_adj_l2_iff darts h_mc refl d0 hdeg5 hu1 hu hq huq⟩
    · -- Case 4-cycle: (c i, c p, c q, c j)
      have hdiag := mc_four_cycle_diag_of_adj darts h_mc
        (l2_ne_spoke darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hp)
        (l2_ne_spoke darts h_mc refl d0 hdeg5 hi.1 hi.2.1 hq)
        (spoke_ne_spoke darts h_mc refl d0 hi.1 hi.2.1 hj.1 hj.2.1 hij_ne)
        hne_pq
        (ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hj.1 hj.2.1 hp))
        (ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hj.1 hj.2.1 hq))
        hadj_ip hadj (adj_symm _ _ hadj_jq) (adj_symm _ _ hij_adj)
      rcases hdiag with hiq | hpj
      · rw [hadj_iq_false] at hiq; exact Bool.false_ne_true hiq
      · have := adj_symm _ _ hpj; rw [hadj_jp_false] at this; exact Bool.false_ne_true this

private theorem active_split {deg : Nat} {cartDeg : Nat → Nat} {p : Nat}
    (hp : p = 0 ∨ (1 ≤ p ∧ p ≤ 2 * deg) ∨
      ∃ i r, 1 ≤ i ∧ i ≤ deg ∧ (r = 2 ∨ r = 3 ∨ r = 4) ∧ p = r * deg + i ∧ r + 4 ≤ cartDeg i ∧ cartDeg i ≤ 8) :
    p = 0 ∨ (1 ≤ p ∧ p ≤ deg) ∨ activeL2Pos deg cartDeg p := by
  rcases hp with rfl | ⟨h1, h2⟩ | hfan
  · exact Or.inl rfl
  · by_cases hle : p ≤ deg
    · exact Or.inr (Or.inl ⟨h1, hle⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2⟩))
  · exact Or.inr (Or.inr (Or.inr hfan))

private theorem pureSpokeAdj_of_spoke_and_l2 {deg : Nat} {cartDeg : Nat → Nat}
    (hdeg5 : 5 ≤ deg) (hdeg11 : deg ≤ 11) {p q : Nat}
    (hp1 : 1 ≤ p) (hp2 : p ≤ deg)
    (hatt : isAttachedSpoke deg cartDeg p q) :
    ∃ i, 1 ≤ i ∧ i ≤ deg ∧
      (pureSpokeAdj deg i (cartDeg i) p q ≠ 63 ∨
       pureSpokeAdj deg i (cartDeg i) q p ≠ 63) := by
  have hpre_ge := prevDeg_ge_one (deg := deg) (i := p) (by omega) hp1
  have hpre_le := prevDeg_le hp2
  have hpre_ne : prevDeg deg p ≠ p := prevDeg_ne_self (by omega) hp1
  rcases hatt.2.2 with rfl | rfl | ⟨r, hr, rfl, hrc, hc8⟩
  · let j := nextDeg deg p
    have hj1 : 1 ≤ j := nextDeg_ge_one
    have hj2 : j ≤ deg := nextDeg_le (by omega) hp2
    have hp_eq : p = prevDeg deg j := (prevDeg_nextDeg hp1 hp2).symm
    refine ⟨j, hj1, hj2, ?_⟩
    rw [hp_eq]
    exact pureSpokeAdj_of_tri2 hdeg11 hj1 hj2
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (by rw [← hp_eq]; omega)
  · refine ⟨p, hp1, hp2, ?_⟩
    exact pureSpokeAdj_of_tri2 hdeg11 hp1 hp2
      (Or.inl rfl) (Or.inr (Or.inr rfl)) (by omega)
  · refine ⟨p, hp1, hp2, ?_⟩
    have hpq : p ≠ r * deg + p := by rcases hr with rfl | rfl | rfl <;> omega
    rcases hr with rfl | rfl | rfl
    · rcases (by omega : cartDeg p = 6 ∨ cartDeg p = 7 ∨ cartDeg p = 8) with hcd | hcd | hcd
      · rw [hcd]
        exact pureSpokeAdj_of_fanTri hdeg11 hp1 hp2 (by omega) (by omega) hpq
          (Or.inr (Or.inl ⟨rfl, Or.inl ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩⟩))
      · rw [hcd]
        exact pureSpokeAdj_of_fanTri hdeg11 hp1 hp2 (by omega) (by omega) hpq
          (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩⟩)))
      · rw [hcd]
        exact pureSpokeAdj_of_fanTri hdeg11 hp1 hp2 (by omega) (by omega) hpq
          (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩⟩)))
    · rcases (by omega : cartDeg p = 7 ∨ cartDeg p = 8) with hcd | hcd
      · rw [hcd]
        exact pureSpokeAdj_of_fanTri hdeg11 hp1 hp2 (by omega) (by omega) hpq
          (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩)⟩)))
      · rw [hcd]
        exact pureSpokeAdj_of_fanTri hdeg11 hp1 hp2 (by omega) (by omega) hpq
          (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩)⟩)))
    · have hcd : cartDeg p = 8 := by omega
      rw [hcd]
      exact pureSpokeAdj_of_fanTri hdeg11 hp1 hp2 (by omega) (by omega) hpq
        (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩))⟩)))

end CartwheelProofHelpers

theorem mc_cartwheelEmbedded_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (refl : Bool) (d0 : H.Dart)
    (hdeg5 : 5 ≤ nodeDegree H.dual d0 darts.length)
    (hdeg11 : nodeDegree H.dual d0 darts.length ≤ 11) :
    CartwheelEmbedded H.dual darts.length refl d0 := by
  unfold CartwheelEmbedded activeCartPos Math.Unavoidability.pureCartAdj
  dsimp only
  let deg := nodeDegree H.dual d0 darts.length
  let cartDeg := cartDegOriented H.dual darts.length deg refl d0
  let c := fun k => cartDartOriented H.dual deg refl d0 k
  have adj_symm : ∀ a b, areAdjacentVertices H.dual a b darts.length = true →
      areAdjacentVertices H.dual b a darts.length = true := fun a b hab => by
    rw [areAdjacentVertices_symm H.dual darts h_mc.complete (Nat.le_refl _) a b] at hab; exact hab
  have ne_symm : ∀ a b, sameVertex H.dual a b darts.length = false →
      sameVertex H.dual b a darts.length = false := fun a b hab => by
    cases hc : sameVertex H.dual b a darts.length
    · rfl
    · exfalso; have := dual_sameVertex_symm darts h_mc hc; rw [hab] at this; exact Bool.false_ne_true this
  have clause1 : ∀ p q,
      (p = 0 ∨ (1 ≤ p ∧ p ≤ 2 * deg) ∨
        ∃ i r, 1 ≤ i ∧ i ≤ deg ∧ (r = 2 ∨ r = 3 ∨ r = 4) ∧ p = r * deg + i ∧ r + 4 ≤ cartDeg i ∧ cartDeg i ≤ 8) →
      (q = 0 ∨ (1 ≤ q ∧ q ≤ 2 * deg) ∨
        ∃ i r, 1 ≤ i ∧ i ≤ deg ∧ (r = 2 ∨ r = 3 ∨ r = 4) ∧ q = r * deg + i ∧ r + 4 ≤ cartDeg i ∧ cartDeg i ≤ 8) →
      p ≠ q →
      sameVertex H.dual (c p) (c q) darts.length = false := by
    intro p q hp hq hpq
    rcases active_split hp with rfl | ⟨hp1, hp2⟩ | hpL2 <;>
    rcases active_split hq with rfl | ⟨hq1, hq2⟩ | hqL2
    · exact False.elim (hpq rfl)
    · exact hub_ne_spoke darts h_mc refl d0 hq1 hq2
    · exact l2_ne_hub darts h_mc refl d0 hdeg5 hqL2
    · exact ne_symm _ _ (hub_ne_spoke darts h_mc refl d0 hp1 hp2)
    · exact spoke_ne_spoke darts h_mc refl d0 hp1 hp2 hq1 hq2 hpq
    · exact l2_ne_spoke darts h_mc refl d0 hdeg5 hp1 hp2 hqL2
    · exact ne_symm _ _ (l2_ne_hub darts h_mc refl d0 hdeg5 hpL2)
    · exact ne_symm _ _ (l2_ne_spoke darts h_mc refl d0 hdeg5 hq1 hq2 hpL2)
    · by_cases hsh : ∃ u, isAttachedSpoke deg cartDeg u p ∧ isAttachedSpoke deg cartDeg u q
      · rcases hsh with ⟨u, hup, huq⟩
        exact (l2_same_spoke_ne_and_adj darts h_mc refl d0 hdeg5 hdeg11 hup huq hpq).1
      · exact (l2_disjoint_spokes_ne_and_not_adj darts h_mc refl d0 hdeg5 hpL2 hqL2 hsh).1
  refine ⟨clause1, ?_, ?_⟩
  · intro p q hp hq hpq hadj
    rcases active_split hp with rfl | ⟨hp1, hp2⟩ | hpL2 <;>
    rcases active_split hq with rfl | ⟨hq1, hq2⟩ | hqL2
    · exact False.elim (hpq rfl)
    · refine ⟨q, hq1, hq2, pureSpokeAdj_of_tri1 hdeg11 hq1 hq2 (Or.inl rfl) (Or.inr (Or.inr rfl)) hpq⟩
    · have := hub_not_adj_l2 darts h_mc refl d0 hdeg5 hqL2
      rw [this] at hadj; exact False.elim (Bool.false_ne_true hadj)
    · refine ⟨p, hp1, hp2, pureSpokeAdj_of_tri1 hdeg11 hp1 hp2 (Or.inr (Or.inr rfl)) (Or.inl rfl) hpq⟩
    · rcases (spoke_adj_iff darts h_mc refl d0 hdeg5 hp1 hp2 hq1 hq2 hpq).mp hadj with rfl | rfl
      · refine ⟨nextDeg deg p, nextDeg_ge_one, nextDeg_le (by omega) hp2, ?_⟩
        refine pureSpokeAdj_of_tri1 hdeg11 nextDeg_ge_one (nextDeg_le (by omega) hp2) ?_ (Or.inr (Or.inr rfl)) hpq
        rw [prevDeg_nextDeg hp1 hp2]; exact Or.inr (Or.inl rfl)
      · exact ⟨p, hp1, hp2, pureSpokeAdj_of_tri1 hdeg11 hp1 hp2 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hpq⟩
    · exact pureSpokeAdj_of_spoke_and_l2 (by omega) hdeg11 hp1 hp2
        (spoke_adj_l2_iff darts h_mc refl d0 hdeg5 hp1 hp2 hqL2 hadj)
    · have := hub_not_adj_l2 darts h_mc refl d0 hdeg5 hpL2
      have hadj' := adj_symm _ _ hadj
      rw [this] at hadj'; exact False.elim (Bool.false_ne_true hadj')
    · rcases pureSpokeAdj_of_spoke_and_l2 (by omega) hdeg11 hq1 hq2
          (spoke_adj_l2_iff darts h_mc refl d0 hdeg5 hq1 hq2 hpL2 (adj_symm _ _ hadj)) with ⟨i, hi1, hi2, h | h⟩
      · exact ⟨i, hi1, hi2, Or.inr h⟩
      · exact ⟨i, hi1, hi2, Or.inl h⟩
    · by_cases hsh : ∃ u, isAttachedSpoke deg cartDeg u p ∧ isAttachedSpoke deg cartDeg u q
      · rcases hsh with ⟨u, hup, huq⟩
        exact ⟨u, hup.1, hup.2.1,
          (l2_same_spoke_ne_and_adj darts h_mc refl d0 hdeg5 hdeg11 hup huq hpq).2 hadj⟩
      · have hno := (l2_disjoint_spokes_ne_and_not_adj darts h_mc refl d0 hdeg5 hpL2 hqL2 hsh).2
        rw [hno] at hadj; exact False.elim (Bool.false_ne_true hadj)
  · intro p q hp hq hpq d1 d2 hd1p hd2p hd1q hd2q
    have h12 := dual_sameVertex_trans darts h_mc hd1p (dual_sameVertex_symm darts h_mc hd2p)
    have he12 := dual_sameVertex_trans darts h_mc hd1q (dual_sameVertex_symm darts h_mc hd2q)
    exact mc_dual_no_parallel darts h_mc h12 he12

end Hypermap
