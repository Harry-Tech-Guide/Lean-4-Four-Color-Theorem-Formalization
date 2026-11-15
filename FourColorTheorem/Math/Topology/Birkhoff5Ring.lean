import FourColorTheorem.Math.Topology.ShortCircuits

/-!
# Birkhoff's 1913 5-Ring Reduction (`Birkhoff5Ring`)

This module proves Birkhoff's 1913 5-cycle reduction theorem for primal minimal
counterexamples `H` (`H.dual` is a minimum counterexample planar triangulation):

* **Small-Side Bound & Single Degree-5 Vertex (`|D_L| = 15`)**:
  For every chordless `cut : H.FaceCycleCut 5`, each side has size `9`, `15`, or `≥ 21`;
  chordlessness rules out `9` (forcing `≥ 2` darts in each `inArcL m`), and `|D_L| = 15`
  forces the entire `L`-side to consist of `{a_m, H.node.f a_m, H.node.inv a_m}` where
  `{H.node.f (cut.cutDart m) | m : Fin 5}` forms a single `H.face`-orbit of degree `5`
  (a single degree-5 vertex in `H.dual`).
* **Birkhoff 10-State System (`IsState5T`, `IsState5Q`) & Kempe Transfers**:
  Realizable 4-colorings on the 5-cycle boundary classify into 10 cyclic states (`T_0..4`
  and `Q_0..4`). Combining the pentagon cap (`+15` darts), vertex-identification cap (`+3`
  darts), and non-crossing `(A,C)`/`(B,D)` Kempe swaps on `H_cap` (`21 ≤ |D_L|, |D_R|`)
  forces a matching boundary coloring between `cut` and `cut.rev`, contradicting minimality.
* **Main Theorems**: `mc_birkhoff_five_ring_dual` and `mc_birkhoff_five_ring_vertex_dual`.
-/

namespace Hypermap

open Math Math.Hypermap Classical

section SmallSideAndNode3Helpers

private theorem mc_node_cube {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d : H.Dart) :
    Perm.iter H.node 3 d = d := by
  have hdeg : (getOrbit H.node darts.length d).length = 3 := mc_nodeDegree_eq_three H darts h_mc d
  have hper := perm_iter_length_getOrbit_eq_self_of_complete H.node darts h_mc.complete (Nat.le_refl _) d
  rw [hdeg] at hper
  exact hper

private theorem mc_node_ne_self {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d : H.Dart) :
    H.node.f d ≠ d := by
  intro h
  have hge := mc_nodeDegree_ge_three H darts h_mc d
  have hpos : 0 < darts.length := List.length_pos_of_mem (h_mc.complete d)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have h_eq := getOrbit_fixed_point H.node d k h
  have hge' : 3 ≤ (getOrbit H.node (k + 1) d).length := by
    change 3 ≤ (getOrbit H.node darts.length d).length at hge
    rwa [hk] at hge
  rw [h_eq] at hge'
  simp only [List.length_singleton] at hge'
  omega

private theorem mc_node_sq_ne_self {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d : H.Dart) :
    H.node.f (H.node.f d) ≠ d := by
  intro h
  have hge := mc_nodeDegree_ge_three H darts h_mc d
  have hsub : ∀ x ∈ getOrbit H.node darts.length d, x ∈ [d, H.node.f d] := by
    intro x hx
    obtain ⟨n, _, hn_eq⟩ := mem_getOrbit_imp_exists_iter H.node darts.length d x hx
    have h2 : Perm.iter H.node 2 d = d := by simpa [Perm.iter_succ, Perm.iter_zero] using h
    have hmul := Perm.iter_mul_period H.node h2 (n / 2)
    have hmod : Perm.iter H.node n d = Perm.iter H.node (n % 2) d := by
      calc Perm.iter H.node n d
          = Perm.iter H.node (n / 2 * 2 + n % 2) d := by congr 1; omega
        _ = Perm.iter H.node (n % 2) (Perm.iter H.node (n / 2 * 2) d) := by
              rw [Nat.add_comm, Perm.iter_add]
        _ = Perm.iter H.node (n % 2) d := by rw [hmul]
    rw [hn_eq, hmod]
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h0 | h1
    · rw [h0, Perm.iter_zero]; simp
    · rw [h1, Perm.iter_succ, Perm.iter_zero]; simp
  have hnd := getOrbit_nodup H.node darts.length d
  have hle := sc_nodup_length_le_of_subset (getOrbit H.node darts.length d) [d, H.node.f d] hnd hsub
  change 3 ≤ (getOrbit H.node darts.length d).length at hge
  have h2len : [d, H.node.f d].length = 2 := rfl
  omega

private theorem mc_node_inv_eq_sq {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d : H.Dart) :
    H.node.inv d = H.node.f (H.node.f d) := by
  have hc : H.node.f (H.node.f (H.node.f d)) = d := by
    simpa [Perm.iter_succ, Perm.iter_zero] using mc_node_cube darts h_mc d
  have h := congrArg H.node.inv hc
  rw [H.node.left_inv] at h
  exact h.symm

private theorem mc_sameOrbit_node_cases {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) {a b : H.Dart} (h : SameOrbit H.node a b) :
    b = a ∨ b = H.node.f a ∨ b = H.node.inv a := by
  obtain ⟨k, hk⟩ := h
  have hc : Perm.iter H.node 3 a = a := mc_node_cube darts h_mc a
  have hmul := Perm.iter_mul_period H.node hc (k / 3)
  have hmod : Perm.iter H.node k a = Perm.iter H.node (k % 3) a := by
    calc Perm.iter H.node k a
        = Perm.iter H.node (k / 3 * 3 + k % 3) a := by congr 1; omega
      _ = Perm.iter H.node (k % 3) (Perm.iter H.node (k / 3 * 3) a) := by
            rw [Nat.add_comm, Perm.iter_add]
      _ = Perm.iter H.node (k % 3) a := by rw [hmul]
  rw [← hk, hmod]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · rw [h0]; exact Or.inl rfl
  · rw [h1]; exact Or.inr (Or.inl rfl)
  · rw [h2]; exact Or.inr (Or.inr (by simp [Perm.iter_succ, Perm.iter_zero, mc_node_inv_eq_sq darts h_mc]))

private theorem dl_node_closed {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : H.FaceCycleCut k) (d : H.Dart) :
    cut.capSingleVertex_DL d ↔ cut.capSingleVertex_DL (H.node.f d) := by
  have h1 : cut.uncoupleTriple.n.f d = H.node.f d := by
    have hn : cut.uncoupleTriple.n = H.node := by
      dsimp [FaceCycleCut.uncoupleTriple]
      exact uncoupleList_n H.hypermapToTriple cut.cutPairs
    rw [hn]
  constructor
  · intro hd
    rw [← h1]
    exact reachEN_trans cut.uncoupleTriple.e cut.uncoupleTriple.n hd
      ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩
  · intro hd
    rw [← h1] at hd
    exact reachEN_trans cut.uncoupleTriple.e cut.uncoupleTriple.n hd
      (reachEN_symm _ _ ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩)

private theorem dl_node_inv_closed {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : H.FaceCycleCut k) (d : H.Dart) :
    cut.capSingleVertex_DL d ↔ cut.capSingleVertex_DL (H.node.inv d) := by
  have heq : H.node.f (H.node.inv d) = d := H.node.right_inv d
  constructor
  · intro hd
    exact (dl_node_closed cut (H.node.inv d)).mpr (by rw [heq]; exact hd)
  · intro hd
    rw [← heq]
    exact (dl_node_closed cut (H.node.inv d)).mp hd

private theorem cutDart_mem_DL {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) {k : Nat} (cut : H.FaceCycleCut k) (m : Fin k) :
    cut.capSingleVertex_DL (cut.cutDart m) :=
  cut.inArcL_sub_DL darts h_mc.nodup h_mc.complete h_mc.is_planar
    (mc_numComponents_eq_one H darts h_mc) (cut.cutDart_mem_inArcL darts h_mc.complete m)

private theorem edge_cutDart_not_DL {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) {k : Nat} (cut : H.FaceCycleCut k) (m : Fin k) :
    ¬cut.capSingleVertex_DL (H.edge.f (cut.cutDart m)) := by
  intro hDL
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have hspec := cut.capSingleVertex_spec darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn h_mc.is_bridgeless
  have hne_cut : ∀ j : Fin k, H.edge.f (cut.cutDart m) ≠ cut.cutDart j :=
    fun j hj => cut.h_disj_edge m j hj
  obtain ⟨hdn, he⟩ := hspec.2.2.2.2.2.2.2.2.1 (H.edge.f (cut.cutDart m)) hDL hne_cut
  have h_m_DL : cut.capSingleVertex_DL (cut.cutDart m) := cutDart_mem_DL darts h_mc cut m
  have hm_eq : H.edge.f (H.edge.f (cut.cutDart m)) = cut.cutDart m := mc_edge_inv (cut.cutDart m)
  have h_edge_m := (hspec.2.2.2.2.2.2.2.1 m).1
  have h_edge_inv : (cut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn).edge.f
      ((cut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn).edge.f
        (Sum.inl ⟨H.edge.f (cut.cutDart m), hDL⟩)) = Sum.inl ⟨H.edge.f (cut.cutDart m), hDL⟩ :=
    Hypermap.edge_edge _ _
  rw [he] at h_edge_inv
  have h_inl_eq : (Sum.inl ⟨H.edge.f (H.edge.f (cut.cutDart m)), hdn⟩ :
      { d // cut.capSingleVertex_DL d } ⊕ Fin k) = Sum.inl ⟨cut.cutDart m, h_m_DL⟩ := by
    congr 1; exact Subtype.ext hm_eq
  rw [h_inl_eq, h_edge_m] at h_edge_inv
  cases h_edge_inv

private theorem sameOrbit_node_inv_mem_face_next {H : Hypermap} [DecidableEq H.Dart]
    {k : Nat} (cut : H.FaceCycleCut k) (m : Fin k) :
    SameOrbit H.face (cut.ringFace ⟨(m.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
      (H.node.inv (cut.cutDart m)) := by
  have h1 : H.face.f (H.edge.f (cut.cutDart m)) = H.node.inv (cut.cutDart m) := by
    have h := H.node_face_edge_id (cut.cutDart m)
    have h2 := congrArg H.node.inv h
    rw [H.node.left_inv] at h2
    exact h2
  have h2 : SameOrbit H.face (H.edge.f (cut.cutDart m)) (H.node.inv (cut.cutDart m)) :=
    ⟨1, by simpa [Perm.iter_succ, Perm.iter_zero] using h1⟩
  exact sameOrbit_trans H.face (cut.h_b m) h2

end SmallSideAndNode3Helpers

section Chordless5Cut

/-- A 5-cycle cut `cut : H.FaceCycleCut 5` is chordless in `H.dual` if no edge
    connects two non-adjacent ring faces `cut.ringFace i` and `cut.ringFace j`. -/
def Chordless5 {H : Hypermap} (cut : H.FaceCycleCut 5) : Prop :=
  ∀ (i j : Fin 5), i ≠ j → j.val ≠ (i.val + 1) % 5 → i.val ≠ (j.val + 1) % 5 →
    ∀ u : H.Dart, SameOrbit H.face (cut.ringFace i) u →
      SameOrbit H.face (cut.ringFace j) (H.edge.f u) → False

theorem chordless5_rev {H : Hypermap} (cut : H.FaceCycleCut 5) (h : Chordless5 cut) :
    Chordless5 cut.rev := by
  intro i j hij hji_adj hij_adj u hu heu
  let i' : Fin 5 := ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩
  let j' : Fin 5 := ⟨(5 - j.val) % 5, Nat.mod_lt _ (by decide)⟩
  have hij' : i' ≠ j' := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp only [i', j'] at hv
    exact hij (Fin.ext (by omega))
  have hji'_adj : j'.val ≠ (i'.val + 1) % 5 := by
    dsimp only [i', j']
    omega
  have hij'_adj : i'.val ≠ (j'.val + 1) % 5 := by
    dsimp only [i', j']
    omega
  exact h i' j' hij' hji'_adj hij'_adj u hu heu

theorem chordless5_rot1 {H : Hypermap} (cut : H.FaceCycleCut 5) (h : Chordless5 cut) :
    Chordless5 cut.rot1 := by
  intro i j hij hji_adj hij_adj u hu heu
  let i' : Fin 5 := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
  let j' : Fin 5 := ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
  have hij' : i' ≠ j' := by
    intro heq
    have hv := congrArg Fin.val heq
    dsimp only [i', j'] at hv
    exact hij (Fin.ext (by omega))
  have hji'_adj : j'.val ≠ (i'.val + 1) % 5 := by
    dsimp only [i', j']
    omega
  have hij'_adj : i'.val ≠ (j'.val + 1) % 5 := by
    dsimp only [i', j']
    omega
  exact h i' j' hij' hji'_adj hij'_adj u hu heu

private theorem non_adj_five_of_add2 (m : Fin 5) :
    let j : Fin 5 := ⟨(m.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
    j ≠ m ∧ m.val ≠ (j.val + 1) % 5 ∧ j.val ≠ (m.val + 1) % 5 := by
  intro j
  refine ⟨?_, ?_, ?_⟩
  · intro h; have hv := congrArg Fin.val h; dsimp only [j] at hv; omega
  · dsimp only [j]; omega
  · dsimp only [j]; omega

private theorem chordless5_no_node_adj_cutDart {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut)
    (i j : Fin 5) (h_eq : H.node.f (cut.cutDart j) = cut.cutDart i) : False := by
  have hfen := H.face_edge_node_id (cut.cutDart j)
  rw [h_eq] at hfen
  have hfi : SameOrbit H.face (H.edge.f (cut.cutDart i)) (cut.cutDart j) :=
    ⟨1, by simpa [Perm.iter_succ, Perm.iter_zero] using hfen⟩
  have hsame : SameOrbit H.face (cut.ringFace ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩)
      (cut.ringFace j) :=
    sameOrbit_trans H.face (cut.h_b i) (sameOrbit_trans H.face hfi (sameOrbit_face_symm darts h_mc (cut.h_a j)))
  have hij_idx : (⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = j := by
    refine Classical.byContradiction fun hne => ?_
    exact cut.h_diff _ _ hne hsame
  have hj_val : j.val = (i.val + 1) % 5 := congrArg Fin.val hij_idx.symm
  let x := H.node.f (cut.cutDart i)
  have hfen_i := H.face_edge_node_id (cut.cutDart i)
  have h_ex_Fi : SameOrbit H.face (cut.ringFace i) (H.edge.f x) :=
    sameOrbit_trans H.face (cut.h_a i)
      (sameOrbit_face_symm darts h_mc ⟨1, by simpa [Perm.iter_succ, Perm.iter_zero, x] using hfen_i⟩)
  have hnx : H.node.f x = cut.cutDart j := by
    have hcube_j : H.node.f (H.node.f (H.node.f (cut.cutDart j))) = cut.cutDart j := by
      simpa [Perm.iter_succ, Perm.iter_zero] using mc_node_cube darts h_mc (cut.cutDart j)
    simpa [x, h_eq] using hcube_j
  have h_x_Fj1 : SameOrbit H.face (cut.ringFace ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) x := by
    have hfx := H.face_edge_node_id x
    rw [hnx] at hfx
    exact sameOrbit_trans H.face (cut.h_b j)
      ⟨1, by simpa [Perm.iter_succ, Perm.iter_zero] using hfx⟩
  have hj1_eq : (⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
      ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ := by
    apply Fin.ext; dsimp only; rw [hj_val]; omega
  rw [hj1_eq] at h_x_Fj1
  have hna := non_adj_five_of_add2 i
  exact h_chord ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ i hna.1 hna.2.1 hna.2.2 x h_x_Fj1 h_ex_Fi

private theorem chordless5_cutDart_node_disjoint {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut)
    {i j : Fin 5} (hij : i ≠ j) :
    ¬SameOrbit H.node (cut.cutDart i) (cut.cutDart j) := by
  intro hsame
  rcases mc_sameOrbit_node_cases darts h_mc hsame with heq | h1 | h2
  · exact cutDart_ne_of_ne darts h_mc cut hij heq.symm
  · exact chordless5_no_node_adj_cutDart darts h_mc cut h_chord j i h1.symm
  · have hstep : H.node.f (cut.cutDart j) = cut.cutDart i := by
      rw [h2]; exact H.node.right_inv (cut.cutDart i)
    exact chordless5_no_node_adj_cutDart darts h_mc cut h_chord i j hstep

private theorem chordless5_inArcL_has_interior {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut)
    (m : Fin 5) :
    ∃ d : H.Dart, d ≠ cut.cutDart m ∧ cut.inArcL darts h_mc.complete m d := by
  let i : Fin 5 := ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
  let d := H.node.inv (cut.cutDart i)
  have hm_eq : (⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = m := by
    apply Fin.ext; dsimp only [i]; omega
  have ha_i_DL : cut.capSingleVertex_DL (cut.cutDart i) := cutDart_mem_DL darts h_mc cut i
  have hd_DL : cut.capSingleVertex_DL d := (dl_node_inv_closed cut (cut.cutDart i)).mp ha_i_DL
  have hd_face : SameOrbit H.face (cut.ringFace m) d := by
    rw [← hm_eq]
    exact sameOrbit_node_inv_mem_face_next cut i
  have hd_arc : cut.inArcL darts h_mc.complete m d :=
    (cut.inArcL_iff_sameOrbit_and_DL darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) m d).mpr ⟨hd_face, hd_DL⟩
  refine ⟨d, ?_, hd_arc⟩
  intro heq
  have hstep : H.node.f (cut.cutDart m) = cut.cutDart i := by
    rw [← heq]; exact H.node.right_inv (cut.cutDart i)
  exact chordless5_no_node_adj_cutDart darts h_mc cut h_chord i m hstep

private theorem nodup_append_disjoint {α : Type} {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hd : ∀ x, x ∈ l1 → x ∈ l2 → False) :
    (l1 ++ l2).Nodup := by
  induction l1 with
  | nil => simpa using h2
  | cons a t ih =>
      rw [List.nodup_cons] at h1
      rw [List.cons_append, List.nodup_cons]
      refine ⟨?_, ih h1.2 (fun x hx => hd x (List.mem_cons_of_mem _ hx))⟩
      intro hmem
      rcases List.mem_append.mp hmem with hat | ha2
      · exact h1.1 hat
      · exact hd a List.mem_cons_self ha2

theorem chordless5_DL_ge_ten {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut) :
    10 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length := by
  have h_conn := mc_numComponents_eq_one H darts h_mc
  let arcList : Fin 5 → List H.Dart := fun m =>
    darts.filter (fun x => decide (cut.inArcL darts h_mc.complete m x))
  have harc_ge2 : ∀ m : Fin 5, 2 ≤ (arcList m).length := by
    intro m
    obtain ⟨d, hne, hd⟩ := chordless5_inArcL_has_interior darts h_mc cut h_chord m
    have ha_mem : cut.cutDart m ∈ arcList m :=
      List.mem_filter.mpr ⟨h_mc.complete _, decide_eq_true (cut.cutDart_mem_inArcL darts h_mc.complete m)⟩
    have hd_mem : d ∈ arcList m :=
      List.mem_filter.mpr ⟨h_mc.complete _, decide_eq_true hd⟩
    have hnd2 : [cut.cutDart m, d].Nodup := by simp [hne.symm]
    have hsub2 : ∀ x, x ∈ [cut.cutDart m, d] → x ∈ arcList m := by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> assumption
    exact sc_nodup_length_le_of_subset [cut.cutDart m, d] (arcList m) hnd2 hsub2
  have harc_nd : ∀ m : Fin 5, (arcList m).Nodup := fun m => nodup_filter_sc _ h_mc.nodup
  have harc_disj : ∀ (i j : Fin 5), i ≠ j → ∀ x, x ∈ arcList i → x ∈ arcList j → False := by
    intro i j hij x hxi hxj
    have hi_arc : cut.inArcL darts h_mc.complete i x := of_decide_eq_true (List.mem_filter.mp hxi).2
    have hj_arc : cut.inArcL darts h_mc.complete j x := of_decide_eq_true (List.mem_filter.mp hxj).2
    have hi_f := cut.inArcL_sub_face darts h_mc.complete hi_arc
    have hj_f := cut.inArcL_sub_face darts h_mc.complete hj_arc
    exact cut.h_diff i j hij (sameOrbit_trans H.face hi_f (sameOrbit_face_symm darts h_mc hj_f))
  let i0 : Fin 5 := ⟨0, by decide⟩
  let i1 : Fin 5 := ⟨1, by decide⟩
  let i2 : Fin 5 := ⟨2, by decide⟩
  let i3 : Fin 5 := ⟨3, by decide⟩
  let i4 : Fin 5 := ⟨4, by decide⟩
  let big := arcList i0 ++ arcList i1 ++ arcList i2 ++ arcList i3 ++ arcList i4
  have hnd34 : (arcList i3 ++ arcList i4).Nodup :=
    nodup_append_disjoint (harc_nd i3) (harc_nd i4) (harc_disj i3 i4 (by decide))
  have hnd234 : (arcList i2 ++ (arcList i3 ++ arcList i4)).Nodup :=
    nodup_append_disjoint (harc_nd i2) hnd34 (fun x hx hmem => by
      rcases List.mem_append.mp hmem with h3 | h4
      · exact harc_disj i2 i3 (by decide) x hx h3
      · exact harc_disj i2 i4 (by decide) x hx h4)
  have hnd1234 : (arcList i1 ++ (arcList i2 ++ (arcList i3 ++ arcList i4))).Nodup :=
    nodup_append_disjoint (harc_nd i1) hnd234 (fun x hx hmem => by
      rcases List.mem_append.mp hmem with h2 | h34
      · exact harc_disj i1 i2 (by decide) x hx h2
      · rcases List.mem_append.mp h34 with h3 | h4
        · exact harc_disj i1 i3 (by decide) x hx h3
        · exact harc_disj i1 i4 (by decide) x hx h4)
  have hnd01234 : (arcList i0 ++ (arcList i1 ++ (arcList i2 ++ (arcList i3 ++ arcList i4)))).Nodup :=
    nodup_append_disjoint (harc_nd i0) hnd1234 (fun x hx hmem => by
      rcases List.mem_append.mp hmem with h1 | h234
      · exact harc_disj i0 i1 (by decide) x hx h1
      · rcases List.mem_append.mp h234 with h2 | h34
        · exact harc_disj i0 i2 (by decide) x hx h2
        · rcases List.mem_append.mp h34 with h3 | h4
          · exact harc_disj i0 i3 (by decide) x hx h3
          · exact harc_disj i0 i4 (by decide) x hx h4)
  have hbig_nd : big.Nodup := by
    simpa [big, List.append_assoc] using hnd01234
  have hbig_sub : ∀ x, x ∈ big → x ∈ darts.filter (fun d => decide (cut.capSingleVertex_DL d)) := by
    intro x hx
    have hmem_m : ∃ m : Fin 5, x ∈ arcList m := by
      simp only [big, List.mem_append] at hx
      rcases hx with (((h0 | h1) | h2) | h3) | h4
      · exact ⟨i0, h0⟩
      · exact ⟨i1, h1⟩
      · exact ⟨i2, h2⟩
      · exact ⟨i3, h3⟩
      · exact ⟨i4, h4⟩
    rcases hmem_m with ⟨m, hm⟩
    have hx_arc : cut.inArcL darts h_mc.complete m x := of_decide_eq_true (List.mem_filter.mp hm).2
    have hx_DL := cut.inArcL_sub_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn hx_arc
    exact List.mem_filter.mpr ⟨h_mc.complete x, decide_eq_true hx_DL⟩
  have hle := sc_nodup_length_le_of_subset big _ hbig_nd hbig_sub
  have hlen_big : 10 ≤ big.length := by
    have h0 := harc_ge2 i0
    have h1 := harc_ge2 i1
    have h2 := harc_ge2 i2
    have h3 := harc_ge2 i3
    have h4 := harc_ge2 i4
    simp only [big, List.length_append]
    omega
  omega

theorem chordless5_DL_cases {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut) :
    (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 15 ∨
    21 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length := by
  have hdiv := (side_parity_divisibility_cap darts h_mc cut).1
  rcases hdiv with ⟨⟨q, h3⟩, _, ⟨m, hm⟩⟩
  have h10 := chordless5_DL_ge_ten darts h_mc cut h_chord
  omega

theorem mc_birkhoff_five_ring_vertex_dual {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut)
    (h15 : (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 15) :
    ∃ w : H.Dart,
      cut.capSingleVertex_DL w ∧
      Math.Hypermap.faceDegree H w darts.length = 5 ∧
      (∀ d : H.Dart, cut.capSingleVertex_DL d →
        (∃ m : Fin 5, SameOrbit H.face (cut.ringFace m) d) ∨ SameOrbit H.face w d) ∧
      (∀ m : Fin 5, SameOrbit H.face (cut.ringFace m)
        (H.edge.f (Perm.iter H.face ((5 - m.val) % 5) w))) := by
  let a : Fin 5 → H.Dart := fun m => cut.cutDart m
  let y : Fin 5 → H.Dart := fun m => H.node.f (a m)
  let z : Fin 5 → H.Dart := fun m => H.node.inv (a m)
  let dartsL := darts.filter (fun x => decide (cut.capSingleVertex_DL x))
  have ha_DL : ∀ m, cut.capSingleVertex_DL (a m) := fun m => cutDart_mem_DL darts h_mc cut m
  have hy_DL : ∀ m, cut.capSingleVertex_DL (y m) := fun m => (dl_node_closed cut (a m)).mp (ha_DL m)
  have hz_DL : ∀ m, cut.capSingleVertex_DL (z m) := fun m => (dl_node_inv_closed cut (a m)).mp (ha_DL m)
  have ha_not_edge_DL : ∀ m, ¬cut.capSingleVertex_DL (H.edge.f (a m)) :=
    fun m => edge_cutDart_not_DL darts h_mc cut m
  let tripleOf : Fin 5 → List H.Dart := fun m => [a m, y m, z m]
  have htr_nd : ∀ m : Fin 5, (tripleOf m).Nodup := by
    intro m
    have h1 : y m ≠ a m := mc_node_ne_self darts h_mc (a m)
    have h2 : z m ≠ a m := by
      change H.node.inv (a m) ≠ a m
      rw [mc_node_inv_eq_sq darts h_mc (a m)]
      exact mc_node_sq_ne_self darts h_mc (a m)
    have h3 : z m ≠ y m := by
      intro heq
      have hf : a m = H.node.f (y m) := by
        calc a m = H.node.f (z m) := (H.node.right_inv (a m)).symm
          _ = H.node.f (y m) := congrArg H.node.f heq
      exact h2 (by
        change H.node.inv (a m) = a m
        rw [mc_node_inv_eq_sq darts h_mc (a m)]
        exact hf.symm)
    simp [tripleOf, h1.symm, h2.symm, h3.symm]
  have htr_so : ∀ m : Fin 5, ∀ x ∈ tripleOf m, SameOrbit H.node (a m) x := by
    intro m x hx
    simp only [tripleOf, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, by simp [Perm.iter_succ, Perm.iter_zero, z, mc_node_inv_eq_sq darts h_mc]⟩
  have htr_disj : ∀ (i j : Fin 5), i ≠ j → ∀ x, x ∈ tripleOf i → x ∈ tripleOf j → False := by
    intro i j hij x hxi hxj
    have hi := htr_so i x hxi
    have hj := htr_so j x hxj
    have hs : SameOrbit H.node (a i) (a j) :=
      sameOrbit_trans H.node hi (sameOrbit_symm_of_complete H.node darts h_mc.complete hj)
    exact chordless5_cutDart_node_disjoint darts h_mc cut h_chord hij hs
  let i0 : Fin 5 := ⟨0, by decide⟩
  let i1 : Fin 5 := ⟨1, by decide⟩
  let i2 : Fin 5 := ⟨2, by decide⟩
  let i3 : Fin 5 := ⟨3, by decide⟩
  let i4 : Fin 5 := ⟨4, by decide⟩
  let big15 := tripleOf i0 ++ tripleOf i1 ++ tripleOf i2 ++ tripleOf i3 ++ tripleOf i4
  have hnd34 : (tripleOf i3 ++ tripleOf i4).Nodup :=
    nodup_append_disjoint (htr_nd i3) (htr_nd i4) (htr_disj i3 i4 (by decide))
  have hnd234 : (tripleOf i2 ++ (tripleOf i3 ++ tripleOf i4)).Nodup :=
    nodup_append_disjoint (htr_nd i2) hnd34 (fun x hx hm => by
      rcases List.mem_append.mp hm with h3 | h4
      · exact htr_disj i2 i3 (by decide) x hx h3
      · exact htr_disj i2 i4 (by decide) x hx h4)
  have hnd1234 : (tripleOf i1 ++ (tripleOf i2 ++ (tripleOf i3 ++ tripleOf i4))).Nodup :=
    nodup_append_disjoint (htr_nd i1) hnd234 (fun x hx hm => by
      rcases List.mem_append.mp hm with h2 | h34
      · exact htr_disj i1 i2 (by decide) x hx h2
      · rcases List.mem_append.mp h34 with h3 | h4
        · exact htr_disj i1 i3 (by decide) x hx h3
        · exact htr_disj i1 i4 (by decide) x hx h4)
  have hnd01234 : (tripleOf i0 ++ (tripleOf i1 ++ (tripleOf i2 ++ (tripleOf i3 ++ tripleOf i4)))).Nodup :=
    nodup_append_disjoint (htr_nd i0) hnd1234 (fun x hx hm => by
      rcases List.mem_append.mp hm with h1 | h234
      · exact htr_disj i0 i1 (by decide) x hx h1
      · rcases List.mem_append.mp h234 with h2 | h34
        · exact htr_disj i0 i2 (by decide) x hx h2
        · rcases List.mem_append.mp h34 with h3 | h4
          · exact htr_disj i0 i3 (by decide) x hx h3
          · exact htr_disj i0 i4 (by decide) x hx h4)
  have hbig_nd : big15.Nodup := by simpa [big15, List.append_assoc] using hnd01234
  have hbig_sub : ∀ x, x ∈ big15 → x ∈ dartsL := by
    intro x hx
    have hex : ∃ m : Fin 5, x ∈ tripleOf m := by
      simp only [big15, List.mem_append] at hx
      rcases hx with (((h0 | h1) | h2) | h3) | h4
      · exact ⟨i0, h0⟩
      · exact ⟨i1, h1⟩
      · exact ⟨i2, h2⟩
      · exact ⟨i3, h3⟩
      · exact ⟨i4, h4⟩
    rcases hex with ⟨m, hm⟩
    simp only [tripleOf, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · exact List.mem_filter.mpr ⟨h_mc.complete _, decide_eq_true (ha_DL m)⟩
    · exact List.mem_filter.mpr ⟨h_mc.complete _, decide_eq_true (hy_DL m)⟩
    · exact List.mem_filter.mpr ⟨h_mc.complete _, decide_eq_true (hz_DL m)⟩
  have hlen15 : big15.length = 15 := by simp [big15, tripleOf]
  have hDL_mem_big : ∀ x, x ∈ dartsL → x ∈ big15 := by
    apply sc_nodup_mem_of_subset_of_length_le big15 dartsL hbig_nd hbig_sub
    have hlenL : dartsL.length = 15 := h15
    omega
  have hDL_cases : ∀ x : H.Dart, cut.capSingleVertex_DL x →
      ∃ m : Fin 5, x = a m ∨ x = y m ∨ x = z m := by
    intro x hx
    have hx_big := hDL_mem_big x (List.mem_filter.mpr ⟨h_mc.complete x, decide_eq_true hx⟩)
    have hex : ∃ m : Fin 5, x ∈ tripleOf m := by
      simp only [big15, List.mem_append] at hx_big
      rcases hx_big with (((h0 | h1) | h2) | h3) | h4
      · exact ⟨i0, h0⟩
      · exact ⟨i1, h1⟩
      · exact ⟨i2, h2⟩
      · exact ⟨i3, h3⟩
      · exact ⟨i4, h4⟩
    rcases hex with ⟨m, hm⟩
    simp only [tripleOf, List.mem_cons, List.mem_nil_iff, or_false] at hm
    exact ⟨m, hm⟩
  have hey_in_Fm : ∀ m : Fin 5, SameOrbit H.face (cut.ringFace m) (H.edge.f (y m)) := by
    intro m
    have hfen := H.face_edge_node_id (a m)
    have h1 : SameOrbit H.face (H.edge.f (y m)) (a m) :=
      ⟨1, by simpa [Perm.iter_succ, Perm.iter_zero, y] using hfen⟩
    exact sameOrbit_trans H.face (cut.h_a m) (sameOrbit_face_symm darts h_mc h1)
  have hy_not_F : ∀ m j : Fin 5, ¬SameOrbit H.face (cut.ringFace j) (y m) := by
    intro m j hyj
    by_cases hjm : j = m
    · rw [hjm] at hyj
      have hbr : SameOrbit H.face (y m) (H.edge.f (y m)) :=
        sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hyj) (hey_in_Fm m)
      exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp h_mc.is_bridgeless (y m) hbr
    · by_cases hj_next : j.val = (m.val + 1) % 5
      · have hne_ea : H.edge.f (y m) ≠ a m := by
          intro h_eq
          have he2 := congrArg H.edge.f h_eq
          rw [mc_edge_inv] at he2
          have := hy_DL m
          rw [he2] at this
          exact ha_not_edge_DL m this
        have hf1 : SameOrbit H.face (H.edge.f (y m)) (a m) :=
          sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc (hey_in_Fm m)) (cut.h_a m)
        have hf2 : SameOrbit H.face (H.edge.f (H.edge.f (y m))) (H.edge.f (a m)) := by
          rw [mc_edge_inv]
          have hjm_eq : (⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = j := Fin.ext hj_next.symm
          exact sameOrbit_trans H.face (by rw [hjm_eq]; exact sameOrbit_face_symm darts h_mc hyj) (cut.h_b m)
        exact mc_no_parallel_edges_of_two_darts H darts h_mc hne_ea hf1 hf2
      · by_cases hm_next : m.val = (j.val + 1) % 5
        · have hne_ya : y m ≠ a j := by
            intro heq
            have hso : SameOrbit H.node (a m) (a j) := ⟨1, heq⟩
            exact chordless5_cutDart_node_disjoint darts h_mc cut h_chord (fun h => hjm h.symm) hso
          have hf1 : SameOrbit H.face (y m) (a j) :=
            sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hyj) (cut.h_a j)
          have hf2 : SameOrbit H.face (H.edge.f (y m)) (H.edge.f (a j)) := by
            have hm_eq : (⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = m := Fin.ext hm_next.symm
            exact sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc (hey_in_Fm m))
              (by rw [← hm_eq]; exact cut.h_b j)
          exact mc_no_parallel_edges_of_two_darts H darts h_mc hne_ya hf1 hf2
        · exact h_chord m j (fun h => hjm h.symm) hj_next hm_next (H.edge.f (y m)) (hey_in_Fm m)
            (by rw [mc_edge_inv]; exact hyj)
  have hey_DL : ∀ m : Fin 5, cut.capSingleVertex_DL (H.edge.f (y m)) := by
    intro m
    have hne : ∀ j : Fin 5, y m ≠ a j := by
      intro j heq
      exact hy_not_F m j (by rw [heq]; exact cut.h_a j)
    exact (dl_edge_of_ne_cutDart darts h_mc cut (hy_DL m) hne).2
  have hey_eq_z : ∀ m : Fin 5, H.edge.f (y m) = z ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ := by
    intro m
    obtain ⟨j, hcases⟩ := hDL_cases (H.edge.f (y m)) (hey_DL m)
    rcases hcases with rfl_a | rfl_y | rfl_z
    · exfalso
      have he2 := congrArg H.edge.f rfl_a
      rw [mc_edge_inv] at he2
      have := hy_DL m
      rw [he2] at this
      exact ha_not_edge_DL j this
    · exfalso
      exact hy_not_F j m (by rw [← rfl_y]; exact hey_in_Fm m)
    · have hz_f : SameOrbit H.face (cut.ringFace ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩)
          (H.edge.f (y m)) := by
        rw [rfl_z]; exact sameOrbit_node_inv_mem_face_next cut j
      have hsame_ring : SameOrbit H.face (cut.ringFace m)
          (cut.ringFace ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩) :=
        sameOrbit_trans H.face (hey_in_Fm m) (sameOrbit_face_symm darts h_mc hz_f)
      have hm_eq : m = ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ := by
        refine Classical.byContradiction fun hne => ?_
        exact cut.h_diff _ _ hne hsame_ring
      have hj_eq : j = ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ := by
        have hv := congrArg Fin.val hm_eq
        dsimp only at hv
        exact Fin.ext (by dsimp only; omega)
      rw [rfl_z, hj_eq]
  have hf_y_step : ∀ m : Fin 5, H.face.f (y m) = y ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ := by
    intro m
    calc H.face.f (y m)
        = H.node.inv (H.edge.inv (y m)) := H.face_eq_node_inv_edge_inv (y m)
      _ = H.node.inv (H.edge.f (y m)) := by rw [H.edge_inv_eq_edge]
      _ = H.node.inv (z ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩) := by rw [hey_eq_z m]
      _ = H.node.inv (H.node.inv (a ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩)) := rfl
      _ = H.node.f (a ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩) := by
            have hc := mc_node_cube darts h_mc (a ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩)
            have h1 := congrArg H.node.inv hc
            rw [Perm.iter_succ, Perm.iter_succ, Perm.iter_succ, Perm.iter_zero, H.node.left_inv] at h1
            have h2 := congrArg H.node.inv h1
            rw [H.node.left_inv] at h2
            exact h2.symm
  let w := y i0
  have hw_iter : ∀ r : Nat, Perm.iter H.face r w = y ⟨(5 - r % 5) % 5, Nat.mod_lt _ (by decide)⟩ := by
    intro r
    induction r with
    | zero =>
        change w = y ⟨(5 - 0 % 5) % 5, Nat.mod_lt _ (by decide)⟩
        have hz : (⟨(5 - 0 % 5) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i0 := Fin.ext (by decide)
        rw [hz]
    | succ r ih =>
        rw [Perm.iter_succ, ih, hf_y_step]
        congr 1; apply Fin.ext; dsimp only; omega
  have hw_deg5 : Math.Hypermap.faceDegree H w darts.length = 5 := by
    change (getOrbit H.face darts.length w).length = 5
    let y5 := [y i0, y ⟨4, by decide⟩, y ⟨3, by decide⟩, y ⟨2, by decide⟩, y ⟨1, by decide⟩]
    have hy_inj : ∀ j1 j2 : Fin 5, y j1 = y j2 → j1 = j2 := by
      intro j1 j2 heq
      have he1 := congrArg H.node.inv heq
      rw [H.node.left_inv, H.node.left_inv] at he1
      exact Classical.byContradiction fun hne => cutDart_ne_of_ne darts h_mc cut hne he1
    have hy5_nd : y5.Nodup := by
      simp only [y5, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or,
        not_false_eq_true, List.nodup_nil, and_true]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;>
        exact fun h => absurd (hy_inj _ _ h) (by decide)
    have hy5_iff : ∀ u, u ∈ getOrbit H.face darts.length w ↔ u ∈ y5 := by
      intro u
      constructor
      · intro hu
        obtain ⟨n, _, hn_eq⟩ := mem_getOrbit_imp_exists_iter H.face darts.length w u hu
        rw [hn_eq, hw_iter n]
        rcases (by omega : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4) with
          h | h | h | h | h <;> rw [h] <;> simp [y5, i0]
      · intro hu
        have horb_mem : ∀ r : Nat, Perm.iter H.face r w ∈ getOrbit H.face darts.length w := fun r =>
          (sameOrbit_iff_mem_getOrbit H.face darts h_mc.complete (Nat.le_refl _) w _).mp ⟨r, rfl⟩
        simp only [y5, List.mem_cons, List.mem_nil_iff, or_false] at hu
        rcases hu with rfl | rfl | rfl | rfl | rfl
        · have h0 := horb_mem 0
          rwa [hw_iter 0] at h0
        · have h1 := horb_mem 1
          rw [hw_iter 1, show (⟨(5 - 1 % 5) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨4, by decide⟩ by ext; decide] at h1
          exact h1
        · have h2 := horb_mem 2
          rw [hw_iter 2, show (⟨(5 - 2 % 5) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨3, by decide⟩ by ext; decide] at h2
          exact h2
        · have h3 := horb_mem 3
          rw [hw_iter 3, show (⟨(5 - 3 % 5) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨2, by decide⟩ by ext; decide] at h3
          exact h3
        · have h4 := horb_mem 4
          rw [hw_iter 4, show (⟨(5 - 4 % 5) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨1, by decide⟩ by ext; decide] at h4
          exact h4
    have hlen_eq := nodup_length_eq_of_iff_mem (getOrbit_nodup H.face darts.length w) hy5_nd hy5_iff
    rw [hlen_eq]
    rfl
  refine ⟨w, hy_DL i0, hw_deg5, ?_, ?_⟩
  · intro d hd
    obtain ⟨m, hcases⟩ := hDL_cases d hd
    rcases hcases with rfl | rfl | rfl
    · exact Or.inl ⟨m, cut.h_a m⟩
    · refine Or.inr ⟨(5 - m.val) % 5, ?_⟩
      rw [hw_iter]
      congr 1; apply Fin.ext; dsimp only; omega
    · exact Or.inl ⟨⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩, sameOrbit_node_inv_mem_face_next cut m⟩
  · intro m
    rw [hw_iter]
    have hm_idx : (⟨(5 - (5 - m.val) % 5 % 5) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = m := by
      apply Fin.ext; dsimp only; omega
    rw [hm_idx]
    exact hey_in_Fm m

end Chordless5Cut

section TenStates5

/-- Birkhoff type-T state `T_i` on a 5-cycle coloring `f : Fin 5 → Color`: vertex `i`
    has a unique color while `(i+1, i+3)` and `(i+2, i+4)` form two monochromatically
    paired diagonals. -/
def IsState5T (i : Fin 5) (f : Fin 5 → Color) : Prop :=
  f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ = f ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩ ∧
  f ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ = f ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩

/-- Birkhoff type-Q state `Q_i` on a 5-cycle coloring `f : Fin 5 → Color`: vertices
    `i+4` and `i+1` share a color while `i` avoids the remaining two non-adjacent colors
    `i+2` and `i+3`. -/
def IsState5Q (i : Fin 5) (f : Fin 5 → Color) : Prop :=
  f ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ = f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ∧
  f i ≠ f ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ ∧
  f i ≠ f ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩

private theorem color_fourth_of_three_ne {a b c d x : Color}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  have hmem : ∀ y, y ∈ [Color.c0, Color.c1, Color.c2, Color.c3] → y ∈ [a, b, c, d] := by
    apply sc_nodup_mem_of_subset_of_length_le [a, b, c, d] [Color.c0, Color.c1, Color.c2, Color.c3]
    · simp [hab, hac, had, hbc, hbd, hcd]
    · intro y _
      cases y <;> simp
    · simp
  have hx := hmem x (by cases x <;> simp)
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  exact hx

private theorem color_pair_of_ne_two {a b x y : Color}
    (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) (hxy : x ≠ y)
    (z : Color) (hza : z ≠ a) (hzb : z ≠ b) : z = x ∨ z = y := by
  rcases color_fourth_of_three_ne hab hxa.symm hya.symm hxb.symm hyb.symm hxy (x := z) with
    rfl | rfl | rfl | rfl
  · exact absurd rfl hza
  · exact absurd rfl hzb
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem color_unique_of_ne_three {a b c x z : Color}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) : z = x := by
  rcases color_fourth_of_three_ne hab hac hxa.symm hbc hxb.symm hxc.symm (x := z) with
    rfl | rfl | rfl | rfl
  · exact absurd rfl hza
  · exact absurd rfl hzb
  · exact absurd rfl hzc
  · rfl

private theorem fin5_three_colors_imp_state5T (f : Fin 5 → Color) (c_W : Color)
    (hadj : ∀ i : Fin 5, f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ≠ f i)
    (havoid : ∀ i : Fin 5, f i ≠ c_W) :
    ∃ i : Fin 5, IsState5T i f := by
  have hf01 : f ⟨0, by decide⟩ ≠ f ⟨1, by decide⟩ := (hadj ⟨0, by decide⟩).symm
  have hf12 : f ⟨1, by decide⟩ ≠ f ⟨2, by decide⟩ := (hadj ⟨1, by decide⟩).symm
  have hf23 : f ⟨2, by decide⟩ ≠ f ⟨3, by decide⟩ := (hadj ⟨2, by decide⟩).symm
  have hf34 : f ⟨3, by decide⟩ ≠ f ⟨4, by decide⟩ := (hadj ⟨3, by decide⟩).symm
  have hf40 : f ⟨4, by decide⟩ ≠ f ⟨0, by decide⟩ := by simpa using (hadj ⟨4, by decide⟩).symm
  have ha0 := havoid ⟨0, by decide⟩
  have ha1 := havoid ⟨1, by decide⟩
  have ha2 := havoid ⟨2, by decide⟩
  have ha3 := havoid ⟨3, by decide⟩
  have ha4 := havoid ⟨4, by decide⟩
  by_cases h02 : f ⟨0, by decide⟩ = f ⟨2, by decide⟩
  · by_cases h13 : f ⟨1, by decide⟩ = f ⟨3, by decide⟩
    · exact ⟨⟨4, by decide⟩, ⟨by dsimp only; exact h02, by dsimp only; exact h13⟩⟩
    · have hcW0 : c_W ≠ f ⟨0, by decide⟩ := ha0.symm
      have hcW3 : c_W ≠ f ⟨3, by decide⟩ := ha3.symm
      have hf03 : f ⟨0, by decide⟩ ≠ f ⟨3, by decide⟩ := by rw [h02]; exact hf23
      have h4_eq1 : f ⟨4, by decide⟩ = f ⟨1, by decide⟩ :=
        color_unique_of_ne_three hcW0 hcW3 hf03
          ha1 hf01.symm h13 ha4 hf40 hf34.symm
      exact ⟨⟨3, by decide⟩, ⟨by dsimp only; exact h4_eq1, by dsimp only; exact h02⟩⟩
  · have hcW2 : c_W ≠ f ⟨2, by decide⟩ := ha2.symm
    have h3_cases : f ⟨3, by decide⟩ = f ⟨0, by decide⟩ ∨ f ⟨3, by decide⟩ = f ⟨1, by decide⟩ :=
      color_pair_of_ne_two hcW2 ha0 h02 ha1 hf12 hf01 (f ⟨3, by decide⟩) ha3 hf23.symm
    rcases h3_cases with h30 | h31
    · have hcW0 : c_W ≠ f ⟨0, by decide⟩ := ha0.symm
      have h20 : f ⟨2, by decide⟩ ≠ f ⟨0, by decide⟩ := fun h => h02 h.symm
      have h4_cases : f ⟨4, by decide⟩ = f ⟨1, by decide⟩ ∨ f ⟨4, by decide⟩ = f ⟨2, by decide⟩ :=
        color_pair_of_ne_two hcW0 ha1 hf01.symm ha2 h20 hf12 (f ⟨4, by decide⟩) ha4 (by rw [← h30]; exact hf34.symm)
      rcases h4_cases with h41 | h42
      · exact ⟨⟨2, by decide⟩, ⟨by dsimp only; exact h30, by dsimp only; exact h41⟩⟩
      · exact ⟨⟨1, by decide⟩, ⟨by dsimp only; exact h42.symm, by dsimp only; exact h30⟩⟩
    · have hcW0 : c_W ≠ f ⟨0, by decide⟩ := ha0.symm
      have hcW1 : c_W ≠ f ⟨1, by decide⟩ := ha1.symm
      have h20 : f ⟨2, by decide⟩ ≠ f ⟨0, by decide⟩ := fun h => h02 h.symm
      have h4_eq2 : f ⟨4, by decide⟩ = f ⟨2, by decide⟩ :=
        color_unique_of_ne_three hcW0 hcW1 hf01
          ha2 h20 hf12.symm ha4 hf40 (by rw [← h31]; exact hf34.symm)
      exact ⟨⟨0, by decide⟩, ⟨by dsimp only; exact h31.symm, by dsimp only; exact h4_eq2.symm⟩⟩

private theorem fin5_eq13_imp_state5 (f : Fin 5 → Color)
    (_hadj : ∀ i : Fin 5, f ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ≠ f i)
    (h13 : f ⟨1, by decide⟩ = f ⟨3, by decide⟩) :
    IsState5T ⟨0, by decide⟩ f ∨ IsState5T ⟨4, by decide⟩ f ∨ IsState5Q ⟨2, by decide⟩ f := by
  by_cases h24 : f ⟨2, by decide⟩ = f ⟨4, by decide⟩
  · exact Or.inl ⟨h13, h24⟩
  · by_cases h02 : f ⟨0, by decide⟩ = f ⟨2, by decide⟩
    · exact Or.inr (Or.inl ⟨by dsimp only; exact h02, by dsimp only; exact h13⟩)
    · exact Or.inr (Or.inr ⟨by dsimp only; exact h13, by dsimp only; exact h24,
        by dsimp only; exact fun h => h02 h.symm⟩)

private def norm5T (i x : Fin 5) : Fin 3 :=
  if x = i then 0
  else if x = ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ∨
          x = ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩ then 1
  else 2

private def norm5Q (i x : Fin 5) : Fin 4 :=
  if x = i then 0
  else if x = ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ∨
          x = ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ then 1
  else if x = ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ then 2
  else 3

private theorem fin5_rot_cases (i x : Fin 5) :
    x = i ∨
    x = ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ∨
    x = ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ ∨
    x = ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩ ∨
    x = ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ := by
  let d := (x.val + 5 - i.val) % 5
  have hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by omega
  rcases hd with hd | hd | hd | hd | hd
  · exact Or.inl (Fin.ext (by omega))
  · exact Or.inr (Or.inl (Fin.ext (by dsimp only; omega)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (by dsimp only; omega))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.ext (by dsimp only; omega)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.ext (by dsimp only; omega)))))

private theorem fin5_state5T_norm_eq {i : Fin 5} {f : Fin 5 → Color}
    (hf_adj : ∀ k : Fin 5, f ⟨(k.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ≠ f k)
    (hfT : IsState5T i f) :
    ∀ x y : Fin 5, f x = f y ↔ norm5T i x = norm5T i y := by
  let i1 : Fin 5 := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
  let i2 : Fin 5 := ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
  let i3 : Fin 5 := ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩
  let i4 : Fin 5 := ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
  have h1s : (⟨(i1.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i2 := Fin.ext (by dsimp [i1, i2]; omega)
  have h4s : (⟨(i4.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i := Fin.ext (by dsimp [i4]; omega)
  have h01 : f i ≠ f i1 := (hf_adj i).symm
  have h12 : f i1 ≠ f i2 := by have h := (hf_adj i1).symm; rwa [h1s] at h
  have h02 : f i ≠ f i2 := by
    have h40 := (hf_adj i4).symm
    rw [h4s] at h40
    change f i1 = f i3 ∧ f i2 = f i4 at hfT
    rw [hfT.2]
    exact fun h => h40 h.symm
  let val : Fin 3 → Color := fun c => match c with
    | ⟨0, _⟩ => f i
    | ⟨1, _⟩ => f i1
    | ⟨2, _⟩ => f i2
  have hval_inj : ∀ a b : Fin 3, val a = val b → a = b := by
    intro ⟨av, ha⟩ ⟨bv, hb⟩ hab
    rcases (by omega : av = 0 ∨ av = 1 ∨ av = 2) with rfl | rfl | rfl <;>
    rcases (by omega : bv = 0 ∨ bv = 1 ∨ bv = 2) with rfl | rfl | rfl <;>
    first
    | rfl
    | exact absurd hab h01
    | exact absurd hab h02
    | exact absurd hab h01.symm
    | exact absurd hab h12
    | exact absurd hab h02.symm
    | exact absurd hab h12.symm
  have hfx : ∀ z : Fin 5, f z = val (norm5T i z) := by
    intro z
    rcases fin5_rot_cases i z with rfl | rfl | rfl | rfl | rfl
    · simp [norm5T, val]
    · have hn0 : i1 ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i1] at this; omega
      simp [norm5T, i1, hn0, val]
    · have hn0 : i2 ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i2] at this; omega
      have hn1 : i2 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i1, i2] at this; omega
      have hn3 : i2 ≠ i3 := by intro h; have := congrArg Fin.val h; dsimp [i2, i3] at this; omega
      simp [norm5T, i1, i2, i3, hn0, hn1, hn3, val]
    · have hn0 : i3 ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i3] at this; omega
      have h_eq : norm5T i i3 = 1 := by
        dsimp only [norm5T]
        change (if i3 = i then 0 else if i3 = i1 ∨ i3 = i3 then 1 else 2) = 1
        rw [if_neg hn0, if_pos (Or.inr rfl)]
      rw [h_eq]; exact hfT.1.symm
    · have hn0 : i4 ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i4] at this; omega
      have hn1 : i4 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i1, i4] at this; omega
      have hn3 : i4 ≠ i3 := by intro h; have := congrArg Fin.val h; dsimp [i3, i4] at this; omega
      have h_eq : norm5T i i4 = 2 := by simp [norm5T, hn0]; exact ⟨hn1, hn3⟩
      rw [h_eq]; exact hfT.2.symm
  intro x y
  rw [hfx x, hfx y]
  exact ⟨fun h => hval_inj _ _ h, fun h => congrArg val h⟩

private theorem fin5_state5Q_norm_eq {i : Fin 5} {f : Fin 5 → Color}
    (hf_adj : ∀ k : Fin 5, f ⟨(k.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ≠ f k)
    (hfQ : IsState5Q i f) :
    ∀ x y : Fin 5, f x = f y ↔ norm5Q i x = norm5Q i y := by
  let i1 : Fin 5 := ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
  let i2 : Fin 5 := ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
  let i3 : Fin 5 := ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩
  let i4 : Fin 5 := ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
  have h1s : (⟨(i1.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i2 := Fin.ext (by dsimp [i1, i2]; omega)
  have h2s : (⟨(i2.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i3 := Fin.ext (by dsimp [i2, i3]; omega)
  have h3s : (⟨(i3.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i4 := Fin.ext (by dsimp [i3, i4]; omega)
  have h01 : f i ≠ f i1 := (hf_adj i).symm
  have h12 : f i1 ≠ f i2 := by have h := (hf_adj i1).symm; rwa [h1s] at h
  have h23 : f i2 ≠ f i3 := by have h := (hf_adj i2).symm; rwa [h2s] at h
  have h13 : f i1 ≠ f i3 := by
    have h34 := (hf_adj i3).symm
    rw [h3s] at h34
    change f i4 = f i1 ∧ f i ≠ f i2 ∧ f i ≠ f i3 at hfQ
    rw [← hfQ.1]
    exact fun h => h34 h.symm
  have h02 : f i ≠ f i2 := hfQ.2.1
  have h03 : f i ≠ f i3 := hfQ.2.2
  let val : Fin 4 → Color := fun c => match c with
    | ⟨0, _⟩ => f i
    | ⟨1, _⟩ => f i1
    | ⟨2, _⟩ => f i2
    | ⟨3, _⟩ => f i3
  have hval_inj : ∀ a b : Fin 4, val a = val b → a = b := by
    intro ⟨av, ha⟩ ⟨bv, hb⟩ hab
    rcases (by omega : av = 0 ∨ av = 1 ∨ av = 2 ∨ av = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : bv = 0 ∨ bv = 1 ∨ bv = 2 ∨ bv = 3) with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | exact absurd hab h01
    | exact absurd hab h02
    | exact absurd hab h03
    | exact absurd hab h01.symm
    | exact absurd hab h12
    | exact absurd hab h13
    | exact absurd hab h02.symm
    | exact absurd hab h12.symm
    | exact absurd hab h23
    | exact absurd hab h03.symm
    | exact absurd hab h13.symm
    | exact absurd hab h23.symm
  have hfx : ∀ z : Fin 5, f z = val (norm5Q i z) := by
    intro z
    rcases fin5_rot_cases i z with rfl | rfl | rfl | rfl | rfl
    · simp [norm5Q, val]
    · have hn0 : i1 ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i1] at this; omega
      simp [norm5Q, i1, hn0, val]
    · have hn0 : i2 ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i2] at this; omega
      have hn1 : i2 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i1, i2] at this; omega
      have hn4 : i2 ≠ i4 := by intro h; have := congrArg Fin.val h; dsimp [i2, i4] at this; omega
      simp [norm5Q, i1, i2, i4, hn0, hn1, hn4, val]
    · have hn0 : i3 ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i3] at this; omega
      have hn1 : i3 ≠ i1 := by intro h; have := congrArg Fin.val h; dsimp [i1, i3] at this; omega
      have hn4 : i3 ≠ i4 := by intro h; have := congrArg Fin.val h; dsimp [i3, i4] at this; omega
      have hn2 : i3 ≠ i2 := by intro h; have := congrArg Fin.val h; dsimp [i2, i3] at this; omega
      have h14 : ¬(i3 = i1 ∨ i3 = i4) := fun h => h.elim hn1 hn4
      have h_eq : norm5Q i i3 = 3 := by
        dsimp only [norm5Q]
        change (if i3 = i then 0 else if i3 = i1 ∨ i3 = i4 then 1 else if i3 = i2 then 2 else 3) = 3
        rw [if_neg hn0, if_neg h14, if_neg hn2]
      rw [h_eq]
    · have hn0 : i4 ≠ i := by intro h; have := congrArg Fin.val h; dsimp [i4] at this; omega
      have h_eq : norm5Q i i4 = 1 := by
        dsimp only [norm5Q]
        change (if i4 = i then 0 else if i4 = i1 ∨ i4 = i4 then 1 else if i4 = i2 then 2 else 3) = 1
        rw [if_neg hn0, if_pos (Or.inr rfl)]
      rw [h_eq]
      exact hfQ.1
  intro x y
  rw [hfx x, hfx y]
  exact ⟨fun h => hval_inj _ _ h, fun h => congrArg val h⟩

private theorem norm5T_rev_eq_iff : ∀ i x y : Fin 5,
    (norm5T i x = norm5T i y) ↔
      (norm5T ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩
        ⟨(5 - x.val) % 5, Nat.mod_lt _ (by decide)⟩ =
       norm5T ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩
        ⟨(5 - y.val) % 5, Nat.mod_lt _ (by decide)⟩) := by decide

private theorem norm5Q_rev_eq_iff : ∀ i x y : Fin 5,
    (norm5Q i x = norm5Q i y) ↔
      (norm5Q ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩
        ⟨(5 - x.val) % 5, Nat.mod_lt _ (by decide)⟩ =
       norm5Q ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩
        ⟨(5 - y.val) % 5, Nat.mod_lt _ (by decide)⟩) := by decide

private theorem fin5_state5T_rev_eq_iff {i : Fin 5} {f g : Fin 5 → Color}
    (hf_adj : ∀ k : Fin 5, f ⟨(k.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ≠ f k)
    (hg_adj : ∀ k : Fin 5, g ⟨(k.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ≠ g k)
    (hfT : IsState5T i f)
    (hgT : IsState5T ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩ g) :
    ∀ x y : Fin 5, f x = f y ↔
      g ⟨(5 - x.val) % 5, Nat.mod_lt _ (by decide)⟩ =
      g ⟨(5 - y.val) % 5, Nat.mod_lt _ (by decide)⟩ := by
  intro x y
  rw [fin5_state5T_norm_eq hf_adj hfT x y,
    fin5_state5T_norm_eq hg_adj hgT]
  exact norm5T_rev_eq_iff i x y

private theorem fin5_state5Q_rev_eq_iff {i : Fin 5} {f g : Fin 5 → Color}
    (hf_adj : ∀ k : Fin 5, f ⟨(k.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ≠ f k)
    (hg_adj : ∀ k : Fin 5, g ⟨(k.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ ≠ g k)
    (hfQ : IsState5Q i f)
    (hgQ : IsState5Q ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩ g) :
    ∀ x y : Fin 5, f x = f y ↔
      g ⟨(5 - x.val) % 5, Nat.mod_lt _ (by decide)⟩ =
      g ⟨(5 - y.val) % 5, Nat.mod_lt _ (by decide)⟩ := by
  intro x y
  rw [fin5_state5Q_norm_eq hf_adj hfQ x y,
    fin5_state5Q_norm_eq hg_adj hgQ]
  exact norm5Q_rev_eq_iff i x y

private theorem glue_of_state5T_match {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (i : Fin 5)
    (colL : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring)
    (colR : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut.rev).FaceColoring)
    (hL : IsState5T i (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut colL))
    (hR : IsState5T ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩
      (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut.rev colR)) :
    False :=
  glue_of_cap_colorings darts h_mc cut colL colR
    (fin5_state5T_rev_eq_iff
      (capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) h_mc.is_bridgeless cut colL)
      (capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) h_mc.is_bridgeless cut.rev colR)
      hL hR)

private theorem glue_of_state5Q_match {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (i : Fin 5)
    (colL : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring)
    (colR : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut.rev).FaceColoring)
    (hL : IsState5Q i (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut colL))
    (hR : IsState5Q ⟨(5 - i.val) % 5, Nat.mod_lt _ (by decide)⟩
      (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut.rev colR)) :
    False :=
  glue_of_cap_colorings darts h_mc cut colL colR
    (fin5_state5Q_rev_eq_iff
      (capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) h_mc.is_bridgeless cut colL)
      (capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) h_mc.is_bridgeless cut.rev colR)
      hL hR)

private theorem capColoring_of_rot1_gen {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts)
    {k : Nat} (hk : 2 ≤ k) (cut : H.FaceCycleCut k)
    (col_rot : (FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut.rot1).FaceColoring) :
    ∃ col : (FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut).FaceColoring,
      ∀ i : Fin k,
        capBoundaryColors darts h_nd h_all h_planar h_conn cut col i =
          capBoundaryColors darts h_nd h_all h_planar h_conn cut.rot1 col_rot
            ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩ := by
  let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut
  let H_rot := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut.rot1
  let hspec := FaceCycleCut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_bridgeless cut
  let hspec_r := FaceCycleCut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_bridgeless cut.rot1
  let darts_cap := FaceCycleCut.capSingleVertexDarts darts cut
  let darts_rot := FaceCycleCut.capSingleVertexDarts darts cut.rot1
  let psi : H_cap.Dart → H_rot.Dart := fun x =>
    match x with
    | Sum.inl ⟨d, hd⟩ => Sum.inl ⟨d, (cut.rot1_DL_iff darts h_nd h_all h_planar h_conn d).mpr hd⟩
    | Sum.inr m => Sum.inr ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  have hmem_orb_next : ∀ (p : Perm H_cap.Dart) (y : H_cap.Dart),
      p.f y ∈ getOrbit p darts_cap.length y := by
    intro p y
    rw [capSingleVertex_beq_eq cut]
    exact (sameOrbit_iff_mem_getOrbit p darts_cap hspec.2.1 (Nat.le_refl _) y (p.f y)).mp ⟨1, rfl⟩
  have hmem_orb_rot : ∀ (y : H_rot.Dart) {u v : H_rot.Dart},
      u ∈ getOrbit H_rot.face darts_rot.length y →
      v ∈ getOrbit H_rot.face darts_rot.length y →
      SameOrbit H_rot.face u v := by
    intro y u v hu hv
    rw [capSingleVertex_beq_eq cut.rot1] at hu hv
    have hu_so := (sameOrbit_iff_mem_getOrbit H_rot.face darts_rot hspec_r.2.1 (Nat.le_refl _) y u).mpr hu
    have hv_so := (sameOrbit_iff_mem_getOrbit H_rot.face darts_rot hspec_r.2.1 (Nat.le_refl _) y v).mpr hv
    exact sameOrbit_trans H_rot.face
      (sameOrbit_symm_of_complete H_rot.face darts_rot hspec_r.2.1 hu_so) hv_so
  have hpsi_ring_orb : ∀ (m : Fin k) (z : H_cap.Dart),
      z ∈ getOrbit H_cap.face darts_cap.length (Sum.inr m) →
      psi z ∈ getOrbit H_rot.face darts_rot.length (psi (Sum.inr m)) := by
    intro m z hz
    let m' : Fin k := ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
    have hm'_succ : (⟨(m'.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = m := by
      apply Fin.ext; dsimp only [m']; exact mod_sub_one_add_one k m.val hk m.isLt
    rcases (hspec.2.2.2.2.2.2.2.2.2.2.2.1 m z).mp hz with rfl | ⟨d, hd, rfl, hd_arc⟩
    · rw [capSingleVertex_beq_eq cut.rot1]
      exact (sameOrbit_iff_mem_getOrbit H_rot.face darts_rot hspec_r.2.1 (Nat.le_refl _) _ _).mp ⟨0, rfl⟩
    · refine (hspec_r.2.2.2.2.2.2.2.2.2.2.2.1 m' (psi (Sum.inl ⟨d, hd⟩))).mpr (Or.inr ⟨d, _, rfl, ?_⟩)
      rw [hm'_succ]
      exact (cut.inArcL_rot1_iff darts h_nd h_all h_planar h_conn m d).mpr hd_arc
  have hpsi_face : ∀ x : H_cap.Dart, SameOrbit H_rot.face (psi x) (psi (H_cap.face.f x)) := by
    intro x
    have hfx_orb : H_cap.face.f x ∈ getOrbit H_cap.face darts_cap.length x := hmem_orb_next H_cap.face x
    rcases x with ⟨d, hd⟩ | m
    · by_cases h_arc : ∃ i : Fin k, cut.inArcL darts h_all i d
      · rcases h_arc with ⟨i, hi_arc⟩
        let m : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
        have hm_succ : (⟨(m.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = i := by
          apply Fin.ext; dsimp only [m]; exact mod_sub_one_add_one k i.val hk i.isLt
        have hx_in_orb : Sum.inl ⟨d, hd⟩ ∈ getOrbit H_cap.face darts_cap.length (Sum.inr m) :=
          (hspec.2.2.2.2.2.2.2.2.2.2.2.1 m (Sum.inl ⟨d, hd⟩)).mpr
            (Or.inr ⟨d, hd, rfl, by simpa [hm_succ] using hi_arc⟩)
        have hfx_in_orb : H_cap.face.f (Sum.inl ⟨d, hd⟩) ∈
            getOrbit H_cap.face darts_cap.length (Sum.inr m) := by
          rw [capSingleVertex_beq_eq cut] at hx_in_orb hfx_orb ⊢
          have hs1 := (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap hspec.2.1 (Nat.le_refl _) _ _).mpr hx_in_orb
          have hs2 := (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap hspec.2.1 (Nat.le_refl _) _ _).mpr hfx_orb
          exact (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap hspec.2.1 (Nat.le_refl _) _ _).mp
            (sameOrbit_trans H_cap.face hs1 hs2)
        exact hmem_orb_rot (psi (Sum.inr m)) (hpsi_ring_orb m _ hx_in_orb) (hpsi_ring_orb m _ hfx_in_orb)
      · have hnotf : ∀ i : Fin k, ¬SameOrbit H.face (cut.ringFace i) d := by
          intro i hso
          exact h_arc ⟨i, (cut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn i d).mpr ⟨hso, hd⟩⟩
        have hnotf_r : ∀ i : Fin k, ¬SameOrbit H.face (cut.rot1.ringFace i) d :=
          fun i hso => hnotf ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ hso
        obtain ⟨hfn, h_eq1⟩ := hspec.2.2.2.2.2.2.2.2.2.2.2.2 d hd hnotf
        obtain ⟨hfn_r, h_eq2⟩ := hspec_r.2.2.2.2.2.2.2.2.2.2.2.2 d
          ((cut.rot1_DL_iff darts h_nd h_all h_planar h_conn d).mpr hd) hnotf_r
        have hpeq : psi (H_cap.face.f (Sum.inl ⟨d, hd⟩)) = H_rot.face.f (psi (Sum.inl ⟨d, hd⟩)) := by
          rw [h_eq1]
          dsimp only [psi]
          rw [h_eq2]
        rw [hpeq]
        exact ⟨1, rfl⟩
    · refine hmem_orb_rot (psi (Sum.inr m)) ?_ (hpsi_ring_orb m _ hfx_orb)
      rw [capSingleVertex_beq_eq cut.rot1]
      exact (sameOrbit_iff_mem_getOrbit H_rot.face darts_rot hspec_r.2.1 (Nat.le_refl _) _ _).mp ⟨0, rfl⟩
  have hpsi_edge : ∀ x : H_cap.Dart, psi (H_cap.edge.f x) = H_rot.edge.f (psi x) := by
    intro x
    rcases x with ⟨d, hd⟩ | m
    · by_cases hcut : ∃ i : Fin k, d = cut.cutDart i
      · rcases hcut with ⟨i, rfl⟩
        have hed := (hspec.2.2.2.2.2.2.2.1 i).1
        have hd_rot : (Sum.inl ⟨cut.cutDart i, hd⟩ : H_cap.Dart) = Sum.inl ⟨cut.cutDart i,
            cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn (cut.cutDart_mem_inArcL darts h_all i)⟩ := rfl
        rw [hed]
        let i' : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
        have hcd_rot : cut.cutDart i = cut.rot1.cutDart i' := by
          dsimp [FaceCycleCut.rot1, i']
          congr 1; apply Fin.ext; dsimp only; exact (mod_sub_one_add_one k i.val hk i.isLt).symm
        have hed_r := (hspec_r.2.2.2.2.2.2.2.1 i').1
        have h_psi_eq : psi (Sum.inl ⟨cut.cutDart i, hd⟩) = Sum.inl ⟨cut.rot1.cutDart i',
            cut.rot1.inArcL_sub_DL darts h_nd h_all h_planar h_conn
              (cut.rot1.cutDart_mem_inArcL darts h_all i')⟩ := by
          dsimp only [psi]; congr 1; exact Subtype.ext hcd_rot
        rw [h_psi_eq, hed_r]
      · have hne : ∀ i : Fin k, d ≠ cut.cutDart i := fun i h => hcut ⟨i, h⟩
        have hne_r : ∀ i : Fin k, d ≠ cut.rot1.cutDart i := fun i h => hne ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ h
        obtain ⟨hdn, he1⟩ := hspec.2.2.2.2.2.2.2.2.1 d hd hne
        obtain ⟨hdn_r, he2⟩ := hspec_r.2.2.2.2.2.2.2.2.1 d
          ((cut.rot1_DL_iff darts h_nd h_all h_planar h_conn d).mpr hd) hne_r
        rw [he1]; dsimp only [psi]; rw [he2]
    · have hed := (hspec.2.2.2.2.2.2.2.1 m).2
      let m' : Fin k := ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
      have hcd_rot : cut.cutDart m = cut.rot1.cutDart m' := by
        dsimp [FaceCycleCut.rot1, m']
        congr 1; apply Fin.ext; dsimp only; exact (mod_sub_one_add_one k m.val hk m.isLt).symm
      rw [hed]
      have hed_r := (hspec_r.2.2.2.2.2.2.2.1 m').2
      dsimp only [psi]
      rw [hed_r]
      congr 1; exact Subtype.ext hcd_rot
  have hcol_face_so : ∀ u v : H_rot.Dart, SameOrbit H_rot.face u v → col_rot.color u = col_rot.color v := by
    intro u v ⟨n, hn⟩
    have hiter : ∀ m : Nat, col_rot.color u = col_rot.color (Perm.iter H_rot.face m u) := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Perm.iter_succ, col_rot.face_invariant, ih]
    rw [← hn]
    exact hiter n
  refine ⟨{
    color := fun x => col_rot.color (psi x)
    face_invariant := fun x => (hcol_face_so _ _ (hpsi_face x)).symm
    edge_proper := fun x => by rw [hpsi_edge x]; exact col_rot.edge_proper (psi x)
  }, ?_⟩
  intro i
  rfl

end TenStates5

section Birkhoff5Gadgets

private theorem sum_beq_eq_decEq {α β : Type} [DecidableEq α] [DecidableEq β]
    [bα : BEq α] [bβ : BEq β]
    (hα : bα = @instBEqOfDecidableEq α _) (hβ : bβ = @instBEqOfDecidableEq β _) :
    (@Sum.instBEq α β bα bβ : BEq (α ⊕ β)) = @instBEqOfDecidableEq (α ⊕ β) (@instDecidableEqSum α β _ _) := by
  have hfn : ∀ x y : α ⊕ β, (@Sum.instBEq α β bα bβ).beq x y =
      (@instBEqOfDecidableEq (α ⊕ β) (@instDecidableEqSum α β _ _)).beq x y := by
    intro x y
    cases x with
    | inl a1 =>
        cases y with
        | inl a2 =>
            change bα.beq a1 a2 = decide (Sum.inl a1 = (Sum.inl a2 : α ⊕ β))
            rw [hα]
            by_cases h : a1 = a2 <;> simp [h]
        | inr b2 => rfl
    | inr b1 =>
        cases y with
        | inl a2 => rfl
        | inr b2 =>
            change bβ.beq b1 b2 = decide (Sum.inr b1 = (Sum.inr b2 : α ⊕ β))
            rw [hβ]
            by_cases h : b1 = b2 <;> simp [h]
  exact congrArg BEq.mk (funext fun x => funext fun y => hfn x y)

private theorem coupleEdge_f_eval {D : Type} [DecidableEq D] (T : PermTriple D) (a b x : D) :
    (coupleEdge T a b).f.f x = T.f.f (if x = a then b else if x = b then a else x) := rfl

private theorem coupleEdge_f_left {D : Type} [DecidableEq D] (T : PermTriple D) (a b : D) :
    (coupleEdge T a b).f.f a = T.f.f b := by
  rw [coupleEdge_f_eval, if_pos rfl]

private theorem coupleEdge_f_right {D : Type} [DecidableEq D] (T : PermTriple D) {a b : D}
    (hab : b ≠ a) :
    (coupleEdge T a b).f.f b = T.f.f a := by
  rw [coupleEdge_f_eval, if_neg hab, if_pos rfl]

private theorem coupleEdge_f_of_ne {D : Type} [DecidableEq D] (T : PermTriple D) {a b x : D}
    (hxa : x ≠ a) (hxb : x ≠ b) :
    (coupleEdge T a b).f.f x = T.f.f x := by
  rw [coupleEdge_f_eval, if_neg hxa, if_neg hxb]

private theorem iter_eq_of_f_agree {D : Type} (p q : Perm D) (x : D) :
    ∀ n : Nat, (∀ k < n, p.f (Perm.iter q k x) = q.f (Perm.iter q k x)) →
      Perm.iter p n x = Perm.iter q n x
  | 0, _ => rfl
  | k + 1, h => by
      rw [Perm.iter_succ, Perm.iter_succ, iter_eq_of_f_agree p q x k (fun j hj => h j (Nat.lt_succ_of_lt hj))]
      exact h k (Nat.lt_succ_self k)

private theorem sameOrbit_of_f_agree_inv {D : Type} (tag : D → Nat) (p : Perm D)
    (hinv : ∀ x : D, tag (p.f x) = tag x) {x y : D} (h : SameOrbit p x y) :
    tag x = tag y := by
  rcases h with ⟨n, rfl⟩
  induction n with
  | zero => rfl
  | succ k ih => rw [Perm.iter_succ, hinv, ih]

private theorem TL_spec {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) :
    let dartsL : List { d : H.Dart // cut.capSingleVertex_DL d } :=
      predDarts cut.capSingleVertex_DL darts
    let TL := cut.capSingleVertex_TL
    dartsL.Nodup ∧ (∀ x, x ∈ dartsL) ∧ dartsL.length =
      (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length ∧
      dartsL.length ≤ darts.length ∧
      genusDeficit TL dartsL.length dartsL = 0 ∧
      countRelClasses (ReachEN TL.e TL.n) dartsL = 1 := by
  intro dartsL TL
  have h_unc := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hDL_e : ∀ d : H.Dart, cut.capSingleVertex_DL d ↔
      cut.capSingleVertex_DL (cut.uncoupleTriple.e.f d) := fun d =>
    ⟨fun hd => reachEN_trans _ _ hd ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩,
     fun hd => reachEN_trans _ _ hd (by
       have h := @WalkEN.step _ cut.uncoupleTriple.e cut.uncoupleTriple.n _ _ _
         (StepEN.e_bwd (cut.uncoupleTriple.e.f d)) (WalkEN.refl _)
       rw [cut.uncoupleTriple.e.left_inv d] at h
       exact ⟨h⟩)⟩
  have hDL_n : ∀ d : H.Dart, cut.capSingleVertex_DL d ↔
      cut.capSingleVertex_DL (cut.uncoupleTriple.n.f d) := fun d =>
    ⟨fun hd => reachEN_trans _ _ hd ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩,
     fun hd => reachEN_trans _ _ hd (by
       have h := @WalkEN.step _ cut.uncoupleTriple.e cut.uncoupleTriple.n _ _ _
         (StepEN.n_bwd (cut.uncoupleTriple.n.f d)) (WalkEN.refl _)
       rw [cut.uncoupleTriple.n.left_inv d] at h
       exact ⟨h⟩)⟩
  have hL_nd : dartsL.Nodup := nodup_predDarts cut.capSingleVertex_DL h_nd
  have hL_all : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d }, x ∈ dartsL :=
    fun x => (mem_predDarts_iff cut.capSingleVertex_DL darts x).mpr (h_all x.val)
  have hL_len : dartsL.length =
      (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length := by
    rw [← List.length_map (f := Subtype.val), map_predDarts cut.capSingleVertex_DL darts]
  have hL_le : dartsL.length ≤ darts.length := by
    rw [hL_len]; exact List.length_filter_le _ _
  have h_gen_le : genusDeficit TL dartsL.length dartsL ≤
      genusDeficit cut.uncoupleTriple darts.length darts :=
    genusDeficit_restrictTriple_le cut.uncoupleTriple darts.length dartsL.length
      darts h_nd h_all (Nat.le_refl _) cut.capSingleVertex_DL
      hDL_e hDL_n dartsL hL_nd hL_all (Nat.le_refl _)
  have h_gen_unc : genusDeficit cut.uncoupleTriple darts.length darts = 0 := h_unc.2.2.1
  have h_gen0 : genusDeficit TL dartsL.length dartsL = 0 :=
    Int.le_antisymm (h_gen_unc ▸ h_gen_le)
      (genusDeficit_nonneg TL dartsL hL_nd hL_all (Nat.le_refl _))
  have hne : dartsL ≠ [] := by
    intro hempty
    have ha0_mem : (⟨cut.cutDart ⟨0, by have := cut.hk; omega⟩, reachEN_refl _ _ _⟩ :
        { d : H.Dart // cut.capSingleVertex_DL d }) ∈ dartsL := hL_all _
    rw [hempty] at ha0_mem
    cases ha0_mem
  have h_c1 : countRelClasses (ReachEN TL.e TL.n) dartsL = 1 := by
    apply countRelClasses_eq_one_of_forall (ReachEN TL.e TL.n)
      ⟨cut.cutDart ⟨0, by have := cut.hk; omega⟩, reachEN_refl _ _ _⟩
    · intro x _
      exact (reachEN_restrictTriple_iff cut.uncoupleTriple.e cut.uncoupleTriple.n
        cut.capSingleVertex_DL hDL_e hDL_n
        ⟨cut.cutDart ⟨0, by have := cut.hk; omega⟩, reachEN_refl _ _ _⟩ x).mpr x.property
    · exact hne
    · intro x y hxy; exact reachEN_symm _ _ hxy
    · intro x y z hxy hyz; exact reachEN_trans _ _ hxy hyz
  exact ⟨hL_nd, hL_all, hL_len, hL_le, h_gen0, h_c1⟩

private theorem TL_f_val {H : Hypermap} [DecidableEq H.Dart] {k : Nat} (cut : H.FaceCycleCut k)
    (z : { d : H.Dart // cut.capSingleVertex_DL d }) :
    (cut.capSingleVertex_TL.f.f z).val = cut.uncoupleTriple.f.f z.val := rfl

private theorem TL_iter_val {H : Hypermap} [DecidableEq H.Dart] {k : Nat} (cut : H.FaceCycleCut k)
    (z : { d : H.Dart // cut.capSingleVertex_DL d }) (n : Nat) :
    (Perm.iter cut.capSingleVertex_TL.f n z).val = Perm.iter cut.uncoupleTriple.f n z.val := by
  induction n with
  | zero => rfl
  | succ m ih => rw [Perm.iter_succ, Perm.iter_succ, TL_f_val, ih]

private theorem TL_arc_segment {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (m : Nat) (hm : m < k) :
    let TL := cut.capSingleVertex_TL
    let a : Fin k → { d : H.Dart // cut.capSingleVertex_DL d } :=
      fun j => ⟨cut.cutDart j, cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn
        (cut.cutDart_mem_inArcL darts h_all j)⟩
    let p0 := cut.posL darts h_all m
    let p1 := cut.posL darts h_all (m + 1)
    let t := p1 - p0
    1 ≤ t ∧
    Perm.iter TL.f t (a ⟨m, hm⟩) = a ⟨(m + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ ∧
    (∀ r : Nat, 1 ≤ r → r ≤ t →
      cut.inArcL darts h_all ⟨(m + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
        (Perm.iter TL.f r (a ⟨m, hm⟩)).val) ∧
    (∀ (d : H.Dart) (hd : cut.inArcL darts h_all ⟨(m + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d),
      ∃ r : Nat, 1 ≤ r ∧ r ≤ t ∧
        Perm.iter TL.f r (a ⟨m, hm⟩) =
          ⟨d, cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn hd⟩) ∧
    (∀ r : Nat, 1 ≤ r → r < t → ∀ j : Fin k, Perm.iter TL.f r (a ⟨m, hm⟩) ≠ a j) := by
  intro TL a p0 p1 t
  have hk := cut.hk
  have hlt : p0 < p1 := cut.posL_strictMono darts h_all (Nat.lt_succ_self m)
  have ht1 : 1 ≤ t := by dsimp [t]; omega
  have hadd : p0 + t = p1 := by dsimp [t]; omega
  let a0 : { d : H.Dart // cut.capSingleVertex_DL d } := a ⟨0, by omega⟩
  have iter_am : ∀ r : Nat,
      (Perm.iter TL.f r (a ⟨m, hm⟩)).val = Perm.iter cut.uncoupleTriple.f (p0 + r) a0.val := by
    intro r
    rw [TL_iter_val]
    have hm_mod : (⟨m % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨m, hm⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hm)
    have h_p0 : Perm.iter cut.uncoupleTriple.f p0 a0.val = (a ⟨m, hm⟩).val := by
      simpa [a0, hm_mod] using cut.uncoupleTriple_iter_posL darts h_all m
    rw [← h_p0, Nat.add_comm, Perm.iter_add]
  have h_end : Perm.iter TL.f t (a ⟨m, hm⟩) =
      a ⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩ := by
    apply Subtype.ext
    rw [iter_am t, hadd]
    exact cut.uncoupleTriple_iter_posL darts h_all (m + 1)
  have h_fwd : ∀ r : Nat, 1 ≤ r → r ≤ t →
      cut.inArcL darts h_all ⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩
        (Perm.iter TL.f r (a ⟨m, hm⟩)).val := by
    intro r hr1 hrt
    refine (cut.inArcL_iff_posL_block darts h_all hm _).mpr ?_
    refine ⟨p0 + r, by omega, by omega, ?_⟩
    exact (iter_am r).symm
  have h_bwd : ∀ (d : H.Dart)
      (hd_arc : cut.inArcL darts h_all ⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩ d),
      ∃ r : Nat, 1 ≤ r ∧ r ≤ t ∧
        Perm.iter TL.f r (a ⟨m, hm⟩) =
          ⟨d, cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn hd_arc⟩ := by
    intro d hd_arc
    obtain ⟨q, hq_gt, hq_le, hq_eq⟩ := (cut.inArcL_iff_posL_block darts h_all hm d).mp hd_arc
    refine ⟨q - p0, by omega, by omega, ?_⟩
    apply Subtype.ext
    rw [iter_am (q - p0), show p0 + (q - p0) = q by omega]
    exact hq_eq
  have h_int_ne : ∀ r : Nat, 1 ≤ r → r < t → ∀ j : Fin k, Perm.iter TL.f r (a ⟨m, hm⟩) ≠ a j := by
    intro r hr1 hrt j heq
    have hval : Perm.iter cut.uncoupleTriple.f (p0 + r) a0.val = (a j).val := by
      rw [← iter_am r]; exact congrArg Subtype.val heq
    have hj_pos : Perm.iter cut.uncoupleTriple.f (cut.posL darts h_all j.val) a0.val = (a j).val := by
      have hm_eq : (⟨j.val % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
      simpa [a0, hm_eq] using cut.uncoupleTriple_iter_posL darts h_all j.val
    have h_orb_len : (getOrbit cut.uncoupleTriple.f darts.length a0.val).length =
        cut.posL darts h_all k :=
      cut.uncoupleTriple_posL_orbit_length darts h_all (Nat.le_refl _)
    have hp1_le_k : p1 ≤ cut.posL darts h_all k := by
      by_cases hm1 : m + 1 = k
      · rw [show p1 = cut.posL darts h_all k by simp [p1, hm1]]; exact Nat.le_refl _
      · exact Nat.le_of_lt (cut.posL_strictMono darts h_all (by omega))
    have hj_lt_k : cut.posL darts h_all j.val < cut.posL darts h_all k :=
      cut.posL_strictMono darts h_all j.isLt
    have heq_pos : p0 + r = cut.posL darts h_all j.val :=
      perm_iter_inj_of_lt_getOrbit_length cut.uncoupleTriple.f
        (by rw [h_orb_len]; omega) (by rw [h_orb_len]; exact hj_lt_k)
        (hval.trans hj_pos.symm)
    by_cases hjm : j.val ≤ m
    · have hle : cut.posL darts h_all j.val ≤ p0 := by
        by_cases heq_jm : j.val = m
        · simp [p0, heq_jm]
        · exact Nat.le_of_lt (cut.posL_strictMono darts h_all (by omega))
      omega
    · have hle : p1 ≤ cut.posL darts h_all j.val := by
        by_cases heq_jm : j.val = m + 1
        · simp [p1, heq_jm]
        · exact Nat.le_of_lt (cut.posL_strictMono darts h_all (by omega))
      omega
  exact ⟨ht1, h_end, h_fwd, h_bwd, h_int_ne⟩

private theorem TL_not_inArcL_f_closed {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {k : Nat} (cut : H.FaceCycleCut k)
    (x : { d : H.Dart // cut.capSingleVertex_DL d })
    (hx : ∀ i : Fin k, ¬cut.inArcL darts h_all i x.val) :
    ∀ i : Fin k, ¬cut.inArcL darts h_all i (cut.capSingleVertex_TL.f.f x).val := by
  intro i hi
  have hk := cut.hk
  have hmem : (cut.capSingleVertex_TL.f.f x).val ∈
      getOrbit cut.uncoupleTriple.f darts.length (cut.cutDart ⟨0, by omega⟩) :=
    (cut.uncoupleTriple_outerL_orbit darts h_all _).mpr ⟨i, hi⟩
  have hso1 : SameOrbit cut.uncoupleTriple.f
      (cut.cutDart ⟨0, by omega⟩) (cut.capSingleVertex_TL.f.f x).val :=
    (sameOrbit_iff_mem_getOrbit cut.uncoupleTriple.f darts h_all (Nat.le_refl _) _ _).mpr hmem
  rw [TL_f_val] at hso1
  have hx_so : SameOrbit cut.uncoupleTriple.f x.val (cut.uncoupleTriple.f.f x.val) := ⟨1, rfl⟩
  have hso2 : SameOrbit cut.uncoupleTriple.f (cut.cutDart ⟨0, by omega⟩) x.val :=
    sameOrbit_trans cut.uncoupleTriple.f hso1
      (sameOrbit_symm_of_complete cut.uncoupleTriple.f darts h_all hx_so)
  have hx_mem : x.val ∈ getOrbit cut.uncoupleTriple.f darts.length (cut.cutDart ⟨0, by omega⟩) :=
    (sameOrbit_iff_mem_getOrbit cut.uncoupleTriple.f darts h_all (Nat.le_refl _) _ _).mp hso2
  obtain ⟨j, hj⟩ := (cut.uncoupleTriple_outerL_orbit darts h_all _).mp hx_mem
  exact hx j hj

private theorem coupleEdge_preserve_outside {D β : Type} [DecidableEq D] [DecidableEq β]
    (P : D → Prop) (T : PermTriple (D ⊕ β)) (fD : D → D)
    (hagree : ∀ x : D, ¬P x → T.f.f (Sum.inl x) = Sum.inl (fD x))
    (u v : D ⊕ β) (hu : ∀ x : D, u = Sum.inl x → P x) (hv : ∀ x : D, v = Sum.inl x → P x) :
    ∀ x : D, ¬P x → (coupleEdge T u v).f.f (Sum.inl x) = Sum.inl (fD x) := by
  intro x hx
  have hxu : Sum.inl x ≠ u := fun heq => hx (hu x heq.symm)
  have hxv : Sum.inl x ≠ v := fun heq => hx (hv x heq.symm)
  rw [coupleEdge_f_of_ne T hxu hxv]
  exact hagree x hx

private theorem arc_transport {H : Hypermap} [DecidableEq H.Dart] {β : Type}
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k)
    (T : PermTriple ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ β))
    (hagree : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d },
      (∀ j : Fin k, x.val ≠ cut.cutDart j) →
      T.f.f (Sum.inl x) = Sum.inl (cut.capSingleVertex_TL.f.f x))
    (m : Nat) (hm : m < k) (s : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ β)
    (hs_start : T.f.f s = Sum.inl (cut.capSingleVertex_TL.f.f
      ⟨cut.cutDart ⟨m, hm⟩, cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn
        (cut.cutDart_mem_inArcL darts h_all ⟨m, hm⟩)⟩)) :
    let TL := cut.capSingleVertex_TL
    let am : { d : H.Dart // cut.capSingleVertex_DL d } :=
      ⟨cut.cutDart ⟨m, hm⟩, cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn
        (cut.cutDart_mem_inArcL darts h_all ⟨m, hm⟩)⟩
    let a_next : { d : H.Dart // cut.capSingleVertex_DL d } :=
      ⟨cut.cutDart ⟨(m + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩,
        cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn
          (cut.cutDart_mem_inArcL darts h_all _)⟩
    let t := cut.posL darts h_all (m + 1) - cut.posL darts h_all m
    (∀ r : Nat, 1 ≤ r → r ≤ t → Perm.iter T.f r s = Sum.inl (Perm.iter TL.f r am)) ∧
    SameOrbit T.f s (Sum.inl a_next) ∧
    (∀ d hd, cut.inArcL darts h_all ⟨(m + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d →
      SameOrbit T.f s (Sum.inl ⟨d, hd⟩)) := by
  intro TL am a_next t
  obtain ⟨ht1, h_end, _, h_bwd, h_int_ne⟩ := TL_arc_segment darts h_nd h_all h_planar h_conn cut m hm
  have hiter : ∀ r : Nat, 1 ≤ r → r ≤ t →
      Perm.iter T.f r s = Sum.inl (Perm.iter TL.f r am) := by
    intro r
    induction r with
    | zero => intro h0; omega
    | succ q ih =>
        intro _ hqt
        by_cases hq0 : q = 0
        · subst hq0
          simpa [Perm.iter_succ, Perm.iter_zero] using hs_start
        · have hq1 : 1 ≤ q := by omega
          have hq_lt : q < t := by omega
          rw [Perm.iter_succ, Perm.iter_succ, ih hq1 (Nat.le_of_lt hq_lt)]
          apply hagree
          intro j heq
          exact h_int_ne q hq1 hq_lt j (Subtype.ext heq)
  have hso_next : SameOrbit T.f s (Sum.inl a_next) := by
    refine ⟨t, ?_⟩
    rw [hiter t ht1 (Nat.le_refl _), h_end]
  have hso_arc : ∀ d hd, cut.inArcL darts h_all
      ⟨(m + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d →
      SameOrbit T.f s (Sum.inl ⟨d, hd⟩) := by
    intro d hd hd_arc
    obtain ⟨r, hr1, hrt, hr_eq⟩ := h_bwd d hd_arc
    refine ⟨r, ?_⟩
    rw [hiter r hr1 hrt, hr_eq]
  exact ⟨hiter, hso_next, hso_arc⟩

private theorem inArcL_unique_idx {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) {i j : Fin k} {d : H.Dart}
    (hi : cut.inArcL darts h_all i d) (hj : cut.inArcL darts h_all j d) : i = j := by
  have hsi : SameOrbit H.face (cut.ringFace i) d :=
    ((cut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn i d).mp hi).1
  have hsj : SameOrbit H.face (cut.ringFace j) d :=
    ((cut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn j d).mp hj).1
  exact Classical.byContradiction fun hne =>
    cut.h_diff i j hne (sameOrbit_trans H.face hsi (sameOrbit_symm_of_complete H.face darts h_all hsj))

private theorem capColoring_of_gadget {H : Hypermap} [DecidableEq H.Dart] {β : Type}
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts)
    (cut : H.FaceCycleCut 5)
    (H' : Hypermap)
    (toH' : ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ β) → H'.Dart)
    (h_edge_int : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      (∀ m : Fin 5, d ≠ cut.cutDart m) →
      ∃ hdn : cut.capSingleVertex_DL (H.edge.f d),
        H'.edge.f (toH' (Sum.inl ⟨d, hd⟩)) = toH' (Sum.inl ⟨H.edge.f d, hdn⟩))
    (h_face_int : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      (∀ i : Fin 5, ¬SameOrbit H.face (cut.ringFace i) d) →
      ∃ hfn : cut.capSingleVertex_DL (H.face.f d),
        H'.face.f (toH' (Sum.inl ⟨d, hd⟩)) = toH' (Sum.inl ⟨H.face.f d, hfn⟩))
    (h_face_ring : ∀ (m : Fin 5) (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      cut.inArcL darts h_all ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ d →
      SameOrbit H'.face
        (H'.edge.f (toH' (Sum.inl ⟨cut.cutDart m, cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn
          (cut.cutDart_mem_inArcL darts h_all m)⟩)))
        (toH' (Sum.inl ⟨d, hd⟩)))
    (col' : H'.FaceColoring) :
    ∃ col : (FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut).FaceColoring,
      (∀ d hd, col.color (Sum.inl ⟨d, hd⟩) = col'.color (toH' (Sum.inl ⟨d, hd⟩))) ∧
      (∀ m : Fin 5, col.color (Sum.inr m) = col'.color (H'.edge.f (toH' (Sum.inl ⟨cut.cutDart m,
        cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn (cut.cutDart_mem_inArcL darts h_all m)⟩)))) := by
  let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut
  let darts_cap := FaceCycleCut.capSingleVertexDarts darts cut
  let hspec := FaceCycleCut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_bridgeless cut
  let phi : H_cap.Dart → H'.Dart := fun x =>
    match x with
    | Sum.inl ⟨d, hd⟩ => toH' (Sum.inl ⟨d, hd⟩)
    | Sum.inr m => H'.edge.f (toH' (Sum.inl ⟨cut.cutDart m,
        cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn (cut.cutDart_mem_inArcL darts h_all m)⟩))
  have hcol_face_so : ∀ u v : H'.Dart, SameOrbit H'.face u v → col'.color u = col'.color v := by
    intro u v ⟨n, hn⟩
    have hiter : ∀ r : Nat, col'.color u = col'.color (Perm.iter H'.face r u) := by
      intro r
      induction r with
      | zero => rfl
      | succ r ih => rw [Perm.iter_succ, col'.face_invariant, ih]
    rw [← hn]; exact hiter n
  have hmem_orb_next : ∀ (y : H_cap.Dart), H_cap.face.f y ∈ getOrbit H_cap.face darts_cap.length y := by
    intro y
    rw [capSingleVertex_beq_eq cut]
    exact (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap hspec.2.1 (Nat.le_refl _) y (H_cap.face.f y)).mp ⟨1, rfl⟩
  have hphi_ring : ∀ (m : Fin 5) (z : H_cap.Dart),
      z ∈ getOrbit H_cap.face darts_cap.length (Sum.inr m) →
      SameOrbit H'.face (phi (Sum.inr m)) (phi z) := by
    intro m z hz
    rcases (hspec.2.2.2.2.2.2.2.2.2.2.2.1 m z).mp hz with rfl | ⟨d, hd, rfl, hd_arc⟩
    · exact ⟨0, rfl⟩
    · exact h_face_ring m d hd hd_arc
  have hface_inv : ∀ x : H_cap.Dart, col'.color (phi (H_cap.face.f x)) = col'.color (phi x) := by
    intro x
    have hfx_orb := hmem_orb_next x
    rcases x with ⟨d, hd⟩ | m
    · by_cases h_arc : ∃ i : Fin 5, cut.inArcL darts h_all i d
      · rcases h_arc with ⟨i, hi_arc⟩
        let m : Fin 5 := ⟨(i.val + 5 - 1) % 5, Nat.mod_lt _ (by decide)⟩
        have hm_succ : (⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i := by
          apply Fin.ext; dsimp only [m]; exact mod_sub_one_add_one 5 i.val (by decide) i.isLt
        have hx_in_orb : Sum.inl ⟨d, hd⟩ ∈ getOrbit H_cap.face darts_cap.length (Sum.inr m) :=
          (hspec.2.2.2.2.2.2.2.2.2.2.2.1 m (Sum.inl ⟨d, hd⟩)).mpr
            (Or.inr ⟨d, hd, rfl, by simpa [hm_succ] using hi_arc⟩)
        have hfx_in_orb : H_cap.face.f (Sum.inl ⟨d, hd⟩) ∈
            getOrbit H_cap.face darts_cap.length (Sum.inr m) := by
          rw [capSingleVertex_beq_eq cut] at hx_in_orb hfx_orb ⊢
          have hs1 := (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap hspec.2.1 (Nat.le_refl _) _ _).mpr hx_in_orb
          have hs2 := (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap hspec.2.1 (Nat.le_refl _) _ _).mpr hfx_orb
          exact (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap hspec.2.1 (Nat.le_refl _) _ _).mp
            (sameOrbit_trans H_cap.face hs1 hs2)
        have h1 := hcol_face_so _ _ (hphi_ring m _ hx_in_orb)
        have h2 := hcol_face_so _ _ (hphi_ring m _ hfx_in_orb)
        rw [← h1, ← h2]
      · have hnotf : ∀ i : Fin 5, ¬SameOrbit H.face (cut.ringFace i) d := fun i hso =>
          h_arc ⟨i, (cut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn i d).mpr ⟨hso, hd⟩⟩
        obtain ⟨hfn1, heq1⟩ := hspec.2.2.2.2.2.2.2.2.2.2.2.2 d hd hnotf
        obtain ⟨hfn2, heq2⟩ := h_face_int d hd hnotf
        have heq_sub : H_cap.face.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.face.f d, hfn2⟩ := by
          rw [heq1]
        rw [heq_sub]
        dsimp only [phi]
        rw [← heq2, col'.face_invariant]
    · have h1 := hcol_face_so _ _ (hphi_ring m _ hfx_orb)
      exact h1.symm
  have hedge_prop : ∀ x : H_cap.Dart, col'.color (phi (H_cap.edge.f x)) ≠ col'.color (phi x) := by
    intro x
    rcases x with ⟨d, hd⟩ | m
    · by_cases hcut : ∃ m : Fin 5, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        have hed := (hspec.2.2.2.2.2.2.2.1 m).1
        have hinl_eq : (Sum.inl ⟨cut.cutDart m, hd⟩ : H_cap.Dart) = Sum.inl ⟨cut.cutDart m,
            cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn (cut.cutDart_mem_inArcL darts h_all m)⟩ := rfl
        rw [hinl_eq, hed]
        dsimp only [phi]
        exact col'.edge_proper _
      · have hne : ∀ m : Fin 5, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
        obtain ⟨hdn1, he1⟩ := hspec.2.2.2.2.2.2.2.2.1 d hd hne
        obtain ⟨hdn2, he2⟩ := h_edge_int d hd hne
        have he1' : H_cap.edge.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn2⟩ := by
          rw [he1]
        rw [he1']
        dsimp only [phi]
        rw [← he2]
        exact col'.edge_proper _
    · have hed := (hspec.2.2.2.2.2.2.2.1 m).2
      rw [hed]
      dsimp only [phi]
      have h_ne := col'.edge_proper (H'.edge.f (toH' (Sum.inl ⟨cut.cutDart m,
        cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn (cut.cutDart_mem_inArcL darts h_all m)⟩)))
      rw [H'.edge_edge] at h_ne
      exact h_ne
  refine ⟨{ color := fun x => col'.color (phi x), face_invariant := hface_inv, edge_proper := hedge_prop }, ?_, ?_⟩
  · intro d hd; rfl
  · intro m; rfl

private theorem nodup_finRange_b5 (m : Nat) : (List.finRange m).Nodup :=
  List.pairwise_iff_getElem.mpr fun i j hi hj hij heq => by
    simp only [List.getElem_finRange] at heq
    have hv := congrArg Fin.val heq
    dsimp at hv
    omega

private def pent5N : Perm (Fin 15) where
  f x := ⟨(x.val / 3) * 3 + (x.val % 3 + 1) % 3, by omega⟩
  inv x := ⟨(x.val / 3) * 3 + (x.val % 3 + 2) % 3, by omega⟩
  left_inv x := by revert x; decide
  right_inv x := by revert x; decide

private def pent5Base : PermTriple (Fin 15) where
  e := (permId : Perm (Fin 15))
  n := pent5N
  f := pent5N.symm
  enf_id x := pent5N.right_inv x

private def pent5E : Perm (Fin 15) where
  f x := match x.val % 3 with
    | 0 => x
    | 1 => ⟨((x.val / 3 + 1) % 5) * 3 + 2, by omega⟩
    | _ => ⟨((x.val / 3 + 4) % 5) * 3 + 1, by omega⟩
  inv x := match x.val % 3 with
    | 0 => x
    | 1 => ⟨((x.val / 3 + 1) % 5) * 3 + 2, by omega⟩
    | _ => ⟨((x.val / 3 + 4) % 5) * 3 + 1, by omega⟩
  left_inv x := by revert x; decide
  right_inv x := by revert x; decide

private def pent5F : Perm (Fin 15) where
  f x := pent5N.inv (pent5E.inv x)
  inv x := pent5E.f (pent5N.f x)
  left_inv x := by simp [pent5N.right_inv, pent5E.right_inv]
  right_inv x := by simp [pent5E.left_inv, pent5N.left_inv]

private def pent5Triple : PermTriple (Fin 15) where
  e := pent5E
  n := pent5N
  f := pent5F
  enf_id x := by simp [pent5F, pent5N.right_inv, pent5E.right_inv]

private def pent5Step : Nat → PermTriple (Fin 15)
  | 0 => pent5Base
  | k + 1 => coupleEdge (pent5Step k)
      ⟨3 * (k % 5) + 1, by omega⟩ ⟨3 * ((k + 1) % 5) + 2, by omega⟩

private theorem reachEN_preserves_bool {D : Type} (e n : Perm D) (S : D → Bool)
    (he : ∀ x, S (e.f x) = S x) (hn : ∀ x, S (n.f x) = S x)
    (he_inv : ∀ x, e.inv x = e.f x) :
    ∀ {x y : D}, ReachEN e n x y → S x = S y := by
  have he_i : ∀ x, S (e.inv x) = S x := fun x => by rw [he_inv]; exact he x
  have hn_i : ∀ x, S (n.inv x) = S x := fun x => by
    have h := hn (n.inv x)
    rw [n.right_inv] at h
    exact h.symm
  rintro x y ⟨w⟩
  induction w with
  | refl => rfl
  | step s _ ih =>
      cases s with
      | e_fwd => exact (he _).symm.trans ih
      | e_bwd => exact (he_i _).symm.trans ih
      | n_fwd => exact (hn _).symm.trans ih
      | n_bwd => exact (hn_i _).symm.trans ih

private theorem pent5Step_e_invol : ∀ (k : Fin 5) (x : Fin 15),
    (pent5Step k.val).e.f ((pent5Step k.val).e.f x) = x := by
  decide

private theorem pent5Step_couple_step (k : Nat) (hk5 : k < 5)
    (he_fix1 : (pent5Step k).e.f ⟨3 * (k % 5) + 1, by omega⟩ = ⟨3 * (k % 5) + 1, by omega⟩)
    (he_fix2 : (pent5Step k).e.f ⟨3 * ((k + 1) % 5) + 2, by omega⟩ = ⟨3 * ((k + 1) % 5) + 2, by omega⟩)
    (hS : ∀ x : Fin 15,
      decide (((pent5Step k).e.f x).val / 3 ≤ k) = decide (x.val / 3 ≤ k))
    (hnS : ∀ x : Fin 15,
      decide (((pent5Step k).n.f x).val / 3 ≤ k) = decide (x.val / 3 ≤ k))
    (hk_diff : decide (((⟨3 * (k % 5) + 1, by omega⟩ : Fin 15).val / 3) ≤ k) ≠
      decide (((⟨3 * ((k + 1) % 5) + 2, by omega⟩ : Fin 15).val / 3) ≤ k))
    (h_gen : genusDeficit (pent5Step k) 15 (List.finRange 15) = 0) :
    genusDeficit (pent5Step (k + 1)) 15 (List.finRange 15) = 0 := by
  have he_inv : ∀ x : Fin 15, (pent5Step k).e.inv x = (pent5Step k).e.f x := by
    intro x
    have h := pent5Step_e_invol ⟨k, hk5⟩ ((pent5Step k).e.inv x)
    rw [(pent5Step k).e.right_inv] at h
    exact h.symm
  have h_not : ¬ ReachEN (pent5Step k).e (pent5Step k).n
      ⟨3 * (k % 5) + 1, by omega⟩ ⟨3 * ((k + 1) % 5) + 2, by omega⟩ := by
    intro hreach
    exact hk_diff (reachEN_preserves_bool _ _ (fun x : Fin 15 => decide (x.val / 3 ≤ k))
      hS hnS he_inv hreach)
  have hc := coupleEdge_diff (pent5Step k) (List.finRange 15)
    (fun x => List.mem_finRange x) (fuel := 15) (by simp [List.length_finRange]) he_fix1 he_fix2 h_not
  rw [← h_gen]
  exact hc.2.2.2.2.2.2.2

private theorem pent5Triple_spec :
    let darts := List.finRange 15
    genusDeficit pent5Triple 15 darts = 0 ∧
    countRelClasses (ReachEN pent5Triple.e pent5Triple.n) darts = 1 ∧
    (∀ x : Fin 15, pent5Triple.e.f (pent5Triple.e.f x) = x) := by
  intro darts
  have h0 : genusDeficit (pent5Step 0) 15 darts = 0 :=
    genusDeficit_eq_zero_of_edge_id pent5Base (fun _ => rfl) darts (nodup_finRange_b5 15)
      (fun x => List.mem_finRange x) (by simp [darts, List.length_finRange])
  have h1 : genusDeficit (pent5Step 1) 15 darts = 0 :=
    pent5Step_couple_step 0 (by decide) rfl rfl (by decide) (by decide) (by decide) h0
  have h2 : genusDeficit (pent5Step 2) 15 darts = 0 :=
    pent5Step_couple_step 1 (by decide) rfl rfl (by decide) (by decide) (by decide) h1
  have h3 : genusDeficit (pent5Step 3) 15 darts = 0 :=
    pent5Step_couple_step 2 (by decide) rfl rfl (by decide) (by decide) (by decide) h2
  have h4 : genusDeficit (pent5Step 4) 15 darts = 0 :=
    pent5Step_couple_step 3 (by decide) rfl rfl (by decide) (by decide) (by decide) h3
  have horb4 : (⟨2, by decide⟩ : Fin 15) ∈ getOrbit (pent5Step 4).f 15 ⟨13, by decide⟩ := by
    have s1 : (pent5Step 4).f.f ⟨13, by decide⟩ = ⟨12, by decide⟩ := by decide
    have s2 : (pent5Step 4).f.f ⟨12, by decide⟩ = ⟨14, by decide⟩ := by decide
    have s3 : (pent5Step 4).f.f ⟨14, by decide⟩ = ⟨9, by decide⟩ := by decide
    have s4 : (pent5Step 4).f.f ⟨9, by decide⟩ = ⟨11, by decide⟩ := by decide
    have s5 : (pent5Step 4).f.f ⟨11, by decide⟩ = ⟨6, by decide⟩ := by decide
    have s6 : (pent5Step 4).f.f ⟨6, by decide⟩ = ⟨8, by decide⟩ := by decide
    have s7 : (pent5Step 4).f.f ⟨8, by decide⟩ = ⟨3, by decide⟩ := by decide
    have s8 : (pent5Step 4).f.f ⟨3, by decide⟩ = ⟨5, by decide⟩ := by decide
    have s9 : (pent5Step 4).f.f ⟨5, by decide⟩ = ⟨0, by decide⟩ := by decide
    have s10 : (pent5Step 4).f.f ⟨0, by decide⟩ = ⟨2, by decide⟩ := by decide
    have hiter : Perm.iter (pent5Step 4).f 10 ⟨13, by decide⟩ = ⟨2, by decide⟩ := by
      simp only [Perm.iter_succ, Perm.iter_zero, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
    exact (sameOrbit_iff_mem_getOrbit (pent5Step 4).f darts (fun x => List.mem_finRange x)
      (by simp [darts, List.length_finRange]) ⟨13, by decide⟩ ⟨2, by decide⟩).mp ⟨10, hiter⟩
  have h5_sf := coupleEdge_sameFace (pent5Step 4) darts (fun x => List.mem_finRange x)
    (by simp [darts, List.length_finRange])
    (rfl : (pent5Step 4).e.f ⟨13, by decide⟩ = ⟨13, by decide⟩)
    (rfl : (pent5Step 4).e.f ⟨2, by decide⟩ = ⟨2, by decide⟩)
    (by decide) horb4
  have h5 : genusDeficit (pent5Step 5) 15 darts = 0 := by
    change genusDeficit (coupleEdge (pent5Step 4) ⟨13, by decide⟩ ⟨2, by decide⟩) 15 darts = 0
    rw [h5_sf.2.2.2.2.2, h4]
  have heq5 : pent5Triple = pent5Step 5 := by
    apply permTriple_eq_of_f_eq
    · intro x; revert x; decide
    · intro x; revert x; decide
    · intro x; revert x; decide
  have h_gen : genusDeficit pent5Triple 15 darts = 0 := by rw [heq5]; exact h5
  have h_reach : ∀ x : Fin 15, ReachEN pent5Triple.e pent5Triple.n ⟨0, by decide⟩ x := by
    have hn0 : ∀ i : Fin 5, pent5Triple.n.f ⟨3 * i.val, by omega⟩ = ⟨3 * i.val + 1, by omega⟩ := by
      intro i; revert i; decide
    have hn1 : ∀ i : Fin 5, pent5Triple.n.f ⟨3 * i.val + 1, by omega⟩ = ⟨3 * i.val + 2, by omega⟩ := by
      intro i; revert i; decide
    have he1 : ∀ i : Fin 5, pent5Triple.e.f ⟨3 * i.val + 1, by omega⟩ =
        ⟨3 * ((i.val + 1) % 5) + 2, by omega⟩ := by
      intro i; revert i; decide
    have htri : ∀ i : Fin 5,
        ReachEN pent5Triple.e pent5Triple.n ⟨3 * i.val, by omega⟩ ⟨3 * i.val + 1, by omega⟩ ∧
        ReachEN pent5Triple.e pent5Triple.n ⟨3 * i.val + 1, by omega⟩ ⟨3 * i.val + 2, by omega⟩ := by
      intro i
      constructor
      · rw [← hn0 i]; exact ⟨WalkEN.step (StepEN.n_fwd _) (WalkEN.refl _)⟩
      · rw [← hn1 i]; exact ⟨WalkEN.step (StepEN.n_fwd _) (WalkEN.refl _)⟩
    have hedge : ∀ i : Fin 5,
        ReachEN pent5Triple.e pent5Triple.n ⟨3 * i.val + 1, by omega⟩
          ⟨3 * ((i.val + 1) % 5) + 2, by omega⟩ := by
      intro i; rw [← he1 i]; exact ⟨WalkEN.step (StepEN.e_fwd _) (WalkEN.refl _)⟩
    have htri_all : ∀ (i : Fin 5) (r : Fin 3),
        ReachEN pent5Triple.e pent5Triple.n ⟨3 * i.val, by omega⟩ ⟨3 * i.val + r.val, by omega⟩ := by
      intro i ⟨rv, hr⟩
      rcases (by omega : rv = 0 ∨ rv = 1 ∨ rv = 2) with rfl | rfl | rfl
      · exact reachEN_refl _ _ _
      · exact (htri i).1
      · exact reachEN_trans _ _ (htri i).1 (htri i).2
    have h_u0_u : ∀ i : Fin 5, ReachEN pent5Triple.e pent5Triple.n ⟨0, by decide⟩ ⟨3 * i.val, by omega⟩ := by
      have hs : ∀ m : Nat, (hm : m < 5) →
          ReachEN pent5Triple.e pent5Triple.n ⟨3 * m, by omega⟩
            ⟨3 * ((m + 1) % 5), by have := Nat.mod_lt (m + 1) (by decide : 0 < 5); omega⟩ := by
        intro m hm
        let i : Fin 5 := ⟨m, hm⟩
        let i1 : Fin 5 := ⟨(m + 1) % 5, Nat.mod_lt _ (by decide)⟩
        have h_12 := hedge i
        have h_21 : ReachEN pent5Triple.e pent5Triple.n ⟨3 * i1.val + 2, by omega⟩ ⟨3 * i1.val, by omega⟩ := by
          have := reachEN_symm _ _ (htri_all i1 ⟨2, by decide⟩)
          simpa using this
        exact reachEN_trans _ _ (htri i).1 (reachEN_trans _ _ h_12 h_21)
      have h01 := hs 0 (by decide)
      have h12 := hs 1 (by decide)
      have h23 := hs 2 (by decide)
      have h34 := hs 3 (by decide)
      intro ⟨iv, hi⟩
      rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4) with rfl | rfl | rfl | rfl | rfl
      · exact reachEN_refl _ _ _
      · exact h01
      · exact reachEN_trans _ _ h01 h12
      · exact reachEN_trans _ _ (reachEN_trans _ _ h01 h12) h23
      · exact reachEN_trans _ _ (reachEN_trans _ _ (reachEN_trans _ _ h01 h12) h23) h34
    intro x
    let i : Fin 5 := ⟨x.val / 3, by omega⟩
    let r : Fin 3 := ⟨x.val % 3, by omega⟩
    have hx_eq : x = ⟨3 * i.val + r.val, by omega⟩ := Fin.ext (by dsimp [i, r]; omega)
    rw [hx_eq]
    exact reachEN_trans _ _ (h_u0_u i) (htri_all i r)
  have h_c1 : countRelClasses (ReachEN pent5Triple.e pent5Triple.n) darts = 1 :=
    countRelClasses_eq_one_of_forall _ ⟨0, by decide⟩ (fun x _ => h_reach x)
      (by decide : List.finRange 15 ≠ [])
      (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
  have h_invol : ∀ x : Fin 15, pent5Triple.e.f (pent5Triple.e.f x) = x := by
    intro x; revert x; decide
  exact ⟨h_gen, h_c1, h_invol⟩

private def pent5U (m : Fin 5) : Fin 15 := ⟨3 * m.val, by omega⟩
private def pent5V (m : Fin 5) : Fin 15 := ⟨3 * m.val + 1, by omega⟩
private def pent5W (m : Fin 5) : Fin 15 := ⟨3 * m.val + 2, by omega⟩

private theorem pent5U_fix : ∀ m : Fin 5, pent5Triple.e.f (pent5U m) = pent5U m := by decide
private theorem pent5U_inj : ∀ i j : Fin 5, pent5U i = pent5U j → i = j := by decide
private theorem pent5U_w : ∀ m : Fin 5, pent5Triple.f.f (pent5U m) = pent5W m := by decide
private theorem pent5W_u :
    ∀ m : Fin 5, pent5Triple.f.f (pent5W m) = pent5U ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ := by
  decide
private theorem pent5V_v :
    ∀ m : Fin 5, pent5Triple.f.f (pent5V m) = pent5V ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ := by
  decide
private theorem pent5_e_vw :
    ∀ m : Fin 5, pent5Triple.e.f (pent5V m) = pent5W ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ := by
  decide
private theorem pent5_e_wv :
    ∀ m : Fin 5, pent5Triple.e.f (pent5W m) = pent5V ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ := by
  decide
private theorem pent5_e_mod3 : ∀ w : Fin 15, pent5Triple.e.f w ≠ w ∨ w.val % 3 = 0 := by decide

private noncomputable def pent5Seq {D : Type} (inst : DecidableEq (D ⊕ Fin 15))
    (TL : PermTriple D) (a : Fin 5 → D) : Nat → PermTriple (D ⊕ Fin 15)
  | 0 => sumTriple TL pent5Triple
  | k + 1 =>
      if hk : k < 5 then
        @coupleEdge (D ⊕ Fin 15) inst (pent5Seq inst TL a k) (Sum.inl (a ⟨k, hk⟩)) (Sum.inr (pent5U ⟨k, hk⟩))
      else pent5Seq inst TL a k

private theorem pent5Seq_succ_lt {D : Type} (inst : DecidableEq (D ⊕ Fin 15))
    (TL : PermTriple D) (a : Fin 5 → D) {k : Nat} (hk : k < 5) :
    pent5Seq inst TL a (k + 1) =
      @coupleEdge (D ⊕ Fin 15) inst (pent5Seq inst TL a k) (Sum.inl (a ⟨k, hk⟩)) (Sum.inr (pent5U ⟨k, hk⟩)) := by
  dsimp [pent5Seq]; rw [dif_pos hk]

private theorem pent5Seq_succ_ge {D : Type} (inst : DecidableEq (D ⊕ Fin 15))
    (TL : PermTriple D) (a : Fin 5 → D) {k : Nat} (hk : ¬ k < 5) :
    pent5Seq inst TL a (k + 1) = pent5Seq inst TL a k := by
  dsimp [pent5Seq]; rw [dif_neg hk]

theorem cap5_pentagon_realizable {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5)
    (h21R : 21 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) :
    ∃ i : Fin 5, ∃ col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
      h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState5T i (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut col) := by
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_unc := uncoupleCycle_two_components H darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
  obtain ⟨_, _, _, _, _, _, h_disjLR, h_cutLR, h_cut_fix, h_unc_ext, _, _, _⟩ := h_unc
  have hDL_e : ∀ d : H.Dart, cut.capSingleVertex_DL d →
      cut.capSingleVertex_DL (cut.uncoupleTriple.e.f d) :=
    fun d hd => reachEN_trans _ _ hd ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩
  let TL := cut.capSingleVertex_TL
  let dartsL := predDarts cut.capSingleVertex_DL darts
  obtain ⟨hL_nd, hL_all, hL_len, _, hL_gen, _⟩ :=
    TL_spec darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
  let darts5 := List.finRange 15
  obtain ⟨h5_gen, _, h5_invol⟩ := pent5Triple_spec
  let a : Fin 5 → { d : H.Dart // cut.capSingleVertex_DL d } :=
    fun m => ⟨cut.cutDart m, cut.inArcL_sub_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
      (cut.cutDart_mem_inArcL darts h_mc.complete m)⟩
  let uFin : Fin 5 → Fin 15 := fun m => ⟨3 * m.val, by omega⟩
  let vFin : Fin 5 → Fin 15 := fun m => ⟨3 * m.val + 1, by omega⟩
  let wFin : Fin 5 → Fin 15 := fun m => ⟨3 * m.val + 2, by omega⟩
  let D5 := { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin 15
  let instDecD5 : DecidableEq D5 := @instDecidableEqSum _ _ _ _
  let T0 : PermTriple D5 := sumTriple TL pent5Triple
  let pairA : Fin 5 → D5 := fun m => Sum.inl (a m)
  let pairU : Fin 5 → D5 := fun m => Sum.inr (uFin m)
  let Tseq : Nat → PermTriple D5 := pent5Seq instDecD5 TL a
  let T5 := Tseq 5
  have hsum := sumTriple_spec TL pent5Triple dartsL hL_nd hL_all darts5
    (nodup_finRange_b5 15) (fun x => List.mem_finRange x) (Nat.le_refl _)
  let dartsU : List D5 := dartsL.map Sum.inl ++ darts5.map Sum.inr
  have hU_nd : dartsU.Nodup := hsum.1
  have hU_all : ∀ z : D5, z ∈ dartsU := hsum.2.1
  have hU_len : dartsU.length = dartsL.length + 15 := by
    simp [dartsU, darts5, List.length_finRange]
  have hsum_gen : genusDeficit T0 dartsU.length dartsU = 0 := by
    have hlen : dartsL.length + darts5.length = dartsU.length := hU_len.symm
    have h_f0 := hsum.2.2.1
    rw [hlen] at h_f0
    have h_f1 : genusDeficit TL dartsU.length dartsL = genusDeficit TL dartsL.length dartsL :=
      genusDeficit_eq_of_complete TL dartsL dartsL hL_nd hL_all hL_nd hL_all (by omega) (Nat.le_refl _)
    have h_f2 : genusDeficit pent5Triple dartsU.length darts5 = genusDeficit pent5Triple 15 darts5 :=
      genusDeficit_eq_of_complete pent5Triple darts5 darts5
        (nodup_finRange_b5 15) (fun x => List.mem_finRange x)
        (nodup_finRange_b5 15) (fun x => List.mem_finRange x)
        (by simp [dartsU, darts5, List.length_finRange]) (by simp [darts5, List.length_finRange])
    change genusDeficit (sumTriple TL pent5Triple) dartsU.length dartsU = 0
    rw [h_f0, h_f1, h_f2, hL_gen, h5_gen]
    rfl
  have ha_fix_TL : ∀ m : Fin 5, TL.e.f (a m) = a m := by
    intro m
    apply Subtype.ext
    exact (h_cut_fix m).1
  have hu_fix_5 : ∀ m : Fin 5, pent5Triple.e.f (uFin m) = uFin m := pent5U_fix
  have ha_inj : ∀ i j : Fin 5, a i = a j → i = j := by
    intro i j heq
    exact Classical.byContradiction fun hne => cutDart_ne_of_ne darts h_mc cut hne (congrArg Subtype.val heq)
  have hu_inj : ∀ i j : Fin 5, uFin i = uFin j → i = j := pent5U_inj
  have hpent_u_w : ∀ m : Fin 5, pent5Triple.f.f (uFin m) = wFin m := pent5U_w
  have hpent_w_u : ∀ m : Fin 5, pent5Triple.f.f (wFin m) = uFin ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ :=
    pent5W_u
  have hpent_v_v : ∀ m : Fin 5, pent5Triple.f.f (vFin m) = vFin ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ :=
    pent5V_v
  have hTseq_e : ∀ k : Nat, k ≤ 5 →
      (∀ x : D5, (Tseq k).e.f ((Tseq k).e.f x) = x) ∧
      (∀ j : Fin 5, k ≤ j.val → (Tseq k).e.f (pairA j) = pairA j ∧ (Tseq k).e.f (pairU j) = pairU j) ∧
      (∀ j : Fin 5, j.val < k → (Tseq k).e.f (pairA j) = pairU j ∧ (Tseq k).e.f (pairU j) = pairA j) := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨?_, ?_, fun j hj => by omega⟩
        · intro x
          cases x with
          | inl d =>
              exact congrArg Sum.inl (Subtype.ext ((uncoupleCycle_two_components H darts h_mc.nodup
                h_mc.complete h_mc.is_planar h_conn cut).2.1 d.val))
          | inr y => exact congrArg Sum.inr (h5_invol y)
        · intro j _
          exact ⟨congrArg Sum.inl (ha_fix_TL j), congrArg Sum.inr (hu_fix_5 j)⟩
    | succ k ih =>
        intro hk5
        have hk5_lt : k < 5 := by omega
        obtain ⟨h_inv, h_ge, h_lt⟩ := ih (by omega)
        have h_eq : Tseq (k + 1) = coupleEdge (Tseq k) (pairA ⟨k, hk5_lt⟩) (pairU ⟨k, hk5_lt⟩) :=
          pent5Seq_succ_lt instDecD5 TL a hk5_lt
        have ha_k : (Tseq k).e.f (pairA ⟨k, hk5_lt⟩) = pairA ⟨k, hk5_lt⟩ := (h_ge ⟨k, hk5_lt⟩ (Nat.le_refl _)).1
        have hu_k : (Tseq k).e.f (pairU ⟨k, hk5_lt⟩) = pairU ⟨k, hk5_lt⟩ := (h_ge ⟨k, hk5_lt⟩ (Nat.le_refl _)).2
        rw [h_eq]
        refine ⟨coupleEdge_edge_invol (Tseq k) h_inv ha_k hu_k, ?_, ?_⟩
        · intro j hj
          have hne_a : pairA j ≠ pairA ⟨k, hk5_lt⟩ := fun h => by
            have := congrArg Fin.val (ha_inj _ _ (Sum.inl.inj h)); dsimp at this; omega
          have hne_u : pairU j ≠ pairU ⟨k, hk5_lt⟩ := fun h => by
            have := congrArg Fin.val (hu_inj _ _ (Sum.inr.inj h)); dsimp at this; omega
          constructor
          · rw [coupleEdge_e_eval (Tseq k) ha_k hu_k, if_neg hne_a, if_neg (by simp [pairA, pairU])]
            exact (h_ge j (by omega)).1
          · rw [coupleEdge_e_eval (Tseq k) ha_k hu_k, if_neg (by simp [pairA, pairU]), if_neg hne_u]
            exact (h_ge j (by omega)).2
        · intro j hj
          by_cases hjk : j.val = k
          · have hjeq : j = ⟨k, hk5_lt⟩ := Fin.ext hjk
            subst hjeq
            exact ⟨coupleEdge_e_left (Tseq k) ha_k hu_k, coupleEdge_e_right (Tseq k) ha_k hu_k⟩
          · have hj_lt : j.val < k := by omega
            have hne_aj : pairA j ≠ pairA ⟨k, hk5_lt⟩ := fun h => by
              have := congrArg Fin.val (ha_inj _ _ (Sum.inl.inj h)); dsimp at this; omega
            have hne_uj : pairU j ≠ pairU ⟨k, hk5_lt⟩ := fun h => by
              have := congrArg Fin.val (hu_inj _ _ (Sum.inr.inj h)); dsimp at this; omega
            constructor
            · rw [coupleEdge_e_eval (Tseq k) ha_k hu_k, if_neg hne_aj, if_neg (by simp [pairA, pairU])]
              exact (h_lt j hj_lt).1
            · rw [coupleEdge_e_eval (Tseq k) ha_k hu_k, if_neg (by simp [pairA, pairU]), if_neg hne_uj]
              exact (h_lt j hj_lt).2
  have hTseq_f_agree : ∀ k : Nat, ∀ x : { d : H.Dart // cut.capSingleVertex_DL d },
      (∀ j : Fin 5, x.val ≠ cut.cutDart j) →
      (Tseq k).f.f (Sum.inl x) = Sum.inl (TL.f.f x) := by
    intro k
    induction k with
    | zero => intro x _; rfl
    | succ k ih =>
        intro x hx
        by_cases hk5 : k < 5
        · have h_eq : Tseq (k + 1) = coupleEdge (Tseq k) (pairA ⟨k, hk5⟩) (pairU ⟨k, hk5⟩) :=
            pent5Seq_succ_lt instDecD5 TL a hk5
          rw [h_eq, coupleEdge_f_of_ne (Tseq k)
            (fun h => hx ⟨k, hk5⟩ (congrArg Subtype.val (Sum.inl.inj h)))
            (by simp [pairU])]
          exact ih x hx
        · dsimp only [Tseq]; rw [pent5Seq_succ_ge instDecD5 TL a hk5]; exact ih x hx
  have hTseq_f_inr : ∀ k : Nat, ∀ z : Fin 15,
      (∀ j : Fin 5, j.val < k → z ≠ uFin j) →
      (Tseq k).f.f (Sum.inr z) = Sum.inr (pent5Triple.f.f z) := by
    intro k
    induction k with
    | zero => intro z _; rfl
    | succ k ih =>
        intro z hz
        by_cases hk5 : k < 5
        · have h_eq : Tseq (k + 1) = coupleEdge (Tseq k) (pairA ⟨k, hk5⟩) (pairU ⟨k, hk5⟩) :=
            pent5Seq_succ_lt instDecD5 TL a hk5
          rw [h_eq, coupleEdge_f_of_ne (Tseq k) (by simp [pairA])
            (fun h => hz ⟨k, hk5⟩ (by dsimp; omega) (Sum.inr.inj h))]
          exact ih z (fun j hj => hz j (by omega))
        · dsimp only [Tseq]; rw [pent5Seq_succ_ge instDecD5 TL a hk5]; exact ih z (fun j hj => hz j (by omega))
  have hTseq_f_inl_ge : ∀ k : Nat, ∀ j : Fin 5, k ≤ j.val →
      (Tseq k).f.f (pairA j) = Sum.inl (TL.f.f (a j)) := by
    intro k
    induction k with
    | zero => intro j _; rfl
    | succ k ih =>
        intro j hj
        by_cases hk5 : k < 5
        · have h_eq : Tseq (k + 1) = coupleEdge (Tseq k) (pairA ⟨k, hk5⟩) (pairU ⟨k, hk5⟩) :=
            pent5Seq_succ_lt instDecD5 TL a hk5
          have hne_a : pairA j ≠ pairA ⟨k, hk5⟩ := fun h => by
            have := congrArg Fin.val (ha_inj _ _ (Sum.inl.inj h)); dsimp at this; omega
          rw [h_eq, coupleEdge_f_of_ne (Tseq k) hne_a (by simp [pairA, pairU])]
          exact ih j (by omega)
        · dsimp only [Tseq]; rw [pent5Seq_succ_ge instDecD5 TL a hk5]; exact ih j (by omega)
  have hTseq_f_inl_lt : ∀ k : Nat, k ≤ 5 → ∀ j : Fin 5, j.val < k →
      (Tseq k).f.f (pairA j) = Sum.inr (wFin j) ∧
      (Tseq k).f.f (pairU j) = Sum.inl (TL.f.f (a j)) := by
    intro k
    induction k with
    | zero => intro _ j hj; omega
    | succ k ih =>
        intro hk5 j hj
        have hk_lt : k < 5 := by omega
        have h_eq : Tseq (k + 1) = coupleEdge (Tseq k) (pairA ⟨k, hk_lt⟩) (pairU ⟨k, hk_lt⟩) :=
          pent5Seq_succ_lt instDecD5 TL a hk_lt
        rw [h_eq]
        by_cases hjk : j.val = k
        · have hjeq : j = ⟨k, hk_lt⟩ := Fin.ext hjk
          subst hjeq
          constructor
          · rw [coupleEdge_f_left (Tseq k)]
            exact (hTseq_f_inr k (uFin ⟨k, hk_lt⟩) (fun m hm heq => by
              have := congrArg Fin.val (hu_inj _ _ heq); omega)).trans (congrArg Sum.inr (hpent_u_w _))
          · rw [coupleEdge_f_right (Tseq k) (by simp [pairA, pairU])]
            exact hTseq_f_inl_ge k ⟨k, hk_lt⟩ (Nat.le_refl _)
        · have hj_lt : j.val < k := by omega
          obtain ⟨ihA, ihU⟩ := ih (by omega) j hj_lt
          have hne_a : pairA j ≠ pairA ⟨k, hk_lt⟩ := fun h => by
            have := congrArg Fin.val (ha_inj _ _ (Sum.inl.inj h)); dsimp at this; omega
          have hne_u : pairU j ≠ pairU ⟨k, hk_lt⟩ := fun h => by
            have := congrArg Fin.val (hu_inj _ _ (Sum.inr.inj h)); dsimp at this; omega
          constructor
          · rw [coupleEdge_f_of_ne (Tseq k) hne_a (by simp [pairA, pairU])]; exact ihA
          · rw [coupleEdge_f_of_ne (Tseq k) (by simp [pairA, pairU]) hne_u]; exact ihU
  have hgen1 : genusDeficit (Tseq 1) dartsU.length dartsU = 0 := by
    have h_eq1 : Tseq 1 = coupleEdge T0 (pairA ⟨0, by decide⟩) (pairU ⟨0, by decide⟩) :=
      pent5Seq_succ_lt instDecD5 TL a (by decide : 0 < 5)
    rw [h_eq1]
    have hc1' := coupleEdge_diff T0 dartsU hU_all (Nat.le_refl _)
      ((hTseq_e 0 (by omega)).2.1 ⟨0, by decide⟩ (Nat.zero_le _)).1
      ((hTseq_e 0 (by omega)).2.1 ⟨0, by decide⟩ (Nat.zero_le _)).2
      (reachEN_sumPerm_inl_inr_false TL.e TL.n pent5Triple.e pent5Triple.n _ _)
    rw [hc1'.2.2.2.2.2.2.2, hsum_gen]
  have hgen_step : ∀ k : Nat, 1 ≤ k → k < 5 →
      genusDeficit (Tseq k) dartsU.length dartsU = 0 →
      genusDeficit (Tseq (k + 1)) dartsU.length dartsU = 0 := by
    intro k hk1 hk5 hgen_k
    have h_eq : Tseq (k + 1) = coupleEdge (Tseq k) (pairA ⟨k, hk5⟩) (pairU ⟨k, hk5⟩) :=
      pent5Seq_succ_lt instDecD5 TL a hk5
    have ha_k : (Tseq k).e.f (pairA ⟨k, hk5⟩) = pairA ⟨k, hk5⟩ :=
      ((hTseq_e k (by omega)).2.1 ⟨k, hk5⟩ (Nat.le_refl _)).1
    have hu_k : (Tseq k).e.f (pairU ⟨k, hk5⟩) = pairU ⟨k, hk5⟩ :=
      ((hTseq_e k (by omega)).2.1 ⟨k, hk5⟩ (Nat.le_refl _)).2
    have h_fwd : ∀ d : Nat, d ≤ 5 - k →
        SameOrbit (Tseq k).f (pairA ⟨k, hk5⟩) (pairA ⟨(k + d) % 5, Nat.mod_lt _ (by decide)⟩) := by
      intro d
      induction d with
      | zero =>
          intro _
          have hkmod : (⟨(k + 0) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨k, hk5⟩ := by
            apply Fin.ext; dsimp; exact Nat.mod_eq_of_lt hk5
          rw [hkmod]
          exact ⟨0, rfl⟩
      | succ d ih =>
          intro hd
          have hkd_lt : k + d < 5 := by omega
          have hstep : SameOrbit (Tseq k).f (pairA ⟨k + d, hkd_lt⟩)
              (pairA ⟨(k + d + 1) % 5, Nat.mod_lt _ (by decide)⟩) := by
            have htr := arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
              (Tseq k) (hTseq_f_agree k) (k + d) hkd_lt (pairA ⟨k + d, hkd_lt⟩)
              (hTseq_f_inl_ge k ⟨k + d, hkd_lt⟩ (by dsimp; omega))
            exact htr.2.1
          have hprev := ih (by omega)
          have hmod_eq : (⟨(k + d) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨k + d, hkd_lt⟩ :=
            Fin.ext (Nat.mod_eq_of_lt hkd_lt)
          rw [hmod_eq] at hprev
          exact sameOrbit_trans (Tseq k).f hprev hstep
    have h_to_0 : SameOrbit (Tseq k).f (pairA ⟨k, hk5⟩) (pairA ⟨0, by decide⟩) := by
      have h5 := h_fwd (5 - k) (Nat.le_refl _)
      have heq0 : (⟨(k + (5 - k)) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨0, by decide⟩ := by
        apply Fin.ext; simp [show k + (5 - k) = 5 by omega]
      rw [heq0] at h5
      exact h5
    have h_0_w0 : SameOrbit (Tseq k).f (pairA ⟨0, by decide⟩) (Sum.inr (wFin ⟨0, by decide⟩)) := by
      refine ⟨1, ?_⟩
      simpa using (hTseq_f_inl_lt k (by omega) ⟨0, by decide⟩ hk1).1
    have h_w0_bwd : ∀ s : Nat, s ≤ 4 - k →
        SameOrbit (Tseq k).f (Sum.inr (wFin ⟨0, by decide⟩)) (pairU ⟨4 - s, by omega⟩) := by
      intro s
      induction s with
      | zero =>
          intro _
          refine ⟨1, ?_⟩
          have hw0 : (Tseq k).f.f (Sum.inr (wFin ⟨0, by decide⟩)) =
              Sum.inr (uFin ⟨4, by decide⟩) := by
            rw [hTseq_f_inr k (wFin ⟨0, by decide⟩)
              (fun j _ heq => by have := congrArg Fin.val heq; dsimp [wFin, uFin] at this; omega)]
            exact congrArg Sum.inr (hpent_w_u ⟨0, by decide⟩)
          simpa using hw0
      | succ s ih =>
          intro hs
          have hPrev := ih (by omega)
          have hge_k : k ≤ 4 - s := by omega
          have h1 : SameOrbit (Tseq k).f (pairU ⟨4 - s, by omega⟩) (Sum.inr (wFin ⟨4 - s, by omega⟩)) := by
            refine ⟨1, ?_⟩
            have hu_eq := hTseq_f_inr k (uFin ⟨4 - s, by omega⟩) (fun j hj heq => by
              have := congrArg Fin.val (hu_inj _ _ heq); dsimp at this; omega)
            rw [hpent_u_w] at hu_eq
            simpa using hu_eq
          have h2 : SameOrbit (Tseq k).f (Sum.inr (wFin ⟨4 - s, by omega⟩))
              (pairU ⟨4 - (s + 1), by omega⟩) := by
            refine ⟨1, ?_⟩
            have hw_eq := hTseq_f_inr k (wFin ⟨4 - s, by omega⟩) (fun j _ heq => by
              have := congrArg Fin.val heq; dsimp [wFin, uFin] at this; omega)
            rw [hpent_w_u] at hw_eq
            have hidx : (⟨((4 - s) + 4) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = ⟨4 - (s + 1), by omega⟩ := by
              apply Fin.ext; dsimp; omega
            rw [hidx] at hw_eq
            simpa using hw_eq
          exact sameOrbit_trans (Tseq k).f (sameOrbit_trans (Tseq k).f hPrev h1) h2
    have h_so : SameOrbit (Tseq k).f (pairA ⟨k, hk5⟩) (pairU ⟨k, hk5⟩) := by
      have hw := h_w0_bwd (4 - k) (Nat.le_refl _)
      have hidx : (⟨4 - (4 - k), by omega⟩ : Fin 5) = ⟨k, hk5⟩ := Fin.ext (by dsimp; omega)
      rw [hidx] at hw
      exact sameOrbit_trans (Tseq k).f (sameOrbit_trans (Tseq k).f h_to_0 h_0_w0) hw
    have horb :=
      (@sameOrbit_iff_mem_getOrbit D5 instDecD5 (Tseq k).f dartsU hU_all dartsU.length (Nat.le_refl _)
        (pairA ⟨k, hk5⟩) (pairU ⟨k, hk5⟩)).mp h_so
    have hsf := coupleEdge_sameFace (Tseq k) dartsU hU_all (Nat.le_refl _) ha_k hu_k
      (by simp [pairA, pairU]) horb
    rw [h_eq, hsf.2.2.2.2.2, hgen_k]
  have hgen2 : genusDeficit (Tseq 2) dartsU.length dartsU = 0 := hgen_step 1 (by omega) (by omega) hgen1
  have hgen3 : genusDeficit (Tseq 3) dartsU.length dartsU = 0 := hgen_step 2 (by omega) (by omega) hgen2
  have hgen4 : genusDeficit (Tseq 4) dartsU.length dartsU = 0 := hgen_step 3 (by omega) (by omega) hgen3
  have hgen5 : genusDeficit T5 dartsU.length dartsU = 0 := hgen_step 4 (by omega) (by omega) hgen4
  have h5_invol : ∀ x : D5, T5.e.f (T5.e.f x) = x := (hTseq_e 5 (Nat.le_refl _)).1
  have h5_e_cut : ∀ m : Fin 5, T5.e.f (pairA m) = pairU m ∧ T5.e.f (pairU m) = pairA m :=
    fun m => (hTseq_e 5 (Nat.le_refl _)).2.2 m m.isLt
  have h5_e_inr_vw : ∀ (P : Fin 15), (∀ m : Fin 5, P ≠ uFin m) →
      T5.e.f (Sum.inr P) = Sum.inr (pent5Triple.e.f P) := by
    intro P hP
    have hrec : ∀ k ≤ 5, (Tseq k).e.f (Sum.inr P) = Sum.inr (pent5Triple.e.f P) := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
          intro hk5
          have hk_lt : k < 5 := by omega
          have h_eq : Tseq (k + 1) = coupleEdge (Tseq k) (pairA ⟨k, hk_lt⟩) (pairU ⟨k, hk_lt⟩) :=
            pent5Seq_succ_lt instDecD5 TL a hk_lt
          have ha_k := ((hTseq_e k (by omega)).2.1 ⟨k, hk_lt⟩ (Nat.le_refl _)).1
          have hu_k := ((hTseq_e k (by omega)).2.1 ⟨k, hk_lt⟩ (Nat.le_refl _)).2
          rw [h_eq, coupleEdge_e_eval (Tseq k) ha_k hu_k, if_neg (by simp [pairA]),
            if_neg (fun h => hP ⟨k, hk_lt⟩ (Sum.inr.inj h))]
          exact ih (by omega)
    exact hrec 5 (Nat.le_refl _)
  have h5_e_ext : ∀ d : H.Dart, ∀ hd : cut.capSingleVertex_DL d,
      (∀ m : Fin 5, d ≠ cut.cutDart m) →
      ∃ hdn : cut.capSingleVertex_DL (H.edge.f d),
        T5.e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩ := by
    intro d hd hne
    have hnot_b : ∀ m : Fin 5, d ≠ H.edge.f (cut.cutDart m) := fun m heq =>
      h_disjLR d ⟨hd, heq ▸ (h_cutLR m).2⟩
    have he_eq : cut.uncoupleTriple.e.f d = H.edge.f d := (h_unc_ext d (fun m => ⟨hne m, hnot_b m⟩)).1
    have hdn : cut.capSingleVertex_DL (H.edge.f d) := he_eq ▸ hDL_e d hd
    refine ⟨hdn, ?_⟩
    have hrec : ∀ k ≤ 5, (Tseq k).e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩ := by
      intro k
      induction k with
      | zero =>
          intro _
          apply congrArg Sum.inl; apply Subtype.ext; exact he_eq
      | succ k ih =>
          intro hk5
          have hk_lt : k < 5 := by omega
          have h_eq : Tseq (k + 1) = coupleEdge (Tseq k) (pairA ⟨k, hk_lt⟩) (pairU ⟨k, hk_lt⟩) :=
            pent5Seq_succ_lt instDecD5 TL a hk_lt
          have ha_k := ((hTseq_e k (by omega)).2.1 ⟨k, hk_lt⟩ (Nat.le_refl _)).1
          have hu_k := ((hTseq_e k (by omega)).2.1 ⟨k, hk_lt⟩ (Nat.le_refl _)).2
          rw [h_eq, coupleEdge_e_eval (Tseq k) ha_k hu_k,
            if_neg (fun h => hne ⟨k, hk_lt⟩ (congrArg Subtype.val (Sum.inl.inj h))),
            if_neg (by simp [pairU])]
          exact ih (by omega)
    exact hrec 5 (Nat.le_refl _)
  have h5_no_fix : ∀ x : D5, T5.e.f x ≠ x := by
    intro x
    rcases x with ⟨d, hd⟩ | z
    · by_cases hcut : ∃ m : Fin 5, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        have h_eq := (h5_e_cut m).1
        have : (Sum.inl ⟨cut.cutDart m, hd⟩ : D5) = pairA m := rfl
        rw [this, h_eq]; simp [pairA, pairU]
      · obtain ⟨hdn, heq⟩ := h5_e_ext d hd (fun m h => hcut ⟨m, h⟩)
        rw [heq]
        intro h
        exact mc_edge_ne_self H darts h_mc d (congrArg Subtype.val (Sum.inl.inj h))
    · by_cases hu : ∃ m : Fin 5, z = uFin m
      · rcases hu with ⟨m, rfl⟩
        rw [(h5_e_cut m).2]; simp [pairA]
      · rw [h5_e_inr_vw z (fun m h => hu ⟨m, h⟩)]
        intro h
        have hzz := Sum.inr.inj h
        rcases pent5_e_mod3 z with hne | h0
        · exact hne hzz
        · exact hu ⟨⟨z.val / 3, by omega⟩, Fin.ext (by dsimp [uFin]; omega)⟩
  -- Build `H5 := tripleToHypermap T5 h5_invol`, prove `isPlanar`, `isBridgeless`, apply `is_minimal`:
  let H5 := tripleToHypermap T5 h5_invol
  let tag5 : D5 → Nat := fun x =>
    match x with
    | Sum.inl ⟨d, _⟩ =>
        if cut.inArcL darts h_mc.complete ⟨0, by decide⟩ d then 0
        else if cut.inArcL darts h_mc.complete ⟨1, by decide⟩ d then 1
        else if cut.inArcL darts h_mc.complete ⟨2, by decide⟩ d then 2
        else if cut.inArcL darts h_mc.complete ⟨3, by decide⟩ d then 3
        else if cut.inArcL darts h_mc.complete ⟨4, by decide⟩ d then 4
        else 6
    | Sum.inr z =>
        match z.val % 3 with
        | 0 => (z.val / 3 + 1) % 5
        | 1 => 5
        | _ => z.val / 3
  have htag5_inArc : ∀ (i : Fin 5) (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      cut.inArcL darts h_mc.complete i d → tag5 (Sum.inl ⟨d, hd⟩) = i.val := by
    intro ⟨iv, hi⟩ d hd hd_arc
    dsimp only [tag5]
    have h_neg : ∀ k : Fin 5, k.val ≠ iv → ¬cut.inArcL darts h_mc.complete k d := fun k hk h =>
      hk (congrArg Fin.val (inArcL_unique_idx darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut h hd_arc))
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [if_pos hd_arc]
    · rw [if_neg (h_neg ⟨0, by decide⟩ (by decide)), if_pos hd_arc]
    · rw [if_neg (h_neg ⟨0, by decide⟩ (by decide)),
          if_neg (h_neg ⟨1, by decide⟩ (by decide)), if_pos hd_arc]
    · rw [if_neg (h_neg ⟨0, by decide⟩ (by decide)),
          if_neg (h_neg ⟨1, by decide⟩ (by decide)),
          if_neg (h_neg ⟨2, by decide⟩ (by decide)), if_pos hd_arc]
    · rw [if_neg (h_neg ⟨0, by decide⟩ (by decide)),
          if_neg (h_neg ⟨1, by decide⟩ (by decide)),
          if_neg (h_neg ⟨2, by decide⟩ (by decide)),
          if_neg (h_neg ⟨3, by decide⟩ (by decide)), if_pos hd_arc]
  have htag5_eq_imp_inArc : ∀ (i : Fin 5) (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      tag5 (Sum.inl ⟨d, hd⟩) = i.val → cut.inArcL darts h_mc.complete i d := by
    intro ⟨iv, hi⟩ d hd htag
    dsimp only [tag5] at htag
    by_cases h0 : cut.inArcL darts h_mc.complete ⟨0, by decide⟩ d
    · rw [if_pos h0] at htag; have : iv = 0 := htag.symm; subst this; exact h0
    · rw [if_neg h0] at htag
      by_cases h1 : cut.inArcL darts h_mc.complete ⟨1, by decide⟩ d
      · rw [if_pos h1] at htag; have : iv = 1 := htag.symm; subst this; exact h1
      · rw [if_neg h1] at htag
        by_cases h2 : cut.inArcL darts h_mc.complete ⟨2, by decide⟩ d
        · rw [if_pos h2] at htag; have : iv = 2 := htag.symm; subst this; exact h2
        · rw [if_neg h2] at htag
          by_cases h3 : cut.inArcL darts h_mc.complete ⟨3, by decide⟩ d
          · rw [if_pos h3] at htag; have : iv = 3 := htag.symm; subst this; exact h3
          · rw [if_neg h3] at htag
            by_cases h4 : cut.inArcL darts h_mc.complete ⟨4, by decide⟩ d
            · rw [if_pos h4] at htag; have : iv = 4 := htag.symm; subst this; exact h4
            · rw [if_neg h4] at htag; omega
  have htag5_none : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      (∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d) → tag5 (Sum.inl ⟨d, hd⟩) = 6 := by
    intro d hd hnone
    dsimp only [tag5]
    rw [if_neg (hnone ⟨0, by decide⟩), if_neg (hnone ⟨1, by decide⟩),
        if_neg (hnone ⟨2, by decide⟩), if_neg (hnone ⟨3, by decide⟩), if_neg (hnone ⟨4, by decide⟩)]
  have htag5_inv : ∀ x : D5, tag5 (T5.f.f x) = tag5 x := by
    intro x
    rcases x with ⟨d, hd⟩ | z
    · by_cases hcut : ∃ m : Fin 5, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        have hf : T5.f.f (pairA m) = Sum.inr (wFin m) := (hTseq_f_inl_lt 5 (Nat.le_refl _) m m.isLt).1
        have h1 : (Sum.inl ⟨cut.cutDart m, hd⟩ : D5) = pairA m := rfl
        rw [h1, hf, htag5_inArc m _ hd (cut.cutDart_mem_inArcL darts h_mc.complete m)]
        dsimp [tag5, wFin]
        rw [show (3 * m.val + 2) % 3 = 2 by omega, show (3 * m.val + 2) / 3 = m.val by omega]
      · have hne : ∀ j : Fin 5, d ≠ cut.cutDart j := fun j h => hcut ⟨j, h⟩
        rw [hTseq_f_agree 5 ⟨d, hd⟩ hne]
        by_cases harc : ∃ i : Fin 5, cut.inArcL darts h_mc.complete i d
        · rcases harc with ⟨i, hi_arc⟩
          let m : Nat := (i.val + 4) % 5
          have hm5 : m < 5 := Nat.mod_lt _ (by decide)
          have hm_succ : (⟨(m + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i := by
            apply Fin.ext; dsimp [m]; omega
          obtain ⟨ht1, h_end, h_fwd, h_bwd, _⟩ :=
            TL_arc_segment darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut m hm5
          obtain ⟨r, hr1, hrt, hr_eq⟩ := h_bwd d (by simpa [hm_succ] using hi_arc)
          have hr_lt : r < (cut.posL darts h_mc.complete (m + 1) - cut.posL darts h_mc.complete m) := by
            by_cases hreq : r = cut.posL darts h_mc.complete (m + 1) - cut.posL darts h_mc.complete m
            · subst hreq
              have heq_am := hr_eq.symm.trans h_end
              exact absurd (congrArg Subtype.val heq_am) (hne ⟨(m + 1) % 5, Nat.mod_lt _ (by decide)⟩)
            · omega
          have hfx_eq : TL.f.f ⟨d, hd⟩ =
              Perm.iter TL.f (r + 1) ⟨cut.cutDart ⟨m, hm5⟩, cut.inArcL_sub_DL darts h_mc.nodup
                h_mc.complete h_mc.is_planar h_conn (cut.cutDart_mem_inArcL darts h_mc.complete ⟨m, hm5⟩)⟩ := by
            rw [← hr_eq, Perm.iter_succ]
          have hfx_arc : cut.inArcL darts h_mc.complete i (TL.f.f ⟨d, hd⟩).val := by
            have := h_fwd (r + 1) (by omega) (by omega)
            rw [← hm_succ, congrArg Subtype.val hfx_eq]; exact this
          rw [htag5_inArc i _ (TL.f.f ⟨d, hd⟩).property hfx_arc, htag5_inArc i _ hd hi_arc]
        · have hnone : ∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d := fun i h => harc ⟨i, h⟩
          have hnone' := TL_not_inArcL_f_closed darts h_mc.complete cut ⟨d, hd⟩ hnone
          rw [htag5_none _ (TL.f.f ⟨d, hd⟩).property hnone', htag5_none _ hd hnone]
    · have hz_dec : z.val < 15 := z.isLt
      have h_cases : (∃ m : Fin 5, z = uFin m) ∨ (∃ m : Fin 5, z = vFin m) ∨ (∃ m : Fin 5, z = wFin m) := by
        let m : Fin 5 := ⟨z.val / 3, by omega⟩
        rcases (by omega : z.val % 3 = 0 ∨ z.val % 3 = 1 ∨ z.val % 3 = 2) with hr | hr | hr
        · exact Or.inl ⟨m, Fin.ext (by dsimp [uFin, m]; omega)⟩
        · exact Or.inr (Or.inl ⟨m, Fin.ext (by dsimp [vFin, m]; omega)⟩)
        · exact Or.inr (Or.inr ⟨m, Fin.ext (by dsimp [wFin, m]; omega)⟩)
      rcases h_cases with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
      · have hf := (hTseq_f_inl_lt 5 (Nat.le_refl _) m m.isLt).2
        change T5.f.f (pairU m) = Sum.inl (TL.f.f (a m)) at hf
        rw [hf]
        obtain ⟨ht1, _, h_fwd, _, _⟩ :=
          TL_arc_segment darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut m.val m.isLt
        have h_in1 : cut.inArcL darts h_mc.complete ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ (TL.f.f (a m)).val := by
          have := h_fwd 1 (by omega) ht1
          simpa [Perm.iter_succ, Perm.iter_zero] using this
        rw [htag5_inArc ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ _ (TL.f.f (a m)).property h_in1]
        dsimp [tag5, uFin]
        rw [show 3 * m.val % 3 = 0 by omega, show 3 * m.val / 3 = m.val by omega]
      · have hne : ∀ j : Fin 5, vFin m ≠ uFin j := by intro j h; have := congrArg Fin.val h; dsimp [vFin, uFin] at this; omega
        rw [hTseq_f_inr 5 (vFin m) (fun j _ => hne j), hpent_v_v]
        dsimp [tag5, vFin]
        rw [show (3 * ((m.val + 1) % 5) + 1) % 3 = 1 by omega, show (3 * m.val + 1) % 3 = 1 by omega]
      · have hne : ∀ j : Fin 5, wFin m ≠ uFin j := by intro j h; have := congrArg Fin.val h; dsimp [wFin, uFin] at this; omega
        rw [hTseq_f_inr 5 (wFin m) (fun j _ => hne j), hpent_w_u]
        dsimp [tag5, uFin, wFin]
        rw [show 3 * ((m.val + 4) % 5) % 3 = 0 by omega,
            show 3 * ((m.val + 4) % 5) / 3 = (m.val + 4) % 5 by omega,
            show (3 * m.val + 2) % 3 = 2 by omega,
            show (3 * m.val + 2) / 3 = m.val by omega]
        dsimp; omega
  have hH5_planar : @Hypermap.isPlanar H5 (@instBEqOfDecidableEq D5 instDecD5) dartsU.length dartsU = true :=
    @tripleToHypermap_isPlanar D5 instDecD5 T5 h5_invol dartsU hU_nd hU_all hgen5 h5_no_fix
  have hH5_br : @Math.Hypermap.isBridgeless H5 instDecD5 dartsU dartsU.length := by
    rw [@isBridgeless_iff_no_sameOrbit_face_edge_jcs H5 instDecD5 dartsU hU_all]
    intro x hso
    change SameOrbit T5.f x (T5.e.f x) at hso
    have htag_eq := sameOrbit_of_f_agree_inv tag5 T5.f htag5_inv hso
    rcases x with ⟨d, hd⟩ | z
    · by_cases hcut : ∃ m : Fin 5, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        have h1 : (Sum.inl ⟨cut.cutDart m, hd⟩ : D5) = pairA m := rfl
        rw [h1, (h5_e_cut m).1] at htag_eq
        rw [htag5_inArc m _ hd (cut.cutDart_mem_inArcL darts h_mc.complete m)] at htag_eq
        dsimp [tag5, pairU, uFin] at htag_eq
        rw [show 3 * m.val % 3 = 0 by omega] at htag_eq
        dsimp at htag_eq; omega
      · have hne : ∀ m : Fin 5, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
        obtain ⟨hdn, he_eq⟩ := h5_e_ext d hd hne
        rw [he_eq] at htag_eq hso
        by_cases harc : ∃ i : Fin 5, cut.inArcL darts h_mc.complete i d
        · rcases harc with ⟨i, hi_arc⟩
          rw [htag5_inArc i _ hd hi_arc] at htag_eq
          have h_edge_arc := htag5_eq_imp_inArc i (H.edge.f d) hdn htag_eq.symm
          have hso1 := ((cut.inArcL_iff_sameOrbit_and_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn i d).mp hi_arc).1
          have hso2 := ((cut.inArcL_iff_sameOrbit_and_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn i (H.edge.f d)).mp h_edge_arc).1
          have hso_H := sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete hso1) hso2
          exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp h_mc.is_bridgeless d hso_H
        · have hnone : ∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d := fun i h => harc ⟨i, h⟩
          rcases hso with ⟨r, hr⟩
          have h_iter : ∀ q : Nat, ∃ d' hd',
              (∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d') ∧
              d' = Perm.iter H.face q d ∧
              Perm.iter T5.f q (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨d', hd'⟩ := by
            intro q
            induction q with
            | zero => exact ⟨d, hd, hnone, rfl, rfl⟩
            | succ q ih =>
                obtain ⟨d', hd', hnone', hd'_eq, hiter_eq⟩ := ih
                have hne' : ∀ m : Fin 5, d' ≠ cut.cutDart m := fun m heq =>
                  hnone' m (heq ▸ cut.cutDart_mem_inArcL darts h_mc.complete m)
                have hnot_b' : ∀ m : Fin 5, d' ≠ H.edge.f (cut.cutDart m) := fun m heq =>
                  h_disjLR d' ⟨hd', heq ▸ (h_cutLR m).2⟩
                have hf_eq' : (TL.f.f ⟨d', hd'⟩).val = H.face.f d' := by
                  rw [TL_f_val]
                  exact (h_unc_ext d' (fun m => ⟨hne' m, hnot_b' m⟩)).2
                refine ⟨(TL.f.f ⟨d', hd'⟩).val, (TL.f.f ⟨d', hd'⟩).property,
                  TL_not_inArcL_f_closed darts h_mc.complete cut ⟨d', hd'⟩ hnone', ?_, ?_⟩
                · rw [hf_eq', Perm.iter_succ, hd'_eq]
                · rw [Perm.iter_succ, hiter_eq, hTseq_f_agree 5 ⟨d', hd'⟩ hne']
          obtain ⟨d', _, _, hd'_eq, hiter_eq⟩ := h_iter r
          have hinl_eq := hiter_eq.symm.trans hr
          have hed_eq : Perm.iter H.face r d = H.edge.f d :=
            hd'_eq.symm.trans (congrArg Subtype.val (Sum.inl.inj hinl_eq))
          exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp h_mc.is_bridgeless d ⟨r, hed_eq⟩
    · have h_cases : (∃ m : Fin 5, z = uFin m) ∨ (∃ m : Fin 5, z = vFin m) ∨ (∃ m : Fin 5, z = wFin m) := by
        let m : Fin 5 := ⟨z.val / 3, by omega⟩
        rcases (by omega : z.val % 3 = 0 ∨ z.val % 3 = 1 ∨ z.val % 3 = 2) with hr | hr | hr
        · exact Or.inl ⟨m, Fin.ext (by dsimp [uFin, m]; omega)⟩
        · exact Or.inr (Or.inl ⟨m, Fin.ext (by dsimp [vFin, m]; omega)⟩)
        · exact Or.inr (Or.inr ⟨m, Fin.ext (by dsimp [wFin, m]; omega)⟩)
      rcases h_cases with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
      · rw [(h5_e_cut m).2] at htag_eq
        have hd_cut : cut.capSingleVertex_DL (cut.cutDart m) :=
          cut.inArcL_sub_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
            (cut.cutDart_mem_inArcL darts h_mc.complete m)
        have h1 : (pairA m : D5) = Sum.inl ⟨cut.cutDart m, hd_cut⟩ := rfl
        rw [h1, htag5_inArc m _ hd_cut (cut.cutDart_mem_inArcL darts h_mc.complete m)] at htag_eq
        dsimp [tag5, uFin] at htag_eq
        rw [show 3 * m.val % 3 = 0 by omega, show 3 * m.val / 3 = m.val by omega] at htag_eq
        dsimp at htag_eq; omega
      · have hne : ∀ j : Fin 5, vFin m ≠ uFin j := fun j h => by
          have := congrArg Fin.val h; dsimp [vFin, uFin] at this; omega
        have he_vw : pent5Triple.e.f (vFin m) = wFin ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ :=
          pent5_e_vw m
        rw [h5_e_inr_vw (vFin m) hne, he_vw] at htag_eq
        dsimp [tag5, vFin, wFin] at htag_eq
        rw [show (3 * m.val + 1) % 3 = 1 by omega,
            show (3 * ((m.val + 1) % 5) + 2) % 3 = 2 by omega,
            show (3 * ((m.val + 1) % 5) + 2) / 3 = (m.val + 1) % 5 by omega] at htag_eq
        dsimp at htag_eq; omega
      · have hne : ∀ j : Fin 5, wFin m ≠ uFin j := fun j h => by
          have := congrArg Fin.val h; dsimp [wFin, uFin] at this; omega
        have he_wv : pent5Triple.e.f (wFin m) = vFin ⟨(m.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ :=
          pent5_e_wv m
        rw [h5_e_inr_vw (wFin m) hne, he_wv] at htag_eq
        dsimp [tag5, vFin, wFin] at htag_eq
        rw [show (3 * m.val + 2) % 3 = 2 by omega,
            show (3 * m.val + 2) / 3 = m.val by omega,
            show (3 * ((m.val + 4) % 5) + 1) % 3 = 1 by omega] at htag_eq
        dsimp at htag_eq; omega
  have hU_ne : dartsU ≠ [] := by
    intro hempty
    have hmem := hU_all (Sum.inr ⟨0, by decide⟩)
    rw [hempty] at hmem; cases hmem
  have hU_lt : dartsU.length < darts.length := by
    have hsum_sides := side_lengths_sum darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
    rw [hU_len, hL_len]; omega
  obtain ⟨col5⟩ := @h_mc.is_minimal H5 instDecD5 dartsU hU_nd hU_all hU_ne hU_lt hH5_planar hH5_br
  have h_edge_int : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d), (∀ m : Fin 5, d ≠ cut.cutDart m) →
      ∃ hdn : cut.capSingleVertex_DL (H.edge.f d), H5.edge.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩ :=
    fun d hd hne => h5_e_ext d hd hne
  have h_face_int : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      (∀ i : Fin 5, ¬SameOrbit H.face (cut.ringFace i) d) →
      ∃ hfn : cut.capSingleVertex_DL (H.face.f d), H5.face.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.face.f d, hfn⟩ := by
    intro d hd hnotf
    have hnone : ∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d := fun i hi =>
      hnotf i ((cut.inArcL_iff_sameOrbit_and_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn i d).mp hi).1
    have hne : ∀ m : Fin 5, d ≠ cut.cutDart m := fun m hm =>
      hnone m (hm ▸ cut.cutDart_mem_inArcL darts h_mc.complete m)
    have hnot_b : ∀ m : Fin 5, d ≠ H.edge.f (cut.cutDart m) := fun m heq =>
      h_disjLR d ⟨hd, heq ▸ (h_cutLR m).2⟩
    have hf_eq : (TL.f.f ⟨d, hd⟩).val = H.face.f d := by
      rw [TL_f_val]; exact (h_unc_ext d (fun m => ⟨hne m, hnot_b m⟩)).2
    refine ⟨hf_eq ▸ (TL.f.f ⟨d, hd⟩).property, ?_⟩
    change T5.f.f (Sum.inl ⟨d, hd⟩) = _
    rw [hTseq_f_agree 5 ⟨d, hd⟩ hne]
    apply congrArg Sum.inl; apply Subtype.ext; exact hf_eq
  have h_face_ring : ∀ (m : Fin 5) (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      cut.inArcL darts h_mc.complete ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ d →
      SameOrbit H5.face (H5.edge.f (Sum.inl ⟨cut.cutDart m, cut.inArcL_sub_DL darts h_mc.nodup
        h_mc.complete h_mc.is_planar h_conn (cut.cutDart_mem_inArcL darts h_mc.complete m)⟩))
        (Sum.inl ⟨d, hd⟩) := by
    intro m d hd hd_arc
    change SameOrbit T5.f (T5.e.f (pairA m)) (Sum.inl ⟨d, hd⟩)
    rw [(h5_e_cut m).1]
    have htr := arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
      T5 (hTseq_f_agree 5) m.val m.isLt (pairU m)
      (hTseq_f_inl_lt 5 (Nat.le_refl _) m m.isLt).2
    exact htr.2.2 d hd hd_arc
  obtain ⟨col, _, hcol_inr⟩ := capColoring_of_gadget darts h_mc.nodup h_mc.complete h_mc.is_planar
    h_conn h_mc.is_bridgeless cut H5 id h_edge_int h_face_int h_face_ring col5
  -- Now prove `∀ j : Fin 5, capBoundaryColors ... col j ≠ col5.color (Sum.inr (vFin ⟨0, _⟩))`!
  have hv_same : ∀ m : Fin 5, col5.color (Sum.inr (vFin m)) = col5.color (Sum.inr (vFin ⟨0, by decide⟩)) := by
    have hstep : ∀ k : Fin 5, col5.color (Sum.inr (vFin ⟨(k.val + 1) % 5, Nat.mod_lt _ (by decide)⟩)) =
        col5.color (Sum.inr (vFin k)) := by
      intro k
      have hne : ∀ j : Fin 5, vFin k ≠ uFin j := fun j h => by
        have := congrArg Fin.val h; dsimp [vFin, uFin] at this; omega
      have hf := hTseq_f_inr 5 (vFin k) (fun j _ => hne j)
      rw [hpent_v_v] at hf
      have hinv := col5.face_invariant (Sum.inr (vFin k))
      change col5.color (T5.f.f (Sum.inr (vFin k))) = _ at hinv
      rw [hf] at hinv; exact hinv
    intro ⟨mv, hm⟩
    rcases (by omega : mv = 0 ∨ mv = 1 ∨ mv = 2 ∨ mv = 3 ∨ mv = 4) with rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact hstep ⟨0, by decide⟩
    · exact (hstep ⟨1, by decide⟩).trans (hstep ⟨0, by decide⟩)
    · exact (hstep ⟨2, by decide⟩).trans ((hstep ⟨1, by decide⟩).trans (hstep ⟨0, by decide⟩))
    · exact (hstep ⟨3, by decide⟩).trans ((hstep ⟨2, by decide⟩).trans ((hstep ⟨1, by decide⟩).trans (hstep ⟨0, by decide⟩)))
  have h_avoid : ∀ j : Fin 5,
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col j ≠
        col5.color (Sum.inr (vFin ⟨0, by decide⟩)) := by
    intro j
    let m : Fin 5 := ⟨(j.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
    have hm_cap : capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col j =
        col.color (Sum.inr m) := rfl
    rw [hm_cap, hcol_inr m]
    have hed : H5.edge.f (pairA m) = pairU m := (h5_e_cut m).1
    dsimp [id]
    change col5.color (H5.edge.f (pairA m)) ≠ _
    rw [hed]
    let k : Fin 5 := ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
    have hne_wk : ∀ i : Fin 5, wFin k ≠ uFin i := fun i h => by
      have := congrArg Fin.val h; dsimp [wFin, uFin] at this; omega
    have hfw : T5.f.f (Sum.inr (wFin k)) = Sum.inr (uFin m) := by
      rw [hTseq_f_inr 5 (wFin k) (fun i _ => hne_wk i), hpent_w_u]
      have hidx : (⟨(k.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = m := by
        apply Fin.ext; dsimp [k]; omega
      rw [hidx]
    have hcol_uw : col5.color (Sum.inr (uFin m)) = col5.color (Sum.inr (wFin k)) := by
      have hinv := col5.face_invariant (Sum.inr (wFin k))
      change col5.color (T5.f.f (Sum.inr (wFin k))) = _ at hinv
      rw [← hinv, hfw]
    have hpw : pent5Triple.e.f (wFin k) = vFin m := by
      have hm_eq : m = ⟨(k.val + 4) % 5, Nat.mod_lt _ (by decide)⟩ := by apply Fin.ext; dsimp [k]; omega
      rw [hm_eq]; exact pent5_e_wv k
    have hew : H5.edge.f (Sum.inr (wFin k)) = Sum.inr (vFin m) := by
      change T5.e.f (Sum.inr (wFin k)) = _
      rw [h5_e_inr_vw (wFin k) hne_wk, hpw]
    rw [hcol_uw]
    change col5.color (Sum.inr (wFin k)) ≠ col5.color (Sum.inr (vFin ⟨0, by decide⟩))
    rw [← hv_same m, ← hew]
    exact Ne.symm (col5.edge_proper (Sum.inr (wFin k)))
  have hT := fin5_three_colors_imp_state5T
    (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col)
    (col5.color (Sum.inr (vFin ⟨0, by decide⟩)))
    (fun j => capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
      h_mc.is_bridgeless cut col j)
    h_avoid
  rcases hT with ⟨i, hiT⟩
  exact ⟨i, col, hiT⟩

/-! ### Step 2: Vertex-Identification Gadget (`cap5_identify0_realizable`) -/

private def c3N : Perm (Fin 3) where
  f x := ⟨(x.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  inv x := ⟨(x.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide
  right_inv := by decide

private def c3F : Perm (Fin 3) where
  f x := ⟨(x.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
  inv x := ⟨(x.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
  left_inv := by decide
  right_inv := by decide

private def c3E : Perm (Fin 3) where
  f := id
  inv := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

private def c3Triple : PermTriple (Fin 3) where
  e := c3E
  n := c3N
  f := c3F
  enf_id := by decide

private theorem c3_f_0 : c3Triple.f.f ⟨0, by decide⟩ = ⟨2, by decide⟩ := rfl
private theorem c3_f_1 : c3Triple.f.f ⟨1, by decide⟩ = ⟨0, by decide⟩ := rfl
private theorem c3_f_2 : c3Triple.f.f ⟨2, by decide⟩ = ⟨1, by decide⟩ := rfl

private theorem c3Triple_spec :
    let darts := List.finRange 3
    genusDeficit c3Triple 3 darts = 0 ∧
    countRelClasses (ReachEN c3Triple.e c3Triple.n) darts = 1 ∧
    (∀ x : Fin 3, c3Triple.e.f (c3Triple.e.f x) = x) := by
  intro darts
  have hgen : genusDeficit c3Triple 3 darts = 0 :=
    genusDeficit_eq_zero_of_edge_id c3Triple (fun _ => rfl) darts (nodup_finRange_b5 3)
      (fun x => List.mem_finRange x) (by simp [darts, List.length_finRange])
  have h01 : ReachEN c3Triple.e c3Triple.n ⟨0, by decide⟩ ⟨1, by decide⟩ :=
    ⟨@WalkEN.step (Fin 3) c3Triple.e c3Triple.n ⟨0, by decide⟩ (c3Triple.n.f (⟨0, by decide⟩ : Fin 3))
      ⟨1, by decide⟩ (StepEN.n_fwd (⟨0, by decide⟩ : Fin 3)) (WalkEN.refl _)⟩
  have h12 : ReachEN c3Triple.e c3Triple.n ⟨1, by decide⟩ ⟨2, by decide⟩ :=
    ⟨@WalkEN.step (Fin 3) c3Triple.e c3Triple.n ⟨1, by decide⟩ (c3Triple.n.f (⟨1, by decide⟩ : Fin 3))
      ⟨2, by decide⟩ (StepEN.n_fwd (⟨1, by decide⟩ : Fin 3)) (WalkEN.refl _)⟩
  have h02 : ReachEN c3Triple.e c3Triple.n ⟨0, by decide⟩ ⟨2, by decide⟩ :=
    reachEN_trans _ _ h01 h12
  have h_reach : ∀ x : Fin 3, ReachEN c3Triple.e c3Triple.n ⟨0, by decide⟩ x := by
    intro ⟨v, hv⟩
    rcases show v = 0 ∨ v = 1 ∨ v = 2 by omega with rfl | rfl | rfl
    · exact reachEN_refl _ _ _
    · exact h01
    · exact h02
  have h_c1 : countRelClasses (ReachEN c3Triple.e c3Triple.n) darts = 1 :=
    countRelClasses_eq_one_of_forall _ ⟨0, by decide⟩ (fun x _ => h_reach x)
      (by decide : List.finRange 3 ≠ [])
      (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
  exact ⟨hgen, h_c1, fun _ => rfl⟩

/-- **Gadget 2 (`identify0` on a chordless 5-cut):** gluing the 3-dart single-vertex
gadget across `a0 ↔ y0`, `a1 ↔ a2`, `a3 ↔ y1`, `a4 ↔ y2` merges boundary faces `1` and `3`
so any coloring satisfies `f 1 = f 3`, forcing `T₀ ∨ T₄ ∨ Q₂`. -/
theorem cap5_identify0_realizable {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut)
    (h21R : 21 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) :
    ∃ col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
      h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState5T ⟨0, by decide⟩ (capBoundaryColors darts h_mc.nodup h_mc.complete
        h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut col) ∨
      IsState5T ⟨4, by decide⟩ (capBoundaryColors darts h_mc.nodup h_mc.complete
        h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut col) ∨
      IsState5Q ⟨2, by decide⟩ (capBoundaryColors darts h_mc.nodup h_mc.complete
        h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut col) := by
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_unc := uncoupleCycle_two_components H darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
  obtain ⟨_, h_unc_invol, _, _, _, _, h_disjLR, h_cutLR, h_cut_fix, h_unc_ext, _, _, _⟩ := h_unc
  have hDL_e : ∀ d : H.Dart, cut.capSingleVertex_DL d →
      cut.capSingleVertex_DL (cut.uncoupleTriple.e.f d) :=
    fun d hd => reachEN_trans _ _ hd ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩
  let dartsL := predDarts cut.capSingleVertex_DL darts
  let TL := cut.capSingleVertex_TL
  obtain ⟨hL_nd, hL_all, hL_len, _, hL_gen, hL_c1⟩ :=
    TL_spec darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
  let a : Fin 5 → { d : H.Dart // cut.capSingleVertex_DL d } :=
    fun m => ⟨cut.cutDart m, cut.inArcL_sub_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
      (cut.cutDart_mem_inArcL darts h_mc.complete m)⟩
  have ha_inj : ∀ i j : Fin 5, a i = a j → i = j := by
    intro i j hij
    exact Classical.byContradiction fun hne =>
      cutDart_ne_of_ne darts h_mc cut hne (congrArg Subtype.val hij)
  let D3 := { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin 3
  let instDecD3 : DecidableEq D3 := instDecidableEqSum
  let T0 : PermTriple D3 := sumTriple TL c3Triple
  let darts3 : List (Fin 3) := List.finRange 3
  have hsum := sumTriple_spec TL c3Triple dartsL hL_nd hL_all darts3
    (nodup_finRange_b5 3) (fun x => List.mem_finRange x) (Nat.le_refl _)
  let dartsU : List D3 := dartsL.map Sum.inl ++ darts3.map Sum.inr
  have hU_nd : dartsU.Nodup := hsum.1
  have hU_all : ∀ z : D3, z ∈ dartsU := hsum.2.1
  have hU_len : dartsU.length = dartsL.length + 3 := by
    simp [dartsU, darts3, List.length_finRange]
  have hsum_gen : genusDeficit T0 dartsU.length dartsU = 0 := by
    have hlen : dartsL.length + darts3.length = dartsU.length := hU_len.symm
    have h_f0 := hsum.2.2.1
    rw [hlen] at h_f0
    have h_f1 : genusDeficit TL dartsU.length dartsL = genusDeficit TL dartsL.length dartsL :=
      genusDeficit_eq_of_complete TL dartsL dartsL hL_nd hL_all hL_nd hL_all (by omega) (Nat.le_refl _)
    have h_f2 : genusDeficit c3Triple dartsU.length darts3 = genusDeficit c3Triple 3 darts3 :=
      genusDeficit_eq_of_complete c3Triple darts3 darts3
        (nodup_finRange_b5 3) (fun x => List.mem_finRange x)
        (nodup_finRange_b5 3) (fun x => List.mem_finRange x)
        (by simp [dartsU, darts3, List.length_finRange]) (by simp [darts3, List.length_finRange])
    change genusDeficit (sumTriple TL c3Triple) dartsU.length (dartsL.map Sum.inl ++ darts3.map Sum.inr) = 0
    rw [h_f0, h_f1, h_f2, hL_gen, c3Triple_spec.1]
    rfl
  let pA : Fin 5 → D3 := fun m => Sum.inl (a m)
  let y0 : D3 := Sum.inr ⟨0, by decide⟩
  let y1 : D3 := Sum.inr ⟨1, by decide⟩
  let y2 : D3 := Sum.inr ⟨2, by decide⟩
  let S1 : PermTriple D3 := coupleEdge T0 (pA 0) y0
  let S2 : PermTriple D3 := coupleEdge S1 (pA 1) (pA 2)
  let S3 : PermTriple D3 := coupleEdge S2 (pA 3) y1
  let T3 : PermTriple D3 := coupleEdge S3 (pA 4) y2
  have hpA_inj : ∀ i j : Fin 5, pA i = pA j → i = j := fun i j h =>
    ha_inj i j (Sum.inl.inj h)
  have hTL_inv : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d }, TL.e.f (TL.e.f x) = x :=
    fun x => Subtype.ext (h_unc_invol x.val)
  have hT0_inv : ∀ z : D3, T0.e.f (T0.e.f z) = z := by
    intro z
    rcases z with x | w
    · exact congrArg Sum.inl (hTL_inv x)
    · rfl
  have hTL_e_a : ∀ m : Fin 5, TL.e.f (a m) = a m := fun m =>
    Subtype.ext (h_cut_fix m).1
  have hT0_e_pA : ∀ m : Fin 5, T0.e.f (pA m) = pA m := fun m =>
    congrArg Sum.inl (hTL_e_a m)
  have hS1_inv : ∀ z : D3, S1.e.f (S1.e.f z) = z :=
    coupleEdge_edge_invol T0 hT0_inv (hT0_e_pA 0) rfl
  have hpA0_S0 : T0.e.f (pA 0) = pA 0 := hT0_e_pA 0
  have hy0_S0 : T0.e.f y0 = y0 := rfl
  have hgen1 : genusDeficit S1 dartsU.length dartsU = 0 := by
    have hc1 := coupleEdge_diff T0 dartsU hU_all (Nat.le_refl _)
      hpA0_S0 hy0_S0 (reachEN_sumPerm_inl_inr_false TL.e TL.n c3Triple.e c3Triple.n _ _)
    rw [hc1.2.2.2.2.2.2.2, hsum_gen]
  have hS1_e_pA1 : S1.e.f (pA 1) = pA 1 := by
    change (coupleEdge T0 (pA 0) y0).e.f (pA 1) = pA 1
    rw [coupleEdge_e_eval T0 hpA0_S0 hy0_S0 (pA 1),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
      if_neg (by simp [pA, y0])]
    exact hT0_e_pA 1
  have hS1_e_pA2 : S1.e.f (pA 2) = pA 2 := by
    change (coupleEdge T0 (pA 0) y0).e.f (pA 2) = pA 2
    rw [coupleEdge_e_eval T0 hpA0_S0 hy0_S0 (pA 2),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
      if_neg (by simp [pA, y0])]
    exact hT0_e_pA 2
  have hne_12 : pA 1 ≠ pA 2 := fun h =>
    absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)
  have hS1_f_agree : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d },
      (∀ j : Fin 5, x.val ≠ cut.cutDart j) →
      S1.f.f (Sum.inl x) = Sum.inl (TL.f.f x) := by
    intro x hx
    change (coupleEdge T0 (pA 0) y0).f.f (Sum.inl x) = Sum.inl (TL.f.f x)
    rw [coupleEdge_f_of_ne T0 (fun h => hx 0 (congrArg Subtype.val (Sum.inl.inj h)))
      (by simp)]
    rfl
  have hS1_same_12 : SameOrbit S1.f (pA 1) (pA 2) := by
    have hstart : S1.f.f (pA 1) = Sum.inl (TL.f.f (a 1)) := by
      change (coupleEdge T0 (pA 0) y0).f.f (pA 1) = Sum.inl (TL.f.f (a 1))
      rw [coupleEdge_f_of_ne T0
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (by simp)]
      rfl
    exact (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
      cut S1 hS1_f_agree 1 (by decide) (pA 1) hstart).2.1
  have hS2_inv : ∀ z : D3, S2.e.f (S2.e.f z) = z :=
    coupleEdge_edge_invol S1 hS1_inv hS1_e_pA1 hS1_e_pA2
  have hgen2 : genusDeficit S2 dartsU.length dartsU = 0 := by
    have horb := (sameOrbit_iff_mem_getOrbit S1.f dartsU hU_all (Nat.le_refl _)
      (pA 1) (pA 2)).mp hS1_same_12
    have hsf := coupleEdge_sameFace S1 dartsU hU_all (Nat.le_refl _)
      hS1_e_pA1 hS1_e_pA2 hne_12 horb
    rw [hsf.2.2.2.2.2, hgen1]
  have hS2_e_pA3 : S2.e.f (pA 3) = pA 3 := by
    change (coupleEdge S1 (pA 1) (pA 2)).e.f (pA 3) = pA 3
    rw [coupleEdge_e_eval S1 hS1_e_pA1 hS1_e_pA2 (pA 3),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
    change (coupleEdge T0 (pA 0) y0).e.f (pA 3) = pA 3
    rw [coupleEdge_e_eval T0 hpA0_S0 hy0_S0 (pA 3),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
      if_neg (by simp)]
    exact hT0_e_pA 3
  have hS2_e_y1 : S2.e.f y1 = y1 := by
    change (coupleEdge S1 (pA 1) (pA 2)).e.f y1 = y1
    rw [coupleEdge_e_eval S1 hS1_e_pA1 hS1_e_pA2 y1,
      if_neg (by simp), if_neg (by simp)]
    change (coupleEdge T0 (pA 0) y0).e.f y1 = y1
    rw [coupleEdge_e_eval T0 hpA0_S0 hy0_S0 y1,
      if_neg (by simp), if_neg (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
    rfl
  have hne_3y1 : pA 3 ≠ y1 := by simp [pA, y1]
  have hS2_f_agree : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d },
      (∀ j : Fin 5, x.val ≠ cut.cutDart j) →
      S2.f.f (Sum.inl x) = Sum.inl (TL.f.f x) := by
    intro x hx
    change (coupleEdge S1 (pA 1) (pA 2)).f.f (Sum.inl x) = Sum.inl (TL.f.f x)
    rw [coupleEdge_f_of_ne S1
      (fun h => hx 1 (congrArg Subtype.val (Sum.inl.inj h)))
      (fun h => hx 2 (congrArg Subtype.val (Sum.inl.inj h)))]
    exact hS1_f_agree x hx
  have hS2_same_3y1 : SameOrbit S2.f (pA 3) y1 := by
    have hstart3 : S2.f.f (pA 3) = Sum.inl (TL.f.f (a 3)) := by
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 3) = Sum.inl (TL.f.f (a 3))
      rw [coupleEdge_f_of_ne S1
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 3) = Sum.inl (TL.f.f (a 3))
      rw [coupleEdge_f_of_ne T0
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (by simp)]
      rfl
    have hstart4 : S2.f.f (pA 4) = Sum.inl (TL.f.f (a 4)) := by
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 4) = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_of_ne S1
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 4) = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_of_ne T0
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (by simp)]
      rfl
    have h34 : SameOrbit S2.f (pA 3) (pA 4) :=
      (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
        cut S2 hS2_f_agree 3 (by decide) (pA 3) hstart3).2.1
    have h40 : SameOrbit S2.f (pA 4) (pA 0) :=
      (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
        cut S2 hS2_f_agree 4 (by decide) (pA 4) hstart4).2.1
    have h0_y2 : S2.f.f (pA 0) = y2 := by
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 0) = y2
      rw [coupleEdge_f_of_ne S1
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 0) = y2
      rw [coupleEdge_f_left T0]
      exact congrArg Sum.inr c3_f_0
    have hy2_y1 : S2.f.f y2 = y1 := by
      change (coupleEdge S1 (pA 1) (pA 2)).f.f y2 = y1
      rw [coupleEdge_f_of_ne S1 (by simp [pA, y2]) (by simp [pA, y2])]
      change (coupleEdge T0 (pA 0) y0).f.f y2 = y1
      rw [coupleEdge_f_of_ne T0 (fun h => by cases h)
        (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      exact congrArg Sum.inr c3_f_2
    have h0_y1 : SameOrbit S2.f (pA 0) y1 :=
      ⟨2, by simp only [Perm.iter_succ, Perm.iter_zero, h0_y2, hy2_y1]⟩
    exact sameOrbit_trans S2.f h34 (sameOrbit_trans S2.f h40 h0_y1)
  have hS3_inv : ∀ z : D3, S3.e.f (S3.e.f z) = z :=
    coupleEdge_edge_invol S2 hS2_inv hS2_e_pA3 hS2_e_y1
  have hgen3 : genusDeficit S3 dartsU.length dartsU = 0 := by
    have horb := (sameOrbit_iff_mem_getOrbit S2.f dartsU hU_all (Nat.le_refl _)
      (pA 3) y1).mp hS2_same_3y1
    have hsf := coupleEdge_sameFace S2 dartsU hU_all (Nat.le_refl _)
      hS2_e_pA3 hS2_e_y1 hne_3y1 horb
    rw [hsf.2.2.2.2.2, hgen2]
  have hS3_e_pA4 : S3.e.f (pA 4) = pA 4 := by
    change (coupleEdge S2 (pA 3) y1).e.f (pA 4) = pA 4
    rw [coupleEdge_e_eval S2 hS2_e_pA3 hS2_e_y1 (pA 4),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
      if_neg (by simp)]
    change (coupleEdge S1 (pA 1) (pA 2)).e.f (pA 4) = pA 4
    rw [coupleEdge_e_eval S1 hS1_e_pA1 hS1_e_pA2 (pA 4),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
    change (coupleEdge T0 (pA 0) y0).e.f (pA 4) = pA 4
    rw [coupleEdge_e_eval T0 hpA0_S0 hy0_S0 (pA 4),
      if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
      if_neg (by simp)]
    exact hT0_e_pA 4
  have hS3_e_y2 : S3.e.f y2 = y2 := by
    change (coupleEdge S2 (pA 3) y1).e.f y2 = y2
    rw [coupleEdge_e_eval S2 hS2_e_pA3 hS2_e_y1 y2,
      if_neg (by simp), if_neg (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
    change (coupleEdge S1 (pA 1) (pA 2)).e.f y2 = y2
    rw [coupleEdge_e_eval S1 hS1_e_pA1 hS1_e_pA2 y2,
      if_neg (by simp), if_neg (by simp)]
    change (coupleEdge T0 (pA 0) y0).e.f y2 = y2
    rw [coupleEdge_e_eval T0 hpA0_S0 hy0_S0 y2,
      if_neg (by simp), if_neg (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
    rfl
  have hne_4y2 : pA 4 ≠ y2 := by simp [pA, y2]
  have hS3_f_agree : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d },
      (∀ j : Fin 5, x.val ≠ cut.cutDart j) →
      S3.f.f (Sum.inl x) = Sum.inl (TL.f.f x) := by
    intro x hx
    change (coupleEdge S2 (pA 3) y1).f.f (Sum.inl x) = Sum.inl (TL.f.f x)
    rw [coupleEdge_f_of_ne S2
      (fun h => hx 3 (congrArg Subtype.val (Sum.inl.inj h)))
      (by simp)]
    exact hS2_f_agree x hx
  have hS3_same_4y2 : SameOrbit S3.f (pA 4) y2 := by
    have hstart4 : S3.f.f (pA 4) = Sum.inl (TL.f.f (a 4)) := by
      change (coupleEdge S2 (pA 3) y1).f.f (pA 4) = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_of_ne S2
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (by simp)]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 4) = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_of_ne S1
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 4) = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_of_ne T0
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (by simp)]
      rfl
    have h40 : SameOrbit S3.f (pA 4) (pA 0) :=
      (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
        cut S3 hS3_f_agree 4 (by decide) (pA 4) hstart4).2.1
    have h0_y2 : S3.f.f (pA 0) = y2 := by
      change (coupleEdge S2 (pA 3) y1).f.f (pA 0) = y2
      rw [coupleEdge_f_of_ne S2
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (by simp)]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 0) = y2
      rw [coupleEdge_f_of_ne S1
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 0) = y2
      rw [coupleEdge_f_left T0]
      exact congrArg Sum.inr c3_f_0
    exact sameOrbit_trans S3.f h40 ⟨1, by simpa [Perm.iter_succ, Perm.iter_zero] using h0_y2⟩
  have h3_invol : ∀ z : D3, T3.e.f (T3.e.f z) = z :=
    coupleEdge_edge_invol S3 hS3_inv hS3_e_pA4 hS3_e_y2
  have hgen4 : genusDeficit T3 dartsU.length dartsU = 0 := by
    have horb := (sameOrbit_iff_mem_getOrbit S3.f dartsU hU_all (Nat.le_refl _)
      (pA 4) y2).mp hS3_same_4y2
    have hsf := coupleEdge_sameFace S3 dartsU hU_all (Nat.le_refl _)
      hS3_e_pA4 hS3_e_y2 hne_4y2 horb
    rw [hsf.2.2.2.2.2, hgen3]
  have h3_e_pairs :
      T3.e.f (pA 0) = y0 ∧ T3.e.f y0 = pA 0 ∧
      T3.e.f (pA 1) = pA 2 ∧ T3.e.f (pA 2) = pA 1 ∧
      T3.e.f (pA 3) = y1 ∧ T3.e.f y1 = pA 3 ∧
      T3.e.f (pA 4) = y2 ∧ T3.e.f y2 = pA 4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (coupleEdge S3 (pA 4) y2).e.f (pA 0) = y0
      rw [coupleEdge_e_eval S3 hS3_e_pA4 hS3_e_y2 (pA 0),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
        if_neg (by simp)]
      change (coupleEdge S2 (pA 3) y1).e.f (pA 0) = y0
      rw [coupleEdge_e_eval S2 hS2_e_pA3 hS2_e_y1 (pA 0),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
        if_neg (by simp)]
      change (coupleEdge S1 (pA 1) (pA 2)).e.f (pA 0) = y0
      rw [coupleEdge_e_eval S1 hS1_e_pA1 hS1_e_pA2 (pA 0),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      exact coupleEdge_e_left T0 hpA0_S0 hy0_S0
    · change (coupleEdge S3 (pA 4) y2).e.f y0 = pA 0
      rw [coupleEdge_e_eval S3 hS3_e_pA4 hS3_e_y2 y0, if_neg (by simp),
        if_neg (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      change (coupleEdge S2 (pA 3) y1).e.f y0 = pA 0
      rw [coupleEdge_e_eval S2 hS2_e_pA3 hS2_e_y1 y0, if_neg (by simp),
        if_neg (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      change (coupleEdge S1 (pA 1) (pA 2)).e.f y0 = pA 0
      rw [coupleEdge_e_eval S1 hS1_e_pA1 hS1_e_pA2 y0, if_neg (by simp), if_neg (by simp)]
      exact coupleEdge_e_right T0 hpA0_S0 hy0_S0
    · change (coupleEdge S3 (pA 4) y2).e.f (pA 1) = pA 2
      rw [coupleEdge_e_eval S3 hS3_e_pA4 hS3_e_y2 (pA 1),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
        if_neg (by simp)]
      change (coupleEdge S2 (pA 3) y1).e.f (pA 1) = pA 2
      rw [coupleEdge_e_eval S2 hS2_e_pA3 hS2_e_y1 (pA 1),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
        if_neg (by simp)]
      exact coupleEdge_e_left S1 hS1_e_pA1 hS1_e_pA2
    · change (coupleEdge S3 (pA 4) y2).e.f (pA 2) = pA 1
      rw [coupleEdge_e_eval S3 hS3_e_pA4 hS3_e_y2 (pA 2),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
        if_neg (by simp)]
      change (coupleEdge S2 (pA 3) y1).e.f (pA 2) = pA 1
      rw [coupleEdge_e_eval S2 hS2_e_pA3 hS2_e_y1 (pA 2),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
        if_neg (by simp)]
      exact coupleEdge_e_right S1 hS1_e_pA1 hS1_e_pA2
    · change (coupleEdge S3 (pA 4) y2).e.f (pA 3) = y1
      rw [coupleEdge_e_eval S3 hS3_e_pA4 hS3_e_y2 (pA 3),
        if_neg (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)),
        if_neg (by simp)]
      exact coupleEdge_e_left S2 hS2_e_pA3 hS2_e_y1
    · change (coupleEdge S3 (pA 4) y2).e.f y1 = pA 3
      rw [coupleEdge_e_eval S3 hS3_e_pA4 hS3_e_y2 y1, if_neg (by simp),
        if_neg (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      exact coupleEdge_e_right S2 hS2_e_pA3 hS2_e_y1
    · exact coupleEdge_e_left S3 hS3_e_pA4 hS3_e_y2
    · exact coupleEdge_e_right S3 hS3_e_pA4 hS3_e_y2
  have h3_e_ext : ∀ d : H.Dart, ∀ hd : cut.capSingleVertex_DL d,
      (∀ m : Fin 5, d ≠ cut.cutDart m) →
      ∃ hdn : cut.capSingleVertex_DL (H.edge.f d),
        T3.e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩ := by
    intro d hd hne
    have hnot : ∀ m : Fin 5, (Sum.inl ⟨d, hd⟩ : D3) ≠ pA m := fun m h =>
      hne m (congrArg Subtype.val (Sum.inl.inj h))
    have hnot_b : ∀ m : Fin 5, d ≠ H.edge.f (cut.cutDart m) := fun m heq =>
      h_disjLR d ⟨hd, heq ▸ (h_cutLR m).2⟩
    have he_eq : cut.uncoupleTriple.e.f d = H.edge.f d :=
      (h_unc_ext d (fun m => ⟨hne m, hnot_b m⟩)).1
    have hdn : cut.capSingleVertex_DL (H.edge.f d) := he_eq ▸ hDL_e d hd
    refine ⟨hdn, ?_⟩
    change (coupleEdge S3 (pA 4) y2).e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩
    rw [coupleEdge_e_eval S3 hS3_e_pA4 hS3_e_y2 (Sum.inl ⟨d, hd⟩),
      if_neg (hnot 4), if_neg (by simp)]
    change (coupleEdge S2 (pA 3) y1).e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩
    rw [coupleEdge_e_eval S2 hS2_e_pA3 hS2_e_y1 (Sum.inl ⟨d, hd⟩),
      if_neg (hnot 3), if_neg (by simp)]
    change (coupleEdge S1 (pA 1) (pA 2)).e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩
    rw [coupleEdge_e_eval S1 hS1_e_pA1 hS1_e_pA2 (Sum.inl ⟨d, hd⟩),
      if_neg (hnot 1), if_neg (hnot 2)]
    change (coupleEdge T0 (pA 0) y0).e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩
    rw [coupleEdge_e_eval T0 hpA0_S0 hy0_S0 (Sum.inl ⟨d, hd⟩),
      if_neg (hnot 0), if_neg (by simp)]
    exact congrArg Sum.inl (Subtype.ext he_eq)
  have h3_no_fix : ∀ z : D3, T3.e.f z ≠ z := by
    intro z
    rcases z with ⟨d, hd⟩ | ⟨j, hj⟩
    · by_cases hcut : ∃ m : Fin 5, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        have hsum_eq : (Sum.inl ⟨cut.cutDart m, hd⟩ : D3) = pA m :=
          congrArg Sum.inl (Subtype.ext rfl)
        rw [hsum_eq]
        rcases m with ⟨mv, hmv⟩
        rcases show mv = 0 ∨ mv = 1 ∨ mv = 2 ∨ mv = 3 ∨ mv = 4 by omega with
          rfl | rfl | rfl | rfl | rfl
        · change T3.e.f (pA 0) ≠ pA 0; rw [h3_e_pairs.1]; simp [pA, y0]
        · change T3.e.f (pA 1) ≠ pA 1; rw [h3_e_pairs.2.2.1]; exact fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)
        · change T3.e.f (pA 2) ≠ pA 2; rw [h3_e_pairs.2.2.2.1]; exact fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)
        · change T3.e.f (pA 3) ≠ pA 3; rw [h3_e_pairs.2.2.2.2.1]; simp [pA, y1]
        · change T3.e.f (pA 4) ≠ pA 4; rw [h3_e_pairs.2.2.2.2.2.2.1]; simp [pA, y2]
      · have hne : ∀ m : Fin 5, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
        obtain ⟨hdn, he_eq⟩ := h3_e_ext d hd hne
        rw [he_eq]
        intro h_fix
        exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp
          h_mc.is_bridgeless d ⟨0, (congrArg Subtype.val (Sum.inl.inj h_fix)).symm⟩
    · rcases show j = 0 ∨ j = 1 ∨ j = 2 by omega with rfl | rfl | rfl
      · rw [show (Sum.inr ⟨0, hj⟩ : D3) = y0 from rfl, h3_e_pairs.2.1]; simp [pA, y0]
      · rw [show (Sum.inr ⟨1, hj⟩ : D3) = y1 from rfl, h3_e_pairs.2.2.2.2.2.1]; simp [pA, y1]
      · rw [show (Sum.inr ⟨2, hj⟩ : D3) = y2 from rfl, h3_e_pairs.2.2.2.2.2.2.2]; simp [pA, y2]
  have hT3_f_agree : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d },
      (∀ j : Fin 5, x.val ≠ cut.cutDart j) →
      T3.f.f (Sum.inl x) = Sum.inl (TL.f.f x) := by
    intro x hx
    change (coupleEdge S3 (pA 4) y2).f.f (Sum.inl x) = Sum.inl (TL.f.f x)
    rw [coupleEdge_f_of_ne S3
      (fun h => hx 4 (congrArg Subtype.val (Sum.inl.inj h)))
      (by simp)]
    exact hS3_f_agree x hx
  have hT3_f_vals :
      T3.f.f (pA 0) = y2 ∧
      T3.f.f y2 = Sum.inl (TL.f.f (a 4)) ∧
      T3.f.f y0 = Sum.inl (TL.f.f (a 0)) ∧
      T3.f.f (pA 1) = Sum.inl (TL.f.f (a 2)) ∧
      T3.f.f (pA 3) = y0 ∧
      T3.f.f (pA 2) = Sum.inl (TL.f.f (a 1)) ∧
      T3.f.f y1 = Sum.inl (TL.f.f (a 3)) ∧
      T3.f.f (pA 4) = y1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (coupleEdge S3 (pA 4) y2).f.f (pA 0) = y2
      rw [coupleEdge_f_of_ne S3
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      change (coupleEdge S2 (pA 3) y1).f.f (pA 0) = y2
      rw [coupleEdge_f_of_ne S2
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 0) = y2
      rw [coupleEdge_f_of_ne S1
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 0) = y2
      rw [coupleEdge_f_left T0]
      exact congrArg Sum.inr c3_f_0
    · change (coupleEdge S3 (pA 4) y2).f.f y2 = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_right S3 (by simp)]
      change (coupleEdge S2 (pA 3) y1).f.f (pA 4) = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_of_ne S2
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 4) = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_of_ne S1
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 4) = Sum.inl (TL.f.f (a 4))
      rw [coupleEdge_f_of_ne T0
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      rfl
    · change (coupleEdge S3 (pA 4) y2).f.f y0 = Sum.inl (TL.f.f (a 0))
      rw [coupleEdge_f_of_ne S3 (by simp) (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      change (coupleEdge S2 (pA 3) y1).f.f y0 = Sum.inl (TL.f.f (a 0))
      rw [coupleEdge_f_of_ne S2 (by simp) (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f y0 = Sum.inl (TL.f.f (a 0))
      rw [coupleEdge_f_of_ne S1 (by simp) (by simp)]
      change (coupleEdge T0 (pA 0) y0).f.f y0 = Sum.inl (TL.f.f (a 0))
      rw [coupleEdge_f_right T0 (by simp)]
      rfl
    · change (coupleEdge S3 (pA 4) y2).f.f (pA 1) = Sum.inl (TL.f.f (a 2))
      rw [coupleEdge_f_of_ne S3
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      change (coupleEdge S2 (pA 3) y1).f.f (pA 1) = Sum.inl (TL.f.f (a 2))
      rw [coupleEdge_f_of_ne S2
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 1) = Sum.inl (TL.f.f (a 2))
      rw [coupleEdge_f_left S1]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 2) = Sum.inl (TL.f.f (a 2))
      rw [coupleEdge_f_of_ne T0
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      rfl
    · change (coupleEdge S3 (pA 4) y2).f.f (pA 3) = y0
      rw [coupleEdge_f_of_ne S3
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      change (coupleEdge S2 (pA 3) y1).f.f (pA 3) = y0
      rw [coupleEdge_f_left S2]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f y1 = y0
      rw [coupleEdge_f_of_ne S1 (by simp) (by simp)]
      change (coupleEdge T0 (pA 0) y0).f.f y1 = y0
      rw [coupleEdge_f_of_ne T0 (by simp) (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      exact congrArg Sum.inr c3_f_1
    · change (coupleEdge S3 (pA 4) y2).f.f (pA 2) = Sum.inl (TL.f.f (a 1))
      rw [coupleEdge_f_of_ne S3
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      change (coupleEdge S2 (pA 3) y1).f.f (pA 2) = Sum.inl (TL.f.f (a 1))
      rw [coupleEdge_f_of_ne S2
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 2) = Sum.inl (TL.f.f (a 1))
      rw [coupleEdge_f_right S1 (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 1) = Sum.inl (TL.f.f (a 1))
      rw [coupleEdge_f_of_ne T0
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      rfl
    · change (coupleEdge S3 (pA 4) y2).f.f y1 = Sum.inl (TL.f.f (a 3))
      rw [coupleEdge_f_of_ne S3 (by simp) (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      change (coupleEdge S2 (pA 3) y1).f.f y1 = Sum.inl (TL.f.f (a 3))
      rw [coupleEdge_f_right S2 (by simp)]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f (pA 3) = Sum.inl (TL.f.f (a 3))
      rw [coupleEdge_f_of_ne S1
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide))]
      change (coupleEdge T0 (pA 0) y0).f.f (pA 3) = Sum.inl (TL.f.f (a 3))
      rw [coupleEdge_f_of_ne T0
        (fun h => absurd (congrArg Fin.val (hpA_inj _ _ h)) (by decide)) (by simp)]
      rfl
    · change (coupleEdge S3 (pA 4) y2).f.f (pA 4) = y1
      rw [coupleEdge_f_left S3]
      change (coupleEdge S2 (pA 3) y1).f.f y2 = y1
      rw [coupleEdge_f_of_ne S2 (by simp) (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      change (coupleEdge S1 (pA 1) (pA 2)).f.f y2 = y1
      rw [coupleEdge_f_of_ne S1 (by simp) (by simp)]
      change (coupleEdge T0 (pA 0) y0).f.f y2 = y1
      rw [coupleEdge_f_of_ne T0 (by simp) (fun h => absurd (congrArg Fin.val (Sum.inr.inj h)) (by decide))]
      exact congrArg Sum.inr c3_f_2
  let H3 : Hypermap := tripleToHypermap T3 h3_invol
  let tag3 : D3 → Nat := fun z =>
    match z with
    | Sum.inr j =>
      if j.val = 0 then 1
      else if j.val = 1 then 4
      else 0
    | Sum.inl x =>
      if cut.inArcL darts h_mc.complete 0 x.val then 0
      else if cut.inArcL darts h_mc.complete 1 x.val then 1
      else if cut.inArcL darts h_mc.complete 2 x.val then 2
      else if cut.inArcL darts h_mc.complete 3 x.val then 1
      else if cut.inArcL darts h_mc.complete 4 x.val then 4
      else 6
  have htag3_inArc : ∀ (i : Fin 5) (x : { d : H.Dart // cut.capSingleVertex_DL d }),
      cut.inArcL darts h_mc.complete i x.val →
      tag3 (Sum.inl x) =
        if i.val = 0 then 0 else if i.val = 2 then 2 else if i.val = 4 then 4 else 1 := by
    intro i x hi
    dsimp [tag3]
    have huniq : ∀ j : Fin 5, cut.inArcL darts h_mc.complete j x.val → j = i := fun j hj =>
      inArcL_unique_idx darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut hj hi
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      rcases i with ⟨iv, hiv⟩
      have hv : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4 := by omega
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    rcases hi_cases with rfl | rfl | rfl | rfl | rfl
    · rw [if_pos hi]; rfl
    · rw [if_neg (fun h => absurd (congrArg Fin.val (huniq 0 h)) (by decide)),
        if_pos hi]; rfl
    · rw [if_neg (fun h => absurd (congrArg Fin.val (huniq 0 h)) (by decide)),
        if_neg (fun h => absurd (congrArg Fin.val (huniq 1 h)) (by decide)),
        if_pos hi]; rfl
    · rw [if_neg (fun h => absurd (congrArg Fin.val (huniq 0 h)) (by decide)),
        if_neg (fun h => absurd (congrArg Fin.val (huniq 1 h)) (by decide)),
        if_neg (fun h => absurd (congrArg Fin.val (huniq 2 h)) (by decide)),
        if_pos hi]; rfl
    · rw [if_neg (fun h => absurd (congrArg Fin.val (huniq 0 h)) (by decide)),
        if_neg (fun h => absurd (congrArg Fin.val (huniq 1 h)) (by decide)),
        if_neg (fun h => absurd (congrArg Fin.val (huniq 2 h)) (by decide)),
        if_neg (fun h => absurd (congrArg Fin.val (huniq 3 h)) (by decide)),
        if_pos hi]; rfl
  have htag3_none : ∀ (x : { d : H.Dart // cut.capSingleVertex_DL d }),
      (∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i x.val) → tag3 (Sum.inl x) = 6 := by
    intro x hnone
    dsimp only [tag3]
    rw [if_neg (hnone 0), if_neg (hnone 1),
      if_neg (hnone 2), if_neg (hnone 3), if_neg (hnone 4)]
  have htag3_inv : ∀ z : D3, tag3 (T3.f.f z) = tag3 z := by
    intro z
    rcases z with ⟨d, hd⟩ | ⟨j, hj⟩
    · by_cases hcut : ∃ m : Fin 5, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        have hsum_eq : (Sum.inl ⟨cut.cutDart m, hd⟩ : D3) = pA m :=
          congrArg Sum.inl (Subtype.ext rfl)
        rw [hsum_eq]
        have hm_arc := cut.cutDart_mem_inArcL darts h_mc.complete m
        rcases m with ⟨mv, hmv⟩
        rcases show mv = 0 ∨ mv = 1 ∨ mv = 2 ∨ mv = 3 ∨ mv = 4 by omega with
          rfl | rfl | rfl | rfl | rfl
        · change tag3 (T3.f.f (pA 0)) = tag3 (pA 0)
          rw [hT3_f_vals.1, htag3_inArc 0 (a 0) hm_arc]; rfl
        · change tag3 (T3.f.f (pA 1)) = tag3 (pA 1)
          rw [hT3_f_vals.2.2.2.1]
          obtain ⟨ht1, _, h_in, _⟩ := TL_arc_segment darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut 2 (by decide)
          have hfx_arc : cut.inArcL darts h_mc.complete 3 (TL.f.f (a 2)).val := by
            have := h_in 1 (by omega) ht1
            simpa [Perm.iter_succ, Perm.iter_zero] using this
          rw [htag3_inArc 3 (TL.f.f (a 2)) hfx_arc, htag3_inArc 1 (a 1) hm_arc]
          decide
        · change tag3 (T3.f.f (pA 2)) = tag3 (pA 2)
          rw [hT3_f_vals.2.2.2.2.2.1]
          obtain ⟨ht1, _, h_in, _⟩ := TL_arc_segment darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut 1 (by decide)
          have hfx_arc : cut.inArcL darts h_mc.complete 2 (TL.f.f (a 1)).val := by
            have := h_in 1 (by omega) ht1
            simpa [Perm.iter_succ, Perm.iter_zero] using this
          rw [htag3_inArc 2 (TL.f.f (a 1)) hfx_arc, htag3_inArc 2 (a 2) hm_arc]
        · change tag3 (T3.f.f (pA 3)) = tag3 (pA 3)
          rw [hT3_f_vals.2.2.2.2.1, htag3_inArc 3 (a 3) hm_arc]; rfl
        · change tag3 (T3.f.f (pA 4)) = tag3 (pA 4)
          rw [hT3_f_vals.2.2.2.2.2.2.2, htag3_inArc 4 (a 4) hm_arc]; rfl
      · have hne : ∀ m : Fin 5, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
        rw [hT3_f_agree ⟨d, hd⟩ hne]
        by_cases harc : ∃ i : Fin 5, cut.inArcL darts h_mc.complete i d
        · rcases harc with ⟨i, hi_arc⟩
          let m : Nat := (i.val + 4) % 5
          have hm5 : m < 5 := Nat.mod_lt _ (by decide)
          have hm_succ : (⟨(m + 1) % 5, by omega⟩ : Fin 5) = i := by
            apply Fin.ext; dsimp [m]; omega
          obtain ⟨ht1, h_end, h_fwd, h_bwd, _⟩ :=
            TL_arc_segment darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut m hm5
          obtain ⟨r, hr1, hrt, hr_eq⟩ := h_bwd d (by simpa [hm_succ] using hi_arc)
          have hr_lt : r < cut.posL darts h_mc.complete (m + 1) - cut.posL darts h_mc.complete m := by
            by_cases hreq : r = cut.posL darts h_mc.complete (m + 1) - cut.posL darts h_mc.complete m
            · subst hreq
              have heq_am := hr_eq.symm.trans h_end
              exact absurd (congrArg Subtype.val heq_am) (hne ⟨(m + 1) % 5, Nat.mod_lt _ (by decide)⟩)
            · omega
          have hfx_eq : TL.f.f ⟨d, hd⟩ = Perm.iter TL.f (r + 1) (a ⟨m, hm5⟩) := by
            rw [← hr_eq, Perm.iter_succ]
          have hfx_arc : cut.inArcL darts h_mc.complete i (TL.f.f ⟨d, hd⟩).val := by
            have := h_fwd (r + 1) (by omega) (by omega)
            rw [← hm_succ, congrArg Subtype.val hfx_eq]; exact this
          rw [htag3_inArc i (TL.f.f ⟨d, hd⟩) hfx_arc, htag3_inArc i ⟨d, hd⟩ hi_arc]
        · have hnone : ∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d := fun i h => harc ⟨i, h⟩
          have hnone' := TL_not_inArcL_f_closed darts h_mc.complete cut ⟨d, hd⟩ hnone
          rw [htag3_none (TL.f.f ⟨d, hd⟩) hnone', htag3_none ⟨d, hd⟩ hnone]
    · rcases show j = 0 ∨ j = 1 ∨ j = 2 by omega with rfl | rfl | rfl
      · rw [show (Sum.inr ⟨0, hj⟩ : D3) = y0 from rfl, hT3_f_vals.2.2.1]
        obtain ⟨ht1, _, h_in, _⟩ := TL_arc_segment darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut 0 (by decide)
        have hfx_arc : cut.inArcL darts h_mc.complete 1 (TL.f.f (a 0)).val := by
          have := h_in 1 (by omega) ht1
          simpa [Perm.iter_succ, Perm.iter_zero] using this
        rw [htag3_inArc 1 (TL.f.f (a 0)) hfx_arc]; rfl
      · rw [show (Sum.inr ⟨1, hj⟩ : D3) = y1 from rfl, hT3_f_vals.2.2.2.2.2.2.1]
        obtain ⟨ht1, _, h_in, _⟩ := TL_arc_segment darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut 3 (by decide)
        have hfx_arc : cut.inArcL darts h_mc.complete 4 (TL.f.f (a 3)).val := by
          have := h_in 1 (by omega) ht1
          simpa [Perm.iter_succ, Perm.iter_zero] using this
        rw [htag3_inArc 4 (TL.f.f (a 3)) hfx_arc]; rfl
      · rw [show (Sum.inr ⟨2, hj⟩ : D3) = y2 from rfl, hT3_f_vals.2.1]
        obtain ⟨ht1, _, h_in, _⟩ := TL_arc_segment darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut 4 (by decide)
        have hfx_arc : cut.inArcL darts h_mc.complete 0 (TL.f.f (a 4)).val := by
          have := h_in 1 (by omega) ht1
          simpa [Perm.iter_succ, Perm.iter_zero] using this
        rw [htag3_inArc 0 (TL.f.f (a 4)) hfx_arc]; rfl
  have hH3_planar : @Hypermap.isPlanar H3 (@instBEqOfDecidableEq D3 instDecD3) dartsU.length dartsU = true :=
    @tripleToHypermap_isPlanar D3 instDecD3 T3 h3_invol dartsU hU_nd hU_all hgen4 h3_no_fix
  have hH3_br : @Math.Hypermap.isBridgeless H3 instDecD3 dartsU dartsU.length := by
    rw [@isBridgeless_iff_no_sameOrbit_face_edge_jcs H3 instDecD3 dartsU hU_all]
    intro x hso
    change SameOrbit T3.f x (T3.e.f x) at hso
    have htag_eq := sameOrbit_of_f_agree_inv tag3 T3.f htag3_inv hso
    rcases x with ⟨d, hd⟩ | ⟨j, hj⟩
    · by_cases hcut : ∃ m : Fin 5, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        have hsum_eq : (Sum.inl ⟨cut.cutDart m, hd⟩ : D3) = pA m :=
          congrArg Sum.inl (Subtype.ext rfl)
        rw [hsum_eq] at htag_eq
        have hm_arc := cut.cutDart_mem_inArcL darts h_mc.complete m
        have htag_m := htag3_inArc m (a m) hm_arc
        have hm_cases : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by
          rcases m with ⟨mv, hmv⟩
          have hv : mv = 0 ∨ mv = 1 ∨ mv = 2 ∨ mv = 3 ∨ mv = 4 := by omega
          rcases hv with rfl | rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        rcases hm_cases with rfl | rfl | rfl | rfl | rfl
        · change tag3 (pA 0) = tag3 (T3.e.f (pA 0)) at htag_eq
          rw [h3_e_pairs.1, htag3_inArc 0 (a 0) hm_arc] at htag_eq
          dsimp [tag3, y0] at htag_eq
          exact absurd htag_eq (by decide)
        · change tag3 (pA 1) = tag3 (T3.e.f (pA 1)) at htag_eq
          rw [h3_e_pairs.2.2.1, htag3_inArc 1 (a 1) hm_arc,
            htag3_inArc 2 (a 2) (cut.cutDart_mem_inArcL darts h_mc.complete 2)] at htag_eq
          exact absurd htag_eq (by decide)
        · change tag3 (pA 2) = tag3 (T3.e.f (pA 2)) at htag_eq
          rw [h3_e_pairs.2.2.2.1, htag3_inArc 2 (a 2) hm_arc,
            htag3_inArc 1 (a 1) (cut.cutDart_mem_inArcL darts h_mc.complete 1)] at htag_eq
          exact absurd htag_eq (by decide)
        · change tag3 (pA 3) = tag3 (T3.e.f (pA 3)) at htag_eq
          rw [h3_e_pairs.2.2.2.2.1, htag3_inArc 3 (a 3) hm_arc] at htag_eq
          dsimp [tag3, y1] at htag_eq
          exact absurd htag_eq (by decide)
        · change tag3 (pA 4) = tag3 (T3.e.f (pA 4)) at htag_eq
          rw [h3_e_pairs.2.2.2.2.2.2.1, htag3_inArc 4 (a 4) hm_arc] at htag_eq
          dsimp [tag3, y2] at htag_eq
          exact absurd htag_eq (by decide)
      · have hne : ∀ m : Fin 5, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
        obtain ⟨hdn, he_eq⟩ := h3_e_ext d hd hne
        rw [he_eq] at htag_eq
        by_cases harc : ∃ i : Fin 5, cut.inArcL darts h_mc.complete i d
        · rcases harc with ⟨i, hi_arc⟩
          rw [htag3_inArc i ⟨d, hd⟩ hi_arc] at htag_eq
          by_cases harc' : ∃ j : Fin 5, cut.inArcL darts h_mc.complete j (H.edge.f d)
          · rcases harc' with ⟨j, hj_arc⟩
            rw [htag3_inArc j ⟨H.edge.f d, hdn⟩ hj_arc] at htag_eq
            have hso1 := ((cut.inArcL_iff_sameOrbit_and_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn i d).mp hi_arc).1
            have hso2 := ((cut.inArcL_iff_sameOrbit_and_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn j (H.edge.f d)).mp hj_arc).1
            by_cases hij : i = j
            · subst hij
              have hbr_d := sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hso1) hso2
              exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp
                h_mc.is_bridgeless d hbr_d
            · rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
              have hij' : iv ≠ jv := fun h => hij (Fin.ext h)
              rcases show iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4 by omega with
                rfl | rfl | rfl | rfl | rfl <;>
              rcases show jv = 0 ∨ jv = 1 ∨ jv = 2 ∨ jv = 3 ∨ jv = 4 by omega with
                rfl | rfl | rfl | rfl | rfl <;>
              simp at htag_eq hij'
              · exact h_chord 1 3 (by decide) (by decide) (by decide) d hso1 hso2
              · exact h_chord 3 1 (by decide) (by decide) (by decide) d hso1 hso2
          · have hnone' : ∀ j : Fin 5, ¬cut.inArcL darts h_mc.complete j (H.edge.f d) := fun j h => harc' ⟨j, h⟩
            rw [htag3_none ⟨H.edge.f d, hdn⟩ hnone'] at htag_eq
            rcases i with ⟨iv, hiv⟩
            rcases show iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4 by omega with
              rfl | rfl | rfl | rfl | rfl <;> simp at htag_eq
        · have hnone : ∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d := fun i h => harc ⟨i, h⟩
          rw [htag3_none ⟨d, hd⟩ hnone] at htag_eq
          have hnone' : ∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i (H.edge.f d) := by
            intro i hi
            rw [htag3_inArc i ⟨H.edge.f d, hdn⟩ hi] at htag_eq
            rcases i with ⟨iv, hiv⟩
            rcases show iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3 ∨ iv = 4 by omega with
              rfl | rfl | rfl | rfl | rfl <;> simp at htag_eq
          have h_iter_ext : ∀ r : Nat,
              ∃ (d' : H.Dart) (hd' : cut.capSingleVertex_DL d'),
                (∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d') ∧
                Perm.iter T3.f r (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨d', hd'⟩ ∧
                Perm.iter H.face r d = d' := by
            intro r
            induction r with
            | zero => exact ⟨d, hd, hnone, rfl, rfl⟩
            | succ r ih =>
              obtain ⟨d', hd', hnone', hiterT, hiterH⟩ := ih
              have hne' : ∀ m : Fin 5, d' ≠ cut.cutDart m := fun m hm =>
                hnone' m (hm ▸ cut.cutDart_mem_inArcL darts h_mc.complete m)
              have hnotf' : ∀ i : Fin 5, ¬SameOrbit H.face (cut.ringFace i) d' := fun i hs =>
                hnone' i ((cut.inArcL_iff_sameOrbit_and_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn i d').mpr
                  ⟨hs, hd'⟩)
              have hnot_b' : ∀ m : Fin 5, d' ≠ H.edge.f (cut.cutDart m) := fun m heq =>
                h_disjLR d' ⟨hd', heq ▸ (h_cutLR m).2⟩
              have hf_eq : (TL.f.f ⟨d', hd'⟩).val = H.face.f d' := by
                rw [TL_f_val]
                exact (h_unc_ext d' (fun m => ⟨hne' m, hnot_b' m⟩)).2
              refine ⟨(TL.f.f ⟨d', hd'⟩).val, (TL.f.f ⟨d', hd'⟩).property,
                TL_not_inArcL_f_closed darts h_mc.complete cut ⟨d', hd'⟩ hnone', ?_, ?_⟩
              · rw [Perm.iter_succ, hiterT, hT3_f_agree ⟨d', hd'⟩ hne']
              · rw [Perm.iter_succ, hiterH, ← hf_eq]
          obtain ⟨t, ht⟩ := hso
          obtain ⟨d', hd', _, hT_t, hH_t⟩ := h_iter_ext t
          rw [hT_t, he_eq] at ht
          have hd_eq : d' = H.edge.f d := congrArg Subtype.val (Sum.inl.inj ht)
          exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp
            h_mc.is_bridgeless d ⟨t, hH_t.trans hd_eq⟩
    · rcases show j = 0 ∨ j = 1 ∨ j = 2 by omega with rfl | rfl | rfl
      · rw [show (Sum.inr ⟨0, hj⟩ : D3) = y0 from rfl, h3_e_pairs.2.1,
          htag3_inArc 0 (a 0) (cut.cutDart_mem_inArcL darts h_mc.complete 0)] at htag_eq
        dsimp [tag3, y0] at htag_eq
        exact absurd htag_eq (by decide)
      · rw [show (Sum.inr ⟨1, hj⟩ : D3) = y1 from rfl, h3_e_pairs.2.2.2.2.2.1,
          htag3_inArc 3 (a 3) (cut.cutDart_mem_inArcL darts h_mc.complete 3)] at htag_eq
        dsimp [tag3, y1] at htag_eq
        exact absurd htag_eq (by decide)
      · rw [show (Sum.inr ⟨2, hj⟩ : D3) = y2 from rfl, h3_e_pairs.2.2.2.2.2.2.2,
          htag3_inArc 4 (a 4) (cut.cutDart_mem_inArcL darts h_mc.complete 4)] at htag_eq
        dsimp [tag3, y2] at htag_eq
        exact absurd htag_eq (by decide)
  have hU_ne : dartsU ≠ [] := by
    intro hempty
    have hmem := hU_all y0
    rw [hempty] at hmem; cases hmem
  have hU_lt : dartsU.length < darts.length := by
    have hsum_sides := side_lengths_sum darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
    rw [hU_len, hL_len]; omega
  obtain ⟨col3⟩ := @h_mc.is_minimal H3 instDecD3 dartsU hU_nd hU_all hU_ne hU_lt hH3_planar hH3_br
  have h_edge_int : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d), (∀ m : Fin 5, d ≠ cut.cutDart m) →
      ∃ hdn : cut.capSingleVertex_DL (H.edge.f d), H3.edge.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩ :=
    fun d hd hne => h3_e_ext d hd hne
  have h_face_int : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      (∀ i : Fin 5, ¬SameOrbit H.face (cut.ringFace i) d) →
      ∃ hfn : cut.capSingleVertex_DL (H.face.f d), H3.face.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.face.f d, hfn⟩ := by
    intro d hd hnotf
    have hnone : ∀ i : Fin 5, ¬cut.inArcL darts h_mc.complete i d := fun i hi =>
      hnotf i ((cut.inArcL_iff_sameOrbit_and_DL darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn i d).mp hi).1
    have hne : ∀ m : Fin 5, d ≠ cut.cutDart m := fun m hm =>
      hnone m (hm ▸ cut.cutDart_mem_inArcL darts h_mc.complete m)
    have hnot_b : ∀ m : Fin 5, d ≠ H.edge.f (cut.cutDart m) := fun m heq =>
      h_disjLR d ⟨hd, heq ▸ (h_cutLR m).2⟩
    have hf_eq : (TL.f.f ⟨d, hd⟩).val = H.face.f d := by
      rw [TL_f_val]; exact (h_unc_ext d (fun m => ⟨hne m, hnot_b m⟩)).2
    refine ⟨hf_eq ▸ (TL.f.f ⟨d, hd⟩).property, ?_⟩
    change T3.f.f (Sum.inl ⟨d, hd⟩) = _
    rw [hT3_f_agree ⟨d, hd⟩ hne]
    apply congrArg Sum.inl; apply Subtype.ext; exact hf_eq
  have h_face_ring : ∀ (m : Fin 5) (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      cut.inArcL darts h_mc.complete ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ d →
      SameOrbit H3.face (H3.edge.f (pA m)) (Sum.inl ⟨d, hd⟩) := by
    intro m d hd hd_arc
    change SameOrbit T3.f (T3.e.f (pA m)) (Sum.inl ⟨d, hd⟩)
    rcases m with ⟨mv, hmv⟩
    rcases show mv = 0 ∨ mv = 1 ∨ mv = 2 ∨ mv = 3 ∨ mv = 4 by omega with
      rfl | rfl | rfl | rfl | rfl
    · change SameOrbit T3.f (T3.e.f (pA 0)) (Sum.inl ⟨d, hd⟩)
      rw [h3_e_pairs.1]
      exact (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
        cut T3 hT3_f_agree 0 (by decide) y0 hT3_f_vals.2.2.1).2.2 d hd hd_arc
    · change SameOrbit T3.f (T3.e.f (pA 1)) (Sum.inl ⟨d, hd⟩)
      rw [h3_e_pairs.2.2.1]
      exact (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
        cut T3 hT3_f_agree 1 (by decide) (pA 2) hT3_f_vals.2.2.2.2.2.1).2.2 d hd hd_arc
    · change SameOrbit T3.f (T3.e.f (pA 2)) (Sum.inl ⟨d, hd⟩)
      rw [h3_e_pairs.2.2.2.1]
      exact (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
        cut T3 hT3_f_agree 2 (by decide) (pA 1) hT3_f_vals.2.2.2.1).2.2 d hd hd_arc
    · change SameOrbit T3.f (T3.e.f (pA 3)) (Sum.inl ⟨d, hd⟩)
      rw [h3_e_pairs.2.2.2.2.1]
      exact (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
        cut T3 hT3_f_agree 3 (by decide) y1 hT3_f_vals.2.2.2.2.2.2.1).2.2 d hd hd_arc
    · change SameOrbit T3.f (T3.e.f (pA 4)) (Sum.inl ⟨d, hd⟩)
      rw [h3_e_pairs.2.2.2.2.2.2.1]
      exact (arc_transport darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
        cut T3 hT3_f_agree 4 (by decide) y2 hT3_f_vals.2.1).2.2 d hd hd_arc
  obtain ⟨col, _, hcol_inr⟩ := capColoring_of_gadget darts h_mc.nodup h_mc.complete h_mc.is_planar
    h_conn h_mc.is_bridgeless cut H3 id h_edge_int h_face_int h_face_ring col3
  have hcol_face_so : ∀ u v : H3.Dart, SameOrbit H3.face u v → col3.color u = col3.color v := by
    intro u v ⟨n, hn⟩
    have hiter : ∀ r : Nat, col3.color u = col3.color (Perm.iter H3.face r u) := by
      intro r
      induction r with
      | zero => rfl
      | succ r ih =>
        rw [Perm.iter_succ]
        exact ih.trans (col3.face_invariant (Perm.iter H3.face r u)).symm
    rw [hiter n, hn]
  have hsame_e02 : SameOrbit H3.face (H3.edge.f (pA 0)) (H3.edge.f (pA 2)) := by
    have hs1 := h_face_ring 0 (cut.cutDart 1)
      (a 1).property (cut.cutDart_mem_inArcL darts h_mc.complete 1)
    change SameOrbit T3.f (T3.e.f (pA 0)) (T3.e.f (pA 2))
    rw [h3_e_pairs.2.2.2.1]
    exact hs1
  have hf13 : capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col 1 =
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col 3 := by
    have h1 := hcol_inr 0
    have h3 := hcol_inr 2
    have hm1 : (⟨(1 + 4) % 5, by decide⟩ : Fin 5) = 0 := rfl
    have hm3 : (⟨(3 + 4) % 5, by decide⟩ : Fin 5) = 2 := rfl
    change col.color (Sum.inr ⟨(1 + 4) % 5, _⟩) = col.color (Sum.inr ⟨(3 + 4) % 5, _⟩)
    rw [hm1, hm3, h1, h3]
    exact hcol_face_so _ _ hsame_e02
  have hres := fin5_eq13_imp_state5
    (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col)
    (fun j => capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
      h_mc.is_bridgeless cut col j)
    hf13
  exact ⟨col, hres⟩

private theorem dl_rev_length_rot1 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) :
    (darts.filter (fun x => decide (cut.rot1.rev.capSingleVertex_DL x))).length =
    (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length := by
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have hs1 := side_lengths_sum darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
  have hs2 := side_lengths_sum darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut.rot1
  have heq : darts.filter (fun x => decide (cut.rot1.capSingleVertex_DL x)) =
      darts.filter (fun x => decide (cut.capSingleVertex_DL x)) := by
    apply List.filter_congr
    intro x _
    exact decide_eq_decide.mpr (cut.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn x)
  rw [heq] at hs2
  omega

private theorem rot1_state5T {f g : Fin 5 → Color}
    (h : ∀ i : Fin 5, f i = g ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩)
    {m : Fin 5} (hm : IsState5T m g) :
    IsState5T ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ f := by
  dsimp [IsState5T] at hm ⊢
  have step : ∀ a : Nat,
      g ⟨(↑(⟨((m.val + 1) % 5 + a) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) + 4) % 5,
        Nat.mod_lt _ (by decide)⟩ = g ⟨(m.val + a) % 5, Nat.mod_lt _ (by decide)⟩ := by
    intro a
    congr 1
    apply Fin.ext
    dsimp
    have hm5 := m.isLt
    omega
  exact ⟨by rw [h _, h _, step 1, step 3]; exact hm.1,
         by rw [h _, h _, step 2, step 4]; exact hm.2⟩

private theorem rot1_state5Q {f g : Fin 5 → Color}
    (h : ∀ i : Fin 5, f i = g ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩)
    {m : Fin 5} (hm : IsState5Q m g) :
    IsState5Q ⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ f := by
  dsimp [IsState5Q] at hm ⊢
  have step0 :
      g ⟨(↑(⟨(m.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) + 4) % 5,
        Nat.mod_lt _ (by decide)⟩ = g m := by
    congr 1
    apply Fin.ext
    dsimp
    have hm5 := m.isLt
    omega
  have step : ∀ a : Nat,
      g ⟨(↑(⟨((m.val + 1) % 5 + a) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) + 4) % 5,
        Nat.mod_lt _ (by decide)⟩ = g ⟨(m.val + a) % 5, Nat.mod_lt _ (by decide)⟩ := by
    intro a
    congr 1
    apply Fin.ext
    dsimp
    have hm5 := m.isLt
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [h _, h _, step 4, step 1]; exact hm.1
  · rw [h _, h _, step0, step 2]; exact hm.2.1
  · rw [h _, h _, step0, step 3]; exact hm.2.2

private theorem pull1_states5 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (c : H.FaceCycleCut 5) (a b q : Fin 5)
    (h : ∃ col_rot : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
        h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) c.rot1).FaceColoring,
      IsState5T a (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) c.rot1 col_rot) ∨
      IsState5T b (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) c.rot1 col_rot) ∨
      IsState5Q q (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) c.rot1 col_rot)) :
    ∃ col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
        h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) c).FaceColoring,
      IsState5T ⟨(a.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) c col) ∨
      IsState5T ⟨(b.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) c col) ∨
      IsState5Q ⟨(q.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) c col) := by
  obtain ⟨col_rot, hst⟩ := h
  obtain ⟨col, hcol⟩ := capColoring_of_rot1_gen darts h_mc.nodup h_mc.complete h_mc.is_planar
    (mc_numComponents_eq_one H darts h_mc) h_mc.is_bridgeless (by decide) c col_rot
  refine ⟨col, ?_⟩
  rcases hst with hTa | hTb | hQq
  · exact Or.inl (rot1_state5T hcol hTa)
  · exact Or.inr (Or.inl (rot1_state5T hcol hTb))
  · exact Or.inr (Or.inr (rot1_state5Q hcol hQq))

theorem cap5_identify_realizable {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut)
    (h21R : 21 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length)
    (k : Fin 5) :
    ∃ col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
      h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState5T ⟨(k.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) cut col) ∨
      IsState5T ⟨(k.val + 3) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) cut col) ∨
      IsState5Q k
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) cut col) := by
  have h1 : Chordless5 cut.rot1 := chordless5_rot1 cut h_chord
  have h2 : Chordless5 cut.rot1.rot1 := chordless5_rot1 _ h1
  have h3 : Chordless5 cut.rot1.rot1.rot1 := chordless5_rot1 _ h2
  have h4 : Chordless5 cut.rot1.rot1.rot1.rot1 := chordless5_rot1 _ h3
  have l1 : 21 ≤ (darts.filter (fun x => decide (cut.rot1.rev.capSingleVertex_DL x))).length := by
    rw [dl_rev_length_rot1 darts h_mc cut]; exact h21R
  have l2 : 21 ≤ (darts.filter (fun x => decide (cut.rot1.rot1.rev.capSingleVertex_DL x))).length := by
    rw [dl_rev_length_rot1 darts h_mc cut.rot1]; exact l1
  have l3 : 21 ≤ (darts.filter (fun x => decide (cut.rot1.rot1.rot1.rev.capSingleVertex_DL x))).length := by
    rw [dl_rev_length_rot1 darts h_mc cut.rot1.rot1]; exact l2
  have l4 : 21 ≤ (darts.filter (fun x => decide (cut.rot1.rot1.rot1.rot1.rev.capSingleVertex_DL x))).length := by
    rw [dl_rev_length_rot1 darts h_mc cut.rot1.rot1.rot1]; exact l3
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    rcases k with ⟨kv, hkv⟩
    simp only [Fin.ext_iff]
    omega
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · have h_base := cap5_identify0_realizable darts h_mc cut.rot1.rot1.rot1 h3 l3
    have p1 := pull1_states5 darts h_mc cut.rot1.rot1 _ _ _ h_base
    have p2 := pull1_states5 darts h_mc cut.rot1 _ _ _ p1
    have p3 := pull1_states5 darts h_mc cut _ _ _ p2
    obtain ⟨col, hst⟩ := p3
    refine ⟨col, ?_⟩
    rcases hst with hA | hB | hC
    · exact Or.inr (Or.inl hA)
    · exact Or.inl hB
    · exact Or.inr (Or.inr hC)
  · have h_base := cap5_identify0_realizable darts h_mc cut.rot1.rot1.rot1.rot1 h4 l4
    have p1 := pull1_states5 darts h_mc cut.rot1.rot1.rot1 _ _ _ h_base
    have p2 := pull1_states5 darts h_mc cut.rot1.rot1 _ _ _ p1
    have p3 := pull1_states5 darts h_mc cut.rot1 _ _ _ p2
    have p4 := pull1_states5 darts h_mc cut _ _ _ p3
    obtain ⟨col, hst⟩ := p4
    refine ⟨col, ?_⟩
    rcases hst with hA | hB | hC
    · exact Or.inr (Or.inl hA)
    · exact Or.inl hB
    · exact Or.inr (Or.inr hC)
  · obtain ⟨col, hst⟩ := cap5_identify0_realizable darts h_mc cut h_chord h21R
    refine ⟨col, ?_⟩
    rcases hst with hA | hB | hC
    · exact Or.inr (Or.inl hA)
    · exact Or.inl hB
    · exact Or.inr (Or.inr hC)
  · have h_base := cap5_identify0_realizable darts h_mc cut.rot1 h1 l1
    have p1 := pull1_states5 darts h_mc cut _ _ _ h_base
    obtain ⟨col, hst⟩ := p1
    refine ⟨col, ?_⟩
    rcases hst with hA | hB | hC
    · exact Or.inr (Or.inl hA)
    · exact Or.inl hB
    · exact Or.inr (Or.inr hC)
  · have h_base := cap5_identify0_realizable darts h_mc cut.rot1.rot1 h2 l2
    have p1 := pull1_states5 darts h_mc cut.rot1 _ _ _ h_base
    have p2 := pull1_states5 darts h_mc cut _ _ _ p1
    obtain ⟨col, hst⟩ := p2
    refine ⟨col, ?_⟩
    rcases hst with hA | hB | hC
    · exact Or.inr (Or.inl hA)
    · exact Or.inl hB
    · exact Or.inr (Or.inr hC)

private noncomputable def cap5RingDart {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (cut : H.FaceCycleCut 5) (j : Fin 5) :
    (FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut).Dart :=
  Sum.inr ⟨(j.val + 4) % 5, Nat.mod_lt _ (by decide)⟩

private noncomputable def cap5_dual_cyclicOrder4_right {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (cut : H.FaceCycleCut 5) (i : Fin 5) :
    let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut
    let r := cap5RingDart darts h_nd h_all h_planar h_conn cut
    CyclicOrder4 H_cap.dual.face 5 (r i) (r (i + 3)) (r (i + 2)) (r (i + 1)) :=
  match i with
  | ⟨0, _⟩ =>
    FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
      (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
  | ⟨1, _⟩ =>
    cyclicOrder4_rot _ (cyclicOrder4_rot _ (cyclicOrder4_rot _
      (FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))))
  | ⟨2, _⟩ =>
    cyclicOrder4_rot _ (cyclicOrder4_rot _ (cyclicOrder4_rot _
      (FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))))
  | ⟨3, _⟩ =>
    cyclicOrder4_rot _ (cyclicOrder4_rot _
      (FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)))
  | ⟨4, _⟩ =>
    cyclicOrder4_rot _
      (FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))

private noncomputable def cap5_dual_cyclicOrder4_left {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (cut : H.FaceCycleCut 5) (i : Fin 5) :
    let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut
    let r := cap5RingDart darts h_nd h_all h_planar h_conn cut
    CyclicOrder4 H_cap.dual.face 5 (r i) (r (i + 4)) (r (i + 3)) (r (i + 2)) :=
  match i with
  | ⟨0, _⟩ =>
    FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
      (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)
  | ⟨1, _⟩ =>
    cyclicOrder4_rot _ (cyclicOrder4_rot _ (cyclicOrder4_rot _
      (FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))))
  | ⟨2, _⟩ =>
    cyclicOrder4_rot _ (cyclicOrder4_rot _
      (FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)))
  | ⟨3, _⟩ =>
    cyclicOrder4_rot _
      (FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))
  | ⟨4, _⟩ =>
    FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
      (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)

private theorem b5_reach_right {D : Type} {e n : Perm D} {P : D → Prop} {x y : D}
    (h : ReachENIn e n P x y) : P y := by
  cases h with
  | refl hp => exact hp
  | step_n_fwd _ hp => exact hp
  | step_n_bwd _ hp => exact hp
  | step_e _ hp => exact hp

private def b5KempePred (H : Hypermap) (col : H.FaceColoring) (a b : Color)
    (start z : H.Dart) : Prop :=
  ReachENIn H.dual.edge H.dual.node (fun w => col.color w = a ∨ col.color w = b) start z

private noncomputable def b5KempeComp (H : Hypermap) (col : H.FaceColoring) (a b : Color)
    (start : H.Dart) : H.Dart → Bool :=
  fun z => decide (b5KempePred H col a b start z)

private theorem b5_reach_to_comp_walk {D : Type} {e n : Perm D} {P : D → Prop} {s y : D}
    (h : ReachENIn e n P s y) : ReachENIn e n (ReachENIn e n P s) s y := by
  induction h with
  | refl hp => exact ReachENIn.refl (ReachENIn.refl hp)
  | step_n_fwd w hp ih => exact ReachENIn.step_n_fwd ih (ReachENIn.step_n_fwd w hp)
  | step_n_bwd w hp ih => exact ReachENIn.step_n_bwd ih (ReachENIn.step_n_bwd w hp)
  | step_e w hp ih => exact ReachENIn.step_e ih (ReachENIn.step_e w hp)

private theorem b5_reach_color {H : Hypermap} {col : H.FaceColoring} {a b : Color} {s z : H.Dart}
    (h : b5KempePred H col a b s z) : col.color z = a ∨ col.color z = b :=
  b5_reach_right (P := fun w => col.color w = a ∨ col.color w = b) h

private theorem b5_kempeComp_closed (H : Hypermap) (col : H.FaceColoring) (a b : Color)
    (start : H.Dart) :
    H.KempeClosed col a b (b5KempeComp H col a b start) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d
    simp only [b5KempeComp]
    apply decide_eq_decide.mpr
    constructor
    · intro h
      have hcd : col.color d = a ∨ col.color d = b := by
        rw [← col.face_invariant d]
        exact b5_reach_color h
      have hw : b5KempePred H col a b start (H.dual.node.f (H.face.f d)) :=
        ReachENIn.step_n_fwd h (by
          change col.color (H.face.inv (H.face.f d)) = a ∨ col.color (H.face.inv (H.face.f d)) = b
          rw [H.face.left_inv d]
          exact hcd)
      have heq : H.dual.node.f (H.face.f d) = d := H.face.left_inv d
      rwa [heq] at hw
    · intro h
      have hfd : col.color (H.face.f d) = a ∨ col.color (H.face.f d) = b := by
        rw [col.face_invariant d]
        exact b5_reach_color h
      exact ReachENIn.step_n_bwd h hfd
  · intro d hd
    exact b5_reach_color (of_decide_eq_true hd)
  · intro d hd hed
    simp only [b5KempeComp]
    apply decide_eq_decide.mpr
    constructor
    · intro h
      have hw : b5KempePred H col a b start (H.dual.edge.f (H.edge.f d)) :=
        ReachENIn.step_e h (by
          change col.color (H.edge.f (H.edge.f d)) = a ∨ col.color (H.edge.f (H.edge.f d)) = b
          rw [H.edge_involution d]
          exact hd)
      have heq : H.dual.edge.f (H.edge.f d) = d := H.edge_involution d
      rwa [heq] at hw
    · intro h
      exact ReachENIn.step_e h hed

private theorem kempe_either_swap_cycle {H_cap : Hypermap} [DecidableEq H_cap.Dart]
    (darts_cap : List H_cap.Dart) (h_nd : darts_cap.Nodup) (h_all : ∀ d, d ∈ darts_cap)
    (h_planar : H_cap.isPlanar darts_cap.length darts_cap = true)
    (col : H_cap.FaceColoring)
    {L : Nat} {d0 d1 d2 d3 : H_cap.Dart}
    (hc : CyclicOrder4 H_cap.dual.face L d0 d1 d2 d3)
    {a b c d : Color}
    (h_disj : (a ≠ c ∧ a ≠ d) ∧ (b ≠ c ∧ b ≠ d))
    (h0 : col.color d0 = a) (h2 : col.color d2 = b)
    (h1 : col.color d1 = c) (h3 : col.color d3 = c) :
    (∃ col' : H_cap.FaceColoring,
      col'.color d0 = b ∧ col'.color d2 = b ∧
      (∀ x, col.color x ≠ a → col.color x ≠ b → col'.color x = col.color x)) ∨
    (∃ col' : H_cap.FaceColoring,
      col'.color d1 = d ∧ col'.color d3 = c ∧
      (∀ x, col.color x ≠ c → col.color x ≠ d → col'.color x = col.color x)) := by
  have h_planar_dual : H_cap.dual.isPlanar darts_cap.length darts_cap = true :=
    (isPlanar_dual H_cap darts_cap h_nd h_all (Nat.le_refl _)).trans h_planar
  have hface_inv : ∀ u, col.color (H_cap.face.inv u) = col.color u := fun u => by
    rw [← col.face_invariant (H_cap.face.inv u), H_cap.face.right_inv u]
  have hinv : ∀ (x y : Color) (s : H_cap.Dart) (z : H_cap.Dart),
      b5KempePred H_cap col x y s (H_cap.dual.node.f z) ↔ b5KempePred H_cap col x y s z := by
    intro x y s z
    constructor
    · intro h
      have hcz : col.color z = x ∨ col.color z = y := by
        have hr := b5_reach_color h
        change col.color (H_cap.face.inv z) = x ∨ col.color (H_cap.face.inv z) = y at hr
        rwa [hface_inv z] at hr
      have hw : b5KempePred H_cap col x y s (H_cap.dual.node.inv (H_cap.dual.node.f z)) :=
        ReachENIn.step_n_bwd h (by rw [H_cap.dual.node.left_inv]; exact hcz)
      rwa [H_cap.dual.node.left_inv] at hw
    · intro h
      have hpr : col.color z = x ∨ col.color z = y := b5_reach_color h
      exact ReachENIn.step_n_fwd h (by
        change col.color (H_cap.face.inv z) = x ∨ col.color (H_cap.face.inv z) = y
        rw [hface_inv z]
        exact hpr)
  by_cases hr1 : b5KempePred H_cap col a b d0 d2
  · have hnr2 : ¬ b5KempePred H_cap col c d d1 d3 := by
      intro hr2
      obtain ⟨z, hz1, hz2⟩ := alternating_walks_intersect_of_cyclic_face
        H_cap.dual darts_cap h_nd h_all h_planar_dual hc
        (b5KempePred H_cap col a b d0) (b5KempePred H_cap col c d d1)
        (hinv a b d0) (hinv c d d1)
        (b5_reach_to_comp_walk hr1) (b5_reach_to_comp_walk hr2)
      rcases b5_reach_color hz1 with hza | hzb <;>
        rcases b5_reach_color hz2 with hzc | hzd
      · exact h_disj.1.1 (hza.symm.trans hzc)
      · exact h_disj.1.2 (hza.symm.trans hzd)
      · exact h_disj.2.1 (hzb.symm.trans hzc)
      · exact h_disj.2.2 (hzb.symm.trans hzd)
    refine Or.inr ⟨H_cap.kempeSwap_valid col c d (b5KempeComp H_cap col c d d1)
      (b5_kempeComp_closed H_cap col c d d1), ?_, ?_, ?_⟩
    · have hd1 : b5KempeComp H_cap col c d d1 d1 = true :=
        decide_eq_true (ReachENIn.refl (Or.inl h1))
      simp [kempeSwap_valid, kempeSwap, hd1, swapColor, h1]
    · have hd3 : b5KempeComp H_cap col c d d1 d3 = false :=
        decide_eq_false hnr2
      simp [kempeSwap_valid, kempeSwap, hd3, h3]
    · intro x hxc hxd
      have hx : b5KempeComp H_cap col c d d1 x = false := decide_eq_false (fun hx_pred => by
        rcases b5_reach_color hx_pred with hc_eq | hd_eq
        · exact hxc hc_eq
        · exact hxd hd_eq)
      simp [kempeSwap_valid, kempeSwap, hx]
  · refine Or.inl ⟨H_cap.kempeSwap_valid col a b (b5KempeComp H_cap col a b d0)
      (b5_kempeComp_closed H_cap col a b d0), ?_, ?_, ?_⟩
    · have hd0 : b5KempeComp H_cap col a b d0 d0 = true :=
        decide_eq_true (ReachENIn.refl (Or.inl h0))
      simp [kempeSwap_valid, kempeSwap, hd0, swapColor, h0]
    · have hd2 : b5KempeComp H_cap col a b d0 d2 = false :=
        decide_eq_false hr1
      simp [kempeSwap_valid, kempeSwap, hd2, h2]
    · intro x hxa hxb
      have hx : b5KempeComp H_cap col a b d0 x = false := decide_eq_false (fun hx_pred => by
        rcases b5_reach_color hx_pred with ha_eq | hb_eq
        · exact hxa ha_eq
        · exact hxb hb_eq)
      simp [kempeSwap_valid, kempeSwap, hx]

private theorem exists_fourth_color (a b c : Color) :
    ∃ d : Color, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  cases a <;> cases b <;> cases c <;>
    first
    | exact ⟨Color.c0, by decide, by decide, by decide⟩
    | exact ⟨Color.c1, by decide, by decide, by decide⟩
    | exact ⟨Color.c2, by decide, by decide, by decide⟩
    | exact ⟨Color.c3, by decide, by decide, by decide⟩

private theorem cap5_bnd_eq {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ (d : H.Dart), d ∈ darts)
    (h_pl : H.isPlanar darts.length darts = true) (h_conn : H.numComponents darts.length darts = 1)
    (cut : H.FaceCycleCut 5)
    (col' : (FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_pl h_conn cut).FaceColoring)
    {x y a b : Fin 5} (hxa : x.val = a.val) (hyb : y.val = b.val)
    (h : col'.color (cap5RingDart darts h_nd h_all h_pl h_conn cut a) =
         col'.color (cap5RingDart darts h_nd h_all h_pl h_conn cut b)) :
    capBoundaryColors darts h_nd h_all h_pl h_conn cut col' x =
    capBoundaryColors darts h_nd h_all h_pl h_conn cut col' y := by
  have hx : x = a := Fin.ext hxa
  have hy : y = b := Fin.ext hyb
  subst hx; subst hy; exact h

private theorem cap5_bnd_ne {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ (d : H.Dart), d ∈ darts)
    (h_pl : H.isPlanar darts.length darts = true) (h_conn : H.numComponents darts.length darts = 1)
    (cut : H.FaceCycleCut 5)
    (col' : (FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_pl h_conn cut).FaceColoring)
    {x y a b : Fin 5} (hxa : x.val = a.val) (hyb : y.val = b.val)
    (h : col'.color (cap5RingDart darts h_nd h_all h_pl h_conn cut a) ≠
         col'.color (cap5RingDart darts h_nd h_all h_pl h_conn cut b)) :
    capBoundaryColors darts h_nd h_all h_pl h_conn cut col' x ≠
    capBoundaryColors darts h_nd h_all h_pl h_conn cut col' y := by
  have hx : x = a := Fin.ext hxa
  have hy : y = b := Fin.ext hyb
  subst hx; subst hy; exact h

theorem cap5_kempe_right {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (i : Fin 5)
    (col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
      h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring)
    (hT : IsState5T i (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut col)) :
    ∃ col' : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
      h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState5T ⟨(i.val + 4) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) cut col') ∨
      IsState5Q ⟨(i.val + 3) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) cut col') := by
  have h_conn := mc_numComponents_eq_one H darts h_mc
  let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
    h_mc.is_planar h_conn cut
  have hspec := FaceCycleCut.capSingleVertex_spec darts h_mc.nodup h_mc.complete
    h_mc.is_planar h_conn h_mc.is_bridgeless cut
  let darts_cap := FaceCycleCut.capSingleVertexDarts darts cut
  let r := cap5RingDart darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
  let f := capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col
  have hf_eq : ∀ j : Fin 5, col.color (r j) = f j := fun _ => rfl
  have hadj : ∀ j : Fin 5, f j ≠ f ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ :=
    fun j => (capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
      h_mc.is_bridgeless cut col j).symm
  let u := f i
  let y := f (i + 1)
  let z := f (i + 2)
  have h13 : f (i + 1) = f (i + 3) := hT.1
  have h24 : f (i + 2) = f (i + 4) := hT.2
  have huy : u ≠ y := by
    have ha := hadj i
    have hi1 : (⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i + 1 := by
      rw [Fin.ext_iff, Fin.val_add]; dsimp
    rwa [hi1] at ha
  have hyz : y ≠ z := by
    have ha := hadj (i + 1)
    have hi2 : (⟨((i + 1).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i + 2 := by
      rw [Fin.ext_iff, Fin.val_add, Fin.val_add]; dsimp; omega
    rwa [hi2] at ha
  have huz : u ≠ z := by
    have ha := hadj (i + 4)
    have hi0 : (⟨((i + 4).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i := by
      rw [Fin.ext_iff, Fin.val_add]; dsimp; omega
    rw [hi0, ← h24] at ha
    exact ha.symm
  obtain ⟨third, h3u, h3y, h3z⟩ := exists_fourth_color u y z
  have hc := cap5_dual_cyclicOrder4_right darts h_mc.nodup h_mc.complete
    h_mc.is_planar h_conn cut i
  have h_cap_pl : @Hypermap.isPlanar H_cap instBEqOfDecidableEq darts_cap.length darts_cap = true := by
    rw [← capSingleVertex_beq_eq cut]
    exact hspec.2.2.2.2.1
  have hswap := kempe_either_swap_cycle darts_cap hspec.1 hspec.2.1 h_cap_pl col hc
    ⟨⟨huy, h3u.symm⟩, ⟨hyz.symm, h3z.symm⟩⟩
    (hf_eq i) (hf_eq (i + 2)) ((hf_eq (i + 3)).trans h13.symm) (hf_eq (i + 1))
  rcases hswap with ⟨col', h0', h2', hpres⟩ | ⟨col', h1', h3', hpres⟩
  · refine ⟨col', Or.inl ?_⟩
    dsimp [IsState5T]
    constructor
    · refine cap5_bnd_eq darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i) (b := i + 2)
        (by dsimp; have := i.isLt; omega)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega) ?_
      change col'.color (r i) = col'.color (r (i + 2))
      rw [h0', h2']
    · refine cap5_bnd_eq darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 1) (b := i + 3)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 1)) = col'.color (r (i + 3))
      have p1 := hpres (r (i + 1)) huy.symm hyz
      have p3 := hpres (r (i + 3))
        (by rw [hf_eq (i + 3), ← h13]; exact huy.symm)
        (by rw [hf_eq (i + 3), ← h13]; exact hyz)
      rw [p1, p3, hf_eq (i + 1), hf_eq (i + 3), h13]
  · refine ⟨col', Or.inr ?_⟩
    dsimp [IsState5Q]
    refine ⟨?_, ?_, ?_⟩
    · refine cap5_bnd_eq darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 2) (b := i + 4)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 2)) = col'.color (r (i + 4))
      have p2 := hpres (r (i + 2)) hyz.symm h3z.symm
      have p4 := hpres (r (i + 4))
        (by rw [hf_eq (i + 4), ← h24]; exact hyz.symm)
        (by rw [hf_eq (i + 4), ← h24]; exact h3z.symm)
      rw [p2, p4, hf_eq (i + 2), hf_eq (i + 4), h24]
    · refine cap5_bnd_ne darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 3) (b := i)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega)
        (by dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 3)) ≠ col'.color (r i)
      have p0 := hpres (r i) huy h3u.symm
      rw [h1', p0, hf_eq i]
      exact h3u
    · refine cap5_bnd_ne darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 3) (b := i + 1)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 3)) ≠ col'.color (r (i + 1))
      rw [h1', h3']
      exact h3y

theorem cap5_kempe_left {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (i : Fin 5)
    (col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
      h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring)
    (hT : IsState5T i (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut col)) :
    ∃ col' : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
      h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState5T ⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) cut col') ∨
      IsState5Q ⟨(i.val + 2) % 5, Nat.mod_lt _ (by decide)⟩
        (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) cut col') := by
  have h_conn := mc_numComponents_eq_one H darts h_mc
  let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete
    h_mc.is_planar h_conn cut
  have hspec := FaceCycleCut.capSingleVertex_spec darts h_mc.nodup h_mc.complete
    h_mc.is_planar h_conn h_mc.is_bridgeless cut
  let darts_cap := FaceCycleCut.capSingleVertexDarts darts cut
  let r := cap5RingDart darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut
  let f := capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col
  have hf_eq : ∀ j : Fin 5, col.color (r j) = f j := fun _ => rfl
  have hadj : ∀ j : Fin 5, f j ≠ f ⟨(j.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ :=
    fun j => (capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn
      h_mc.is_bridgeless cut col j).symm
  let u := f i
  let y := f (i + 1)
  let z := f (i + 2)
  have h13 : f (i + 1) = f (i + 3) := hT.1
  have h24 : f (i + 2) = f (i + 4) := hT.2
  have huy : u ≠ y := by
    have ha := hadj i
    have hi1 : (⟨(i.val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i + 1 := by
      rw [Fin.ext_iff, Fin.val_add]; dsimp
    rwa [hi1] at ha
  have hyz : y ≠ z := by
    have ha := hadj (i + 1)
    have hi2 : (⟨((i + 1).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i + 2 := by
      rw [Fin.ext_iff, Fin.val_add, Fin.val_add]; dsimp; omega
    rwa [hi2] at ha
  have huz : u ≠ z := by
    have ha := hadj (i + 4)
    have hi0 : (⟨((i + 4).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = i := by
      rw [Fin.ext_iff, Fin.val_add]; dsimp; omega
    rw [hi0, ← h24] at ha
    exact ha.symm
  obtain ⟨third, h3u, h3y, h3z⟩ := exists_fourth_color u y z
  have hc := cap5_dual_cyclicOrder4_left darts h_mc.nodup h_mc.complete
    h_mc.is_planar h_conn cut i
  have h_cap_pl : @Hypermap.isPlanar H_cap instBEqOfDecidableEq darts_cap.length darts_cap = true := by
    rw [← capSingleVertex_beq_eq cut]
    exact hspec.2.2.2.2.1
  have hswap := kempe_either_swap_cycle darts_cap hspec.1 hspec.2.1 h_cap_pl col hc
    ⟨⟨huz, h3u.symm⟩, ⟨hyz, h3y.symm⟩⟩
    (hf_eq i) ((hf_eq (i + 3)).trans h13.symm) ((hf_eq (i + 4)).trans h24.symm) (hf_eq (i + 2))
  rcases hswap with ⟨col', h0', h2', hpres⟩ | ⟨col', h1', h3', hpres⟩
  · refine ⟨col', Or.inl ?_⟩
    dsimp [IsState5T]
    constructor
    · refine cap5_bnd_eq darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 2) (b := i + 4)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 2)) = col'.color (r (i + 4))
      have p2 := hpres (r (i + 2)) huz.symm hyz.symm
      have p4 := hpres (r (i + 4))
        (by rw [hf_eq (i + 4), ← h24]; exact huz.symm)
        (by rw [hf_eq (i + 4), ← h24]; exact hyz.symm)
      rw [p2, p4, hf_eq (i + 2), hf_eq (i + 4), h24]
    · refine cap5_bnd_eq darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 3) (b := i)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega)
        (by dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 3)) = col'.color (r i)
      rw [h2', h0']
  · refine ⟨col', Or.inr ?_⟩
    dsimp [IsState5Q]
    refine ⟨?_, ?_, ?_⟩
    · refine cap5_bnd_eq darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 1) (b := i + 3)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 1)) = col'.color (r (i + 3))
      have p1 := hpres (r (i + 1)) hyz h3y.symm
      have p3 := hpres (r (i + 3))
        (by rw [hf_eq (i + 3), ← h13]; exact hyz)
        (by rw [hf_eq (i + 3), ← h13]; exact h3y.symm)
      rw [p1, p3, hf_eq (i + 1), hf_eq (i + 3), h13]
    · refine cap5_bnd_ne darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 2) (b := i + 4)
        (by rw [Fin.val_add]; dsimp)
        (by rw [Fin.val_add]; dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 2)) ≠ col'.color (r (i + 4))
      rw [h3', h1']
      exact h3z.symm
    · refine cap5_bnd_ne darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col' (a := i + 2) (b := i)
        (by rw [Fin.val_add]; dsimp)
        (by dsimp; have := i.isLt; omega) ?_
      change col'.color (r (i + 2)) ≠ col'.color (r i)
      have p0 := hpres (r i) huz h3u.symm
      rw [h3', p0, hf_eq i]
      exact huz.symm

end Birkhoff5Gadgets

section BirkhoffCombinatorics

private def pack5Bits (b0 b1 b2 b3 b4 : Bool) : Nat :=
  (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
  (if b3 then 8 else 0) + (if b4 then 16 else 0)

private theorem pack5Bits_lt32 (b0 b1 b2 b3 b4 : Bool) : pack5Bits b0 b1 b2 b3 b4 < 32 := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private theorem testBit5_pack (b0 b1 b2 b3 b4 : Bool) :
    (((pack5Bits b0 b1 b2 b3 b4 >>> 0) &&& 1 == 1) = b0) ∧
    (((pack5Bits b0 b1 b2 b3 b4 >>> 1) &&& 1 == 1) = b1) ∧
    (((pack5Bits b0 b1 b2 b3 b4 >>> 2) &&& 1 == 1) = b2) ∧
    (((pack5Bits b0 b1 b2 b3 b4 >>> 3) &&& 1 == 1) = b3) ∧
    (((pack5Bits b0 b1 b2 b3 b4 >>> 4) &&& 1 == 1) = b4) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private def encodeT (S : Fin 10 → Bool) : Fin 32 :=
  ⟨pack5Bits (S 0) (S 1) (S 2) (S 3) (S 4), pack5Bits_lt32 _ _ _ _ _⟩

private def hasT (m : Nat) (i : Fin 5) : Bool :=
  ((m >>> i.val) &&& 1) == 1

private theorem hasT_encodeT (S : Fin 10 → Bool) (i : Fin 5) :
    hasT (encodeT S).val i = S ⟨i.val, by omega⟩ := by
  have hp := testBit5_pack (S 0) (S 1) (S 2) (S 3) (S 4)
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    rcases i with ⟨iv, hiv⟩; simp only [Fin.ext_iff]; omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.1
  · exact hp.2.2.2.1
  · exact hp.2.2.2.2

private def forcedQ (m : Nat) (q : Fin 5) : Bool :=
  (!(hasT m ⟨(q.val + 2) % 5, Nat.mod_lt _ (by decide)⟩) &&
   !(hasT m ⟨(q.val + 3) % 5, Nat.mod_lt _ (by decide)⟩)) ||
  (hasT m ⟨(q.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ &&
   !(hasT m ⟨(q.val + 1) % 5, Nat.mod_lt _ (by decide)⟩)) ||
  (hasT m ⟨(q.val + 3) % 5, Nat.mod_lt _ (by decide)⟩ &&
   !(hasT m ⟨(q.val + 4) % 5, Nat.mod_lt _ (by decide)⟩))

private def maskPairBad (mL mR : Nat) : Bool :=
  !((List.finRange 5).any (fun i => hasT mL i)) ||
  !((List.finRange 5).any (fun i => hasT mR i)) ||
  (List.finRange 5).any (fun i => hasT mL i && hasT mR i) ||
  (List.finRange 5).any (fun q => forcedQ mL q && forcedQ mR q)

private def allMasksBad : Bool :=
  (List.finRange 32).all (fun mL =>
    (List.finRange 32).all (fun mR => maskPairBad mL.val mR.val))

private theorem allMasksBad_true : allMasksBad = true := by decide

private theorem forcedQ_sound (S : Fin 10 → Bool)
    (h_id : ∀ k : Fin 5,
      S ⟨(k.val + 2) % 5, by omega⟩ = true ∨
      S ⟨(k.val + 3) % 5, by omega⟩ = true ∨
      S ⟨k.val + 5, by omega⟩ = true)
    (h_kr : ∀ i : Fin 5, S ⟨i.val, by omega⟩ = true →
      S ⟨(i.val + 4) % 5, by omega⟩ = true ∨
      S ⟨(i.val + 3) % 5 + 5, by omega⟩ = true)
    (h_kl : ∀ i : Fin 5, S ⟨i.val, by omega⟩ = true →
      S ⟨(i.val + 1) % 5, by omega⟩ = true ∨
      S ⟨(i.val + 2) % 5 + 5, by omega⟩ = true)
    (q : Fin 5) (hq : forcedQ (encodeT S).val q = true) :
    S ⟨q.val + 5, by omega⟩ = true := by
  dsimp [forcedQ] at hq
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    hasT_encodeT] at hq
  rcases hq with (⟨h2, h3⟩ | ⟨h2, h1⟩) | ⟨h3, h4⟩
  · rcases h_id q with hT2 | hT3 | hQ
    · rw [hT2] at h2; cases h2
    · rw [hT3] at h3; cases h3
    · exact hQ
  · have hstep := h_kr ⟨(q.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ h2
    have hidx1 : (⟨((⟨(q.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5).val + 4) % 5,
        by omega⟩ : Fin 10) = ⟨(q.val + 1) % 5, by omega⟩ := by
      rw [Fin.ext_iff]; dsimp; omega
    have hidxQ : (⟨((⟨(q.val + 2) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5).val + 3) % 5 + 5,
        by omega⟩ : Fin 10) = ⟨q.val + 5, by omega⟩ := by
      rw [Fin.ext_iff]; dsimp; have := q.isLt; omega
    rcases hstep with hT | hQ
    · rw [hidx1] at hT; rw [hT] at h1; cases h1
    · rw [hidxQ] at hQ; exact hQ
  · have hstep := h_kl ⟨(q.val + 3) % 5, Nat.mod_lt _ (by decide)⟩ h3
    have hidx1 : (⟨((⟨(q.val + 3) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5).val + 1) % 5,
        by omega⟩ : Fin 10) = ⟨(q.val + 4) % 5, by omega⟩ := by
      rw [Fin.ext_iff]; dsimp; omega
    have hidxQ : (⟨((⟨(q.val + 3) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5).val + 2) % 5 + 5,
        by omega⟩ : Fin 10) = ⟨q.val + 5, by omega⟩ := by
      rw [Fin.ext_iff]; dsimp; have := q.isLt; omega
    rcases hstep with hT | hQ
    · rw [hidx1] at hT; rw [hT] at h4; cases h4
    · rw [hidxQ] at hQ; exact hQ

theorem birkhoff_ten_state_contradiction (S_L S_R : Fin 10 → Bool)
    (h_pentL : ∃ i : Fin 5, S_L ⟨i.val, by omega⟩ = true)
    (h_pentR : ∃ i : Fin 5, S_R ⟨i.val, by omega⟩ = true)
    (h_idL : ∀ k : Fin 5, S_L ⟨(k.val + 2) % 5, by omega⟩ = true ∨
      S_L ⟨(k.val + 3) % 5, by omega⟩ = true ∨ S_L ⟨k.val + 5, by omega⟩ = true)
    (h_idR : ∀ k : Fin 5, S_R ⟨(k.val + 2) % 5, by omega⟩ = true ∨
      S_R ⟨(k.val + 3) % 5, by omega⟩ = true ∨ S_R ⟨k.val + 5, by omega⟩ = true)
    (h_krL : ∀ i : Fin 5, S_L ⟨i.val, by omega⟩ = true →
      S_L ⟨(i.val + 4) % 5, by omega⟩ = true ∨ S_L ⟨(i.val + 3) % 5 + 5, by omega⟩ = true)
    (h_klL : ∀ i : Fin 5, S_L ⟨i.val, by omega⟩ = true →
      S_L ⟨(i.val + 1) % 5, by omega⟩ = true ∨ S_L ⟨(i.val + 2) % 5 + 5, by omega⟩ = true)
    (h_krR : ∀ i : Fin 5, S_R ⟨i.val, by omega⟩ = true →
      S_R ⟨(i.val + 4) % 5, by omega⟩ = true ∨ S_R ⟨(i.val + 3) % 5 + 5, by omega⟩ = true)
    (h_klR : ∀ i : Fin 5, S_R ⟨i.val, by omega⟩ = true →
      S_R ⟨(i.val + 1) % 5, by omega⟩ = true ∨ S_R ⟨(i.val + 2) % 5 + 5, by omega⟩ = true)
    (h_disj : ∀ x : Fin 10, ¬(S_L x = true ∧ S_R x = true)) :
    False := by
  let mL := encodeT S_L
  let mR := encodeT S_R
  have hall : maskPairBad mL.val mR.val = true := by
    have h1 := List.all_eq_true.mp allMasksBad_true mL (List.mem_finRange mL)
    exact List.all_eq_true.mp h1 mR (List.mem_finRange mR)
  dsimp [maskPairBad] at hall
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, List.any_eq_false,
    Bool.and_eq_true] at hall
  rcases hall with ((hnL | hnR) | ⟨i, _, hiL, hiR⟩) | ⟨q, _, hqL, hqR⟩
  · rcases h_pentL with ⟨i, hi⟩
    have hfi := hnL i (List.mem_finRange i)
    rw [hasT_encodeT, hi] at hfi; contradiction
  · rcases h_pentR with ⟨i, hi⟩
    have hfi := hnR i (List.mem_finRange i)
    rw [hasT_encodeT, hi] at hfi; contradiction
  · rw [hasT_encodeT] at hiL hiR
    exact h_disj ⟨i.val, by omega⟩ ⟨hiL, hiR⟩
  · have hsL := forcedQ_sound S_L h_idL h_krL h_klL q hqL
    have hsR := forcedQ_sound S_R h_idR h_krR h_klR q hqR
    exact h_disj ⟨q.val + 5, by omega⟩ ⟨hsL, hsR⟩

theorem mc_five_cycle_both_sides_ge21_impossible {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut)
    (h21L : 21 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length)
    (h21R : 21 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) :
    False := by
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h21LL : 21 ≤ (darts.filter (fun x => decide (cut.rev.rev.capSingleVertex_DL x))).length := by
    have hfilt : darts.filter (fun x => decide (cut.rev.rev.capSingleVertex_DL x)) =
        darts.filter (fun x => decide (cut.capSingleVertex_DL x)) := by
      apply List.filter_congr
      intro x _
      rw [FaceCycleCut.rev_rev cut]
    rw [hfilt]; exact h21L
  have h_chordR : Chordless5 cut.rev := chordless5_rev cut h_chord
  let bndL := fun col => capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut col
  let bndR := fun col => capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar h_conn cut.rev col
  let S_L : Fin 10 → Bool := fun x =>
    if hx : x.val < 5 then
      decide (∃ col, IsState5T ⟨x.val, hx⟩ (bndL col))
    else
      decide (∃ col, IsState5Q ⟨x.val - 5, by omega⟩ (bndL col))
  let revIdx : Fin 5 → Fin 5 := fun j => ⟨(5 - j.val) % 5, Nat.mod_lt _ (by decide)⟩
  let S_R : Fin 10 → Bool := fun x =>
    if hx : x.val < 5 then
      decide (∃ col, IsState5T (revIdx ⟨x.val, hx⟩) (bndR col))
    else
      decide (∃ col, IsState5Q (revIdx ⟨x.val - 5, by omega⟩) (bndR col))
  have hL_T_spec : ∀ i : Fin 5, S_L ⟨i.val, by omega⟩ = true ↔ ∃ col, IsState5T i (bndL col) := by
    intro i; dsimp [S_L]; simp [i.isLt]
  have hL_Q_spec : ∀ q : Fin 5, S_L ⟨q.val + 5, by omega⟩ = true ↔ ∃ col, IsState5Q q (bndL col) := by
    intro q; dsimp [S_L]
    have hnot : ¬(q.val + 5 < 5) := by omega
    rw [dif_neg hnot, decide_eq_true_eq]
    have hsub : (⟨q.val + 5 - 5, by omega⟩ : Fin 5) = q := by rw [Fin.ext_iff]; dsimp; omega
    rw [hsub]
  have hR_T_spec : ∀ i : Fin 5, S_R ⟨i.val, by omega⟩ = true ↔ ∃ col, IsState5T (revIdx i) (bndR col) := by
    intro i; dsimp [S_R]; simp [i.isLt]
  have hR_Q_spec : ∀ q : Fin 5, S_R ⟨q.val + 5, by omega⟩ = true ↔ ∃ col, IsState5Q (revIdx q) (bndR col) := by
    intro q; dsimp [S_R]
    have hnot : ¬(q.val + 5 < 5) := by omega
    rw [dif_neg hnot, decide_eq_true_eq]
    have hsub : (⟨q.val + 5 - 5, by omega⟩ : Fin 5) = q := by rw [Fin.ext_iff]; dsimp; omega
    rw [hsub]
  have h_pentL : ∃ i : Fin 5, S_L ⟨i.val, by omega⟩ = true := by
    obtain ⟨i, col, hT⟩ := cap5_pentagon_realizable darts h_mc cut h21R
    exact ⟨i, (hL_T_spec i).mpr ⟨col, hT⟩⟩
  have h_pentR : ∃ i : Fin 5, S_R ⟨i.val, by omega⟩ = true := by
    obtain ⟨j, col, hT⟩ := cap5_pentagon_realizable darts h_mc cut.rev h21LL
    have hrev_inv : revIdx (revIdx j) = j := by
      rw [Fin.ext_iff]; dsimp [revIdx]; have := j.isLt; omega
    exact ⟨revIdx j, (hR_T_spec (revIdx j)).mpr ⟨col, by rw [hrev_inv]; exact hT⟩⟩
  have h_idL : ∀ k : Fin 5, S_L ⟨(k.val + 2) % 5, by omega⟩ = true ∨
      S_L ⟨(k.val + 3) % 5, by omega⟩ = true ∨ S_L ⟨k.val + 5, by omega⟩ = true := by
    intro k
    obtain ⟨col, hst⟩ := cap5_identify_realizable darts h_mc cut h_chord h21R k
    rcases hst with h2 | h3 | hQ
    · exact Or.inl ((hL_T_spec ⟨(k.val + 2) % 5, by omega⟩).mpr ⟨col, h2⟩)
    · exact Or.inr (Or.inl ((hL_T_spec ⟨(k.val + 3) % 5, by omega⟩).mpr ⟨col, h3⟩))
    · exact Or.inr (Or.inr ((hL_Q_spec k).mpr ⟨col, hQ⟩))
  have h_idR : ∀ k : Fin 5, S_R ⟨(k.val + 2) % 5, by omega⟩ = true ∨
      S_R ⟨(k.val + 3) % 5, by omega⟩ = true ∨ S_R ⟨k.val + 5, by omega⟩ = true := by
    intro k
    obtain ⟨col, hst⟩ := cap5_identify_realizable darts h_mc cut.rev h_chordR h21LL (revIdx k)
    rcases hst with h2 | h3 | hQ
    · have hid : (⟨((revIdx k).val + 2) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
          revIdx ⟨(k.val + 3) % 5, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp [revIdx]; have := k.isLt; omega
      rw [hid] at h2
      exact Or.inr (Or.inl ((hR_T_spec ⟨(k.val + 3) % 5, by omega⟩).mpr ⟨col, h2⟩))
    · have hid : (⟨((revIdx k).val + 3) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
          revIdx ⟨(k.val + 2) % 5, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp [revIdx]; have := k.isLt; omega
      rw [hid] at h3
      exact Or.inl ((hR_T_spec ⟨(k.val + 2) % 5, by omega⟩).mpr ⟨col, h3⟩)
    · exact Or.inr (Or.inr ((hR_Q_spec k).mpr ⟨col, hQ⟩))
  have h_krL : ∀ i : Fin 5, S_L ⟨i.val, by omega⟩ = true →
      S_L ⟨(i.val + 4) % 5, by omega⟩ = true ∨ S_L ⟨(i.val + 3) % 5 + 5, by omega⟩ = true := by
    intro i hi
    obtain ⟨col, hT⟩ := (hL_T_spec i).mp hi
    obtain ⟨col', hT' | hQ'⟩ := cap5_kempe_right darts h_mc cut i col hT
    · exact Or.inl ((hL_T_spec ⟨(i.val + 4) % 5, by omega⟩).mpr ⟨col', hT'⟩)
    · exact Or.inr ((hL_Q_spec ⟨(i.val + 3) % 5, by omega⟩).mpr ⟨col', hQ'⟩)
  have h_klL : ∀ i : Fin 5, S_L ⟨i.val, by omega⟩ = true →
      S_L ⟨(i.val + 1) % 5, by omega⟩ = true ∨ S_L ⟨(i.val + 2) % 5 + 5, by omega⟩ = true := by
    intro i hi
    obtain ⟨col, hT⟩ := (hL_T_spec i).mp hi
    obtain ⟨col', hT' | hQ'⟩ := cap5_kempe_left darts h_mc cut i col hT
    · exact Or.inl ((hL_T_spec ⟨(i.val + 1) % 5, by omega⟩).mpr ⟨col', hT'⟩)
    · exact Or.inr ((hL_Q_spec ⟨(i.val + 2) % 5, by omega⟩).mpr ⟨col', hQ'⟩)
  have h_krR : ∀ i : Fin 5, S_R ⟨i.val, by omega⟩ = true →
      S_R ⟨(i.val + 4) % 5, by omega⟩ = true ∨ S_R ⟨(i.val + 3) % 5 + 5, by omega⟩ = true := by
    intro i hi
    obtain ⟨col, hT⟩ := (hR_T_spec i).mp hi
    obtain ⟨col', hT' | hQ'⟩ := cap5_kempe_left darts h_mc cut.rev (revIdx i) col hT
    · have hid : (⟨((revIdx i).val + 1) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
          revIdx ⟨(i.val + 4) % 5, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp [revIdx]; have := i.isLt; omega
      rw [hid] at hT'
      exact Or.inl ((hR_T_spec ⟨(i.val + 4) % 5, by omega⟩).mpr ⟨col', hT'⟩)
    · have hid : (⟨((revIdx i).val + 2) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
          revIdx ⟨(i.val + 3) % 5, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp [revIdx]; have := i.isLt; omega
      rw [hid] at hQ'
      exact Or.inr ((hR_Q_spec ⟨(i.val + 3) % 5, by omega⟩).mpr ⟨col', hQ'⟩)
  have h_klR : ∀ i : Fin 5, S_R ⟨i.val, by omega⟩ = true →
      S_R ⟨(i.val + 1) % 5, by omega⟩ = true ∨ S_R ⟨(i.val + 2) % 5 + 5, by omega⟩ = true := by
    intro i hi
    obtain ⟨col, hT⟩ := (hR_T_spec i).mp hi
    obtain ⟨col', hT' | hQ'⟩ := cap5_kempe_right darts h_mc cut.rev (revIdx i) col hT
    · have hid : (⟨((revIdx i).val + 4) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
          revIdx ⟨(i.val + 1) % 5, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp [revIdx]; have := i.isLt; omega
      rw [hid] at hT'
      exact Or.inl ((hR_T_spec ⟨(i.val + 1) % 5, by omega⟩).mpr ⟨col', hT'⟩)
    · have hid : (⟨((revIdx i).val + 3) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) =
          revIdx ⟨(i.val + 2) % 5, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp [revIdx]; have := i.isLt; omega
      rw [hid] at hQ'
      exact Or.inr ((hR_Q_spec ⟨(i.val + 2) % 5, by omega⟩).mpr ⟨col', hQ'⟩)
  have h_disj : ∀ x : Fin 10, ¬(S_L x = true ∧ S_R x = true) := by
    intro x ⟨hLx, hRx⟩
    by_cases hx : x.val < 5
    · let i : Fin 5 := ⟨x.val, hx⟩
      obtain ⟨colL, hL⟩ := (hL_T_spec i).mp hLx
      obtain ⟨colR, hR⟩ := (hR_T_spec i).mp hRx
      exact glue_of_state5T_match darts h_mc cut i colL colR hL hR
    · let q : Fin 5 := ⟨x.val - 5, by omega⟩
      have hx_eq : x = ⟨q.val + 5, by omega⟩ := by rw [Fin.ext_iff]; dsimp [q]; omega
      rw [hx_eq] at hLx hRx
      obtain ⟨colL, hL⟩ := (hL_Q_spec q).mp hLx
      obtain ⟨colR, hR⟩ := (hR_Q_spec q).mp hRx
      exact glue_of_state5Q_match darts h_mc cut q colL colR hL hR
  exact birkhoff_ten_state_contradiction S_L S_R
    h_pentL h_pentR h_idL h_idR h_krL h_klL h_krR h_klR h_disj

theorem mc_birkhoff_five_ring_dual {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut) :
    (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 15 ∨
    (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length = 15 := by
  rcases chordless5_DL_cases darts h_mc cut h_chord with h15L | h21L
  · exact Or.inl h15L
  · rcases chordless5_DL_cases darts h_mc cut.rev (chordless5_rev cut h_chord) with h15R | h21R
    · exact Or.inr h15R
    · exact False.elim (mc_five_cycle_both_sides_ge21_impossible darts h_mc cut h_chord h21L h21R)

theorem mc_birkhoff_five_ring_encloses_single_vertex_dual {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 5) (h_chord : Chordless5 cut) :
    (∃ w : H.Dart,
      cut.capSingleVertex_DL w ∧
      Math.Hypermap.faceDegree H w darts.length = 5 ∧
      (∀ d : H.Dart, cut.capSingleVertex_DL d →
        (∃ m : Fin 5, SameOrbit H.face (cut.ringFace m) d) ∨ SameOrbit H.face w d) ∧
      (∀ m : Fin 5, SameOrbit H.face (cut.ringFace m)
        (H.edge.f (Perm.iter H.face ((5 - m.val) % 5) w)))) ∨
    (∃ w : H.Dart,
      cut.rev.capSingleVertex_DL w ∧
      Math.Hypermap.faceDegree H w darts.length = 5 ∧
      (∀ d : H.Dart, cut.rev.capSingleVertex_DL d →
        (∃ m : Fin 5, SameOrbit H.face (cut.rev.ringFace m) d) ∨ SameOrbit H.face w d) ∧
      (∀ m : Fin 5, SameOrbit H.face (cut.rev.ringFace m)
        (H.edge.f (Perm.iter H.face ((5 - m.val) % 5) w)))) := by
  rcases mc_birkhoff_five_ring_dual darts h_mc cut h_chord with h15L | h15R
  · exact Or.inl (mc_birkhoff_five_ring_vertex_dual darts h_mc cut h_chord h15L)
  · exact Or.inr (mc_birkhoff_five_ring_vertex_dual darts h_mc cut.rev (chordless5_rev cut h_chord) h15R)

end BirkhoffCombinatorics

end Hypermap






