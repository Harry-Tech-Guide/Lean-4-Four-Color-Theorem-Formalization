module

public import FourColorTheorem.Math.Topology.MinimalCounterexamplePrimal
public import FourColorTheorem.Math.Topology.PlanarKempe

@[expose] public section

/-!
# Cubic & Girth >= 5 Properties of a Minimal Counterexample (`T.2`)

Proves without importing broken legacy `Degree4.lean`:
- `mc_simple_face_corners`: distinct darts sharing a vertex lie on distinct faces
- `mc_faceDegree_ne_one` / `mc_no_self_loop`
- `mc_nodeDegree_eq_three`: every vertex has degree 3
- `mc_faceDegree_ne_two`, `mc_faceDegree_ne_three`, `mc_faceDegree_ne_four`
- `mc_faceDegree_ge_five`: every face has size >= 5
-/

namespace Hypermap

/-! ## Section 1: Color, Permutation & Bridgelss Helpers -/

private theorem exists_other_color (col1 : Color) : ∃ c : Color, c ≠ col1 := by
  cases col1
  · exact ⟨Color.c1, by decide⟩
  · exact ⟨Color.c0, by decide⟩
  · exact ⟨Color.c0, by decide⟩
  · exact ⟨Color.c0, by decide⟩

private theorem exists_third_color (col1 col2 : Color) : ∃ c : Color, c ≠ col1 ∧ c ≠ col2 := by
  cases col1 <;> cases col2
  · exact ⟨Color.c1, by decide, by decide⟩
  · exact ⟨Color.c2, by decide, by decide⟩
  · exact ⟨Color.c1, by decide, by decide⟩
  · exact ⟨Color.c1, by decide, by decide⟩
  · exact ⟨Color.c2, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩
  · exact ⟨Color.c1, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩
  · exact ⟨Color.c1, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩
  · exact ⟨Color.c0, by decide, by decide⟩

private theorem exists_fourth_color (col1 col2 col3 : Color) :
    ∃ c : Color, c ≠ col1 ∧ c ≠ col2 ∧ c ≠ col3 := by
  cases col1 <;> cases col2 <;> cases col3 <;>
    first
    | exact ⟨Color.c0, by decide, by decide, by decide⟩
    | exact ⟨Color.c1, by decide, by decide, by decide⟩
    | exact ⟨Color.c2, by decide, by decide, by decide⟩
    | exact ⟨Color.c3, by decide, by decide, by decide⟩

private theorem swapFun_apply_left {D : Type} [DecidableEq D] (a b : D) :
    swapFun a b a = b := by
  simp [swapFun]

private theorem swapFun_apply_right {D : Type} [DecidableEq D] (a b : D) :
    swapFun a b b = a := by
  unfold swapFun
  by_cases h1 : b = a
  · simp [h1]
  · simp [h1]

private theorem swapFun_inj {D : Type} [DecidableEq D] (a b x y : D)
    (h : swapFun a b x = swapFun a b y) : x = y := by
  have h' := congrArg (swapFun a b) h
  rw [swapFun_involutive, swapFun_involutive] at h'
  exact h'

private theorem node_face_eq_edge (H : Hypermap) (x : H.Dart) :
    H.node.f (H.face.f x) = H.edge.f x := by
  have h := congrArg H.edge.f (H.edge_node_face_id x)
  rw [H.edge_involution] at h
  exact h

private theorem face_edge_eq_node_inv (H : Hypermap) (x : H.Dart) :
    H.face.f (H.edge.f x) = H.node.inv x := by
  have h := congrArg H.node.inv (node_face_eq_edge H (H.edge.f x))
  rw [H.node.left_inv, H.edge_involution] at h
  exact h

private theorem sameOrbit_node_of_face_color_inv (H : Hypermap) (c : H.FaceColoring)
    {x y : H.Dart} (h : SameOrbit H.face x y) : c.color x = c.color y := by
  rcases h with ⟨k, rfl⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    change c.color x = c.color (H.face.f (Perm.iter H.face k x))
    rw [c.face_invariant, ih]

private theorem isBridgeless_iff_no_sameOrbit_face_edge (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_comp : ∀ d : H.Dart, d ∈ darts) :
    Math.Hypermap.isBridgeless H darts darts.length ↔
      ∀ d : H.Dart, ¬ SameOrbit H.face d (H.edge.f d) := by
  constructor
  · intro hb d hs
    have hcl : orbitClosesWithin H.face d d darts.length :=
      orbitClosesWithin_of_complete H.face darts h_comp d
    have hmem : H.edge.f d ∈ getOrbit H.face darts.length d :=
      (sameOrbit_iff_mem_getOrbit_of_complete H.face darts h_comp (Nat.le_refl _) d (H.edge.f d)).mp hs
    have hc : (getOrbit H.face darts.length d).contains (H.edge.f d) = true :=
      List.contains_iff_mem.mpr hmem
    have hbd := hb d (h_comp d)
    change (getOrbit H.face darts.length d).contains (H.edge.f d) = false at hbd
    rw [hc] at hbd
    exact Bool.false_ne_true hbd.symm
  · intro h_no d _
    rw [Bool.eq_false_iff]
    intro hc
    change (getOrbit H.face darts.length d).contains (H.edge.f d) = true at hc
    have hmem : H.edge.f d ∈ getOrbit H.face darts.length d := List.contains_iff_mem.mp hc
    have hs : SameOrbit H.face d (H.edge.f d) :=
      (sameOrbit_iff_mem_getOrbit_of_complete H.face darts h_comp (Nat.le_refl _) d (H.edge.f d)).mpr hmem
    exact h_no d hs

private theorem mc_not_sameOrbit_face_edge (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (d : H.Dart) :
    ¬ SameOrbit H.face d (H.edge.f d) :=
  (isBridgeless_iff_no_sameOrbit_face_edge H darts h_mc.complete).mp h_mc.is_bridgeless d

private theorem getOrbit_length_eq_one_iff {D : Type} [DecidableEq D] (p : Perm D)
    (darts : List D) (h_comp : ∀ d : D, d ∈ darts) (d : D) :
    (getOrbit p darts.length d).length = 1 ↔ p.f d = d := by
  constructor
  · intro hlen
    have hid := perm_iter_length_getOrbit_eq_self_of_complete p darts h_comp (Nat.le_refl _) d
    rw [hlen] at hid
    exact hid
  · intro hfix
    have h_iter : ∀ k, Perm.iter p k d = d := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        change p.f (Perm.iter p k d) = d
        rw [ih, hfix]
    have h_empty : darts ≠ [] := by
      intro hem
      have hd := h_comp d
      rw [hem] at hd
      exact List.not_mem_nil hd
    have hpos : 1 ≤ darts.length := by
      cases hdl : darts with
      | nil => exact absurd hdl h_empty
      | cons _ _ => simp
    have hge : 1 ≤ (getOrbit p darts.length d).length := getOrbit_length_pos p hpos d
    have hcl : orbitClosesWithin p d d darts.length := orbitClosesWithin_of_complete p darts h_comp d
    by_cases hgt : (getOrbit p darts.length d).length ≥ 2
    · have h1 := perm_iter_inj_of_lt_getOrbit_length p (Nat.lt_of_lt_of_le (by omega) hge) hgt
        (show Perm.iter p 0 d = Perm.iter p 1 d by rw [h_iter 0, h_iter 1])
      omega
    · omega

private theorem sameOrbit_eq_perm_iter_succ {D : Type} (p : Perm D) {x y : D} :
    SameOrbit p x y → SameOrbit p x (p.f y) := by
  rintro ⟨k, rfl⟩
  exact ⟨k + 1, rfl⟩

private theorem perm_iter_excise_val (H : Hypermap) (removed : List H.Dart)
    (e' n' f' : Perm H.Dart)
    (he : ∀ d, e'.f (e'.f d) = d) (henf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_edge : ∀ d, d ∈ removed ↔ e'.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ n'.f d ∈ removed) :
    ∀ k (z : (H.exciseSubtype removed e' n' f' he henf h_edge h_node).Dart),
      (Perm.iter (H.exciseSubtype removed e' n' f' he henf h_edge h_node).face k z).val =
        Perm.iter f' k z.val
  | 0, _ => rfl
  | k + 1, z => by
    let H' := H.exciseSubtype removed e' n' f' he henf h_edge h_node
    change (H'.face.f (Perm.iter H'.face k z)).val = f'.f (Perm.iter f' k z.val)
    have h_step : (H'.face.f (Perm.iter H'.face k z)).val = f'.f (Perm.iter H'.face k z).val := rfl
    rw [h_step, perm_iter_excise_val H removed e' n' f' he henf h_edge h_node k z]

private theorem exciseSubtype_isBridgeless_of_id (H : Hypermap) [DecidableEq H.Dart]
    (darts removed : List H.Dart)
    (h_comp : ∀ d : H.Dart, d ∈ darts)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts darts.length)
    (h_edge : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ H.node.f d ∈ removed)
    (darts' : List (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).Dart)
    (h_comp' : ∀ x : (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).Dart, x ∈ darts') :
    Math.Hypermap.isBridgeless
      (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node)
      darts' darts'.length := by
  let H' := H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node
  rw [isBridgeless_iff_no_sameOrbit_face_edge H' darts' h_comp']
  intro u hs
  rcases hs with ⟨k, hk⟩
  have hval : H.edge.f u.val = Perm.iter H.face k u.val := by
    have hev : (H'.edge.f u).val = H.edge.f u.val := rfl
    have hk' := congrArg Subtype.val hk
    rw [hev] at hk'
    exact ((perm_iter_excise_val H removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node k u).symm.trans hk').symm
  have h_no := (isBridgeless_iff_no_sameOrbit_face_edge H darts h_comp).mp h_bridgeless u.val
  exact h_no ⟨k, hval.symm⟩

private theorem list_filter_length_lt_of_mem_false {D : Type} (p : D → Bool) :
    ∀ (l : List D) (a : D), a ∈ l → p a = false → (l.filter p).length < l.length
  | [], _, ha, _ => nomatch ha
  | x :: xs, a, ha, hpa => by
    simp only [List.filter_cons]
    by_cases hpx : p x = true
    · simp only [hpx, ↓reduceIte, List.length_cons]
      have ha' : a ∈ xs := by
        rcases List.mem_cons.mp ha with rfl | hmem
        · rw [hpx] at hpa; cases hpa
        · exact hmem
      exact Nat.succ_lt_succ (list_filter_length_lt_of_mem_false p xs a ha' hpa)
    · have hpxf : p x = false := Bool.eq_false_iff.mpr hpx
      simp only [hpxf, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le p xs)

private theorem filter_subDarts_comm {D : Type} [DecidableEq D]
    (R : D → D → Prop) [DecidableRel R]
    (rem : List D) (R' : {x : D // ¬ x ∈ rem} → {x : D // ¬ x ∈ rem} → Prop) [DecidableRel R']
    (hR' : ∀ u w, R' u w ↔ R u.val w.val)
    (y : {x : D // ¬ x ∈ rem}) :
    ∀ (l : List D),
      (subDarts l rem).filter (fun w => !decide (R' y w)) =
        subDarts (l.filter (fun z => !decide (R y.val z))) rem
  | [] => rfl
  | a :: tl => by
    change (if h : a ∈ rem then subDarts tl rem else ⟨a, h⟩ :: subDarts tl rem).filter _ = _
    by_cases ha : a ∈ rem
    · simp only [ha, ↓reduceDIte]
      by_cases hra : R y.val a
      · simp only [List.filter_cons, hra, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact filter_subDarts_comm R rem R' hR' y tl
      · simp only [List.filter_cons, hra, decide_false, Bool.not_false, ↓reduceIte]
        change _ = if h : a ∈ rem then _ else _
        simp only [ha, ↓reduceDIte]
        exact filter_subDarts_comm R rem R' hR' y tl
    · simp only [ha, ↓reduceDIte]
      by_cases hra : R y.val a
      · have hra' : R' y ⟨a, ha⟩ := (hR' y ⟨a, ha⟩).mpr hra
        simp only [List.filter_cons, hra, hra', decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact filter_subDarts_comm R rem R' hR' y tl
      · have hra' : ¬ R' y ⟨a, ha⟩ := fun h => hra ((hR' y ⟨a, ha⟩).mp h)
        simp only [List.filter_cons, hra, hra', decide_false, Bool.not_false, ↓reduceIte]
        change ⟨a, ha⟩ :: (subDarts tl rem).filter _ =
          if h : a ∈ rem then _ else ⟨a, h⟩ :: subDarts (tl.filter _) rem
        simp only [ha, ↓reduceDIte]
        congr 1
        exact filter_subDarts_comm R rem R' hR' y tl

private theorem countRelClasses_subDarts_eq_of_cover {D : Type} [DecidableEq D]
    (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    (rem : List D) (R' : {x : D // ¬ x ∈ rem} → {x : D // ¬ x ∈ rem} → Prop) [DecidableRel R']
    (hR' : ∀ u w, R' u w ↔ R u.val w.val) :
    ∀ n (l : List D), l.length ≤ n →
      (∀ x ∈ l, ∃ y ∈ l, ¬ y ∈ rem ∧ R x y) →
      countRelClasses R' (subDarts l rem) = countRelClasses R l := by
  intro n
  induction n with
  | zero =>
    intro l hlen _
    cases l with
    | nil => rfl
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro l hlen h_cov
    by_cases hsd_empty : subDarts l rem = []
    · rw [hsd_empty]
      cases l with
      | nil => rfl
      | cons a rest =>
        obtain ⟨y, hy_mem, hy_nrem, _⟩ := h_cov a List.mem_cons_self
        have hy_sub : (⟨y, hy_nrem⟩ : {x // ¬ x ∈ rem}) ∈ subDarts (a :: rest) rem :=
          (mem_subDarts (a :: rest) rem ⟨y, hy_nrem⟩).mpr hy_mem
        rw [hsd_empty] at hy_sub
        cases hy_sub
    · obtain ⟨y, rest', hsd⟩ := List.exists_cons_of_ne_nil hsd_empty
      have hy_sub : y ∈ subDarts l rem := by
        rw [hsd]
        exact List.mem_cons_self
      have hy_mem : y.val ∈ l := (mem_subDarts l rem y).mp hy_sub
      have h_lhs : countRelClasses R' (subDarts l rem) =
          1 + countRelClasses R' ((subDarts l rem).filter (fun w => !decide (R' y w))) := by
        refine countRelClasses_eq_one_add_filter_of_mem R' ?_ ?_ ?_ (subDarts l rem) y hy_sub
        · intro u; exact (hR' u u).mpr (h_refl u.val)
        · intro u w h; exact (hR' w u).mpr (h_symm ((hR' u w).mp h))
        · intro u v w h1 h2; exact (hR' u w).mpr (h_trans ((hR' u v).mp h1) ((hR' v w).mp h2))
      have h_rhs : countRelClasses R l =
          1 + countRelClasses R (l.filter (fun z => !decide (R y.val z))) :=
        countRelClasses_eq_one_add_filter_of_mem R h_refl h_symm h_trans l y.val hy_mem
      rw [h_lhs, h_rhs, filter_subDarts_comm R rem R' hR' y l]
      have h_lt : (l.filter (fun z => !decide (R y.val z))).length < l.length :=
        list_filter_length_lt_of_mem_false (fun z => !decide (R y.val z)) l y.val hy_mem
          (by simp [h_refl y.val])
      have h_sub_cov : ∀ x ∈ l.filter (fun z => !decide (R y.val z)),
          ∃ w ∈ l.filter (fun z => !decide (R y.val z)), ¬ w ∈ rem ∧ R x w := by
        intro x hx
        rw [List.mem_filter] at hx
        obtain ⟨hx_l, hx_nr⟩ := hx
        obtain ⟨w, hw_l, hw_nrem, hxw⟩ := h_cov x hx_l
        refine ⟨w, List.mem_filter.mpr ⟨hw_l, ?_⟩, hw_nrem, hxw⟩
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hx_nr ⊢
        intro hyw
        exact hx_nr (h_trans hyw (h_symm hxw))
      congr 1
      exact ih (l.filter (fun z => !decide (R y.val z))) (by omega) h_sub_cov

/-! ## Section 2: Simple Face Corners (`mc_simple_face_corners`) -/

/-- No two distinct darts on the same vertex (`SameOrbit H.node`) can share a face
    (`SameOrbit H.face`) in a minimal counterexample. -/
theorem mc_simple_face_corners (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    {d_a d_b : H.Dart} (hne : d_a ≠ d_b)
    (h_node : SameOrbit H.node d_a d_b)
    (h_face : SameOrbit H.face d_a d_b) : False := by
  let H_s := H.splitVertexAtPair d_a d_b
  obtain ⟨hs_planar, _, hs_no_reach⟩ :=
    splitVertexAtPair_disconnected_isPlanar H darts h_mc.nodup h_mc.complete (Nat.le_refl _)
      h_mc.is_planar d_a d_b hne h_node h_face
  have hs_face_to_H : ∀ {x y : H.Dart}, SameOrbit H_s.face x y → SameOrbit H.face x y := by
    intro x y ⟨k, hk⟩
    subst hk
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
      have h_step : H_s.face.f (Perm.iter H_s.face k x) =
          swapFun d_a d_b (H.face.f (Perm.iter H_s.face k x)) := rfl
      change SameOrbit H.face x (H_s.face.f (Perm.iter H_s.face k x))
      rw [h_step]
      have ih1 : SameOrbit H.face x (H.face.f (Perm.iter H_s.face k x)) :=
        sameOrbit_eq_perm_iter_succ H.face ih
      dsimp only [swapFun]
      by_cases h1 : H.face.f (Perm.iter H_s.face k x) = d_a
      · rw [if_pos h1]
        rw [h1] at ih1
        exact sameOrbit_trans H.face ih1 h_face
      · rw [if_neg h1]
        by_cases h2 : H.face.f (Perm.iter H_s.face k x) = d_b
        · rw [if_pos h2]
          rw [h2] at ih1
          exact sameOrbit_trans H.face ih1
            (sameOrbit_symm_of_complete H.face darts h_mc.complete h_face)
        · rw [if_neg h2]
          exact ih1
  have hs_bridgeless : Math.Hypermap.isBridgeless H_s darts darts.length := by
    rw [isBridgeless_iff_no_sameOrbit_face_edge H_s darts h_mc.complete]
    intro d hd_face
    have he_eq : H_s.edge.f d = H.edge.f d := rfl
    rw [he_eq] at hd_face
    exact mc_not_sameOrbit_face_edge H darts h_mc d (hs_face_to_H hd_face)
  let remA : List H.Dart := H_s.getComponent darts.length d_a
  let remB : List H.Dart := darts.filter (fun x => !decide (x ∈ remA))
  have h_mem_remA_iff : ∀ x, x ∈ remA ↔ Nonempty (H_s.Walk d_a x) := fun x =>
    mem_getComponent_iff_walk H_s darts h_mc.complete (Nat.le_refl _) d_a x
  have h_mem_remB_iff : ∀ x, x ∈ remB ↔ ¬ x ∈ remA := by
    intro x
    simp [remB, h_mc.complete x]
  have h_da_in_A : d_a ∈ remA := mem_getComponent_self H_s darts.length d_a
  have h_db_notin_A : ¬ d_b ∈ remA := by
    intro hmem
    have hw := (h_mem_remA_iff d_b).mp hmem
    exact hs_no_reach ((reachEN_hypermap_iff_walk H_s d_a d_b).mpr hw)
  have h_db_in_B : d_b ∈ remB := (h_mem_remB_iff d_b).mpr h_db_notin_A
  have h_da_notin_B : ¬ d_a ∈ remB := fun h => ((h_mem_remB_iff d_a).mp h) h_da_in_A
  have h_remA_edge : ∀ d, d ∈ remA ↔ H_s.edge.f d ∈ remA := by
    intro d
    constructor
    · intro h
      exact getComponent_step_closed_of_complete H_s darts h_mc.complete (Nat.le_refl _) d_a
        (Hypermap.Step.edge rfl) h
    · intro h
      have h' := getComponent_step_closed_of_complete H_s darts h_mc.complete (Nat.le_refl _) d_a
        (Hypermap.Step.edge (H_s.edge_involution d).symm) h
      exact h'
  have h_remA_node : ∀ d, d ∈ remA ↔ H_s.node.f d ∈ remA := by
    intro d
    constructor
    · intro h
      exact getComponent_step_closed_of_complete H_s darts h_mc.complete (Nat.le_refl _) d_a
        (Hypermap.Step.node rfl) h
    · intro h
      exact getComponent_step_closed_of_complete H_s darts h_mc.complete (Nat.le_refl _) d_a
        (Hypermap.Step.nodeInv (H_s.node.left_inv d).symm) h
  have h_remA_face : ∀ d, d ∈ remA ↔ H_s.face.f d ∈ remA := by
    intro d
    constructor
    · intro h
      exact getComponent_step_closed_of_complete H_s darts h_mc.complete (Nat.le_refl _) d_a
        (Hypermap.Step.face rfl) h
    · intro h
      exact getComponent_step_closed_of_complete H_s darts h_mc.complete (Nat.le_refl _) d_a
        (Hypermap.Step.faceInv (H_s.face.left_inv d).symm) h
  have h_remB_edge : ∀ d, d ∈ remB ↔ H_s.edge.f d ∈ remB := by
    intro d; rw [h_mem_remB_iff, h_mem_remB_iff, h_remA_edge]
  have h_remB_node : ∀ d, d ∈ remB ↔ H_s.node.f d ∈ remB := by
    intro d; rw [h_mem_remB_iff, h_mem_remB_iff, h_remA_node]
  let H_A := H_s.exciseSubtype remB H_s.edge H_s.node H_s.face
    H_s.edge_involution H_s.edge_node_face_id h_remB_edge h_remB_node
  let H_B := H_s.exciseSubtype remA H_s.edge H_s.node H_s.face
    H_s.edge_involution H_s.edge_node_face_id h_remA_edge h_remA_node
  let dartsA := subDarts darts remB
  let dartsB := subDarts darts remA
  obtain ⟨hndA, hcompA, hneA⟩ := exciseSubtype_complete H_s darts remB
    H_s.edge H_s.node H_s.face H_s.edge_involution H_s.edge_node_face_id h_remB_edge h_remB_node
    h_mc.nodup h_mc.complete ⟨d_a, h_mc.complete d_a, h_da_notin_B⟩
  obtain ⟨hndB, hcompB, hneB⟩ := exciseSubtype_complete H_s darts remA
    H_s.edge H_s.node H_s.face H_s.edge_involution H_s.edge_node_face_id h_remA_edge h_remA_node
    h_mc.nodup h_mc.complete ⟨d_b, h_mc.complete d_b, h_db_notin_A⟩
  have hltA : dartsA.length < darts.length :=
    exciseSubtype_strictly_smaller darts remB ⟨d_b, h_mc.complete d_b, h_db_in_B⟩
  have hltB : dartsB.length < darts.length :=
    exciseSubtype_strictly_smaller darts remA ⟨d_a, h_mc.complete d_a, h_da_in_A⟩
  have hpA : H_A.isPlanar dartsA.length dartsA = true :=
    exciseSubtype_isPlanar H_s darts remB h_remB_edge h_remB_node h_mc.nodup h_mc.complete
      (Nat.le_refl _) hs_planar dartsA hndA hcompA (Nat.le_refl _)
  have hpB : H_B.isPlanar dartsB.length dartsB = true :=
    exciseSubtype_isPlanar H_s darts remA h_remA_edge h_remA_node h_mc.nodup h_mc.complete
      (Nat.le_refl _) hs_planar dartsB hndB hcompB (Nat.le_refl _)
  have hbA : Math.Hypermap.isBridgeless H_A dartsA dartsA.length :=
    exciseSubtype_isBridgeless_of_id H_s darts remB h_mc.complete hs_bridgeless
      h_remB_edge h_remB_node dartsA hcompA
  have hbB : Math.Hypermap.isBridgeless H_B dartsB dartsB.length :=
    exciseSubtype_isBridgeless_of_id H_s darts remA h_mc.complete hs_bridgeless
      h_remA_edge h_remA_node dartsB hcompB
  obtain ⟨cA⟩ := h_mc.is_minimal H_A dartsA hndA hcompA hneA hltA hpA hbA
  obtain ⟨cB⟩ := h_mc.is_minimal H_B dartsB hndB hcompB hneB hltB hpB hbB
  let colA : Color := cA.color ⟨d_a, h_da_notin_B⟩
  let colB : Color := cB.color ⟨d_b, h_db_notin_A⟩
  let σ : Color → Color := swapFun colA colB
  let glueColor : H.Dart → Color := fun z =>
    if hz : z ∈ remA then
      cA.color ⟨z, fun h => ((h_mem_remB_iff z).mp h) hz⟩
    else
      σ (cB.color ⟨z, hz⟩)
  have h_glue_da : glueColor d_a = colA := by
    simp [glueColor, h_da_in_A, colA]
  have h_glue_db : glueColor d_b = colA := by
    simp [glueColor, h_db_notin_A, σ, colB]
  have h_glue_face_s : ∀ z : H.Dart, glueColor (H_s.face.f z) = glueColor z := by
    intro z
    by_cases hz : z ∈ remA
    · have hfz : H_s.face.f z ∈ remA := (h_remA_face z).mp hz
      simp only [glueColor, hz, hfz, ↓reduceDIte]
      exact cA.face_invariant ⟨z, fun h => ((h_mem_remB_iff z).mp h) hz⟩
    · have hfz : ¬ H_s.face.f z ∈ remA := fun h => hz ((h_remA_face z).mpr h)
      simp only [glueColor, hz, hfz, ↓reduceDIte]
      exact congrArg σ (cB.face_invariant ⟨z, hz⟩)
  have h_glue_edge : ∀ z : H.Dart, glueColor (H.edge.f z) ≠ glueColor z := by
    intro z
    have he_eq : H.edge.f z = H_s.edge.f z := rfl
    rw [he_eq]
    by_cases hz : z ∈ remA
    · have hez : H_s.edge.f z ∈ remA := (h_remA_edge z).mp hz
      simp only [glueColor, hz, hez, ↓reduceDIte]
      exact cA.edge_proper ⟨z, fun h => ((h_mem_remB_iff z).mp h) hz⟩
    · have hez : ¬ H_s.edge.f z ∈ remA := fun h => hz ((h_remA_edge z).mpr h)
      simp only [glueColor, hz, hez, ↓reduceDIte]
      intro h_eq
      exact cB.edge_proper ⟨z, hz⟩ (swapFun_inj colA colB _ _ h_eq)
  have h_glue_face : ∀ z : H.Dart, glueColor (H.face.f z) = glueColor z := by
    intro z
    have hinv := h_glue_face_s z
    have h_step : H_s.face.f z = swapFun d_a d_b (H.face.f z) := rfl
    rw [h_step] at hinv
    by_cases h1 : H.face.f z = d_a
    · have hsw : swapFun d_a d_b (H.face.f z) = d_b := by rw [h1, swapFun_apply_left]
      rw [h1, h_glue_da, ← hinv, hsw, h_glue_db]
    · by_cases h2 : H.face.f z = d_b
      · have hsw : swapFun d_a d_b (H.face.f z) = d_a := by rw [h2, swapFun_apply_right]
        rw [h2, h_glue_db, ← hinv, hsw, h_glue_da]
      · rw [swapFun_of_ne h1 h2] at hinv
        exact hinv
  exact h_mc.not_colorable ⟨glueColor, h_glue_face, h_glue_edge⟩

/-! ## Section 3: No 1-Faces & No Self-Loops -/

/-- No face in a minimal counterexample has size 1. -/
theorem mc_faceDegree_ne_one (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (d : H.Dart) : Math.Hypermap.faceDegree H d darts.length ≠ 1 := by
  intro h_len
  have h_fix : H.face.f d = d :=
    (getOrbit_length_eq_one_iff H.face darts h_mc.complete d).mp h_len
  let b := H.edge.f d
  have h_b_ne_d : b ≠ d := mc_edge_ne_self H darts h_mc d
  have h_node_d : H.node.f d = b := by
    have h := node_face_eq_edge H d
    rw [h_fix] at h
    exact h
  have h_fb_ne_b : H.face.f b ≠ b := by
    intro hfb
    have hinv : H.face.f b = H.node.inv d := face_edge_eq_node_inv H d
    rw [hfb] at hinv
    have h2 : H.node.f (H.node.f d) = d := by
      rw [h_node_d, hinv]
      exact H.node.right_inv d
    have h_ge3 : 3 ≤ (getOrbit H.node darts.length d).length :=
      mc_nodeDegree_ge_three H darts h_mc d
    have h02 := perm_iter_inj_of_lt_getOrbit_length H.node
      (by omega : 0 < (getOrbit H.node darts.length d).length)
      (by omega : 2 < (getOrbit H.node darts.length d).length)
      (by simpa [Perm.iter] using h2.symm)
    omega
  have h_fb_ne_d : H.face.f b ≠ d := by
    intro hfd
    have hinv := congrArg H.face.inv hfd
    rw [H.face.left_inv] at hinv
    have hd_inv : H.face.inv d = d := by
      have hh := congrArg H.face.inv h_fix
      rw [H.face.left_inv] at hh
      exact hh.symm
    rw [hd_inv] at hinv
    exact h_b_ne_d hinv
  let H' := H.deleteEdgeSubtype d
  let darts' := subDarts darts [d, b]
  have h_fb_nmem : ¬ H.face.f b ∈ [d, b] := by
    simp [h_fb_ne_d, h_fb_ne_b]
  have h_rem : ∀ z : H'.Dart, z.val ≠ d ∧ z.val ≠ b := by
    intro z
    have hnz := z.property
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnz
    exact hnz
  have hnd' : darts'.Nodup := subDarts_nodup darts [d, b] h_mc.nodup
  have hcomp' : ∀ x : H'.Dart, x ∈ darts' := fun x =>
    (mem_subDarts darts [d, b] x).mpr (h_mc.complete x.val)
  have hne' : darts' ≠ [] := subDarts_nonempty darts [d, b] ⟨H.face.f b, h_mc.complete _, h_fb_nmem⟩
  have hlt' : darts'.length < darts.length :=
    exciseSubtype_strictly_smaller darts [d, b] ⟨d, h_mc.complete d, by simp⟩
  have hp' : H'.isPlanar darts'.length darts' = true :=
    deleteEdgeSubtype_isPlanar H darts h_mc.nodup h_mc.complete (Nat.le_refl _) h_mc.is_planar
      d h_b_ne_d darts' hnd' hcomp' (Nat.le_refl _)
  have h_face_step_in_orbit : ∀ u : H'.Dart, SameOrbit H.face u.val (H'.face.f u).val := by
    intro u
    obtain ⟨hud, hub⟩ := h_rem u
    have hfu_ne_d : H.face.f u.val ≠ d := by
      intro h
      apply hud
      have h1 := congrArg H.face.inv (h.trans h_fix.symm)
      rw [H.face.left_inv, H.face.left_inv] at h1
      exact h1
    have h_fval : (H'.face.f u).val =
        (bypass (bypass (swapCompRight H.face d b) d) b).f u.val := rfl
    let q := swapCompRight H.face d b
    have hqu : q.f u.val = H.face.f u.val := by
      change H.face.f (swapFun d b u.val) = H.face.f u.val
      rw [swapFun_of_ne hud hub]
    have hqb : q.f b = d := by
      change H.face.f (swapFun d b b) = d
      rw [swapFun_apply_right, h_fix]
    have hqd : q.f d = H.face.f b := by
      change H.face.f (swapFun d b d) = H.face.f b
      rw [swapFun_apply_left]
    rw [h_fval]
    by_cases hfub : H.face.f u.val = b
    · have h1 : (bypass q d).f u.val = b := by
        rw [bypass_apply_of_ne q d u.val hud (by rw [hqu, hfub]; exact h_b_ne_d)]
        rw [hqu, hfub]
      have h2 : (bypass q d).f b = H.face.f b := by
        rw [bypass_apply_pred q d b h_b_ne_d hqb, hqd]
      have h3 : (bypass (bypass q d) b).f u.val = H.face.f b := by
        rw [bypass_apply_pred (bypass q d) b u.val hub h1, h2]
      rw [h3, ← hfub]
      exact ⟨2, rfl⟩
    · have h1 : (bypass q d).f u.val = H.face.f u.val := by
        rw [bypass_apply_of_ne q d u.val hud (by rw [hqu]; exact hfu_ne_d), hqu]
      have h2 : (bypass (bypass q d) b).f u.val = H.face.f u.val := by
        rw [bypass_apply_of_ne (bypass q d) b u.val hub (by rw [h1]; exact hfub), h1]
      rw [h2]
      exact ⟨1, rfl⟩
  have h_face_sub : ∀ {u w : H'.Dart}, SameOrbit H'.face u w → SameOrbit H.face u.val w.val := by
    intro u w ⟨k, hk⟩
    subst hk
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
      exact sameOrbit_trans H.face ih (h_face_step_in_orbit (Perm.iter H'.face k u))
  have hb' : Math.Hypermap.isBridgeless H' darts' darts'.length := by
    rw [isBridgeless_iff_no_sameOrbit_face_edge H' darts' hcomp']
    intro u hs
    have hev : (H'.edge.f u).val = H.edge.f u.val := deleteEdgeSubtype_edge_val H d u
    have hsH := h_face_sub hs
    rw [hev] at hsH
    exact mc_not_sameOrbit_face_edge H darts h_mc u.val hsH
  obtain ⟨c'⟩ := h_mc.is_minimal H' darts' hnd' hcomp' hne' hlt' hp' hb'
  let col_b : Color := c'.color ⟨H.face.f b, h_fb_nmem⟩
  obtain ⟨col_d, h_cd_ne_cb⟩ := exists_other_color col_b
  let lift : H.Dart → Color := fun z =>
    if hz1 : z = d then col_d
    else if hz2 : z = b then col_b
    else c'.color ⟨z, fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> contradiction⟩
  have h_lift_face : ∀ z : H.Dart, lift (H.face.f z) = lift z := by
    intro z
    by_cases hzd : z = d
    · subst hzd
      simp [lift, h_fix]
    · by_cases hzb : z = b
      · subst hzb
        simp [lift, h_b_ne_d, h_fb_ne_d, h_fb_ne_b, col_b]
      · have hz_nmem : ¬ z ∈ [d, b] := by simp [hzd, hzb]
        have hfz_ne_d : H.face.f z ≠ d := by
          intro h
          apply hzd
          have h1 := congrArg H.face.inv (h.trans h_fix.symm)
          rw [H.face.left_inv, H.face.left_inv] at h1
          exact h1
        have hfinv := c'.face_invariant ⟨z, hz_nmem⟩
        by_cases hfz_b : H.face.f z = b
        · have h_fstep : (H'.face.f ⟨z, hz_nmem⟩).val = H.face.f b := by
            let q := swapCompRight H.face d b
            have hqu : q.f z = H.face.f z := by
              change H.face.f (swapFun d b z) = H.face.f z
              rw [swapFun_of_ne hzd hzb]
            have hqb : q.f b = d := by
              change H.face.f (swapFun d b b) = d
              rw [swapFun_apply_right, h_fix]
            have hqd : q.f d = H.face.f b := by
              change H.face.f (swapFun d b d) = H.face.f b
              rw [swapFun_apply_left]
            change (bypass (bypass q d) b).f z = H.face.f b
            have h1 : (bypass q d).f z = b := by
              rw [bypass_apply_of_ne q d z hzd (by rw [hqu, hfz_b]; exact h_b_ne_d), hqu, hfz_b]
            have h2 : (bypass q d).f b = H.face.f b := by
              rw [bypass_apply_pred q d b h_b_ne_d hqb, hqd]
            rw [bypass_apply_pred (bypass q d) b z hzb h1, h2]
          have hsub : H'.face.f ⟨z, hz_nmem⟩ = ⟨H.face.f b, h_fb_nmem⟩ :=
            Subtype.ext h_fstep
          rw [hsub] at hfinv
          simp only [lift, hfz_b, h_b_ne_d, ↓reduceDIte, hzd, hzb, col_b]
          exact hfinv
        · have h_fstep : (H'.face.f ⟨z, hz_nmem⟩).val = H.face.f z := by
            let q := swapCompRight H.face d b
            have hqu : q.f z = H.face.f z := by
              change H.face.f (swapFun d b z) = H.face.f z
              rw [swapFun_of_ne hzd hzb]
            change (bypass (bypass q d) b).f z = H.face.f z
            have h1 : (bypass q d).f z = H.face.f z := by
              rw [bypass_apply_of_ne q d z hzd (by rw [hqu]; exact hfz_ne_d), hqu]
            rw [bypass_apply_of_ne (bypass q d) b z hzb (by rw [h1]; exact hfz_b), h1]
          have hsub : H'.face.f ⟨z, hz_nmem⟩ = ⟨H.face.f z, fun h => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              rcases h with h1 | h2
              · exact hfz_ne_d h1
              · exact hfz_b h2⟩ := Subtype.ext h_fstep
          rw [hsub] at hfinv
          simp only [lift, hfz_ne_d, hfz_b, ↓reduceDIte, hzd, hzb]
          exact hfinv
  have h_lift_edge : ∀ z : H.Dart, lift (H.edge.f z) ≠ lift z := by
    intro z
    by_cases hzd : z = d
    · subst hzd
      simp [lift, b, h_b_ne_d, h_cd_ne_cb.symm]
    · by_cases hzb : z = b
      · subst hzb
        have heb : H.edge.f b = d := by dsimp only [b]; exact H.edge_involution d
        simp [lift, heb, h_b_ne_d]
        exact h_cd_ne_cb
      · have hz_nmem : ¬ z ∈ [d, b] := by simp [hzd, hzb]
        have hez_ne_d : H.edge.f z ≠ d := by
          intro h
          apply hzb
          have h1 := congrArg H.edge.f h
          rw [H.edge_involution] at h1
          exact h1
        have hez_ne_b : H.edge.f z ≠ b := by
          intro h
          apply hzd
          have h1 := congrArg H.edge.f h
          dsimp only [b] at h1
          rw [H.edge_involution, H.edge_involution] at h1
          exact h1
        have he_sub : H'.edge.f ⟨z, hz_nmem⟩ = ⟨H.edge.f z, fun h => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h1 | h2
            · exact hez_ne_d h1
            · exact hez_ne_b h2⟩ :=
          Subtype.ext (deleteEdgeSubtype_edge_val H d ⟨z, hz_nmem⟩)
        have hep := c'.edge_proper ⟨z, hz_nmem⟩
        rw [he_sub] at hep
        simp only [lift, hez_ne_d, hez_ne_b, ↓reduceDIte, hzd, hzb]
        exact hep
  exact h_mc.not_colorable ⟨lift, h_lift_face, h_lift_edge⟩

/-- No self-loops (`H.edge.f a` is never on the same vertex as `a`). -/
theorem mc_no_self_loop (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (a : H.Dart) : ¬ SameOrbit H.node a (H.edge.f a) := by
  intro hs
  have h_inv : SameOrbit H.node a (H.node.inv a) :=
    sameOrbit_inv_step_of_complete H.node darts h_mc.complete a
  have h_node_ea : SameOrbit H.node (H.edge.f a) (H.node.inv a) :=
    sameOrbit_trans H.node (sameOrbit_symm_of_complete H.node darts h_mc.complete hs) h_inv
  rw [← face_edge_eq_node_inv H a] at h_node_ea
  have h_eq : H.edge.f a = H.face.f (H.edge.f a) :=
    Classical.byContradiction fun hne =>
      mc_simple_face_corners H darts h_mc hne h_node_ea ⟨1, rfl⟩
  exact mc_faceDegree_ne_one H darts h_mc (H.edge.f a)
    ((getOrbit_length_eq_one_iff H.face darts h_mc.complete (H.edge.f a)).mpr h_eq.symm)

/-! ## Section 4: Cubic Property (`mc_nodeDegree_eq_three`) -/

private theorem dual_opp_face_edge_disjoint (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : PrimalMinimalCounterexample H darts) (d0 : H.Dart)
    (h_ge4 : 4 ≤ Math.Hypermap.nodeDegree H d0 darts.length) :
    let d1 := H.node.f d0
    let d2 := H.node.f d1
    let d3 := H.node.f d2
    (∀ u : H.Dart, SameOrbit H.face u d0 → ¬ SameOrbit H.face (H.edge.f u) d2) ∨
    (∀ v : H.Dart, SameOrbit H.face v d1 → ¬ SameOrbit H.face (H.edge.f v) d3) := by
  intro d1 d2 d3
  change 4 ≤ (getOrbit H.node darts.length d0).length at h_ge4
  have hc_node : CyclicOrder4 H.node (getOrbit H.node darts.length d0).length d0 d1 d2 d3 :=
    cyclicOrder4_of_complete H.node darts h_mc.complete d0 d1 d2 d3
      (i1 := 1) (i2 := 2) (i3 := 3) (by decide) (by decide) (by decide) h_ge4 rfl rfl rfl
  let L := (getOrbit H.node darts.length d0).length
  have h_L : 4 ≤ L := h_ge4
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := cyclicOrder4_distinct hc_node
  obtain ⟨hn01, hn02, hn03⟩ := cyclicOrder4_sameOrbit hc_node
  have h_simple : ∀ {x y : H.Dart}, x ≠ y → SameOrbit H.node x y → ¬ SameOrbit H.face x y :=
    fun hne hn hf => mc_simple_face_corners H darts h_mc hne hn hf
  have h_f01 : ¬ SameOrbit H.face d0 d1 := h_simple h01 hn01
  have h_f02 : ¬ SameOrbit H.face d0 d2 := h_simple h02 hn02
  have h_f03 : ¬ SameOrbit H.face d0 d3 := h_simple h03 hn03
  have h_f12 : ¬ SameOrbit H.face d1 d2 :=
    h_simple h12 (sameOrbit_trans H.node (sameOrbit_symm_of_complete H.node darts h_mc.complete hn01) hn02)
  have h_f13 : ¬ SameOrbit H.face d1 d3 :=
    h_simple h13 (sameOrbit_trans H.node (sameOrbit_symm_of_complete H.node darts h_mc.complete hn01) hn03)
  have h_f23 : ¬ SameOrbit H.face d2 d3 :=
    h_simple h23 (sameOrbit_trans H.node (sameOrbit_symm_of_complete H.node darts h_mc.complete hn02) hn03)
  have hd3_orb : d3 ∈ getOrbit H.node darts.length d0 :=
    (sameOrbit_iff_mem_getOrbit_of_complete H.node darts h_mc.complete (Nat.le_refl _) d0 d3).mp hn03
  have hL_d3 : (getOrbit H.node darts.length d3).length = L :=
    getOrbit_length_eq_of_mem H.node darts.length
      (orbitClosesWithin_of_complete H.node darts h_mc.complete d0) hd3_orb
  have hLd_eq : (getOrbit H.dual.face darts.length d3).length = L := by
    change (getOrbit H.node.symm darts.length d3).length = L
    rw [getOrbit_symm_length_eq_of_complete H.node darts h_mc.complete (Nat.le_refl _) d3, hL_d3]
  have hi1 : Perm.iter H.dual.face 1 d3 = d2 := by
    change H.node.inv (H.node.f d2) = d2
    exact H.node.left_inv d2
  have hi2 : Perm.iter H.dual.face 2 d3 = d1 := by
    change H.dual.face.f (Perm.iter H.dual.face 1 d3) = d1
    rw [hi1]
    change H.node.inv (H.node.f d1) = d1
    exact H.node.left_inv d1
  have hi3 : Perm.iter H.dual.face 3 d3 = d0 := by
    change H.dual.face.f (Perm.iter H.dual.face 2 d3) = d0
    rw [hi2]
    change H.node.inv (H.node.f d0) = d0
    exact H.node.left_inv d0
  have hc_dual : CyclicOrder4 H.dual.face (getOrbit H.dual.face darts.length d3).length d3 d2 d1 d0 :=
    cyclicOrder4_of_complete H.dual.face darts h_mc.complete d3 d2 d1 d0
      (i1 := 1) (i2 := 2) (i3 := 3) (by decide) (by decide) (by decide) (hLd_eq ▸ h_L) hi1 hi2 hi3
  apply Classical.byContradiction
  intro h_neg
  have h_ex1 : ∃ u : H.Dart, SameOrbit H.face u d0 ∧ SameOrbit H.face (H.edge.f u) d2 :=
    Classical.byContradiction fun h => h_neg (Or.inl fun u hu he => h ⟨u, hu, he⟩)
  have h_ex2 : ∃ v : H.Dart, SameOrbit H.face v d1 ∧ SameOrbit H.face (H.edge.f v) d3 :=
    Classical.byContradiction fun h => h_neg (Or.inr fun v hv he => h ⟨v, hv, he⟩)
  obtain ⟨u, hu0, hu2⟩ := h_ex1
  obtain ⟨v, hv1, hv3⟩ := h_ex2
  let S1 : H.Dart → Prop := fun z => SameOrbit H.face z d3 ∨ SameOrbit H.face z d1
  let S2 : H.Dart → Prop := fun z => SameOrbit H.face z d2 ∨ SameOrbit H.face z d0
  have hS1_inv : ∀ z, S1 (H.dual.node.f z) ↔ S1 z := by
    intro z
    have hinv : SameOrbit H.face z (H.face.inv z) :=
      sameOrbit_inv_step_of_complete H.face darts h_mc.complete z
    have hinv' : SameOrbit H.face (H.face.inv z) z :=
      sameOrbit_symm_of_complete H.face darts h_mc.complete hinv
    change (SameOrbit H.face (H.face.inv z) d3 ∨ SameOrbit H.face (H.face.inv z) d1) ↔
      (SameOrbit H.face z d3 ∨ SameOrbit H.face z d1)
    constructor
    · rintro (h | h)
      · exact Or.inl (sameOrbit_trans H.face hinv h)
      · exact Or.inr (sameOrbit_trans H.face hinv h)
    · rintro (h | h)
      · exact Or.inl (sameOrbit_trans H.face hinv' h)
      · exact Or.inr (sameOrbit_trans H.face hinv' h)
  have hS2_inv : ∀ z, S2 (H.dual.node.f z) ↔ S2 z := by
    intro z
    have hinv : SameOrbit H.face z (H.face.inv z) :=
      sameOrbit_inv_step_of_complete H.face darts h_mc.complete z
    have hinv' : SameOrbit H.face (H.face.inv z) z :=
      sameOrbit_symm_of_complete H.face darts h_mc.complete hinv
    change (SameOrbit H.face (H.face.inv z) d2 ∨ SameOrbit H.face (H.face.inv z) d0) ↔
      (SameOrbit H.face z d2 ∨ SameOrbit H.face z d0)
    constructor
    · rintro (h | h)
      · exact Or.inl (sameOrbit_trans H.face hinv h)
      · exact Or.inr (sameOrbit_trans H.face hinv h)
    · rintro (h | h)
      · exact Or.inl (sameOrbit_trans H.face hinv' h)
      · exact Or.inr (sameOrbit_trans H.face hinv' h)
  have hR1 : ReachENIn H.dual.edge H.dual.node S1 d3 d1 := by
    have hp1 : ReachENIn H.dual.edge H.dual.node S1 d3 (H.edge.f v) := by
      refine reachENIn_of_sameOrbit H.dual.edge H.dual.node S1 hS1_inv
        (Or.inl ⟨0, rfl⟩) ?_
      change SameOrbit H.face.symm d3 (H.edge.f v)
      exact (sameOrbit_symm_perm H.face).mpr hv3
    have hp2 : ReachENIn H.dual.edge H.dual.node S1 d3 v := by
      have h_step := ReachENIn.step_e (e := H.dual.edge) (n := H.dual.node) (P := S1) hp1
      have hev : H.dual.edge.f (H.edge.f v) = v := H.edge_involution v
      rw [hev] at h_step
      exact h_step (Or.inr hv1)
    have hp3 : ReachENIn H.dual.edge H.dual.node S1 v d1 := by
      refine reachENIn_of_sameOrbit H.dual.edge H.dual.node S1 hS1_inv (Or.inr hv1) ?_
      change SameOrbit H.face.symm v d1
      exact (sameOrbit_symm_perm H.face).mpr (sameOrbit_symm_of_complete H.face darts h_mc.complete hv1)
    exact reachENIn_trans hp2 hp3
  have hR2 : ReachENIn H.dual.edge H.dual.node S2 d2 d0 := by
    have hp1 : ReachENIn H.dual.edge H.dual.node S2 d2 (H.edge.f u) := by
      refine reachENIn_of_sameOrbit H.dual.edge H.dual.node S2 hS2_inv
        (Or.inl ⟨0, rfl⟩) ?_
      change SameOrbit H.face.symm d2 (H.edge.f u)
      exact (sameOrbit_symm_perm H.face).mpr hu2
    have hp2 : ReachENIn H.dual.edge H.dual.node S2 d2 u := by
      have h_step := ReachENIn.step_e (e := H.dual.edge) (n := H.dual.node) (P := S2) hp1
      have heu : H.dual.edge.f (H.edge.f u) = u := H.edge_involution u
      rw [heu] at h_step
      exact h_step (Or.inr hu0)
    have hp3 : ReachENIn H.dual.edge H.dual.node S2 u d0 := by
      refine reachENIn_of_sameOrbit H.dual.edge H.dual.node S2 hS2_inv (Or.inr hu0) ?_
      change SameOrbit H.face.symm u d0
      exact (sameOrbit_symm_perm H.face).mpr (sameOrbit_symm_of_complete H.face darts h_mc.complete hu0)
    exact reachENIn_trans hp2 hp3
  have h_dp : H.dual.isPlanar darts.length darts = true := by
    rw [isPlanar_dual H darts h_mc.nodup h_mc.complete (Nat.le_refl _)]
    exact h_mc.is_planar
  obtain ⟨z, hz1, hz2⟩ :=
    alternating_walks_intersect_of_cyclic_face H.dual darts h_mc.nodup h_mc.complete h_dp
      hc_dual S1 S2 hS1_inv hS2_inv hR1 hR2
  have hsym : ∀ {x y : H.Dart}, SameOrbit H.face z x → SameOrbit H.face z y → SameOrbit H.face x y :=
    fun hzx hzy => sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete hzx) hzy
  rcases hz1 with hz3 | hz1'
  · rcases hz2 with hz2' | hz0
    · exact h_f23 (sameOrbit_symm_of_complete H.face darts h_mc.complete (hsym hz3 hz2'))
    · exact h_f03 (sameOrbit_symm_of_complete H.face darts h_mc.complete (hsym hz3 hz0))
  · rcases hz2 with hz2' | hz0
    · exact h_f12 (hsym hz1' hz2')
    · exact h_f01 (sameOrbit_symm_of_complete H.face darts h_mc.complete (hsym hz1' hz0))

private theorem splitVertex_opposite_faces_reachEN (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : PrimalMinimalCounterexample H darts)
    {a0 a1 a2 : H.Dart} (ha1 : H.node.f a0 = a1)
    (h_nface : ¬ SameOrbit H.face a0 a2) :
    ReachEN (H.splitVertexAtPair a0 a2).edge (H.splitVertexAtPair a0 a2).node a0 a2 := by
  let H_s := H.splitVertexAtPair a0 a2
  apply Classical.byContradiction
  intro h_no
  let P : H.Dart → Prop := fun z => ReachEN H_s.edge H_s.node a2 z
  have hP_a0 : ¬ P a0 := fun h => h_no (reachEN_symm H_s.edge H_s.node h)
  have hP_a2 : P a2 := reachEN_refl H_s.edge H_s.node a2
  have h_sn_a2 : H_s.node.f a2 = a1 := by
    change H.node.f (swapFun a0 a2 a2) = a1
    rw [swapFun_apply_right, ha1]
  have hP_a1 : P a1 := by
    rw [← h_sn_a2]
    exact reachEN_trans H_s.edge H_s.node hP_a2 ⟨WalkEN.step (StepEN.n_fwd a2) (WalkEN.refl _)⟩
  have hP_ea1 : P (H.edge.f a1) := by
    have he_eq : H_s.edge.f a1 = H.edge.f a1 := rfl
    refine reachEN_trans H_s.edge H_s.node hP_a1 ?_
    rw [← he_eq]
    exact ⟨WalkEN.step (StepEN.e_fwd a1) (WalkEN.refl _)⟩
  have h_fa1 : H.face.f (H.edge.f a1) = a0 := by
    rw [face_edge_eq_node_inv H a1, ← ha1]
    exact H.node.left_inv a0
  have h_orbit : SameOrbit H.face a0 (H.edge.f a1) :=
    sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, h_fa1⟩
  rcases h_orbit with ⟨k, hk⟩
  have hP_iter : P (Perm.iter H.face k a0) := by
    rw [hk]
    exact hP_ea1
  have h_step_ex : ∃ z, SameOrbit H.face a0 z ∧ ¬ P z ∧ P (H.face.f z) := by
    clear hk hP_ea1 hP_a1 hP_a2 h_sn_a2 h_fa1
    induction k with
    | zero => exact absurd hP_iter hP_a0
    | succ k ih =>
      by_cases hpk : P (Perm.iter H.face k a0)
      · exact ih hpk
      · exact ⟨Perm.iter H.face k a0, ⟨k, rfl⟩, hpk, hP_iter⟩
  obtain ⟨z, hz_orb, hPz, hPfz⟩ := h_step_ex
  have hP_sface : ¬ P (H_s.face.f z) := by
    intro hps
    apply hPz
    have hid : H_s.edge.f (H_s.node.f (H_s.face.f z)) = z := H_s.edge_node_face_id z
    rw [← hid]
    have h1 : ReachEN H_s.edge H_s.node (H_s.face.f z) (H_s.node.f (H_s.face.f z)) :=
      ⟨WalkEN.step (StepEN.n_fwd (H_s.face.f z)) (WalkEN.refl _)⟩
    have h2 : ReachEN H_s.edge H_s.node (H_s.node.f (H_s.face.f z))
        (H_s.edge.f (H_s.node.f (H_s.face.f z))) :=
      ⟨WalkEN.step (StepEN.e_fwd _) (WalkEN.refl _)⟩
    exact reachEN_trans H_s.edge H_s.node hps (reachEN_trans H_s.edge H_s.node h1 h2)
  have h_sf : H_s.face.f z = swapFun a0 a2 (H.face.f z) := rfl
  rw [h_sf] at hP_sface
  by_cases hfz0 : H.face.f z = a0
  · rw [hfz0] at hPfz
    exact hP_a0 hPfz
  · by_cases hfz2 : H.face.f z = a2
    · exact h_nface (hfz2 ▸ sameOrbit_eq_perm_iter_succ H.face hz_orb)
    · rw [swapFun_of_ne hfz0 hfz2] at hP_sface
      exact hP_sface hPfz

private theorem splitVertex_opposite_faces_isPlanar_bridgeless (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : PrimalMinimalCounterexample H darts)
    {a0 a2 : H.Dart} (h_ne02 : a0 ≠ a2)
    (h_node : SameOrbit H.node a0 a2) (h_nface : ¬ SameOrbit H.face a0 a2)
    (h_reach : ReachEN (H.splitVertexAtPair a0 a2).edge (H.splitVertexAtPair a0 a2).node a0 a2)
    (h_no_cross : ∀ u : H.Dart, SameOrbit H.face u a0 → ¬ SameOrbit H.face (H.edge.f u) a2) :
    (H.splitVertexAtPair a0 a2).isPlanar darts.length darts = true ∧
      Math.Hypermap.isBridgeless (H.splitVertexAtPair a0 a2) darts darts.length := by
  let H_s := H.splitVertexAtPair a0 a2
  have ha2_node : a2 ∈ getOrbit H.node darts.length a0 :=
    (sameOrbit_iff_mem_getOrbit_of_complete H.node darts h_mc.complete (Nat.le_refl _) a0 a2).mp h_node
  have h_V : countOrbits H_s.node darts.length darts =
      countOrbits H.node darts.length darts + 1 :=
    countOrbits_swapCompRight_same H.node darts h_mc.complete (Nat.le_refl _) h_ne02 ha2_node
  have ha2_not_symm : ¬ a2 ∈ getOrbit H.face.symm darts.length a0 := by
    intro hmem
    have hs : SameOrbit H.face.symm a0 a2 :=
      (sameOrbit_iff_mem_getOrbit_of_complete H.face.symm darts h_mc.complete (Nat.le_refl _) a0 a2).mpr hmem
    exact h_nface (sameOrbit_symm_of_complete H.face darts h_mc.complete ((sameOrbit_symm_perm H.face).mp hs))
  have h_F : countOrbits H_s.face darts.length darts + 1 =
      countOrbits H.face darts.length darts := by
    have h_symm_s : countOrbits H_s.face.symm darts.length darts =
        countOrbits H_s.face darts.length darts :=
      countOrbits_symm_perm_of_complete H_s.face darts h_mc.complete (Nat.le_refl _) darts
    have h_symm_H : countOrbits H.face.symm darts.length darts =
        countOrbits H.face darts.length darts :=
      countOrbits_symm_perm_of_complete H.face darts h_mc.complete (Nat.le_refl _) darts
    have h_diff := countOrbits_swapCompRight_diff H.face.symm darts h_mc.complete (Nat.le_refl _) ha2_not_symm
    have h_fs : H_s.face.symm = swapCompRight H.face.symm a0 a2 := rfl
    rw [← h_symm_s, h_fs, h_diff, h_symm_H]
  have h_reach_T : ReachEN (splitVertexTriple H.hypermapToTriple a0 a2).e
      (splitVertexTriple H.hypermapToTriple a0 a2).n a0 a2 := by
    rw [← splitVertexAtPair_hypermapToTriple]
    exact h_reach
  have h_K : countRelClasses (ReachEN H_s.edge H_s.node) darts =
      countRelClasses (ReachEN H.edge H.node) darts := by
    have hk := countRelClasses_splitVertexTriple_eq_of_reachEN H.hypermapToTriple a0 a2 h_node darts h_reach_T
    rw [← splitVertexAtPair_hypermapToTriple] at hk
    exact hk
  have h_gH : genusDeficit H.hypermapToTriple darts.length darts = 0 :=
    ((eulerChar_le_two_mul_numComponents H darts h_mc.nodup h_mc.complete (Nat.le_refl _)).2.mp
      h_mc.is_planar).1
  have h_gHs : genusDeficit H_s.hypermapToTriple darts.length darts = 0 := by
    unfold genusDeficit at h_gH ⊢
    change (darts.length : Int) + 2 * countRelClasses (ReachEN H_s.edge H_s.node) darts -
      (countOrbits H_s.node darts.length darts + countOrbits H_s.edge darts.length darts +
        countOrbits H_s.face darts.length darts) = 0
    have h_e_eq : H_s.edge = H.edge := rfl
    rw [h_K, h_V, h_e_eq]
    have h_F' : (countOrbits H_s.face darts.length darts : Int) =
        (countOrbits H.face darts.length darts : Int) - 1 := by omega
    change (darts.length : Int) + 2 * countRelClasses (ReachEN H.edge H.node) darts -
      (countOrbits H.node darts.length darts + countOrbits H.edge darts.length darts +
        countOrbits H.face darts.length darts) = 0 at h_gH
    omega
  have h_planar : H_s.isPlanar darts.length darts = true := by
    refine (eulerChar_le_two_mul_numComponents H_s darts h_mc.nodup h_mc.complete (Nat.le_refl _)).2.mpr
      ⟨h_gHs, fun d => mc_edge_ne_self H darts h_mc d⟩
  have h_bridgeless : Math.Hypermap.isBridgeless H_s darts darts.length := by
    rw [isBridgeless_iff_no_sameOrbit_face_edge H_s darts h_mc.complete]
    intro d hs
    have hfs : SameOrbit (swapCompRight H.face.symm a0 a2) (H.edge.f d) d := by
      have h_eq_s : H_s.face.symm = swapCompRight H.face.symm a0 a2 := rfl
      have h_eq_e : H_s.edge.f d = H.edge.f d := rfl
      rw [h_eq_e] at hs
      rw [← h_eq_s]
      exact (sameOrbit_symm_perm H_s.face).mpr hs
    have h_nfs : ¬ SameOrbit H.face.symm a0 a2 :=
      fun h => h_nface (sameOrbit_symm_of_complete H.face darts h_mc.complete ((sameOrbit_symm_perm H.face).mp h))
    have h_sw := (sameOrbit_swapCompRight_of_ne H.face.symm darts h_mc.complete a0 a2 h_nfs
      (H.edge.f d) d).mp hfs
    have toH : ∀ {x y}, SameOrbit H.face.symm x y → SameOrbit H.face x y :=
      fun {x y} h => sameOrbit_symm_of_complete H.face darts h_mc.complete ((sameOrbit_symm_perm H.face).mp h)
    rcases h_sw with hd | ⟨(he0 | he2), (hd0 | hd2)⟩
    · exact mc_not_sameOrbit_face_edge H darts h_mc d (sameOrbit_symm_of_complete H.face darts h_mc.complete (toH hd))
    · exact mc_not_sameOrbit_face_edge H darts h_mc d
        (sameOrbit_trans H.face (toH hd0) (sameOrbit_symm_of_complete H.face darts h_mc.complete (toH he0)))
    · have hed : H.edge.f (H.edge.f d) = d := H.edge_involution d
      exact h_no_cross (H.edge.f d) (toH he0) (by rw [hed]; exact toH hd2)
    · exact h_no_cross d (toH hd0) (toH he2)
    · exact mc_not_sameOrbit_face_edge H darts h_mc d
        (sameOrbit_trans H.face (toH hd2) (sameOrbit_symm_of_complete H.face darts h_mc.complete (toH he2)))
  exact ⟨h_planar, h_bridgeless⟩

/-- Every vertex in a minimal counterexample has degree exactly 3. -/
theorem mc_nodeDegree_eq_three (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (d0 : H.Dart) : Math.Hypermap.nodeDegree H d0 darts.length = 3 := by
  have h_ge3 : 3 ≤ Math.Hypermap.nodeDegree H d0 darts.length :=
    mc_nodeDegree_ge_three H darts h_mc d0
  apply Classical.byContradiction
  intro h_ne3
  have h_ge4 : 4 ≤ (getOrbit H.node darts.length d0).length := by
    change 3 ≤ (getOrbit H.node darts.length d0).length at h_ge3
    change (getOrbit H.node darts.length d0).length ≠ 3 at h_ne3
    omega
  have h_ge4' : 4 ≤ Math.Hypermap.nodeDegree H d0 darts.length := h_ge4
  let L := (getOrbit H.node darts.length d0).length
  let d1 := H.node.f d0
  let d2 := H.node.f d1
  let d3 := H.node.f d2
  have hc_node : CyclicOrder4 H.node (getOrbit H.node darts.length d0).length d0 d1 d2 d3 :=
    cyclicOrder4_of_complete H.node darts h_mc.complete d0 d1 d2 d3
      (i1 := 1) (i2 := 2) (i3 := 3) (by decide) (by decide) (by decide) h_ge4 rfl rfl rfl
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ := cyclicOrder4_distinct hc_node
  have h_disj := dual_opp_face_edge_disjoint H darts h_mc d0 h_ge4'
  have h_triple : ∃ a0 a1 a2 : H.Dart,
      H.node.f a0 = a1 ∧ H.node.f a1 = a2 ∧
      a0 ≠ a1 ∧ a1 ≠ a2 ∧ a0 ≠ a2 ∧
      SameOrbit H.node a0 a2 ∧
      (∀ u : H.Dart, SameOrbit H.face u a0 → ¬ SameOrbit H.face (H.edge.f u) a2) := by
    rcases h_disj with h02_disj | h13_disj
    · exact ⟨d0, d1, d2, rfl, rfl, h01, h12, h02, ⟨2, rfl⟩, h02_disj⟩
    · exact ⟨d1, d2, d3, rfl, rfl, h12, h23, h13, ⟨2, rfl⟩, h13_disj⟩
  obtain ⟨a0, a1, a2, ha1, ha2, h_ne01, h_ne12, h_ne02, h_n02, h_no_cross⟩ := h_triple
  have h_sn01 : SameOrbit H.node a0 a1 := ⟨1, ha1⟩
  have h_sn12 : SameOrbit H.node a1 a2 := ⟨1, ha2⟩
  have h_nfa02 : ¬ SameOrbit H.face a0 a2 := fun hf => mc_simple_face_corners H darts h_mc h_ne02 h_n02 hf
  have h_nfa01 : ¬ SameOrbit H.face a0 a1 := fun hf => mc_simple_face_corners H darts h_mc h_ne01 h_sn01 hf
  have h_nfa12 : ¬ SameOrbit H.face a1 a2 := fun hf => mc_simple_face_corners H darts h_mc h_ne12 h_sn12 hf
  have h_reach := splitVertex_opposite_faces_reachEN H darts h_mc ha1 h_nfa02
  obtain ⟨hs_planar, hs_bridgeless⟩ :=
    splitVertex_opposite_faces_isPlanar_bridgeless H darts h_mc h_ne02 h_n02 h_nfa02 h_reach h_no_cross
  let H_s := H.splitVertexAtPair a0 a2
  have h1 : H_s.node.f a1 ≠ a1 := by
    change H.node.f (swapFun a0 a2 a1) ≠ a1
    rw [swapFun_of_ne h_ne01.symm h_ne12, ha2]
    exact h_ne12.symm
  have h2 : H_s.node.f (H_s.node.f a1) = a1 := by
    have hs1 : H_s.node.f a1 = a2 := by
      change H.node.f (swapFun a0 a2 a1) = a2
      rw [swapFun_of_ne h_ne01.symm h_ne12, ha2]
    rw [hs1]
    change H.node.f (swapFun a0 a2 a2) = a1
    rw [swapFun_apply_right, ha1]
  have h3 : H_s.edge.f a1 ≠ a1 := mc_edge_ne_self H darts h_mc a1
  have h4 : H_s.edge.f (H_s.node.f a1) ≠ H_s.node.f a1 :=
    mc_edge_ne_self H darts h_mc (H_s.node.f a1)
  have h5 : H_s.edge.f a1 ≠ H_s.node.f a1 := by
    have hs1 : H_s.node.f a1 = a2 := by
      change H.node.f (swapFun a0 a2 a1) = a2
      rw [swapFun_of_ne h_ne01.symm h_ne12, ha2]
    rw [hs1]
    intro h_eq
    have h_eq' : H.edge.f a1 = a2 := h_eq
    have h_f_eq := congrArg H.face.f h_eq'
    have hfa1 : H.face.f (H.edge.f a1) = a0 := by
      rw [face_edge_eq_node_inv H a1, ← ha1]
      exact H.node.left_inv a0
    rw [hfa1] at h_f_eq
    exact h_nfa02 (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, h_f_eq.symm⟩)
  let H_A := H_s.smoothDeg2Subtype a1 h1 h2 h3 h4 h5
  have h_sn_a1_val : H_s.node.f a1 = a2 := by
    change H.node.f (swapFun a0 a2 a1) = a2
    rw [swapFun_of_ne h_ne01.symm h_ne12, ha2]
  let rem := [a1, H_s.node.f a1]
  let dartsA := subDarts darts rem
  have h_a0_nmem : ¬ a0 ∈ rem := by
    simp [rem, h_sn_a1_val, h_ne01, h_ne02]
  have hndA : dartsA.Nodup := subDarts_nodup darts rem h_mc.nodup
  have hcompA : ∀ x : H_A.Dart, x ∈ dartsA := fun x =>
    (mem_subDarts darts rem x).mpr (h_mc.complete x.val)
  have hneA : dartsA ≠ [] := subDarts_nonempty darts rem ⟨a0, h_mc.complete a0, h_a0_nmem⟩
  have hltA : dartsA.length < darts.length :=
    exciseSubtype_strictly_smaller darts rem ⟨a1, h_mc.complete a1, List.mem_cons_self⟩
  have hpA : H_A.isPlanar dartsA.length dartsA = true :=
    smoothDeg2Subtype_isPlanar H_s darts h_mc.nodup h_mc.complete (Nat.le_refl _) hs_planar
      a1 h1 h2 h3 h4 h5 dartsA hndA hcompA (Nat.le_refl _)
  have h_ea1_nmem : ¬ H.edge.f a1 ∈ rem := by
    have hne_ea1_a1 : H.edge.f a1 ≠ a1 := h3
    have hne_ea1_a2 : H.edge.f a1 ≠ a2 := by rw [← h_sn_a1_val]; exact h5
    simp [rem, h_sn_a1_val, hne_ea1_a1, hne_ea1_a2]
  have h_ea2_nmem : ¬ H.edge.f a2 ∈ rem := by
    have hne_ea2_a1 : H.edge.f a2 ≠ a1 := by
      intro h
      have h' := congrArg H.edge.f h
      rw [H.edge_involution] at h'
      rw [← h_sn_a1_val] at h'
      exact h5 h'.symm
    have hne_ea2_a2 : H.edge.f a2 ≠ a2 := mc_edge_ne_self H darts h_mc a2
    simp [rem, h_sn_a1_val, hne_ea2_a1, hne_ea2_a2]
  have h_e1_ne_e2 : H.edge.f a1 ≠ H.edge.f a2 := by
    intro h
    have h' := congrArg H.edge.f h
    rw [H.edge_involution, H.edge_involution] at h'
    exact h_ne12 h'
  have h_s_ea2_ea1_nf : ¬ SameOrbit H_s.face (H.edge.f a2) (H.edge.f a1) := by
    intro hs
    have hfs : SameOrbit (swapCompRight H.face.symm a0 a2) (H.edge.f a1) (H.edge.f a2) := by
      have h_eq_s : H_s.face.symm = swapCompRight H.face.symm a0 a2 := rfl
      rw [← h_eq_s]
      exact (sameOrbit_symm_perm H_s.face).mpr hs
    have h_nfs : ¬ SameOrbit H.face.symm a0 a2 :=
      fun h => h_nfa02 (sameOrbit_symm_of_complete H.face darts h_mc.complete ((sameOrbit_symm_perm H.face).mp h))
    have h_sw := (sameOrbit_swapCompRight_of_ne H.face.symm darts h_mc.complete a0 a2 h_nfs
      (H.edge.f a1) (H.edge.f a2)).mp hfs
    have toH : ∀ {x y}, SameOrbit H.face.symm x y → SameOrbit H.face x y :=
      fun {x y} h => sameOrbit_symm_of_complete H.face darts h_mc.complete ((sameOrbit_symm_perm H.face).mp h)
    have hfa2_a1 : SameOrbit H.face (H.edge.f a2) a1 := by
      refine ⟨1, ?_⟩
      change H.face.f (H.edge.f a2) = a1
      rw [face_edge_eq_node_inv H a2, ← ha2]
      exact H.node.left_inv a1
    have hfa1_a0 : SameOrbit H.face (H.edge.f a1) a0 := by
      refine ⟨1, ?_⟩
      change H.face.f (H.edge.f a1) = a0
      rw [face_edge_eq_node_inv H a1, ← ha1]
      exact H.node.left_inv a0
    have ha1_sym := sameOrbit_symm_of_complete H.face darts h_mc.complete hfa2_a1
    rcases h_sw with hh | ⟨_, (hc1 | hc2)⟩
    · have h12 := sameOrbit_trans H.face ha1_sym (sameOrbit_trans H.face
        (sameOrbit_symm_of_complete H.face darts h_mc.complete (toH hh)) hfa1_a0)
      exact h_nfa01 (sameOrbit_symm_of_complete H.face darts h_mc.complete h12)
    · exact h_nfa01 (sameOrbit_symm_of_complete H.face darts h_mc.complete
        (sameOrbit_trans H.face ha1_sym (toH hc1)))
    · exact h_nfa12 (sameOrbit_trans H.face ha1_sym (toH hc2))
  have h_se : ∀ w, H_s.edge.f w = H.edge.f w := fun _ => rfl
  have he1 : H_s.edge.f a1 = H.edge.f a1 := rfl
  have he2 : H_s.edge.f (H_s.node.f a1) = H.edge.f a2 := by rw [h_sn_a1_val]
  have h_sw_fval : ∀ v : H.Dart,
      H_s.face.f (swapFun a1 (H_s.edge.f (H_s.node.f a1))
        (swapFun (H_s.node.f a1) (H_s.edge.f a1) v)) =
      H_s.face.f (swapFun a1 (H.edge.f a2) (swapFun a2 (H.edge.f a1) v)) := by
    intro v
    rw [he1, he2, h_sn_a1_val]
  have h_sw_eval : ∀ v : H.Dart,
      swapFun (H_s.node.f a1) (H_s.edge.f a1)
        (swapFun a1 (H_s.edge.f (H_s.node.f a1))
          (H_s.edge.f (swapFun a1 (H_s.node.f a1) v))) =
      swapFun a2 (H.edge.f a1)
        (swapFun a1 (H.edge.f a2) (H.edge.f (swapFun a1 a2 v))) := by
    intro v
    rw [he1, he2, h_sn_a1_val, h_se]
  have hA_face_to_s : ∀ u : H_A.Dart, SameOrbit H_s.face u.val (H_A.face.f u).val := by
    intro u
    have hu_nmem := u.property
    have hu_ne1 : u.val ≠ a1 := fun h => hu_nmem (by simp [h])
    have hu_ne2 : u.val ≠ a2 := fun h => hu_nmem (by simp [h_sn_a1_val, h])
    have h_fval : (H_A.face.f u).val =
        H_s.face.f (swapFun a1 (H_s.edge.f (H_s.node.f a1))
          (swapFun (H_s.node.f a1) (H_s.edge.f a1) u.val)) := rfl
    rw [h_fval, h_sw_fval u.val]
    by_cases hu_e1 : u.val = H.edge.f a1
    · have hsw1 : swapFun a2 (H.edge.f a1) u.val = a2 := by rw [hu_e1, swapFun_apply_right]
      have hsw2 : swapFun a1 (H.edge.f a2) a2 = a2 :=
        swapFun_of_ne h_ne12.symm (mc_edge_ne_self H darts h_mc a2).symm
      rw [hsw1, hsw2, hu_e1]
      have hfa1 : H.face.f (H.edge.f a1) = a0 := by
        rw [face_edge_eq_node_inv H a1, ← ha1]
        exact H.node.left_inv a0
      have hsf_e1 : H_s.face.f (H.edge.f a1) = a2 := by
        change swapFun a0 a2 (H.face.f (H.edge.f a1)) = a2
        rw [hfa1, swapFun_left]
      refine ⟨2, ?_⟩
      change H_s.face.f (H_s.face.f (H.edge.f a1)) = H_s.face.f a2
      rw [hsf_e1]
    · by_cases hu_e2 : u.val = H.edge.f a2
      · have hsw1 : swapFun a2 (H.edge.f a1) u.val = H.edge.f a2 := by
          rw [hu_e2]
          exact swapFun_of_ne (mc_edge_ne_self H darts h_mc a2) h_e1_ne_e2.symm
        have hsw2 : swapFun a1 (H.edge.f a2) (H.edge.f a2) = a1 := swapFun_apply_right a1 (H.edge.f a2)
        rw [hsw1, hsw2, hu_e2]
        have hfa2 : H.face.f (H.edge.f a2) = a1 := by
          rw [face_edge_eq_node_inv H a2, ← ha2]
          exact H.node.left_inv a1
        have hsf_e2 : H_s.face.f (H.edge.f a2) = a1 := by
          change swapFun a0 a2 (H.face.f (H.edge.f a2)) = a1
          rw [hfa2, swapFun_of_ne h_ne01.symm h_ne12]
        refine ⟨2, ?_⟩
        change H_s.face.f (H_s.face.f (H.edge.f a2)) = H_s.face.f a1
        rw [hsf_e2]
      · have hsw1 : swapFun a2 (H.edge.f a1) u.val = u.val := swapFun_of_ne hu_ne2 hu_e1
        have hsw2 : swapFun a1 (H.edge.f a2) u.val = u.val := swapFun_of_ne hu_ne1 hu_e2
        rw [hsw1, hsw2]
        exact ⟨1, rfl⟩
  have hA_face_sub : ∀ {u w : H_A.Dart}, SameOrbit H_A.face u w → SameOrbit H_s.face u.val w.val := by
    intro u w ⟨k, hk⟩
    subst hk
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
      exact sameOrbit_trans H_s.face ih (hA_face_to_s (Perm.iter H_A.face k u))
  have hbA : Math.Hypermap.isBridgeless H_A dartsA dartsA.length := by
    rw [isBridgeless_iff_no_sameOrbit_face_edge H_A dartsA hcompA]
    intro u hs
    have hu_nmem := u.property
    have hu_ne1 : u.val ≠ a1 := fun h => hu_nmem (by simp [h])
    have hu_ne2 : u.val ≠ a2 := fun h => hu_nmem (by simp [h_sn_a1_val, h])
    have h_eval : (H_A.edge.f u).val =
        swapFun (H_s.node.f a1) (H_s.edge.f a1)
          (swapFun a1 (H_s.edge.f (H_s.node.f a1))
            (H_s.edge.f (swapFun a1 (H_s.node.f a1) u.val))) := rfl
    rw [h_sw_eval u.val, swapFun_of_ne hu_ne1 hu_ne2] at h_eval
    have hs_s := hA_face_sub hs
    rw [h_eval] at hs_s
    by_cases hu_e1 : u.val = H.edge.f a1
    · have hea : H.edge.f u.val = a1 := by rw [hu_e1, H.edge_involution]
      have hsw2 : swapFun a1 (H.edge.f a2) (H.edge.f u.val) = H.edge.f a2 := by
        rw [hea, swapFun_apply_left]
      have hsw3 : swapFun a2 (H.edge.f a1) (H.edge.f a2) = H.edge.f a2 :=
        swapFun_of_ne (mc_edge_ne_self H darts h_mc a2) h_e1_ne_e2.symm
      rw [hsw2, hsw3, hu_e1] at hs_s
      exact h_s_ea2_ea1_nf (sameOrbit_symm_of_complete H_s.face darts h_mc.complete hs_s)
    · by_cases hu_e2 : u.val = H.edge.f a2
      · have hea : H.edge.f u.val = a2 := by rw [hu_e2, H.edge_involution]
        have hsw2 : swapFun a1 (H.edge.f a2) (H.edge.f u.val) = a2 := by
          rw [hea]
          exact swapFun_of_ne h_ne12.symm (mc_edge_ne_self H darts h_mc a2).symm
        have hsw3 : swapFun a2 (H.edge.f a1) a2 = H.edge.f a1 := swapFun_apply_left a2 (H.edge.f a1)
        rw [hsw2, hsw3, hu_e2] at hs_s
        exact h_s_ea2_ea1_nf hs_s
      · have heu_ne1 : H.edge.f u.val ≠ a1 := fun h => hu_e1 (by
          have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
        have heu_ne2 : H.edge.f u.val ≠ a2 := fun h => hu_e2 (by
          have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
        have heu_ne_e1 : H.edge.f u.val ≠ H.edge.f a1 := fun h => hu_ne1 (by
          have h' := congrArg H.edge.f h; rw [H.edge_involution, H.edge_involution] at h'; exact h')
        have heu_ne_e2 : H.edge.f u.val ≠ H.edge.f a2 := fun h => hu_ne2 (by
          have h' := congrArg H.edge.f h; rw [H.edge_involution, H.edge_involution] at h'; exact h')
        rw [swapFun_of_ne heu_ne1 heu_ne_e2, swapFun_of_ne heu_ne2 heu_ne_e1] at hs_s
        exact ((isBridgeless_iff_no_sameOrbit_face_edge H_s darts h_mc.complete).mp hs_bridgeless) u.val hs_s
  obtain ⟨cA⟩ := h_mc.is_minimal H_A dartsA hndA hcompA hneA hltA hpA hbA
  let liftS : H.Dart → Color := fun z =>
    if hz1 : z = a1 then cA.color ⟨H.edge.f a2, h_ea2_nmem⟩
    else if hz2 : z = a2 then cA.color ⟨H.edge.f a1, h_ea1_nmem⟩
    else cA.color ⟨z, fun h => by
      change z ∈ [a1, H_s.node.f a1] at h
      rw [h_sn_a1_val] at h
      rcases List.mem_cons.mp h with h | h
      · exact hz1 h
      · exact hz2 (List.mem_singleton.mp h)⟩
  have h_e1_ne_e2_edge : H.edge.f (H.edge.f a1) = a1 := H.edge_involution a1
  have h_e2_ne_e1_edge : H.edge.f (H.edge.f a2) = a2 := H.edge_involution a2
  have hfa1_a0 : H.face.f (H.edge.f a1) = a0 := by
    rw [face_edge_eq_node_inv H a1, ← ha1]
    exact H.node.left_inv a0
  have hfa2_a1 : H.face.f (H.edge.f a2) = a1 := by
    rw [face_edge_eq_node_inv H a2, ← ha2]
    exact H.node.left_inv a1
  have hsf_e1 : H_s.face.f (H.edge.f a1) = a2 := by
    change swapFun a0 a2 (H.face.f (H.edge.f a1)) = a2
    rw [hfa1_a0, swapFun_apply_left]
  have hsf_e2 : H_s.face.f (H.edge.f a2) = a1 := by
    change swapFun a0 a2 (H.face.f (H.edge.f a2)) = a1
    rw [hfa2_a1, swapFun_of_ne h_ne01.symm h_ne12]
  have hsfa1_nmem : ¬ H_s.face.f a1 ∈ rem := by
    have hsf1_eq : H_s.face.f a1 = H.face.f a1 := by
      change swapFun a0 a2 (H.face.f a1) = H.face.f a1
      have hf10 : H.face.f a1 ≠ a0 := fun h => h_nfa01 (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, h⟩)
      have hf12 : H.face.f a1 ≠ a2 := fun h => h_nfa12 ⟨1, h⟩
      exact swapFun_of_ne hf10 hf12
    rw [hsf1_eq]
    have hf11 : H.face.f a1 ≠ a1 := fun h =>
      mc_faceDegree_ne_one H darts h_mc a1 ((getOrbit_length_eq_one_iff H.face darts h_mc.complete a1).mpr h)
    have hf12 : H.face.f a1 ≠ a2 := fun h => h_nfa12 ⟨1, h⟩
    simp [rem, h_sn_a1_val, hf11, hf12]
  have hsfa2_nmem : ¬ H_s.face.f a2 ∈ rem := by
    have hsf2_eq : H_s.face.f a2 = H.face.f a2 := by
      change swapFun a0 a2 (H.face.f a2) = H.face.f a2
      have hf20 : H.face.f a2 ≠ a0 := fun h => h_nfa02 (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, h⟩)
      have hf22 : H.face.f a2 ≠ a2 := fun h =>
        mc_faceDegree_ne_one H darts h_mc a2 ((getOrbit_length_eq_one_iff H.face darts h_mc.complete a2).mpr h)
      exact swapFun_of_ne hf20 hf22
    rw [hsf2_eq]
    have hf21 : H.face.f a2 ≠ a1 := fun h => h_nfa12 (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, h⟩)
    have hf22 : H.face.f a2 ≠ a2 := fun h =>
      mc_faceDegree_ne_one H darts h_mc a2 ((getOrbit_length_eq_one_iff H.face darts h_mc.complete a2).mpr h)
    simp [rem, h_sn_a1_val, hf21, hf22]
  have h_liftS_face : ∀ z : H.Dart, liftS (H_s.face.f z) = liftS z := by
    intro z
    by_cases hz1 : z = a1
    · subst hz1
      have hsf_a1_ne1 : H_s.face.f z ≠ z := fun h => hsfa1_nmem (by simp [rem, h])
      have hsf_a1_ne2 : H_s.face.f z ≠ a2 := fun h => hsfa1_nmem (by simp [rem, h_sn_a1_val, h])
      have hAf : H_A.face.f ⟨H.edge.f a2, h_ea2_nmem⟩ = ⟨H_s.face.f z, hsfa1_nmem⟩ := by
        apply Subtype.ext
        have h_fval : (H_A.face.f ⟨H.edge.f a2, h_ea2_nmem⟩).val =
            H_s.face.f (swapFun z (H_s.edge.f (H_s.node.f z))
              (swapFun (H_s.node.f z) (H_s.edge.f z) (H.edge.f a2))) := rfl
        rw [h_fval, h_sw_fval (H.edge.f a2)]
        change H_s.face.f (swapFun z (H.edge.f a2) (swapFun a2 (H.edge.f z) (H.edge.f a2))) = H_s.face.f z
        rw [swapFun_of_ne (mc_edge_ne_self H darts h_mc a2) h_e1_ne_e2.symm, swapFun_apply_right]
      have hinv := cA.face_invariant ⟨H.edge.f a2, h_ea2_nmem⟩
      rw [hAf] at hinv
      simp only [liftS, hsf_a1_ne1, hsf_a1_ne2, ↓reduceDIte]
      exact hinv
    · by_cases hz2 : z = a2
      · subst hz2
        have hsf_a2_ne1 : H_s.face.f z ≠ a1 := fun h => hsfa2_nmem (by simp [rem, h])
        have hsf_a2_ne2 : H_s.face.f z ≠ z := fun h => hsfa2_nmem (by simp [rem, h_sn_a1_val, h])
        have hAf : H_A.face.f ⟨H.edge.f a1, h_ea1_nmem⟩ = ⟨H_s.face.f z, hsfa2_nmem⟩ := by
          apply Subtype.ext
          have h_fval : (H_A.face.f ⟨H.edge.f a1, h_ea1_nmem⟩).val =
              H_s.face.f (swapFun a1 (H_s.edge.f (H_s.node.f a1))
                (swapFun (H_s.node.f a1) (H_s.edge.f a1) (H.edge.f a1))) := rfl
          rw [h_fval, h_sw_fval (H.edge.f a1)]
          change H_s.face.f (swapFun a1 (H.edge.f z) (swapFun z (H.edge.f a1) (H.edge.f a1))) = H_s.face.f z
          rw [swapFun_apply_right, swapFun_of_ne h_ne12.symm (mc_edge_ne_self H darts h_mc z).symm]
        have hinv := cA.face_invariant ⟨H.edge.f a1, h_ea1_nmem⟩
        rw [hAf] at hinv
        simp only [liftS, hsf_a2_ne1, hsf_a2_ne2, ↓reduceDIte, h_ne12.symm]
        exact hinv
      · have hz_nmem : ¬ z ∈ rem := by simp [rem, h_sn_a1_val, hz1, hz2]
        by_cases hsf1 : H_s.face.f z = a1
        · have hz_eq : z = H.edge.f a2 := by
            have hinv := congrArg H_s.face.inv (hsf1.trans hsf_e2.symm)
            rw [H_s.face.left_inv, H_s.face.left_inv] at hinv
            exact hinv
          subst hz_eq
          simp only [liftS, hsf1, ↓reduceDIte, hz1, hz2]
        · by_cases hsf2 : H_s.face.f z = a2
          · have hz_eq : z = H.edge.f a1 := by
              have hinv := congrArg H_s.face.inv (hsf2.trans hsf_e1.symm)
              rw [H_s.face.left_inv, H_s.face.left_inv] at hinv
              exact hinv
            subst hz_eq
            simp only [liftS, hsf2, h_ne12.symm, ↓reduceDIte, hz1, hz2]
          · have hz_ne_e1 : z ≠ H.edge.f a1 := fun h => hsf2 (by rw [h, hsf_e1])
            have hz_ne_e2 : z ≠ H.edge.f a2 := fun h => hsf1 (by rw [h, hsf_e2])
            have hsf_nmem : ¬ H_s.face.f z ∈ rem := by simp [rem, h_sn_a1_val, hsf1, hsf2]
            have hAf : H_A.face.f ⟨z, hz_nmem⟩ = ⟨H_s.face.f z, hsf_nmem⟩ := by
              apply Subtype.ext
              have h_fval : (H_A.face.f ⟨z, hz_nmem⟩).val =
                  H_s.face.f (swapFun a1 (H_s.edge.f (H_s.node.f a1))
                    (swapFun (H_s.node.f a1) (H_s.edge.f a1) z)) := rfl
              rw [h_fval, h_sw_fval z]
              change H_s.face.f (swapFun a1 (H.edge.f a2) (swapFun a2 (H.edge.f a1) z)) = H_s.face.f z
              rw [swapFun_of_ne hz2 hz_ne_e1, swapFun_of_ne hz1 hz_ne_e2]
            have hinv := cA.face_invariant ⟨z, hz_nmem⟩
            rw [hAf] at hinv
            simp only [liftS, hsf1, hsf2, ↓reduceDIte, hz1, hz2]
            exact hinv
  have h_liftS_edge : ∀ z : H.Dart, liftS (H.edge.f z) ≠ liftS z := by
    intro z
    by_cases hz1 : z = a1
    · subst hz1
      have he_ne1 : H.edge.f z ≠ z := h3
      have he_ne2 : H.edge.f z ≠ a2 := by rw [← h_sn_a1_val]; exact h5
      have hAe : H_A.edge.f ⟨H.edge.f a2, h_ea2_nmem⟩ = ⟨H.edge.f z, h_ea1_nmem⟩ := by
        apply Subtype.ext
        have h_eval : (H_A.edge.f ⟨H.edge.f a2, h_ea2_nmem⟩).val =
            swapFun (H_s.node.f z) (H_s.edge.f z)
              (swapFun z (H_s.edge.f (H_s.node.f z))
                (H_s.edge.f (swapFun z (H_s.node.f z) (H.edge.f a2)))) := rfl
        have hne_ea2_a2 : H.edge.f a2 ≠ a2 := mc_edge_ne_self H darts h_mc a2
        have hne_ea2_a1 : H.edge.f a2 ≠ z := fun h => he_ne2 (by rw [← h, H.edge_involution])
        rw [h_eval, h_sw_eval (H.edge.f a2)]
        change swapFun a2 (H.edge.f z) (swapFun z (H.edge.f a2) (H.edge.f (swapFun z a2 (H.edge.f a2)))) = H.edge.f z
        rw [swapFun_of_ne hne_ea2_a1 hne_ea2_a2, h_e2_ne_e1_edge,
          swapFun_of_ne h_ne12.symm hne_ea2_a2.symm, swapFun_apply_left]
      have hep := cA.edge_proper ⟨H.edge.f a2, h_ea2_nmem⟩
      rw [hAe] at hep
      simp only [liftS, he_ne1, he_ne2, ↓reduceDIte]
      exact hep
    · by_cases hz2 : z = a2
      · subst hz2
        have he_ne1 : H.edge.f z ≠ a1 := fun h => by
          have h5' : H.edge.f a1 ≠ z := by rw [← h_sn_a1_val]; exact h5
          exact h5' (by rw [← h, H.edge_involution])
        have he_ne2 : H.edge.f z ≠ z := mc_edge_ne_self H darts h_mc z
        have hAe : H_A.edge.f ⟨H.edge.f a1, h_ea1_nmem⟩ = ⟨H.edge.f z, h_ea2_nmem⟩ := by
          apply Subtype.ext
          have h_eval : (H_A.edge.f ⟨H.edge.f a1, h_ea1_nmem⟩).val =
              swapFun (H_s.node.f a1) (H_s.edge.f a1)
                (swapFun a1 (H_s.edge.f (H_s.node.f a1))
                  (H_s.edge.f (swapFun a1 (H_s.node.f a1) (H.edge.f a1)))) := rfl
          have hne_ea1_a2 : H.edge.f a1 ≠ z := fun h => he_ne1 (by rw [← h, H.edge_involution])
          rw [h_eval, h_sw_eval (H.edge.f a1)]
          change swapFun z (H.edge.f a1) (swapFun a1 (H.edge.f z) (H.edge.f (swapFun a1 z (H.edge.f a1)))) = H.edge.f z
          rw [swapFun_of_ne (show H.edge.f a1 ≠ a1 from h3) hne_ea1_a2, h_e1_ne_e2_edge, swapFun_apply_left]
          exact swapFun_of_ne he_ne2 h_e1_ne_e2.symm
        have hep := cA.edge_proper ⟨H.edge.f a1, h_ea1_nmem⟩
        rw [hAe] at hep
        simp only [liftS, he_ne1, he_ne2, ↓reduceDIte, h_ne12.symm]
        exact hep
      · have hz_nmem : ¬ z ∈ rem := by simp [rem, h_sn_a1_val, hz1, hz2]
        by_cases he1 : H.edge.f z = a1
        · have hz_eq : z = H.edge.f a1 := by rw [← he1, H.edge_involution]
          subst hz_eq
          have he_ne1 : H.edge.f a1 ≠ a1 := h3
          have he_ne2 : H.edge.f a1 ≠ a2 := by rw [← h_sn_a1_val]; exact h5
          have hAe : H_A.edge.f ⟨H.edge.f a1, hz_nmem⟩ = ⟨H.edge.f a2, h_ea2_nmem⟩ := by
            apply Subtype.ext
            have h_eval : (H_A.edge.f ⟨H.edge.f a1, hz_nmem⟩).val =
                swapFun (H_s.node.f a1) (H_s.edge.f a1)
                  (swapFun a1 (H_s.edge.f (H_s.node.f a1))
                    (H_s.edge.f (swapFun a1 (H_s.node.f a1) (H.edge.f a1)))) := rfl
            rw [h_eval, h_sw_eval (H.edge.f a1)]
            change swapFun a2 (H.edge.f a1) (swapFun a1 (H.edge.f a2) (H.edge.f (swapFun a1 a2 (H.edge.f a1)))) = H.edge.f a2
            rw [swapFun_of_ne (show H.edge.f a1 ≠ a1 from h3) he_ne2, h_e1_ne_e2_edge, swapFun_apply_left]
            exact swapFun_of_ne (mc_edge_ne_self H darts h_mc a2) h_e1_ne_e2.symm
          have hep := cA.edge_proper ⟨H.edge.f a1, hz_nmem⟩
          rw [hAe] at hep
          simp only [liftS, he1, ↓reduceDIte, hz1, hz2]
          exact hep
        · by_cases he2 : H.edge.f z = a2
          · have hz_eq : z = H.edge.f a2 := by rw [← he2, H.edge_involution]
            subst hz_eq
            have he_ne1 : H.edge.f a2 ≠ a1 := fun h => by
              have h5' : H.edge.f a1 ≠ a2 := by rw [← h_sn_a1_val]; exact h5
              exact h5' (by rw [← h, H.edge_involution])
            have he_ne2 : H.edge.f a2 ≠ a2 := mc_edge_ne_self H darts h_mc a2
            have hAe : H_A.edge.f ⟨H.edge.f a2, hz_nmem⟩ = ⟨H.edge.f a1, h_ea1_nmem⟩ := by
              apply Subtype.ext
              have h_eval : (H_A.edge.f ⟨H.edge.f a2, hz_nmem⟩).val =
                  swapFun (H_s.node.f a1) (H_s.edge.f a1)
                    (swapFun a1 (H_s.edge.f (H_s.node.f a1))
                      (H_s.edge.f (swapFun a1 (H_s.node.f a1) (H.edge.f a2)))) := rfl
              rw [h_eval, h_sw_eval (H.edge.f a2)]
              change swapFun a2 (H.edge.f a1) (swapFun a1 (H.edge.f a2) (H.edge.f (swapFun a1 a2 (H.edge.f a2)))) = H.edge.f a1
              rw [swapFun_of_ne he_ne1 he_ne2, h_e2_ne_e1_edge,
                swapFun_of_ne h_ne12.symm he_ne2.symm, swapFun_apply_left]
            have hep := cA.edge_proper ⟨H.edge.f a2, hz_nmem⟩
            rw [hAe] at hep
            simp only [liftS, he2, h_ne12.symm, ↓reduceDIte, hz1, hz2]
            exact hep
          · have hz_ne_e1 : H.edge.f z ≠ H.edge.f a1 := fun h => hz1 (by
              have h' := congrArg H.edge.f h; rw [H.edge_involution, H.edge_involution] at h'; exact h')
            have hz_ne_e2 : H.edge.f z ≠ H.edge.f a2 := fun h => hz2 (by
              have h' := congrArg H.edge.f h; rw [H.edge_involution, H.edge_involution] at h'; exact h')
            have he_nmem : ¬ H.edge.f z ∈ rem := by simp [rem, h_sn_a1_val, he1, he2]
            have hAe : H_A.edge.f ⟨z, hz_nmem⟩ = ⟨H.edge.f z, he_nmem⟩ := by
              apply Subtype.ext
              have h_eval : (H_A.edge.f ⟨z, hz_nmem⟩).val =
                  swapFun (H_s.node.f a1) (H_s.edge.f a1)
                    (swapFun a1 (H_s.edge.f (H_s.node.f a1))
                      (H_s.edge.f (swapFun a1 (H_s.node.f a1) z))) := rfl
              rw [h_eval, h_sw_eval z]
              change swapFun a2 (H.edge.f a1) (swapFun a1 (H.edge.f a2) (H.edge.f (swapFun a1 a2 z))) = H.edge.f z
              rw [swapFun_of_ne hz1 hz2, swapFun_of_ne he1 hz_ne_e2, swapFun_of_ne he2 hz_ne_e1]
            have hep := cA.edge_proper ⟨z, hz_nmem⟩
            rw [hAe] at hep
            simp only [liftS, he1, he2, ↓reduceDIte, hz1, hz2]
            exact hep
  let c_split : H_s.FaceColoring := ⟨liftS, h_liftS_face, h_liftS_edge⟩
  have h_H_face_to_s : ∀ {x y : H.Dart}, SameOrbit H.face x y → SameOrbit H_s.face x y := by
    intro x y hxy
    have h_nfs : ¬ SameOrbit H.face.symm a0 a2 :=
      fun h => h_nfa02 (sameOrbit_symm_of_complete H.face darts h_mc.complete ((sameOrbit_symm_perm H.face).mp h))
    have hsym : SameOrbit H.face.symm y x := (sameOrbit_symm_perm H.face).mpr hxy
    have hsw : SameOrbit (swapCompRight H.face.symm a0 a2) y x :=
      (sameOrbit_swapCompRight_of_ne H.face.symm darts h_mc.complete a0 a2 h_nfs y x).mpr (Or.inl hsym)
    have hfs : H_s.face.symm = swapCompRight H.face.symm a0 a2 := rfl
    rw [← hfs] at hsw
    exact (sameOrbit_symm_perm H_s.face).mp hsw
  have h_lift_face : ∀ z : H.Dart, liftS (H.face.f z) = liftS z := by
    intro z
    have hs : SameOrbit H_s.face (H.face.f z) z :=
      h_H_face_to_s (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, rfl⟩)
    exact sameOrbit_node_of_face_color_inv H_s c_split hs
  exact h_mc.not_colorable ⟨liftS, h_lift_face, h_liftS_edge⟩

/-! ## Section 5: Girth >= 5 (`mc_faceDegree_ge_five`) -/

private theorem nodeDegree_three_inv_eq (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (d : H.Dart) :
    H.node.inv d = H.node.f (H.node.f d) := by
  have h3 := mc_nodeDegree_eq_three H darts h_mc d
  have hid := perm_iter_length_getOrbit_eq_self_of_complete H.node darts h_mc.complete (Nat.le_refl _) d
  change (getOrbit H.node darts.length d).length = 3 at h3
  rw [h3] at hid
  have hid' : H.node.f (H.node.f (H.node.f d)) = d := hid
  have h := congrArg H.node.inv hid'
  rw [H.node.left_inv] at h
  exact h.symm

private theorem nodeDegree_three_node_f_eq_inv_inv (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (d : H.Dart) :
    H.node.inv (H.node.inv d) = H.node.f d := by
  rw [nodeDegree_three_inv_eq H darts h_mc d, H.node.left_inv]

private theorem node_edge_of_face_step (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (x : H.Dart) :
    let y := H.face.f x
    let u := H.node.inv y
    H.node.f y = H.edge.f x ∧
    H.face.f (H.edge.f y) = u ∧
    H.face.f (H.edge.f u) = H.edge.f x := by
  intro y u
  refine ⟨node_face_eq_edge H x, face_edge_eq_node_inv H y, ?_⟩
  rw [face_edge_eq_node_inv H u]
  dsimp only [u]
  rw [nodeDegree_three_node_f_eq_inv_inv H darts h_mc y, node_face_eq_edge H x]

private theorem adjacent_outer_faces_ne (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (x : H.Dart) :
    ¬ SameOrbit H.face (H.edge.f x) (H.edge.f (H.face.f x)) := by
  intro hs
  let y := H.face.f x
  let u := H.node.inv y
  obtain ⟨_, hfy, hfu⟩ := node_edge_of_face_step H darts h_mc x
  have h_ey_u : SameOrbit H.face (H.edge.f y) u := ⟨1, hfy⟩
  have h_eu_ex : SameOrbit H.face (H.edge.f u) (H.edge.f x) := ⟨1, hfu⟩
  have h_u_eu : SameOrbit H.face u (H.edge.f u) := by
    have h1 := sameOrbit_symm_of_complete H.face darts h_mc.complete h_ey_u
    have h2 := sameOrbit_symm_of_complete H.face darts h_mc.complete hs
    have h3 := sameOrbit_symm_of_complete H.face darts h_mc.complete h_eu_ex
    exact sameOrbit_trans H.face h1 (sameOrbit_trans H.face h2 h3)
  exact mc_not_sameOrbit_face_edge H darts h_mc u h_u_eu

private theorem perm_iter_deleteEdgeSubtype_face_val (H : Hypermap) [DecidableEq H.Dart]
    (d : H.Dart) :
    ∀ k (u : (H.deleteEdgeSubtype d).Dart),
      (Perm.iter (H.deleteEdgeSubtype d).face k u).val =
        Perm.iter (bypass (bypass (swapCompRight H.face d (H.edge.f d)) d) (H.edge.f d)) k u.val
  | 0, _ => rfl
  | k + 1, u => by
    let H' := H.deleteEdgeSubtype d
    let b := bypass (bypass (swapCompRight H.face d (H.edge.f d)) d) (H.edge.f d)
    change (H'.face.f (Perm.iter H'.face k u)).val = b.f (Perm.iter b k u.val)
    have h_step : (H'.face.f (Perm.iter H'.face k u)).val = b.f (Perm.iter H'.face k u).val := rfl
    rw [h_step, perm_iter_deleteEdgeSubtype_face_val H d k u]

private theorem deleteEdgeSubtype_face_sameOrbit_iff_swapCompRight (H : Hypermap) [DecidableEq H.Dart]
    (d : H.Dart) (u w : (H.deleteEdgeSubtype d).Dart) :
    SameOrbit (H.deleteEdgeSubtype d).face u w ↔
      SameOrbit (swapCompRight H.face d (H.edge.f d)) u.val w.val := by
  let b := bypass (bypass (swapCompRight H.face d (H.edge.f d)) d) (H.edge.f d)
  have hu_ne_d : u.val ≠ d := fun h => u.property (by simp [h])
  have hu_ne_e : u.val ≠ H.edge.f d := fun h => u.property (by simp [h])
  have hw_ne_d : w.val ≠ d := fun h => w.property (by simp [h])
  have hw_ne_e : w.val ≠ H.edge.f d := fun h => w.property (by simp [h])
  have h_sub_b : SameOrbit (H.deleteEdgeSubtype d).face u w ↔ SameOrbit b u.val w.val := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; exact (perm_iter_deleteEdgeSubtype_face_val H d k u).symm⟩
    · rintro ⟨k, hk⟩
      have hbd_step : ∀ m (v : (H.deleteEdgeSubtype d).Dart),
          ∃ v' : (H.deleteEdgeSubtype d).Dart, Perm.iter b m v.val = v'.val ∧ Perm.iter (H.deleteEdgeSubtype d).face m v = v' := by
        intro m v
        exact ⟨Perm.iter (H.deleteEdgeSubtype d).face m v,
          (perm_iter_deleteEdgeSubtype_face_val H d m v).symm, rfl⟩
      obtain ⟨v', hv1, hv2⟩ := hbd_step k u
      rw [hv1] at hk
      exact ⟨k, hv2.trans (Subtype.ext hk)⟩
  rw [h_sub_b]
  have hb1 := sameOrbit_bypass_iff (bypass (swapCompRight H.face d (H.edge.f d)) d) (H.edge.f d)
    u.val w.val hu_ne_e hw_ne_e
  have hb2 := sameOrbit_bypass_iff (swapCompRight H.face d (H.edge.f d)) d
    u.val w.val hu_ne_d hw_ne_d
  exact hb1.trans hb2

private theorem deleteEdgeSubtype_face_sameOrbit_iff_ne (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_comp : ∀ z : H.Dart, z ∈ darts)
    (d : H.Dart) (h_ndb : ¬ SameOrbit H.face d (H.edge.f d))
    (u w : (H.deleteEdgeSubtype d).Dart) :
    SameOrbit (H.deleteEdgeSubtype d).face u w ↔
      SameOrbit H.face u.val w.val ∨
        (SameOrbit H.face u.val d ∨ SameOrbit H.face u.val (H.edge.f d)) ∧
          (SameOrbit H.face w.val d ∨ SameOrbit H.face w.val (H.edge.f d)) := by
  rw [deleteEdgeSubtype_face_sameOrbit_iff_swapCompRight H d u w]
  exact sameOrbit_swapCompRight_of_ne H.face darts h_comp d (H.edge.f d) h_ndb u.val w.val

/-- No face in a minimal counterexample has size 2. -/
theorem mc_faceDegree_ne_two (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (d0 : H.Dart) : Math.Hypermap.faceDegree H d0 darts.length ≠ 2 := by
  intro h_len
  let d1 := H.face.f d0
  have hid := perm_iter_length_getOrbit_eq_self_of_complete H.face darts h_mc.complete (Nat.le_refl _) d0
  change (getOrbit H.face darts.length d0).length = 2 at h_len
  rw [h_len] at hid
  have hd10 : H.face.f d1 = d0 := hid
  have h_ne01 : d0 ≠ d1 := fun h =>
    mc_faceDegree_ne_one H darts h_mc d0 ((getOrbit_length_eq_one_iff H.face darts h_mc.complete d0).mpr h.symm)
  let b0 := H.edge.f d0
  let b1 := H.edge.f d1
  have hb0_ne_d0 : b0 ≠ d0 := mc_edge_ne_self H darts h_mc d0
  have hb0_ne_d1 : b0 ≠ d1 := by
    intro h
    exact mc_not_sameOrbit_face_edge H darts h_mc d0 ⟨1, h.symm⟩
  have hb1_ne_d0 : b1 ≠ d0 := by
    intro h
    exact mc_not_sameOrbit_face_edge H darts h_mc d1 ⟨1, hd10.trans h.symm⟩
  have hb1_ne_d1 : b1 ≠ d1 := mc_edge_ne_self H darts h_mc d1
  have hF_01 : ¬ SameOrbit H.face b0 b1 := adjacent_outer_faces_ne H darts h_mc d0
  let u0 := H.face.f b0
  have hu0_ne_b0 : u0 ≠ b0 := fun h =>
    mc_faceDegree_ne_one H darts h_mc b0 ((getOrbit_length_eq_one_iff H.face darts h_mc.complete b0).mpr h)
  have hu0_ne_d0 : u0 ≠ d0 := fun h =>
    mc_not_sameOrbit_face_edge H darts h_mc d0
      (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, h⟩)
  let H' := H.deleteEdgeSubtype d0
  let darts' := subDarts darts [d0, b0]
  have hd1_nmem : ¬ d1 ∈ [d0, b0] := by simp [h_ne01.symm, hb0_ne_d1.symm]
  have hb1_nmem : ¬ b1 ∈ [d0, b0] := by simp [hb1_ne_d0, show b1 ≠ b0 from fun h => hF_01 (h ▸ ⟨0, rfl⟩)]
  have hu0_nmem : ¬ u0 ∈ [d0, b0] := by simp [hu0_ne_d0, hu0_ne_b0]
  have hnd' : darts'.Nodup := subDarts_nodup darts [d0, b0] h_mc.nodup
  have hcomp' : ∀ x : H'.Dart, x ∈ darts' := fun x =>
    (mem_subDarts darts [d0, b0] x).mpr (h_mc.complete x.val)
  have hne' : darts' ≠ [] := subDarts_nonempty darts [d0, b0] ⟨d1, h_mc.complete d1, hd1_nmem⟩
  have hlt' : darts'.length < darts.length :=
    exciseSubtype_strictly_smaller darts [d0, b0] ⟨d0, h_mc.complete d0, List.mem_cons_self⟩
  have hp' : H'.isPlanar darts'.length darts' = true :=
    deleteEdgeSubtype_isPlanar H darts h_mc.nodup h_mc.complete (Nat.le_refl _) h_mc.is_planar
      d0 hb0_ne_d0 darts' hnd' hcomp' (Nat.le_refl _)
  have h_ndb0 : ¬ SameOrbit H.face d0 b0 := mc_not_sameOrbit_face_edge H darts h_mc d0
  have hb' : Math.Hypermap.isBridgeless H' darts' darts'.length := by
    rw [isBridgeless_iff_no_sameOrbit_face_edge H' darts' hcomp']
    intro z hs
    have hev : (H'.edge.f z).val = H.edge.f z.val := deleteEdgeSubtype_edge_val H d0 z
    have hsw := (deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 z (H'.edge.f z)).mp hs
    rw [hev] at hsw
    have hz_ne_d0 : z.val ≠ d0 := fun h => z.property (by simp [h])
    have hz_ne_b0 : z.val ≠ b0 := fun h => z.property (by simp [h, b0])
    have hez_ne_d0 : H.edge.f z.val ≠ d0 := fun h => hz_ne_b0 (by
      have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
    have hez_ne_b0 : H.edge.f z.val ≠ b0 := fun h => hz_ne_d0 (by
      have h' := congrArg H.edge.f h; dsimp only [b0] at h'; rw [H.edge_involution, H.edge_involution] at h'; exact h')
    have h_or_face : ∀ w : H.Dart, SameOrbit H.face w d0 → w ≠ d0 → w = d1 := by
      intro w hw hne
      obtain ⟨k, hk⟩ := sameOrbit_symm_of_complete H.face darts h_mc.complete hw
      have hmod : ∀ m : Nat, Perm.iter H.face m d0 = d0 ∨ Perm.iter H.face m d0 = d1 := by
        intro m
        induction m with
        | zero => exact Or.inl rfl
        | succ m ih =>
          rcases ih with h | h
          · exact Or.inr (by change H.face.f (Perm.iter H.face m d0) = d1; rw [h])
          · exact Or.inl (by change H.face.f (Perm.iter H.face m d0) = d0; rw [h, hd10])
      rcases hmod k with h | h
      · exact absurd (hk.symm.trans h) hne
      · exact hk.symm.trans h
    rcases hsw with hh | ⟨(hz_d0 | hz_b0), (he_d0 | he_b0)⟩
    · exact mc_not_sameOrbit_face_edge H darts h_mc z.val hh
    · exact mc_not_sameOrbit_face_edge H darts h_mc z.val
        (sameOrbit_trans H.face hz_d0 (sameOrbit_symm_of_complete H.face darts h_mc.complete he_d0))
    · have hzd1 : z.val = d1 := h_or_face z.val hz_d0 hz_ne_d0
      have he_b1 : H.edge.f z.val = b1 := by rw [hzd1]
      exact hF_01 (sameOrbit_symm_of_complete H.face darts h_mc.complete (he_b1 ▸ he_b0))
    · have hed1 : H.edge.f z.val = d1 := h_or_face (H.edge.f z.val) he_d0 hez_ne_d0
      have hz_b1 : z.val = b1 := by
        have h' := congrArg H.edge.f hed1; rw [H.edge_involution] at h'; exact h'
      exact hF_01 (sameOrbit_symm_of_complete H.face darts h_mc.complete (hz_b1 ▸ hz_b0))
    · exact mc_not_sameOrbit_face_edge H darts h_mc z.val
        (sameOrbit_trans H.face hz_b0 (sameOrbit_symm_of_complete H.face darts h_mc.complete he_b0))
  obtain ⟨c'⟩ := h_mc.is_minimal H' darts' hnd' hcomp' hne' hlt' hp' hb'
  let col0 : Color := c'.color ⟨d1, hd1_nmem⟩
  let col1 : Color := c'.color ⟨b1, hb1_nmem⟩
  obtain ⟨c_F, hcF_0, hcF_1⟩ := exists_third_color col0 col1
  have h_col_F0 : ∀ {z : H.Dart} (hz : ¬ z ∈ [d0, b0]), SameOrbit H.face z b0 → c'.color ⟨z, hz⟩ = col0 := by
    intro z hz hzb
    have hsf : SameOrbit H'.face ⟨z, hz⟩ ⟨d1, hd1_nmem⟩ := by
      refine (deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 _ _).mpr ?_
      exact Or.inr ⟨Or.inr hzb, Or.inl ⟨1, hd10⟩⟩
    exact sameOrbit_node_of_face_color_inv H' c' hsf
  let lift : H.Dart → Color := fun z =>
    if hz1 : z = d0 then c_F
    else if hz2 : z = d1 then c_F
    else if hz3 : z = b0 then col0
    else c'.color ⟨z, fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> contradiction⟩
  have h_in_F : ∀ w, SameOrbit H.face w d0 → w = d0 ∨ w = d1 := by
    intro w hw
    obtain ⟨k, hk⟩ := sameOrbit_symm_of_complete H.face darts h_mc.complete hw
    have hmod : ∀ m : Nat, Perm.iter H.face m d0 = d0 ∨ Perm.iter H.face m d0 = d1 := by
      intro m
      induction m with
      | zero => exact Or.inl rfl
      | succ m ih =>
        rcases ih with h | h
        · exact Or.inr (by change H.face.f (Perm.iter H.face m d0) = d1; rw [h])
        · exact Or.inl (by change H.face.f (Perm.iter H.face m d0) = d0; rw [h, hd10])
    rcases hmod k with h | h
    · exact Or.inl (hk.symm.trans h)
    · exact Or.inr (hk.symm.trans h)
  have h_lift_face : ∀ z : H.Dart, lift (H.face.f z) = lift z := by
    intro z
    by_cases hz0 : z = d0
    · subst hz0; simp [lift, d1, h_ne01.symm]
    · by_cases hz1 : z = d1
      · subst hz1; simp [lift, hd10, h_ne01.symm]
      · by_cases hzb0 : z = b0
        · subst hzb0
          have hu0_ne_d1 : u0 ≠ d1 := fun h => h_ndb0 (sameOrbit_symm_of_complete H.face darts h_mc.complete
            ⟨2, by change H.face.f u0 = d0; rw [h, hd10]⟩)
          have h_u0_col := h_col_F0 hu0_nmem (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, rfl⟩)
          simp only [lift, u0, hu0_ne_d0, hu0_ne_d1, hu0_ne_b0, ↓reduceDIte, hb0_ne_d0, hb0_ne_d1]
          exact h_u0_col
        · have hz_nmem : ¬ z ∈ [d0, b0] := by simp [hz0, hzb0]
          have hfz_ne0 : H.face.f z ≠ d0 := fun h => hz1 (by
            have h' := congrArg H.face.inv (h.trans hd10.symm); rw [H.face.left_inv, H.face.left_inv] at h'; exact h')
          have hfz_ne1 : H.face.f z ≠ d1 := fun h => hz0 (by
            have h' := congrArg H.face.inv h; rw [H.face.left_inv, H.face.left_inv] at h'; exact h')
          by_cases hfz_b0 : H.face.f z = b0
          · have hzb : SameOrbit H.face z b0 := ⟨1, hfz_b0⟩
            have hz_col := h_col_F0 hz_nmem hzb
            simp only [lift, hfz_b0, hb0_ne_d0, hb0_ne_d1, ↓reduceDIte, hz0, hz1, hzb0]
            exact hz_col.symm
          · have hfz_nmem : ¬ H.face.f z ∈ [d0, b0] := by simp [hfz_ne0, hfz_b0]
            have hsf : SameOrbit H'.face ⟨H.face.f z, hfz_nmem⟩ ⟨z, hz_nmem⟩ :=
              (deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 _ _).mpr
                (Or.inl (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, rfl⟩))
            simp only [lift, hfz_ne0, hfz_ne1, hfz_b0, ↓reduceDIte, hz0, hz1, hzb0]
            exact sameOrbit_node_of_face_color_inv H' c' hsf
  have h_lift_edge : ∀ z : H.Dart, lift (H.edge.f z) ≠ lift z := by
    intro z
    by_cases hz0 : z = d0
    · subst hz0
      simp only [lift, b0, hb0_ne_d0, hb0_ne_d1, ↓reduceDIte]
      exact hcF_0.symm
    · by_cases hz1 : z = d1
      · subst hz1
        have heb0 : b1 ≠ b0 := fun h => hF_01 (h ▸ ⟨0, rfl⟩)
        simp only [lift, b1, hb1_ne_d0, hb1_ne_d1, heb0, ↓reduceDIte, h_ne01.symm]
        exact hcF_1.symm
      · by_cases hzb0 : z = b0
        · subst hzb0
          have hed : H.edge.f b0 = d0 := by dsimp only [b0]; exact H.edge_involution d0
          simp only [lift, hed, ↓reduceDIte, hb0_ne_d0, hb0_ne_d1]
          exact hcF_0
        · by_cases hzb1 : z = b1
          · subst hzb1
            have heb0 : b1 ≠ b0 := fun h => hF_01 (h ▸ ⟨0, rfl⟩)
            have hed : H.edge.f b1 = d1 := by dsimp only [b1]; exact H.edge_involution d1
            simp only [lift, hed, h_ne01.symm, ↓reduceDIte, hb1_ne_d0, hb1_ne_d1, heb0]
            exact hcF_1
          · have hz_nmem : ¬ z ∈ [d0, b0] := by simp [hz0, hzb0]
            have hez_ne0 : H.edge.f z ≠ d0 := fun h => hzb0 (by
              have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
            have hez_ne1 : H.edge.f z ≠ d1 := fun h => hzb1 (by
              have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
            have hez_neb0 : H.edge.f z ≠ b0 := fun h => hz0 (by
              have h' := congrArg H.edge.f h; dsimp only [b0] at h'; rw [H.edge_involution, H.edge_involution] at h'; exact h')
            have he_nmem : ¬ H.edge.f z ∈ [d0, b0] := by simp [hez_ne0, hez_neb0]
            have he_sub : H'.edge.f ⟨z, hz_nmem⟩ = ⟨H.edge.f z, he_nmem⟩ :=
              Subtype.ext (deleteEdgeSubtype_edge_val H d0 ⟨z, hz_nmem⟩)
            have hep := c'.edge_proper ⟨z, hz_nmem⟩
            rw [he_sub] at hep
            simp only [lift, hez_ne0, hez_ne1, hez_neb0, ↓reduceDIte, hz0, hz1, hzb0]
            exact hep
  exact h_mc.not_colorable ⟨lift, h_lift_face, h_lift_edge⟩

/-- No face in a minimal counterexample has size 3. -/
theorem mc_faceDegree_ne_three (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts)
    (d0 : H.Dart) : Math.Hypermap.faceDegree H d0 darts.length ≠ 3 := by
  intro h_len
  let d1 := H.face.f d0
  let d2 := H.face.f d1
  have hid := perm_iter_length_getOrbit_eq_self_of_complete H.face darts h_mc.complete (Nat.le_refl _) d0
  change (getOrbit H.face darts.length d0).length = 3 at h_len
  rw [h_len] at hid
  have hd20 : H.face.f d2 = d0 := hid
  have hinj : ∀ {i j : Nat}, i < 3 → j < 3 → Perm.iter H.face i d0 = Perm.iter H.face j d0 → i = j :=
    fun hi hj heq => perm_iter_inj_of_lt_getOrbit_length H.face (h_len ▸ hi) (h_len ▸ hj) heq
  have h01 : d0 ≠ d1 := fun h => by
    have : (0 : Nat) = 1 := hinj (i := 0) (j := 1) (by decide) (by decide) h
    omega
  have h02 : d0 ≠ d2 := fun h => by
    have : (0 : Nat) = 2 := hinj (i := 0) (j := 2) (by decide) (by decide) h
    omega
  have h12 : d1 ≠ d2 := fun h => by
    have : (1 : Nat) = 2 := hinj (i := 1) (j := 2) (by decide) (by decide) h
    omega
  let b0 := H.edge.f d0
  let b1 := H.edge.f d1
  let b2 := H.edge.f d2
  have hF_01 : ¬ SameOrbit H.face b0 b1 := adjacent_outer_faces_ne H darts h_mc d0
  have hF_12 : ¬ SameOrbit H.face b1 b2 := adjacent_outer_faces_ne H darts h_mc d1
  have hF_20 : ¬ SameOrbit H.face b2 b0 := by
    have h' := adjacent_outer_faces_ne H darts h_mc d2
    rw [hd20] at h'
    exact h'
  have h_inF : ∀ d ∈ [d0, d1, d2], SameOrbit H.face d0 d := by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  have h_bi_notin_F : ∀ b ∈ [b0, b1, b2], ¬ SameOrbit H.face d0 b := by
    intro b hb hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact mc_not_sameOrbit_face_edge H darts h_mc d0 hs
    · exact mc_not_sameOrbit_face_edge H darts h_mc d1
        (sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, rfl⟩) hs)
    · exact mc_not_sameOrbit_face_edge H darts h_mc d2
        (sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨2, rfl⟩) hs)
  have hb0_ne : b0 ≠ d0 ∧ b0 ≠ d1 ∧ b0 ≠ d2 :=
    ⟨fun h => h_bi_notin_F b0 List.mem_cons_self (h ▸ ⟨0, rfl⟩),
     fun h => h_bi_notin_F b0 List.mem_cons_self (h ▸ ⟨1, rfl⟩),
     fun h => h_bi_notin_F b0 List.mem_cons_self (h ▸ ⟨2, rfl⟩)⟩
  have hb1_ne : b1 ≠ d0 ∧ b1 ≠ d1 ∧ b1 ≠ d2 :=
    ⟨fun h => h_bi_notin_F b1 (by simp) (h ▸ ⟨0, rfl⟩),
     fun h => h_bi_notin_F b1 (by simp) (h ▸ ⟨1, rfl⟩),
     fun h => h_bi_notin_F b1 (by simp) (h ▸ ⟨2, rfl⟩)⟩
  have hb2_ne : b2 ≠ d0 ∧ b2 ≠ d1 ∧ b2 ≠ d2 :=
    ⟨fun h => h_bi_notin_F b2 (by simp) (h ▸ ⟨0, rfl⟩),
     fun h => h_bi_notin_F b2 (by simp) (h ▸ ⟨1, rfl⟩),
     fun h => h_bi_notin_F b2 (by simp) (h ▸ ⟨2, rfl⟩)⟩
  let H' := H.deleteEdgeSubtype d0
  let darts' := subDarts darts [d0, b0]
  have hd1_nmem : ¬ d1 ∈ [d0, b0] := by simp [h01.symm, hb0_ne.2.1.symm]
  have hd2_nmem : ¬ d2 ∈ [d0, b0] := by simp [h02.symm, hb0_ne.2.2.symm]
  have hb1_nmem : ¬ b1 ∈ [d0, b0] := by simp [hb1_ne.1, show b1 ≠ b0 from fun h => hF_01 ⟨0, h.symm⟩]
  have hb2_nmem : ¬ b2 ∈ [d0, b0] := by simp [hb2_ne.1, show b2 ≠ b0 from fun h => hF_20 ⟨0, h⟩]
  have hnd' : darts'.Nodup := subDarts_nodup darts [d0, b0] h_mc.nodup
  have hcomp' : ∀ x : H'.Dart, x ∈ darts' := fun x =>
    (mem_subDarts darts [d0, b0] x).mpr (h_mc.complete x.val)
  have hne' : darts' ≠ [] := subDarts_nonempty darts [d0, b0] ⟨d1, h_mc.complete d1, hd1_nmem⟩
  have hlt' : darts'.length < darts.length :=
    exciseSubtype_strictly_smaller darts [d0, b0] ⟨d0, h_mc.complete d0, List.mem_cons_self⟩
  have hp' : H'.isPlanar darts'.length darts' = true :=
    deleteEdgeSubtype_isPlanar H darts h_mc.nodup h_mc.complete (Nat.le_refl _) h_mc.is_planar
      d0 hb0_ne.1 darts' hnd' hcomp' (Nat.le_refl _)
  have h_ndb0 : ¬ SameOrbit H.face d0 b0 := mc_not_sameOrbit_face_edge H darts h_mc d0
  have hb' : Math.Hypermap.isBridgeless H' darts' darts'.length := by
    rw [isBridgeless_iff_no_sameOrbit_face_edge H' darts' hcomp']
    intro z hs
    have hev : (H'.edge.f z).val = H.edge.f z.val := deleteEdgeSubtype_edge_val H d0 z
    have hsw := (deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 z (H'.edge.f z)).mp hs
    rw [hev] at hsw
    have hz_ne0 : z.val ≠ d0 := fun h => z.property (by simp [h])
    have hz_neb0 : z.val ≠ b0 := fun h => z.property (by simp [h, b0])
    have hez_ne0 : H.edge.f z.val ≠ d0 := fun h => hz_neb0 (by
      have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
    have h_or_face : ∀ w : H.Dart, SameOrbit H.face w d0 → w ≠ d0 → w = d1 ∨ w = d2 := by
      intro w hw hne
      obtain ⟨k, hk⟩ := sameOrbit_symm_of_complete H.face darts h_mc.complete hw
      have hmod : ∀ m : Nat, Perm.iter H.face m d0 = d0 ∨ Perm.iter H.face m d0 = d1 ∨ Perm.iter H.face m d0 = d2 := by
        intro m
        induction m with
        | zero => exact Or.inl rfl
        | succ m ih =>
          rcases ih with h | h | h
          · exact Or.inr (Or.inl (by change H.face.f (Perm.iter H.face m d0) = d1; rw [h]))
          · exact Or.inr (Or.inr (by change H.face.f (Perm.iter H.face m d0) = d2; rw [h]))
          · exact Or.inl (by change H.face.f (Perm.iter H.face m d0) = d0; rw [h, hd20])
      rcases hmod k with h | h | h
      · exact absurd (hk.symm.trans h) hne
      · exact Or.inl (hk.symm.trans h)
      · exact Or.inr (hk.symm.trans h)
    rcases hsw with hh | ⟨(hz_d0 | hz_b0), (he_d0 | he_b0)⟩
    · exact mc_not_sameOrbit_face_edge H darts h_mc z.val hh
    · exact mc_not_sameOrbit_face_edge H darts h_mc z.val
        (sameOrbit_trans H.face hz_d0 (sameOrbit_symm_of_complete H.face darts h_mc.complete he_d0))
    · rcases h_or_face z.val hz_d0 hz_ne0 with h | h
      · rw [h] at he_b0
        exact hF_01 (sameOrbit_symm_of_complete H.face darts h_mc.complete he_b0)
      · rw [h] at he_b0
        exact hF_20 he_b0
    · rcases h_or_face (H.edge.f z.val) he_d0 hez_ne0 with h | h
      · have hz_eq : z.val = b1 := by
          have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h'
        rw [hz_eq] at hz_b0
        exact hF_01 (sameOrbit_symm_of_complete H.face darts h_mc.complete hz_b0)
      · have hz_eq : z.val = b2 := by
          have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h'
        rw [hz_eq] at hz_b0
        exact hF_20 hz_b0
    · exact mc_not_sameOrbit_face_edge H darts h_mc z.val
        (sameOrbit_trans H.face hz_b0 (sameOrbit_symm_of_complete H.face darts h_mc.complete he_b0))
  obtain ⟨c'⟩ := h_mc.is_minimal H' darts' hnd' hcomp' hne' hlt' hp' hb'
  let col0 : Color := c'.color ⟨d1, hd1_nmem⟩
  let col1 : Color := c'.color ⟨b1, hb1_nmem⟩
  let col2 : Color := c'.color ⟨b2, hb2_nmem⟩
  obtain ⟨c_F, hcF_0, hcF_1, hcF_2⟩ := exists_fourth_color col0 col1 col2
  have h_col_F0 : ∀ {z : H.Dart} (hz : ¬ z ∈ [d0, b0]), SameOrbit H.face z b0 → c'.color ⟨z, hz⟩ = col0 := by
    intro z hz hzb
    have hsf : SameOrbit H'.face ⟨z, hz⟩ ⟨d1, hd1_nmem⟩ :=
      (deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 _ _).mpr
        (Or.inr ⟨Or.inr hzb, Or.inl ⟨2, hd20⟩⟩)
    exact sameOrbit_node_of_face_color_inv H' c' hsf
  let u0 := H.face.f b0
  have hu0_ne_b0 : u0 ≠ b0 := fun h =>
    mc_faceDegree_ne_one H darts h_mc b0 ((getOrbit_length_eq_one_iff H.face darts h_mc.complete b0).mpr h)
  have hu0_notin_F : ¬ SameOrbit H.face d0 u0 := fun h =>
    h_ndb0 (sameOrbit_symm_of_complete H.face darts h_mc.complete (sameOrbit_trans H.face (⟨1, rfl⟩) (sameOrbit_symm_of_complete H.face darts h_mc.complete h)))
  have hu0_nmem : ¬ u0 ∈ [d0, b0] := by
    simp [show u0 ≠ d0 from fun h => hu0_notin_F ⟨0, h.symm⟩, hu0_ne_b0]
  let lift : H.Dart → Color := fun z =>
    if hz0 : z = d0 then c_F
    else if hz1 : z = d1 then c_F
    else if hz2 : z = d2 then c_F
    else if hzb0 : z = b0 then col0
    else c'.color ⟨z, fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> contradiction⟩
  have h_lift_face : ∀ z : H.Dart, lift (H.face.f z) = lift z := by
    intro z
    by_cases hz0 : z = d0
    · subst hz0; simp [lift, d1, h01.symm]
    · by_cases hz1 : z = d1
      · subst hz1; simp [lift, d2, h02.symm, h12.symm, h01.symm]
      · by_cases hz2 : z = d2
        · subst hz2; simp [lift, hd20, h02.symm, h12.symm]
        · by_cases hzb0 : z = b0
          · subst hzb0
            have hu0_ne0 : u0 ≠ d0 := fun h => hu0_notin_F (h ▸ ⟨0, rfl⟩)
            have hu0_ne1 : u0 ≠ d1 := fun h => hu0_notin_F (h ▸ ⟨1, rfl⟩)
            have hu0_ne2 : u0 ≠ d2 := fun h => hu0_notin_F (h ▸ ⟨2, rfl⟩)
            have hu0_col := h_col_F0 hu0_nmem (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, rfl⟩)
            simp only [lift, u0, hu0_ne0, hu0_ne1, hu0_ne2, hu0_ne_b0, ↓reduceDIte, hb0_ne.1, hb0_ne.2.1, hb0_ne.2.2]
            exact hu0_col
          · have hz_nmem : ¬ z ∈ [d0, b0] := by simp [hz0, hzb0]
            have hfz_ne0 : H.face.f z ≠ d0 := fun h => hz2 (by
              have h' := congrArg H.face.inv (h.trans hd20.symm); rw [H.face.left_inv, H.face.left_inv] at h'; exact h')
            have hfz_ne1 : H.face.f z ≠ d1 := fun h => hz0 (by
              have h' := congrArg H.face.inv h; rw [H.face.left_inv, H.face.left_inv] at h'; exact h')
            have hfz_ne2 : H.face.f z ≠ d2 := fun h => hz1 (by
              have h' := congrArg H.face.inv h; rw [H.face.left_inv, H.face.left_inv] at h'; exact h')
            by_cases hfz_b0 : H.face.f z = b0
            · have hz_col := h_col_F0 hz_nmem ⟨1, hfz_b0⟩
              simp only [lift, hfz_b0, hb0_ne.1, hb0_ne.2.1, hb0_ne.2.2, ↓reduceDIte, hz0, hz1, hz2, hzb0]
              exact hz_col.symm
            · have hfz_nmem : ¬ H.face.f z ∈ [d0, b0] := by simp [hfz_ne0, hfz_b0]
              have hsf : SameOrbit H'.face ⟨H.face.f z, hfz_nmem⟩ ⟨z, hz_nmem⟩ :=
                (deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 _ _).mpr
                  (Or.inl (sameOrbit_symm_of_complete H.face darts h_mc.complete ⟨1, rfl⟩))
              simp only [lift, hfz_ne0, hfz_ne1, hfz_ne2, hfz_b0, ↓reduceDIte, hz0, hz1, hz2, hzb0]
              exact sameOrbit_node_of_face_color_inv H' c' hsf
  have h_lift_edge : ∀ z : H.Dart, lift (H.edge.f z) ≠ lift z := by
    intro z
    by_cases hz0 : z = d0
    · subst hz0
      simp only [lift, b0, hb0_ne.1, hb0_ne.2.1, hb0_ne.2.2, ↓reduceDIte]
      exact hcF_0.symm
    · by_cases hz1 : z = d1
      · subst hz1
        have hb1_neb0 : b1 ≠ b0 := fun h => hF_01 ⟨0, h.symm⟩
        simp only [lift, b1, hb1_ne.1, hb1_ne.2.1, hb1_ne.2.2, hb1_neb0, ↓reduceDIte, h01.symm]
        exact hcF_1.symm
      · by_cases hz2 : z = d2
        · subst hz2
          have hb2_neb0 : b2 ≠ b0 := fun h => hF_20 ⟨0, h⟩
          simp only [lift, b2, hb2_ne.1, hb2_ne.2.1, hb2_ne.2.2, hb2_neb0, ↓reduceDIte, h02.symm, h12.symm]
          exact hcF_2.symm
        · by_cases hzb0 : z = b0
          · subst hzb0
            have hed : H.edge.f b0 = d0 := by dsimp only [b0]; exact H.edge_involution d0
            simp only [lift, hed, ↓reduceDIte, hb0_ne.1, hb0_ne.2.1, hb0_ne.2.2]
            exact hcF_0
          · by_cases hzb1 : z = b1
            · subst hzb1
              have hb1_neb0 : b1 ≠ b0 := fun h => hF_01 ⟨0, h.symm⟩
              have hed : H.edge.f b1 = d1 := by dsimp only [b1]; exact H.edge_involution d1
              simp only [lift, hed, h01.symm, ↓reduceDIte, hb1_ne.1, hb1_ne.2.1, hb1_ne.2.2, hb1_neb0]
              exact hcF_1
            · by_cases hzb2 : z = b2
              · subst hzb2
                have hb2_neb0 : b2 ≠ b0 := fun h => hF_20 ⟨0, h⟩
                have hed : H.edge.f b2 = d2 := by dsimp only [b2]; exact H.edge_involution d2
                simp only [lift, hed, h02.symm, h12.symm, ↓reduceDIte, hb2_ne.1, hb2_ne.2.1, hb2_ne.2.2, hb2_neb0]
                exact hcF_2
              · have hz_nmem : ¬ z ∈ [d0, b0] := by simp [hz0, hzb0]
                have hez_ne0 : H.edge.f z ≠ d0 := fun h => hzb0 (by
                  have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
                have hez_ne1 : H.edge.f z ≠ d1 := fun h => hzb1 (by
                  have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
                have hez_ne2 : H.edge.f z ≠ d2 := fun h => hzb2 (by
                  have h' := congrArg H.edge.f h; rw [H.edge_involution] at h'; exact h')
                have hez_neb0 : H.edge.f z ≠ b0 := fun h => hz0 (by
                  have h' := congrArg H.edge.f h; dsimp only [b0] at h'; rw [H.edge_involution, H.edge_involution] at h'; exact h')
                have he_nmem : ¬ H.edge.f z ∈ [d0, b0] := by simp [hez_ne0, hez_neb0]
                have he_sub : H'.edge.f ⟨z, hz_nmem⟩ = ⟨H.edge.f z, he_nmem⟩ :=
                  Subtype.ext (deleteEdgeSubtype_edge_val H d0 ⟨z, hz_nmem⟩)
                have hep := c'.edge_proper ⟨z, hz_nmem⟩
                rw [he_sub] at hep
                simp only [lift, hez_ne0, hez_ne1, hez_ne2, hez_neb0, ↓reduceDIte, hz0, hz1, hz2, hzb0]
                exact hep
  exact h_mc.not_colorable ⟨lift, h_lift_face, h_lift_edge⟩

/-! ### Section 5b: Excluding 4-faces (`mc_faceDegree_ne_four`, `mc_faceDegree_ge_five`) -/

private theorem subDarts_length_congr {D : Type} [DecidableEq D] (l r1 r2 : List D)
    (h_iff : ∀ x ∈ l, (x ∈ r1 ↔ x ∈ r2)) :
    (subDarts l r1).length = (subDarts l r2).length := by
  induction l with
  | nil => simp [subDarts]
  | cons x xs ih =>
    have h_xs : ∀ y ∈ xs, (y ∈ r1 ↔ y ∈ r2) := fun y hy => h_iff y (List.mem_cons.mpr (.inr hy))
    have ih' := ih h_xs
    have hx := h_iff x (List.mem_cons.mpr (.inl rfl))
    by_cases h1 : x ∈ r1
    · have h2 : x ∈ r2 := hx.mp h1
      simp only [subDarts]
      rw [dif_pos h1, dif_pos h2, ih']
    · have h2 : x ∉ r2 := fun h => h1 (hx.mpr h)
      simp only [subDarts]
      rw [dif_neg h1, dif_neg h2, List.length_cons, List.length_cons, ih']

private theorem subDarts_length_of_disjoint {D : Type} [DecidableEq D] (l rem : List D)
    (h_disj : ∀ x ∈ l, x ∉ rem) :
    (subDarts l rem).length = l.length := by
  induction l with
  | nil => simp [subDarts]
  | cons x xs ih =>
    have hx : x ∉ rem := h_disj x (List.mem_cons.mpr (.inl rfl))
    have hxs : ∀ y ∈ xs, y ∉ rem := fun y hy => h_disj y (List.mem_cons.mpr (.inr hy))
    simp only [subDarts]
    rw [dif_neg hx, List.length_cons, List.length_cons, ih hxs]

private theorem subDarts_single_length {D : Type} [DecidableEq D] (l : List D) (h_nodup : l.Nodup)
    {a : D} (ha : a ∈ l) :
    (subDarts l [a]).length + 1 = l.length := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have hx_nmem : x ∉ xs := (List.nodup_cons.mp h_nodup).1
    have hxs_nd : xs.Nodup := (List.nodup_cons.mp h_nodup).2
    by_cases hxa : x = a
    · subst hxa
      have hx_rem : x ∈ [x] := List.mem_cons.mpr (.inl rfl)
      have h_disj : ∀ y ∈ xs, y ∉ [x] := fun y hy hmem => by
        rw [List.mem_singleton.mp hmem] at hy
        exact hx_nmem hy
      simp only [subDarts]
      rw [dif_pos hx_rem, subDarts_length_of_disjoint xs [x] h_disj, List.length_cons]
    · have ha_xs : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
      have hx_rem : x ∉ [a] := fun h => hxa (List.mem_singleton.mp h)
      have ih' := ih hxs_nd ha_xs
      simp only [subDarts]
      rw [dif_neg hx_rem, List.length_cons, List.length_cons]
      omega

/-- Removing two distinct elements from a `Nodup` list drops length by 2. -/
theorem subDarts_pair_length {D : Type} [DecidableEq D] (l : List D) (h_nodup : l.Nodup)
    {a b : D} (hab : a ≠ b) (ha : a ∈ l) (hb : b ∈ l) :
    (subDarts l [a, b]).length + 2 = l.length := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have hx_nmem : x ∉ xs := (List.nodup_cons.mp h_nodup).1
    have hxs_nd : xs.Nodup := (List.nodup_cons.mp h_nodup).2
    by_cases hxa : x = a
    · subst hxa
      have hx_rem : x ∈ [x, b] := List.mem_cons.mpr (.inl rfl)
      have hb_xs : b ∈ xs := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
      have h_congr : ∀ y ∈ xs, (y ∈ [x, b] ↔ y ∈ [b]) := by
        intro y hy
        constructor
        · intro h
          rcases List.mem_cons.mp h with rfl | h'
          · exact absurd hy hx_nmem
          · exact h'
        · intro h
          exact List.mem_cons.mpr (.inr h)
      have h_len := subDarts_length_congr xs [x, b] [b] h_congr
      have h_sgl := subDarts_single_length xs hxs_nd hb_xs
      simp only [subDarts]
      rw [dif_pos hx_rem, h_len, List.length_cons]
      omega
    · by_cases hxb : x = b
      · subst hxb
        have hx_rem : x ∈ [a, x] := List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))
        have ha_xs : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
        have h_congr : ∀ y ∈ xs, (y ∈ [a, x] ↔ y ∈ [a]) := by
          intro y hy
          constructor
          · intro h
            rcases List.mem_cons.mp h with rfl | h'
            · exact List.mem_singleton.mpr rfl
            · rw [List.mem_singleton.mp h'] at hy
              exact absurd hy hx_nmem
          · intro h
            exact List.mem_cons.mpr (.inl (List.mem_singleton.mp h))
        have h_len := subDarts_length_congr xs [a, x] [a] h_congr
        have h_sgl := subDarts_single_length xs hxs_nd ha_xs
        simp only [subDarts]
        rw [dif_pos hx_rem, h_len, List.length_cons]
        omega
      · have hx_nrem : x ∉ [a, b] := by
          intro h
          rcases List.mem_cons.mp h with rfl | h'
          · exact hxa rfl
          · exact hxb (List.mem_singleton.mp h')
        have ha_xs : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hxa)
        have hb_xs : b ∈ xs := (List.mem_cons.mp hb).resolve_left (Ne.symm hxb)
        have ih' := ih hxs_nd ha_xs hb_xs
        simp only [subDarts]
        rw [dif_neg hx_nrem, List.length_cons, List.length_cons]
        omega

/-- On darts whose image under `H.face.f` stays outside `[d, H.edge.f d]`, `deleteEdgeSubtype.face.f` agrees with `H.face.f`. -/
theorem deleteEdgeSubtype_face_val_of_ne (H : Hypermap) [DecidableEq H.Dart] (d : H.Dart)
    (x : (H.deleteEdgeSubtype d).Dart)
    (hx_ne_d : H.face.f x.val ≠ d) (hx_ne_ed : H.face.f x.val ≠ H.edge.f d) :
    ((H.deleteEdgeSubtype d).face.f x).val = H.face.f x.val := by
  have h1 := perm_iter_deleteEdgeSubtype_face_val H d 1 x
  change ((H.deleteEdgeSubtype d).face.f x).val =
    (bypass (bypass (swapCompRight H.face d (H.edge.f d)) d) (H.edge.f d)).f x.val at h1
  have hx_nd : x.val ≠ d := fun h => x.property (by rw [h]; exact List.mem_cons.mpr (.inl rfl))
  have hx_ned : x.val ≠ H.edge.f d := fun h =>
    x.property (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))
  have h_swap : (swapCompRight H.face d (H.edge.f d)).f x.val = H.face.f x.val := by
    simp [swapCompRight, swapFun, hx_nd, hx_ned]
  have h_byp1 : (bypass (swapCompRight H.face d (H.edge.f d)) d).f x.val = H.face.f x.val := by
    simp [bypass, hx_nd, h_swap, hx_ne_d]
  have h_byp2 : (bypass (bypass (swapCompRight H.face d (H.edge.f d)) d) (H.edge.f d)).f x.val =
      H.face.f x.val := by
    simp only [bypass, hx_nd, hx_ned, h_swap, hx_ne_d, hx_ne_ed, ↓reduceIte]
  rw [h1, h_byp2]

private theorem quad_iter4 (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4) :
    H.face.f (H.face.f (H.face.f (H.face.f d0))) = d0 := by
  have h_len := perm_iter_length_getOrbit_eq_self_of_complete H.face darts h_mc.complete
    (Nat.le_refl _) d0
  change Perm.iter H.face (Math.Hypermap.faceDegree H d0 darts.length) d0 = d0 at h_len
  rw [hd0_deg] at h_len
  simpa [Perm.iter, perm_iter_succ_left] using h_len

private theorem quad_corners_distinct (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (d0 : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4) :
    let d1 := H.face.f d0
    let d2 := H.face.f d1
    let d3 := H.face.f d2
    d0 ≠ d1 ∧ d0 ≠ d2 ∧ d0 ≠ d3 ∧ d1 ≠ d2 ∧ d1 ≠ d3 ∧ d2 ≠ d3 := by
  have hlt : ∀ k : Nat, k < 4 → k < (getOrbit H.face darts.length d0).length := fun k hk => by
    change k < Math.Hypermap.faceDegree H d0 darts.length
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hi := perm_iter_inj_of_lt_getOrbit_length H.face (hlt 0 (by omega))
      (hlt 1 (by omega)) (by simpa [Perm.iter] using h)
    omega
  · intro h
    have hi := perm_iter_inj_of_lt_getOrbit_length H.face (hlt 0 (by omega))
      (hlt 2 (by omega)) (by simpa [Perm.iter, perm_iter_succ_left] using h)
    omega
  · intro h
    have hi := perm_iter_inj_of_lt_getOrbit_length H.face (hlt 0 (by omega))
      (hlt 3 (by omega)) (by simpa [Perm.iter, perm_iter_succ_left] using h)
    omega
  · intro h
    have hi := perm_iter_inj_of_lt_getOrbit_length H.face (hlt 1 (by omega))
      (hlt 2 (by omega)) (by simpa [Perm.iter, perm_iter_succ_left] using h)
    omega
  · intro h
    have hi := perm_iter_inj_of_lt_getOrbit_length H.face (hlt 1 (by omega))
      (hlt 3 (by omega)) (by simpa [Perm.iter, perm_iter_succ_left] using h)
    omega
  · intro h
    have hi := perm_iter_inj_of_lt_getOrbit_length H.face (hlt 2 (by omega))
      (hlt 3 (by omega)) (by simpa [Perm.iter, perm_iter_succ_left] using h)
    omega

private theorem perm_iter_mod4 {D : Type} (p : Perm D) (x : D) (h4 : Perm.iter p 4 x = x) :
    ∀ k : Nat, Perm.iter p k x = Perm.iter p (k % 4) x := by
  have h_mul : ∀ q : Nat, Perm.iter p (4 * q) x = x := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [show 4 * (q + 1) = 4 + 4 * q by omega, perm_iter_add, ih, h4]
  intro k
  have hdiv : k = k % 4 + 4 * (k / 4) := by omega
  have hk_eq : Perm.iter p k x = Perm.iter p (k % 4 + 4 * (k / 4)) x :=
    congrArg (fun n => Perm.iter p n x) hdiv
  rw [hk_eq, perm_iter_add, h_mul (k / 4)]

private theorem quad_face_mem_iff (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 x : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4) :
    SameOrbit H.face x d0 ↔
      x = d0 ∨ x = H.face.f d0 ∨ x = H.face.f (H.face.f d0) ∨ x = H.face.f (H.face.f (H.face.f d0)) := by
  have h4 : Perm.iter H.face 4 d0 = d0 := by
    have h := quad_iter4 H darts h_mc d0 hd0_deg
    simpa [Perm.iter, perm_iter_succ_left] using h
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := sameOrbit_symm_of_complete H.face darts h_mc.complete hx
    rw [perm_iter_mod4 H.face d0 h4 k] at hk
    have hcase : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hcase with hm | hm | hm | hm
    · left; rw [hm] at hk; exact hk.symm
    · right; left; rw [hm] at hk; exact hk.symm
    · right; right; left; rw [hm] at hk; simpa [Perm.iter, perm_iter_succ_left] using hk.symm
    · right; right; right; rw [hm] at hk; simpa [Perm.iter, perm_iter_succ_left] using hk.symm
  · intro hx
    apply sameOrbit_symm_of_complete H.face darts h_mc.complete
    rcases hx with hx0 | hx1 | hx2 | hx3
    · rw [hx0]; exact perm_iter_sameOrbit H.face 0 d0
    · rw [hx1]; exact perm_iter_sameOrbit H.face 1 d0
    · rw [hx2]; exact perm_iter_sameOrbit H.face 2 d0
    · rw [hx3]; exact perm_iter_sameOrbit H.face 3 d0

private theorem quad_next_deg4 (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4) :
    Math.Hypermap.faceDegree H (H.face.f d0) darts.length = 4 := by
  have h_so : SameOrbit H.face d0 (H.face.f d0) := perm_iter_sameOrbit H.face 1 d0
  have h_mem : H.face.f d0 ∈ getOrbit H.face darts.length d0 :=
    (sameOrbit_iff_mem_getOrbit_of_complete H.face darts h_mc.complete (Nat.le_refl _) d0 (H.face.f d0)).mp h_so
  have h_eq := getOrbit_length_eq_of_complete_mem H.face darts h_mc.complete (Nat.le_refl _) h_mem
  change Math.Hypermap.faceDegree H (H.face.f d0) darts.length =
    Math.Hypermap.faceDegree H d0 darts.length at h_eq
  rw [hd0_deg] at h_eq
  exact h_eq

private theorem quad_outer_ne_inner (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 u v : H.Dart)
    (hu : SameOrbit H.face u d0) (hv : SameOrbit H.face v d0) :
    ¬ SameOrbit H.face u (H.edge.f v) := by
  intro h
  have h_vu := sameOrbit_trans H.face hv (sameOrbit_symm_of_complete H.face darts h_mc.complete hu)
  exact mc_not_sameOrbit_face_edge H darts h_mc v (sameOrbit_trans H.face h_vu h)

private theorem quad_node_disjoint_opp (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4) :
    let d1 := H.face.f d0
    let d2 := H.face.f d1
    let b0 := H.edge.f d0
    let b2 := H.edge.f d2
    ¬ SameOrbit H.node d0 b0 ∧ ¬ SameOrbit H.node d0 d2 ∧ ¬ SameOrbit H.node d0 b2 ∧
      ¬ SameOrbit H.node b0 d2 ∧ ¬ SameOrbit H.node b0 b2 ∧ ¬ SameOrbit H.node d2 b2 := by
  have ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ := quad_corners_distinct H darts d0 hd0_deg
  have hb0_d1 : SameOrbit H.node (H.face.f d0) (H.edge.f d0) := by
    rw [← node_face_eq_edge H d0]
    exact perm_iter_sameOrbit H.node 1 (H.face.f d0)
  have hb2_d3 : SameOrbit H.node (H.face.f (H.face.f (H.face.f d0)))
      (H.edge.f (H.face.f (H.face.f d0))) := by
    rw [← node_face_eq_edge H (H.face.f (H.face.f d0))]
    exact perm_iter_sameOrbit H.node 1 (H.face.f (H.face.f (H.face.f d0)))
  refine ⟨mc_no_self_loop H darts h_mc d0, ?_, ?_, ?_, ?_, mc_no_self_loop H darts h_mc (H.face.f (H.face.f d0))⟩
  · intro h
    exact mc_simple_face_corners H darts h_mc hd02 h (perm_iter_sameOrbit H.face 2 d0)
  · intro h
    have h_03 : SameOrbit H.node d0 (H.face.f (H.face.f (H.face.f d0))) :=
      sameOrbit_trans H.node h (sameOrbit_symm_of_complete H.node darts h_mc.complete hb2_d3)
    exact mc_simple_face_corners H darts h_mc hd03 h_03 (perm_iter_sameOrbit H.face 3 d0)
  · intro h
    have h_12 : SameOrbit H.node (H.face.f d0) (H.face.f (H.face.f d0)) := sameOrbit_trans H.node hb0_d1 h
    exact mc_simple_face_corners H darts h_mc hd12 h_12
      (sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 1 d0))
        (perm_iter_sameOrbit H.face 2 d0))
  · intro h
    have h_13 : SameOrbit H.node (H.face.f d0) (H.face.f (H.face.f (H.face.f d0))) :=
      sameOrbit_trans H.node hb0_d1 (sameOrbit_trans H.node h
        (sameOrbit_symm_of_complete H.node darts h_mc.complete hb2_d3))
    exact mc_simple_face_corners H darts h_mc hd13 h_13
      (sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 1 d0))
        (perm_iter_sameOrbit H.face 3 d0))

private theorem reachEN_H02_of_sameOrbit_face_avoid (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_comp : ∀ z : H.Dart, z ∈ darts)
    (d0 d2 : H.Dart) (hd2_nrem0 : d2 ∉ [d0, H.edge.f d0])
    (h_edge_closed : ∀ z, z ∈ [d0, H.edge.f d0, d2, H.edge.f d2] →
      H.edge.f z ∈ [d0, H.edge.f d0, d2, H.edge.f d2])
    (x y : H.Dart) (hxy : SameOrbit H.face x y)
    (h_avoid : ∀ z, SameOrbit H.face x z → z ∉ [d0, H.edge.f d0, d2, H.edge.f d2]) :
    let H1 := H.deleteEdgeSubtype d0
    let d2' : H1.Dart := ⟨d2, hd2_nrem0⟩
    let b2' := H1.edge.f d2'
    let H02 := H1.deleteEdgeSubtype d2'
    ∀ (hx : x ∉ [d0, H.edge.f d0]) (hx' : (⟨x, hx⟩ : H1.Dart) ∉ [d2', b2'])
      (hy : y ∉ [d0, H.edge.f d0]) (hy' : (⟨y, hy⟩ : H1.Dart) ∉ [d2', b2']),
      ReachEN H02.edge H02.node ⟨⟨x, hx⟩, hx'⟩ ⟨⟨y, hy⟩, hy'⟩ := by
  obtain ⟨k, hk⟩ := hxy
  intro H1 d2' b2' H02 hx hx' hy hy'
  have h_gen : ∀ (m : Nat) (w : H.Dart), Perm.iter H.face m x = w →
      ∀ (hw : w ∉ [d0, H.edge.f d0]) (hw' : (⟨w, hw⟩ : H1.Dart) ∉ [d2', b2']),
        ReachEN H02.edge H02.node ⟨⟨x, hx⟩, hx'⟩ ⟨⟨w, hw⟩, hw'⟩ := by
    intro m
    induction m with
    | zero =>
      intro w hmw hw hw'
      have hxw : x = w := hmw
      subst hxw
      exact reachEN_refl H02.edge H02.node _
    | succ m ih =>
      intro w hmw hw hw'
      let z := Perm.iter H.face m x
      have hz_so : SameOrbit H.face x z := perm_iter_sameOrbit H.face m x
      have hfz_so : SameOrbit H.face x (H.face.f z) := perm_iter_sameOrbit H.face (m + 1) x
      have hz_nrem4 := h_avoid z hz_so
      have hfz_nrem4 := h_avoid (H.face.f z) hfz_so
      have hez_nrem4 : H.edge.f z ∉ [d0, H.edge.f d0, d2, H.edge.f d2] := by
        intro hmem
        have := h_edge_closed (H.edge.f z) hmem
        rw [H.edge_involution] at this
        exact hz_nrem4 this
      have hz0 : z ∉ [d0, H.edge.f d0] := fun h => hz_nrem4 (by
        rcases List.mem_cons.mp h with h1 | h1
        · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
        · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
      have hez0 : H.edge.f z ∉ [d0, H.edge.f d0] := fun h => hez_nrem4 (by
        rcases List.mem_cons.mp h with h1 | h1
        · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
        · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
      have hz' : (⟨z, hz0⟩ : H1.Dart) ∉ [d2', b2'] := fun h => hz_nrem4 (by
        rcases List.mem_cons.mp h with h1 | h2
        · have hv : z = d2 := congrArg Subtype.val h1
          rw [hv]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))
        · have hv : z = b2'.val := congrArg Subtype.val (List.mem_singleton.mp h2)
          have hb2v : b2'.val = H.edge.f d2 := deleteEdgeSubtype_edge_val H d0 d2'
          rw [hv, hb2v]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))))))
      have hez' : (⟨H.edge.f z, hez0⟩ : H1.Dart) ∉ [d2', b2'] := fun h => hez_nrem4 (by
        rcases List.mem_cons.mp h with h1 | h2
        · have hv : H.edge.f z = d2 := congrArg Subtype.val h1
          rw [hv]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))
        · have hv : H.edge.f z = b2'.val := congrArg Subtype.val (List.mem_singleton.mp h2)
          have hb2v : b2'.val = H.edge.f d2 := deleteEdgeSubtype_edge_val H d0 d2'
          rw [hv, hb2v]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))))))
      have h_reach_z := ih z rfl hz0 hz'
      have h_step_edge : ReachEN H02.edge H02.node ⟨⟨z, hz0⟩, hz'⟩ ⟨⟨H.edge.f z, hez0⟩, hez'⟩ := by
        have hev : H02.edge.f ⟨⟨z, hz0⟩, hz'⟩ = ⟨⟨H.edge.f z, hez0⟩, hez'⟩ := by
          apply Subtype.ext; apply Subtype.ext
          rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
        rw [← hev]
        exact ⟨WalkEN.step (StepEN.e_fwd _) (WalkEN.refl _)⟩
      have h_fz_w : H.face.f z = w := by simpa [z, perm_iter_succ_left] using hmw
      have h_step_node : ReachEN H02.edge H02.node ⟨⟨H.edge.f z, hez0⟩, hez'⟩ ⟨⟨w, hw⟩, hw'⟩ := by
        apply sameOrbit_imp_reachEN H02.hypermapToTriple
        change SameOrbit H02.node ⟨⟨H.edge.f z, hez0⟩, hez'⟩ ⟨⟨w, hw⟩, hw'⟩
        rw [deleteEdgeSubtype_node_sameOrbit_iff, deleteEdgeSubtype_node_sameOrbit_iff]
        change SameOrbit H.node (H.edge.f z) w
        rw [← h_fz_w, ← node_face_eq_edge H z]
        exact sameOrbit_symm_of_complete H.node darts h_comp (perm_iter_sameOrbit H.node 1 (H.face.f z))
      exact reachEN_trans H02.edge H02.node h_reach_z (reachEN_trans H02.edge H02.node h_step_edge h_step_node)
  exact h_gen k y hk hy hy'

private theorem quad_H1_face_b2_ne_d2 (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4)
    (hb2_nrem0 : H.edge.f (H.face.f (H.face.f d0)) ∉ [d0, H.edge.f d0]) :
    ((H.deleteEdgeSubtype d0).face.f ⟨H.edge.f (H.face.f (H.face.f d0)), hb2_nrem0⟩).val ≠
      H.face.f (H.face.f d0) := by
  let d1 := H.face.f d0
  let d2 := H.face.f d1
  let b0 := H.edge.f d0
  let b2 := H.edge.f d2
  have ⟨hd01, hd02, _, hd12, _, _⟩ := quad_corners_distinct H darts d0 hd0_deg
  have hb0_ne_d0 : b0 ≠ d0 := mc_edge_ne_self H darts h_mc d0
  have h_d2_in : SameOrbit H.face d2 d0 :=
    sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 2 d0)
  have hb2_ne_d0 : b2 ≠ d0 := fun h =>
    quad_outer_ne_inner H darts h_mc d0 d0 d2 (sameOrbit_refl _ _) h_d2_in
      (by rw [← h]; exact sameOrbit_refl _ _)
  have hb2_ne_b0 : b2 ≠ b0 := fun h => hd02 (by
    have := congrArg H.edge.f h; simpa [b0, b2, H.edge_involution] using this.symm)
  have h_fb2_ne_d0 : H.face.f b2 ≠ d0 := by
    intro h
    apply quad_outer_ne_inner H darts h_mc d0 d0 d2 (sameOrbit_refl _ _) h_d2_in
    rw [← h]
    exact sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 1 b2)
  by_cases h_fb2_b0 : H.face.f b2 = b0
  · let q := swapCompRight H.face d0 b0
    let q1 := bypass q d0
    let q2 := bypass q1 b0
    have h1 := perm_iter_deleteEdgeSubtype_face_val H d0 1 ⟨b2, hb2_nrem0⟩
    change ((H.deleteEdgeSubtype d0).face.f ⟨b2, hb2_nrem0⟩).val = q2.f b2 at h1
    have hq_b2 : q.f b2 = b0 := by
      change H.face.f (swapFun d0 b0 b2) = b0
      simp [swapFun, hb2_ne_d0, hb2_ne_b0, h_fb2_b0]
    have hq_b0 : q.f b0 = d1 := by
      change H.face.f (swapFun d0 b0 b0) = d1
      simp [swapFun, hb0_ne_d0, d1]
    have hq1_b2 : q1.f b2 = b0 := by
      change (if b2 = d0 then d0 else if q.f b2 = d0 then q.f d0 else q.f b2) = b0
      rw [hq_b2]
      simp [hb2_ne_d0, hb0_ne_d0]
    have hq1_b0 : q1.f b0 = d1 := by
      change (if b0 = d0 then d0 else if q.f b0 = d0 then q.f d0 else q.f b0) = d1
      rw [if_neg hb0_ne_d0, hq_b0, if_neg (Ne.symm hd01)]
    have hq2_b2 : q2.f b2 = d1 := by
      change (if b2 = b0 then b0 else if q1.f b2 = b0 then q1.f b0 else q1.f b2) = d1
      rw [hq1_b2, hq1_b0]
      simp [hb2_ne_b0]
    rw [h1, hq2_b2]
    exact hd12
  · rw [deleteEdgeSubtype_face_val_of_ne H d0 ⟨b2, hb2_nrem0⟩ h_fb2_ne_d0 h_fb2_b0]
    intro h
    apply quad_outer_ne_inner H darts h_mc d0 d2 d2 h_d2_in h_d2_in
    have h_so : SameOrbit H.face b2 (H.face.f b2) := perm_iter_sameOrbit H.face 1 b2
    rw [h] at h_so
    exact sameOrbit_symm_of_complete H.face darts h_mc.complete h_so

/-- If opposite outer faces `F0` and `F2` of a 4-face are identical (`SameOrbit H.face b0 b2`),
then `F1` and `F3` can neither coincide nor share an edge. -/
private theorem quad_H02_disconnected_of_F0_eq_F2 (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4)
    (hF02 : SameOrbit H.face (H.edge.f d0) (H.edge.f (H.face.f (H.face.f d0))))
    (h_opp : SameOrbit H.face (H.edge.f (H.face.f d0)) (H.edge.f (H.face.f (H.face.f (H.face.f d0)))) ∨
      ∃ w : H.Dart, SameOrbit H.face w (H.edge.f (H.face.f d0)) ∧
        SameOrbit H.face (H.edge.f w) (H.edge.f (H.face.f (H.face.f (H.face.f d0))))) :
    False := by
  classical
  let d1 := H.face.f d0
  let d2 := H.face.f d1
  let d3 := H.face.f d2
  let b0 := H.edge.f d0
  let b1 := H.edge.f d1
  let b2 := H.edge.f d2
  let b3 := H.edge.f d3
  have h_fd3 : H.face.f d3 = d0 := quad_iter4 H darts h_mc d0 hd0_deg
  have ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ := quad_corners_distinct H darts d0 hd0_deg
  have h_d0_in : SameOrbit H.face d0 d0 := sameOrbit_refl _ _
  have h_d1_in : SameOrbit H.face d1 d0 := sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 1 d0)
  have h_d2_in : SameOrbit H.face d2 d0 := sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 2 d0)
  have h_d3_in : SameOrbit H.face d3 d0 := sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 3 d0)
  have hb_ne_d : ∀ u v : H.Dart, SameOrbit H.face u d0 → SameOrbit H.face v d0 → u ≠ H.edge.f v := by
    intro u v hu hv h
    exact quad_outer_ne_inner H darts h_mc d0 u v hu hv (by rw [← h]; exact sameOrbit_refl _ _)
  have hb0_ne_d0 : b0 ≠ d0 := mc_edge_ne_self H darts h_mc d0
  have hb_inj_ne : ∀ u v : H.Dart, u ≠ v → H.edge.f u ≠ H.edge.f v := fun u v huv h =>
    huv (by have := congrArg H.edge.f h; simpa [H.edge_involution] using this)
  have hd2_nrem0 : d2 ∉ [d0, b0] := by
    intro h
    rcases List.mem_cons.mp h with h1 | h1
    · exact hd02 h1.symm
    · exact hb_ne_d d2 d0 h_d2_in h_d0_in (List.mem_singleton.mp h1)
  have hb2_nrem0 : b2 ∉ [d0, b0] := by
    intro h
    rcases List.mem_cons.mp h with h1 | h1
    · exact hb_ne_d d0 d2 h_d0_in h_d2_in h1.symm
    · exact hb_inj_ne d2 d0 hd02.symm (List.mem_singleton.mp h1)
  have hb3_nrem0 : b3 ∉ [d0, b0] := by
    intro h
    rcases List.mem_cons.mp h with h1 | h1
    · exact hb_ne_d d0 d3 h_d0_in h_d3_in h1.symm
    · exact hb_inj_ne d3 d0 hd03.symm (List.mem_singleton.mp h1)
  have hd1_nrem0 : d1 ∉ [d0, b0] := by
    intro h
    rcases List.mem_cons.mp h with h1 | h1
    · exact hd01 h1.symm
    · exact hb_ne_d d1 d0 h_d1_in h_d0_in (List.mem_singleton.mp h1)
  have hd3_nrem0 : d3 ∉ [d0, b0] := by
    intro h
    rcases List.mem_cons.mp h with h1 | h1
    · exact hd03 h1.symm
    · exact hb_ne_d d3 d0 h_d3_in h_d0_in (List.mem_singleton.mp h1)
  have hb1_nrem0 : b1 ∉ [d0, b0] := by
    intro h
    rcases List.mem_cons.mp h with h1 | h1
    · exact hb_ne_d d0 d1 h_d0_in h_d1_in h1.symm
    · exact hb_inj_ne d1 d0 hd01.symm (List.mem_singleton.mp h1)
  let H1 := H.deleteEdgeSubtype d0
  let d2' : H1.Dart := ⟨d2, hd2_nrem0⟩
  let b2' := H1.edge.f d2'
  have hb2'_val : b2'.val = b2 := deleteEdgeSubtype_edge_val H d0 d2'
  have hd2'_ne_b2' : d2' ≠ b2' := fun h =>
    hb_ne_d d2 d2 h_d2_in h_d2_in (by have := congrArg Subtype.val h; rwa [hb2'_val] at this)
  let d1' : H1.Dart := ⟨d1, hd1_nrem0⟩
  let d3' : H1.Dart := ⟨d3, hd3_nrem0⟩
  let b1' : H1.Dart := ⟨b1, hb1_nrem0⟩
  let b3' : H1.Dart := ⟨b3, hb3_nrem0⟩
  have h_nrem2 : ∀ z : H.Dart, (hz : z ∉ [d0, b0]) → z ≠ d2 → z ≠ b2 → (⟨z, hz⟩ : H1.Dart) ∉ [d2', b2'] := by
    intro z hz hzd hzb hmem
    rcases List.mem_cons.mp hmem with h1 | h1
    · exact hzd (congrArg Subtype.val h1)
    · have hv := congrArg Subtype.val (List.mem_singleton.mp h1)
      rw [hb2'_val] at hv
      exact hzb hv
  have hd1'_nrem : d1' ∉ [d2', b2'] := h_nrem2 d1 hd1_nrem0 hd12 (hb_ne_d d1 d2 h_d1_in h_d2_in)
  have hd3'_nrem : d3' ∉ [d2', b2'] := h_nrem2 d3 hd3_nrem0 hd23.symm (hb_ne_d d3 d2 h_d3_in h_d2_in)
  have hb1'_nrem : b1' ∉ [d2', b2'] := h_nrem2 b1 hb1_nrem0 (hb_ne_d d2 d1 h_d2_in h_d1_in).symm (hb_inj_ne d1 d2 hd12)
  have hb3'_nrem : b3' ∉ [d2', b2'] := h_nrem2 b3 hb3_nrem0 (hb_ne_d d2 d3 h_d2_in h_d3_in).symm (hb_inj_ne d3 d2 hd23.symm)
  let H02 := H1.deleteEdgeSubtype d2'
  let d1'' : H02.Dart := ⟨d1', hd1'_nrem⟩
  let d3'' : H02.Dart := ⟨d3', hd3'_nrem⟩
  let b1'' : H02.Dart := ⟨b1', hb1'_nrem⟩
  let b3'' : H02.Dart := ⟨b3', hb3'_nrem⟩
  let darts1 := subDarts darts [d0, b0]
  let darts2 := subDarts darts1 [d2', b2']
  have h_nd1 : darts1.Nodup := subDarts_nodup darts [d0, b0] h_mc.nodup
  have h_comp1 : ∀ x : H1.Dart, x ∈ darts1 := fun x => (mem_subDarts darts [d0, b0] x).mpr (h_mc.complete x.val)
  have h_len1 : darts1.length + 2 = darts.length :=
    subDarts_pair_length darts h_mc.nodup hb0_ne_d0.symm (h_mc.complete d0) (h_mc.complete b0)
  have h_nd2 : darts2.Nodup := subDarts_nodup darts1 [d2', b2'] h_nd1
  have h_comp2 : ∀ x : H02.Dart, x ∈ darts2 := fun x => (mem_subDarts darts1 [d2', b2'] x).mpr (h_comp1 x.val)
  have h_len2 : darts2.length + 2 = darts1.length :=
    subDarts_pair_length darts1 h_nd1 hd2'_ne_b2' (h_comp1 d2') (h_comp1 b2')
  have h_ne2 : darts2 ≠ [] := fun h => by
    have := h_comp2 d1''
    rw [h] at this
    cases this
  have h_planar1 : H1.isPlanar darts1.length darts1 = true :=
    deleteEdgeSubtype_isPlanar H darts h_mc.nodup h_mc.complete (Nat.le_refl _) h_mc.is_planar
      d0 hb0_ne_d0 darts1 h_nd1 h_comp1 (Nat.le_refl _)
  have hd2'_e : H1.edge.f d2' ≠ d2' := hd2'_ne_b2'.symm
  have h_planar2 : H02.isPlanar darts2.length darts2 = true :=
    deleteEdgeSubtype_isPlanar H1 darts1 h_nd1 h_comp1 (Nat.le_refl _) h_planar1
      d2' hd2'_e darts2 h_nd2 h_comp2 (Nat.le_refl _)
  -- Node counts: `H02.numNodes = H1.numNodes = H.numNodes`
  have h_V1 : H1.numNodes darts1.length darts1 = H.numNodes darts.length darts := by
    change countOrbits H1.node darts1.length darts1 = countOrbits H.node darts.length darts
    rw [countOrbits_eq_countRelClasses H1.node darts1 h_comp1 (Nat.le_refl _) darts1,
      countOrbits_eq_countRelClasses H.node darts h_mc.complete (Nat.le_refl _) darts]
    apply countRelClasses_subDarts_eq_of_cover (SameOrbit H.node)
      (fun x => sameOrbit_refl H.node x)
      (fun {x y} h => sameOrbit_symm_of_complete H.node darts h_mc.complete h)
      (fun {x y z} h1 h2 => sameOrbit_trans H.node h1 h2)
      [d0, b0] (SameOrbit H1.node)
      (fun u w => deleteEdgeSubtype_node_sameOrbit_iff H d0 u w)
      darts.length darts (Nat.le_refl _)
    intro x hx
    by_cases hxd : x = d0
    · refine ⟨b3, h_mc.complete b3, hb3_nrem0, ?_⟩
      change SameOrbit H.node x (H.edge.f d3)
      rw [hxd, ← node_face_eq_edge H d3, h_fd3]
      exact perm_iter_sameOrbit H.node 1 d0
    · by_cases hxb : x = b0
      · refine ⟨d1, h_mc.complete d1, hd1_nrem0, ?_⟩
        change SameOrbit H.node x d1
        rw [hxb]
        change SameOrbit H.node (H.edge.f d0) d1
        rw [← node_face_eq_edge H d0]
        exact sameOrbit_symm_of_complete H.node darts h_mc.complete (perm_iter_sameOrbit H.node 1 d1)
      · refine ⟨x, hx, ?_, sameOrbit_refl H.node x⟩
        intro hmem
        rcases List.mem_cons.mp hmem with h1 | h1
        · exact hxd h1
        · exact hxb (List.mem_singleton.mp h1)
  have h_V2 : H02.numNodes darts2.length darts2 = H1.numNodes darts1.length darts1 := by
    change countOrbits H02.node darts2.length darts2 = countOrbits H1.node darts1.length darts1
    rw [countOrbits_eq_countRelClasses H02.node darts2 h_comp2 (Nat.le_refl _) darts2,
      countOrbits_eq_countRelClasses H1.node darts1 h_comp1 (Nat.le_refl _) darts1]
    apply countRelClasses_subDarts_eq_of_cover (SameOrbit H1.node)
      (fun x => sameOrbit_refl H1.node x)
      (fun {x y} h => sameOrbit_symm_of_complete H1.node darts1 h_comp1 h)
      (fun {x y z} h1 h2 => sameOrbit_trans H1.node h1 h2)
      [d2', b2'] (SameOrbit H02.node)
      (fun u w => deleteEdgeSubtype_node_sameOrbit_iff H1 d2' u w)
      darts1.length darts1 (Nat.le_refl _)
    intro x hx
    by_cases hxd : x = d2'
    · refine ⟨b1', h_comp1 b1', hb1'_nrem, ?_⟩
      rw [hxd]
      rw [deleteEdgeSubtype_node_sameOrbit_iff H d0 d2' b1']
      change SameOrbit H.node d2 (H.edge.f d1)
      rw [← node_face_eq_edge H d1]
      exact perm_iter_sameOrbit H.node 1 d2
    · by_cases hxb : x = b2'
      · refine ⟨d3', h_comp1 d3', hd3'_nrem, ?_⟩
        rw [hxb, deleteEdgeSubtype_node_sameOrbit_iff H d0 b2' d3']
        change SameOrbit H.node b2'.val d3
        rw [hb2'_val]
        change SameOrbit H.node (H.edge.f d2) d3
        rw [← node_face_eq_edge H d2]
        exact sameOrbit_symm_of_complete H.node darts h_mc.complete (perm_iter_sameOrbit H.node 1 d3)
      · refine ⟨x, hx, ?_, sameOrbit_refl H1.node x⟩
        intro hmem
        rcases List.mem_cons.mp hmem with h1 | h1
        · exact hxd h1
        · exact hxb (List.mem_singleton.mp h1)
  -- Edge counts: `H02.numEdges + 2 = H.numEdges`
  have h_E0 : darts.length = 2 * H.numEdges darts.length darts := by
    have hfree := ((eulerChar_le_two_mul_numComponents H darts h_mc.nodup h_mc.complete (Nat.le_refl _)).2.mp
      h_mc.is_planar).2
    exact (length_le_two_mul_countOrbits_of_involution H.edge H.edge_involution darts h_mc.nodup
      h_mc.complete (Nat.le_refl _)).2.mpr hfree
  have h_E2 : darts2.length = 2 * H02.numEdges darts2.length darts2 := by
    have hfree := ((eulerChar_le_two_mul_numComponents H02 darts2 h_nd2 h_comp2 (Nat.le_refl _)).2.mp
      h_planar2).2
    exact (length_le_two_mul_countOrbits_of_involution H02.edge H02.edge_involution darts2 h_nd2
      h_comp2 (Nat.le_refl _)).2.mpr hfree
  -- Face counts: `H1.numFaces + 1 = H.numFaces` and `H02.numFaces = H1.numFaces + 1`
  have h_ndb0 : ¬ SameOrbit H.face d0 b0 := mc_not_sameOrbit_face_edge H darts h_mc d0
  have h_F1 : H1.numFaces darts1.length darts1 + 1 = H.numFaces darts.length darts := by
    change countOrbits H1.face darts1.length darts1 + 1 = countOrbits H.face darts.length darts
    have hb0_nmem_orb : b0 ∉ getOrbit H.face darts.length d0 := by
      rw [← sameOrbit_iff_mem_getOrbit_of_complete H.face darts h_mc.complete (Nat.le_refl _) d0 b0]
      exact h_ndb0
    have h_swap := countOrbits_swapCompRight_diff H.face darts h_mc.complete (Nat.le_refl _) hb0_nmem_orb
    have h_rel : countOrbits H1.face darts1.length darts1 =
        countOrbits (swapCompRight H.face d0 b0) darts.length darts := by
      rw [countOrbits_eq_countRelClasses H1.face darts1 h_comp1 (Nat.le_refl _) darts1,
        countOrbits_eq_countRelClasses (swapCompRight H.face d0 b0) darts h_mc.complete (Nat.le_refl _) darts]
      apply countRelClasses_subDarts_eq_of_cover (SameOrbit (swapCompRight H.face d0 b0))
        (fun x => sameOrbit_refl _ x)
        (fun {x y} h => sameOrbit_symm_of_complete _ darts h_mc.complete h)
        (fun {x y z} h1 h2 => sameOrbit_trans _ h1 h2)
        [d0, b0] (SameOrbit H1.face)
        (fun u w => deleteEdgeSubtype_face_sameOrbit_iff_swapCompRight H d0 u w)
        darts.length darts (Nat.le_refl _)
      intro x hx
      have h_fb0_ne_b0 : H.face.f b0 ≠ b0 := by
        intro heq
        exact mc_faceDegree_ne_one H darts h_mc b0
          ((getOrbit_length_eq_one_iff H.face darts h_mc.complete b0).mpr heq)
      have h_fb0_ne_d0 : H.face.f b0 ≠ d0 := by
        intro heq
        apply h_ndb0
        apply sameOrbit_symm_of_complete H.face darts h_mc.complete
        rw [← heq]
        exact perm_iter_sameOrbit H.face 1 b0
      by_cases hxd : x = d0
      · refine ⟨H.face.f b0, h_mc.complete _, ?_, ?_⟩
        · intro hmem
          rcases List.mem_cons.mp hmem with h1 | h1
          · exact h_fb0_ne_d0 h1
          · exact h_fb0_ne_b0 (List.mem_singleton.mp h1)
        · rw [hxd]
          have hstep : (swapCompRight H.face d0 b0).f d0 = H.face.f b0 := by
            simp [swapCompRight, swapFun]
          rw [← hstep]
          exact perm_iter_sameOrbit _ 1 d0
      · by_cases hxb : x = b0
        · refine ⟨d1, h_mc.complete d1, hd1_nrem0, ?_⟩
          rw [hxb]
          have hstep : (swapCompRight H.face d0 b0).f b0 = d1 := by
            simp [swapCompRight, swapFun, hb0_ne_d0, d1]
          rw [← hstep]
          exact perm_iter_sameOrbit _ 1 b0
        · refine ⟨x, hx, ?_, sameOrbit_refl _ x⟩
          intro hmem
          rcases List.mem_cons.mp hmem with h1 | h1
          · exact hxd h1
          · exact hxb (List.mem_singleton.mp h1)
    omega
  have h_d2b2_1 : SameOrbit H1.face d2' b2' := by
    rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 d2' b2']
    right
    constructor
    · left; exact h_d2_in
    · right
      change SameOrbit H.face b2'.val b0
      rw [hb2'_val]
      exact sameOrbit_symm_of_complete H.face darts h_mc.complete hF02
  have h_F2 : H02.numFaces darts2.length darts2 = H1.numFaces darts1.length darts1 + 1 := by
    change countOrbits H02.face darts2.length darts2 = countOrbits H1.face darts1.length darts1 + 1
    have hb2_mem_orb : b2' ∈ getOrbit H1.face darts1.length d2' :=
      (sameOrbit_iff_mem_getOrbit_of_complete H1.face darts1 h_comp1 (Nat.le_refl _) d2' b2').mp h_d2b2_1
    have h_swap := countOrbits_swapCompRight_same H1.face darts1 h_comp1 (Nat.le_refl _) hd2'_ne_b2' hb2_mem_orb
    have h_rel : countOrbits H02.face darts2.length darts2 =
        countOrbits (swapCompRight H1.face d2' b2') darts1.length darts1 := by
      rw [countOrbits_eq_countRelClasses H02.face darts2 h_comp2 (Nat.le_refl _) darts2,
        countOrbits_eq_countRelClasses (swapCompRight H1.face d2' b2') darts1 h_comp1 (Nat.le_refl _) darts1]
      apply countRelClasses_subDarts_eq_of_cover (SameOrbit (swapCompRight H1.face d2' b2'))
        (fun x => sameOrbit_refl _ x)
        (fun {x y} h => sameOrbit_symm_of_complete _ darts1 h_comp1 h)
        (fun {x y z} h1 h2 => sameOrbit_trans _ h1 h2)
        [d2', b2'] (SameOrbit H02.face)
        (fun u w => deleteEdgeSubtype_face_sameOrbit_iff_swapCompRight H1 d2' u w)
        darts1.length darts1 (Nat.le_refl _)
      intro x hx
      by_cases hxb : x = b2'
      · have h_fd2_val : (H1.face.f d2').val = d3 :=
          deleteEdgeSubtype_face_val_of_ne H d0 d2' (by change d3 ≠ d0; exact hd03.symm)
            (hb_ne_d d3 d0 h_d3_in h_d0_in)
        have h_fd2_eq : H1.face.f d2' = d3' := Subtype.ext h_fd2_val
        refine ⟨d3', h_comp1 d3', hd3'_nrem, ?_⟩
        rw [hxb]
        have hstep : (swapCompRight H1.face d2' b2').f b2' = d3' := by
          simp [swapCompRight, swapFun, hd2'_ne_b2'.symm, h_fd2_eq]
        rw [← hstep]
        exact perm_iter_sameOrbit _ 1 b2'
      · by_cases hxd : x = d2'
        · have h_fb2_ne_b2 : H1.face.f b2' ≠ b2' := by
            intro hfix
            have h_all : ∀ k : Nat, Perm.iter H1.face k b2' = b2' := by
              intro k
              induction k with
              | zero => rfl
              | succ k ihk => rw [perm_iter_succ_left, ihk, hfix]
            obtain ⟨k, hk⟩ := sameOrbit_symm_of_complete H1.face darts1 h_comp1 h_d2b2_1
            rw [h_all k] at hk
            exact hd2'_ne_b2' hk.symm
          have h_fb2_ne_d2 : H1.face.f b2' ≠ d2' := by
            intro h
            have hv := congrArg Subtype.val h
            have hb2'_coe : b2' = ⟨b2, hb2_nrem0⟩ := Subtype.ext hb2'_val
            rw [hb2'_coe] at hv
            exact quad_H1_face_b2_ne_d2 H darts h_mc d0 hd0_deg hb2_nrem0 hv
          refine ⟨H1.face.f b2', h_comp1 _, ?_, ?_⟩
          · intro hmem
            rcases List.mem_cons.mp hmem with h1 | h1
            · exact h_fb2_ne_d2 h1
            · exact h_fb2_ne_b2 (List.mem_singleton.mp h1)
          · rw [hxd]
            have hstep : (swapCompRight H1.face d2' b2').f d2' = H1.face.f b2' := by
              simp [swapCompRight, swapFun]
            rw [← hstep]
            exact perm_iter_sameOrbit _ 1 d2'
        · refine ⟨x, hx, ?_, sameOrbit_refl _ x⟩
          intro hmem
          rcases List.mem_cons.mp hmem with h1 | h1
          · exact hxd h1
          · exact hxb (List.mem_singleton.mp h1)
    omega
  -- Euler formula yields `H02.numComponents = 2`
  have h_C2 : H02.numComponents darts2.length darts2 = 2 := by
    have hp0 := h_mc.is_planar
    dsimp only [Hypermap.isPlanar] at hp0
    have heq0 := beq_iff_eq.mp hp0
    have h_C0 : H.countComponents darts.length darts = 1 := mc_numComponents_eq_one H darts h_mc
    have hp2 := h_planar2
    dsimp only [Hypermap.isPlanar] at hp2
    have heq2 := beq_iff_eq.mp hp2
    dsimp only [Hypermap.numNodes] at h_V1 h_V2
    dsimp only [Hypermap.numEdges] at h_E0 h_E2
    dsimp only [Hypermap.numFaces] at h_F1 h_F2
    have hV : countOrbits H02.node darts2.length darts2 = countOrbits H.node darts.length darts :=
      h_V2.trans h_V1
    have hE : countOrbits H02.edge darts2.length darts2 + 2 = countOrbits H.edge darts.length darts := by
      omega
    have hF : countOrbits H02.face darts2.length darts2 = countOrbits H.face darts.length darts := by
      omega
    change H02.countComponents darts2.length darts2 = 2
    omega
  -- Lift `F1` / `F3` reachability from `h_opp` into `H02`: `ReachEN H02.edge H02.node b1'' d3''`
  have h_edge_closed : ∀ z, z ∈ [d0, b0, d2, b2] → H.edge.f z ∈ [d0, b0, d2, b2] := by
    intro z hz
    rcases List.mem_cons.mp hz with h0 | h1
    · rw [h0]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))
    · rcases List.mem_cons.mp h1 with h1' | h2
      · rw [h1', show b0 = H.edge.f d0 from rfl, H.edge_involution]
        exact List.mem_cons.mpr (.inl rfl)
      · rcases List.mem_cons.mp h2 with h2' | h3
        · rw [h2']
          exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))
        · rw [List.mem_singleton.mp h3, show b2 = H.edge.f d2 from rfl, H.edge_involution]
          exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))
  have h_F1_avoid : ∀ z, SameOrbit H.face b1 z → z ∉ [d0, b0, d2, b2] := by
    intro z hz hmem
    have hz_b1 := sameOrbit_symm_of_complete H.face darts h_mc.complete hz
    rcases List.mem_cons.mp hmem with h0 | h1
    · rw [h0] at hz_b1
      exact quad_outer_ne_inner H darts h_mc d0 d0 d1 h_d0_in h_d1_in hz_b1
    · rcases List.mem_cons.mp h1 with h1' | h2
      · rw [h1'] at hz_b1
        exact adjacent_outer_faces_ne H darts h_mc d0 hz_b1
      · rcases List.mem_cons.mp h2 with h2' | h3
        · rw [h2'] at hz_b1
          exact quad_outer_ne_inner H darts h_mc d0 d2 d1 h_d2_in h_d1_in hz_b1
        · rw [List.mem_singleton.mp h3] at hz_b1
          exact adjacent_outer_faces_ne H darts h_mc d1 (sameOrbit_symm_of_complete H.face darts h_mc.complete hz_b1)
  have h_F3_avoid : ∀ z, SameOrbit H.face b3 z → z ∉ [d0, b0, d2, b2] := by
    intro z hz hmem
    have hz_b3 := sameOrbit_symm_of_complete H.face darts h_mc.complete hz
    rcases List.mem_cons.mp hmem with h0 | h1
    · rw [h0] at hz_b3
      exact quad_outer_ne_inner H darts h_mc d0 d0 d3 h_d0_in h_d3_in hz_b3
    · rcases List.mem_cons.mp h1 with h1' | h2
      · rw [h1'] at hz_b3
        have adj := adjacent_outer_faces_ne H darts h_mc d3
        rw [h_fd3] at adj
        exact adj (sameOrbit_symm_of_complete H.face darts h_mc.complete hz_b3)
      · rcases List.mem_cons.mp h2 with h2' | h3
        · rw [h2'] at hz_b3
          exact quad_outer_ne_inner H darts h_mc d0 d2 d3 h_d2_in h_d3_in hz_b3
        · rw [List.mem_singleton.mp h3] at hz_b3
          exact adjacent_outer_faces_ne H darts h_mc d2 hz_b3
  have h_reach_b1_b3 : ReachEN H02.edge H02.node b1'' b3'' := by
    rcases h_opp with h13 | ⟨w, hw1, hw3⟩
    · exact reachEN_H02_of_sameOrbit_face_avoid H darts h_mc.complete d0 d2 hd2_nrem0
        h_edge_closed b1 b3 h13 h_F1_avoid hb1_nrem0 hb1'_nrem hb3_nrem0 hb3'_nrem
    · have hw_nrem4 : w ∉ [d0, b0, d2, b2] :=
        h_F1_avoid w (sameOrbit_symm_of_complete H.face darts h_mc.complete hw1)
      have hew_nrem4 : H.edge.f w ∉ [d0, b0, d2, b2] :=
        h_F3_avoid (H.edge.f w) (sameOrbit_symm_of_complete H.face darts h_mc.complete hw3)
      have hw0 : w ∉ [d0, b0] := fun h => hw_nrem4 (by
        rcases List.mem_cons.mp h with h1 | h1
        · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
        · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
      have hew0 : H.edge.f w ∉ [d0, b0] := fun h => hew_nrem4 (by
        rcases List.mem_cons.mp h with h1 | h1
        · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
        · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
      have hw' : (⟨w, hw0⟩ : H1.Dart) ∉ [d2', b2'] := h_nrem2 w hw0
        (fun h => hw_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))))
        (fun h => hw_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))))
      have hew' : (⟨H.edge.f w, hew0⟩ : H1.Dart) ∉ [d2', b2'] := h_nrem2 (H.edge.f w) hew0
        (fun h => hew_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))))
        (fun h => hew_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))))
      have h_b1_w := reachEN_H02_of_sameOrbit_face_avoid H darts h_mc.complete d0 d2 hd2_nrem0
        h_edge_closed b1 w (sameOrbit_symm_of_complete H.face darts h_mc.complete hw1)
        h_F1_avoid hb1_nrem0 hb1'_nrem hw0 hw'
      have h_w_ew : ReachEN H02.edge H02.node ⟨⟨w, hw0⟩, hw'⟩ ⟨⟨H.edge.f w, hew0⟩, hew'⟩ := by
        have hev : H02.edge.f ⟨⟨w, hw0⟩, hw'⟩ = ⟨⟨H.edge.f w, hew0⟩, hew'⟩ := by
          apply Subtype.ext; apply Subtype.ext
          rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
        rw [← hev]
        exact ⟨WalkEN.step (StepEN.e_fwd _) (WalkEN.refl _)⟩
      have h_ew_b3 := reachEN_H02_of_sameOrbit_face_avoid H darts h_mc.complete d0 d2 hd2_nrem0
        h_edge_closed (H.edge.f w) b3 hw3
        (fun z hz => h_F3_avoid z (sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete hw3) hz))
        hew0 hew' hb3_nrem0 hb3'_nrem
      exact reachEN_trans H02.edge H02.node h_b1_w (reachEN_trans H02.edge H02.node h_w_ew h_ew_b3)
  -- `d1'' --edge--> b1''` and `b3'' --edge--> d3''` give full connectivity of `H02`
  have h_d1_b1 : ReachEN H02.edge H02.node d1'' b1'' := by
    have hev : H02.edge.f d1'' = b1'' := by
      apply Subtype.ext; apply Subtype.ext
      rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
    rw [← hev]
    exact ⟨WalkEN.step (StepEN.e_fwd d1'') (WalkEN.refl _)⟩
  have h_b3_d3 : ReachEN H02.edge H02.node b3'' d3'' := by
    have hev : H02.edge.f b3'' = d3'' := by
      apply Subtype.ext; apply Subtype.ext
      rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
      exact H.edge_involution d3
    rw [← hev]
    exact ⟨WalkEN.step (StepEN.e_fwd b3'') (WalkEN.refl _)⟩
  have h_b1_d3 : ReachEN H02.edge H02.node b1'' d3'' := reachEN_trans H02.edge H02.node h_reach_b1_b3 h_b3_d3
  -- Define `v_rep : H.Dart → H02.Dart` preserving vertices and merging removed edges into `{d1'', b1'', d3'', b3''}`
  let v_rep (x : H.Dart) : H02.Dart :=
    if hx0 : x ∈ [d0, b0] then
      if x = d0 then b3'' else d1''
    else
      if hx2 : (⟨x, hx0⟩ : H1.Dart) ∈ [d2', b2'] then
        if (⟨x, hx0⟩ : H1.Dart) = d2' then b1'' else d3''
      else ⟨⟨x, hx0⟩, hx2⟩
  have hb3_val : b3''.val.val = b3 := rfl
  have hd1_val : d1''.val.val = d1 := rfl
  have hb1_val : b1''.val.val = b1 := rfl
  have hd3_val : d3''.val.val = d3 := rfl
  have h_vrep_node : ∀ x : H.Dart, SameOrbit H.node x (v_rep x).val.val := by
    intro x
    dsimp only [v_rep]
    split
    · case isTrue hx0 =>
      split
      · case isTrue hxd =>
        rw [hb3_val]
        change SameOrbit H.node x (H.edge.f d3)
        rw [hxd, ← node_face_eq_edge H d3, h_fd3]
        exact perm_iter_sameOrbit H.node 1 d0
      · case isFalse hxd =>
        have hxb : x = b0 := List.mem_singleton.mp ((List.mem_cons.mp hx0).resolve_left hxd)
        rw [hd1_val]
        change SameOrbit H.node x d1
        rw [hxb]
        change SameOrbit H.node (H.edge.f d0) d1
        rw [← node_face_eq_edge H d0]
        exact sameOrbit_symm_of_complete H.node darts h_mc.complete (perm_iter_sameOrbit H.node 1 d1)
    · case isFalse hx0 =>
      split
      · case isTrue hx2 =>
        split
        · case isTrue hxd2 =>
          have hxv : x = d2 := congrArg Subtype.val hxd2
          rw [hb1_val]
          change SameOrbit H.node x (H.edge.f d1)
          rw [hxv, ← node_face_eq_edge H d1]
          exact perm_iter_sameOrbit H.node 1 d2
        · case isFalse hxd2 =>
          have hmem := (List.mem_cons.mp hx2).resolve_left hxd2
          have hxv : x = b2 := by
            have hv := congrArg Subtype.val (List.mem_singleton.mp hmem)
            simpa [hb2'_val] using hv
          rw [hd3_val]
          change SameOrbit H.node x d3
          rw [hxv]
          change SameOrbit H.node (H.edge.f d2) d3
          rw [← node_face_eq_edge H d2]
          exact sameOrbit_symm_of_complete H.node darts h_mc.complete (perm_iter_sameOrbit H.node 1 d3)
      · case isFalse hx2 =>
        exact sameOrbit_refl H.node x
  have h_vrep_surv : ∀ z : H02.Dart, v_rep z.val.val = z := by
    intro z
    dsimp only [v_rep]
    rw [dif_neg z.val.property]
    have hzx : (⟨z.val.val, z.val.property⟩ : H1.Dart) = z.val := rfl
    rw [dif_neg (by simpa [hzx] using z.property)]
  have h_four : ∀ a b : H02.Dart,
      (a = b3'' ∨ a = d1'' ∨ a = b1'' ∨ a = d3'') →
      (b = b3'' ∨ b = d1'' ∨ b = b1'' ∨ b = d3'') →
      ReachEN H02.edge H02.node a b := by
    have h_to_b1 : ∀ c : H02.Dart, (c = b3'' ∨ c = d1'' ∨ c = b1'' ∨ c = d3'') →
        ReachEN H02.edge H02.node c b1'' := by
      intro c hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact reachEN_symm H02.edge H02.node h_reach_b1_b3
      · exact h_d1_b1
      · exact reachEN_refl _ _ _
      · exact reachEN_symm H02.edge H02.node h_b1_d3
    intro a b ha hb
    exact reachEN_trans H02.edge H02.node (h_to_b1 a ha) (reachEN_symm H02.edge H02.node (h_to_b1 b hb))
  have h_efwd_lift : ∀ u : H.Dart,
      ReachEN H02.edge H02.node (v_rep u) (v_rep (H.edge.f u)) := by
    intro u
    by_cases hu4 : u ∈ [d0, b0, d2, b2]
    · have heu4 : H.edge.f u ∈ [d0, b0, d2, b2] := h_edge_closed u hu4
      have h_in4 : ∀ x, x ∈ [d0, b0, d2, b2] → v_rep x = b3'' ∨ v_rep x = d1'' ∨ v_rep x = b1'' ∨ v_rep x = d3'' := by
        intro x hx4
        dsimp only [v_rep]
        by_cases hx0 : x ∈ [d0, b0]
        · rw [dif_pos hx0]
          split <;> simp
        · rw [dif_neg hx0]
          have hx2 : (⟨x, hx0⟩ : H1.Dart) ∈ [d2', b2'] := by
            rcases List.mem_cons.mp hx4 with h0 | h1
            · exact absurd (by rw [h0]; exact List.mem_cons.mpr (.inl rfl)) hx0
            · rcases List.mem_cons.mp h1 with h1' | h2
              · exact absurd (by rw [h1']; exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))) hx0
              · rcases List.mem_cons.mp h2 with h2' | h3
                · exact List.mem_cons.mpr (.inl (Subtype.ext h2'))
                · exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr (Subtype.ext (by
                    rw [hb2'_val]; exact List.mem_singleton.mp h3))))
          rw [dif_pos hx2]
          split <;> simp
      exact h_four (v_rep u) (v_rep (H.edge.f u)) (h_in4 u hu4) (h_in4 (H.edge.f u) heu4)
    · have heu4 : H.edge.f u ∉ [d0, b0, d2, b2] := fun h => hu4 (by
        have := h_edge_closed _ h; rwa [H.edge_involution] at this)
      have h_surv : ∀ x, x ∉ [d0, b0, d2, b2] → ∃ p1 p2, v_rep x = ⟨⟨x, p1⟩, p2⟩ := by
        intro x hx4
        have hx0 : x ∉ [d0, b0] := fun h => hx4 (by
          rcases List.mem_cons.mp h with h1 | h1
          · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
          · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
        have hx2 : (⟨x, hx0⟩ : H1.Dart) ∉ [d2', b2'] := h_nrem2 x hx0
          (fun h => hx4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))))
          (fun h => hx4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))))
        refine ⟨hx0, hx2, ?_⟩
        dsimp only [v_rep]
        rw [dif_neg hx0, dif_neg hx2]
      obtain ⟨pu0, pu2, hvu⟩ := h_surv u hu4
      obtain ⟨peu0, peu2, hveu⟩ := h_surv (H.edge.f u) heu4
      rw [hvu, hveu]
      have hev : H02.edge.f ⟨⟨u, pu0⟩, pu2⟩ = ⟨⟨H.edge.f u, peu0⟩, peu2⟩ := by
        apply Subtype.ext; apply Subtype.ext
        rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
      rw [← hev]
      exact ⟨WalkEN.step (StepEN.e_fwd _) (WalkEN.refl _)⟩
  have h_step_lift : ∀ {u v : H.Dart}, StepEN H.edge H.node u v →
      ReachEN H02.edge H02.node (v_rep u) (v_rep v) := by
    intro u v hs
    cases hs with
    | n_fwd =>
      apply sameOrbit_imp_reachEN H02.hypermapToTriple
      change SameOrbit H02.node (v_rep u) (v_rep (H.node.f u))
      rw [deleteEdgeSubtype_node_sameOrbit_iff, deleteEdgeSubtype_node_sameOrbit_iff]
      exact sameOrbit_trans H.node (sameOrbit_symm_of_complete H.node darts h_mc.complete (h_vrep_node u))
        (sameOrbit_trans H.node (perm_iter_sameOrbit H.node 1 u) (h_vrep_node (H.node.f u)))
    | n_bwd =>
      apply sameOrbit_imp_reachEN H02.hypermapToTriple
      change SameOrbit H02.node (v_rep u) (v_rep (H.node.inv u))
      rw [deleteEdgeSubtype_node_sameOrbit_iff, deleteEdgeSubtype_node_sameOrbit_iff]
      have h1 : SameOrbit H.node (H.node.inv u) u := by
        have hstep := perm_iter_sameOrbit H.node 1 (H.node.inv u)
        change SameOrbit H.node (H.node.inv u) (H.node.f (H.node.inv u)) at hstep
        rwa [H.node.right_inv u] at hstep
      exact sameOrbit_trans H.node (sameOrbit_symm_of_complete H.node darts h_mc.complete (h_vrep_node u))
        (sameOrbit_trans H.node (sameOrbit_symm_of_complete H.node darts h_mc.complete h1) (h_vrep_node (H.node.inv u)))
    | e_fwd => exact h_efwd_lift u
    | e_bwd =>
      rw [H.edge_inv_eq_edge u]
      exact h_efwd_lift u
  have h_walk_lift : ∀ {u v : H.Dart}, ReachEN H.edge H.node u v →
      ReachEN H02.edge H02.node (v_rep u) (v_rep v) := by
    intro u v ⟨w⟩
    induction w with
    | refl _ => exact reachEN_refl _ _ _
    | step s _ ih => exact reachEN_trans H02.edge H02.node (h_step_lift s) ih
  have h_conn2 : H02.numComponents darts2.length darts2 = 1 := by
    rw [numComponents_eq_one_iff_of_complete H02 darts2 h_comp2 h_ne2 (Nat.le_refl _)]
    intro a b
    have h_ab_H : Nonempty (H.Walk a.val.val b.val.val) :=
      (numComponents_eq_one_iff_of_complete H darts h_mc.complete h_mc.nonempty (Nat.le_refl _)).mp
        (mc_numComponents_eq_one H darts h_mc) a.val.val b.val.val
    have h_reach_H : ReachEN H.edge H.node a.val.val b.val.val :=
      (reachEN_hypermap_iff_walk H a.val.val b.val.val).mpr h_ab_H
    have h_reach_02 := h_walk_lift h_reach_H
    rw [h_vrep_surv a, h_vrep_surv b] at h_reach_02
    exact (reachEN_hypermap_iff_walk H02 a b).mp h_reach_02
  omega

/-- Opposite outer faces `F0` and `F2` of a 4-face in a minimal counterexample either coincide
or are adjacent across an edge; otherwise deleting `{d0, b0}` and `{d2, b2}` leaves a
smaller bridgeless planar hypermap whose 4-coloring extends back to `H`. -/
private theorem quad_opp_touch_or_eq_of_deg4 (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4) :
    SameOrbit H.face (H.edge.f d0) (H.edge.f (H.face.f (H.face.f d0))) ∨
      ∃ w : H.Dart, SameOrbit H.face w (H.edge.f d0) ∧
        SameOrbit H.face (H.edge.f w) (H.edge.f (H.face.f (H.face.f d0))) := by
  classical
  let d1 := H.face.f d0
  let d2 := H.face.f d1
  let d3 := H.face.f d2
  let b0 := H.edge.f d0
  let b1 := H.edge.f d1
  let b2 := H.edge.f d2
  let b3 := H.edge.f d3
  by_cases hF02 : SameOrbit H.face b0 b2
  · exact .inl hF02
  · right
    by_cases h_touch : ∃ w : H.Dart, SameOrbit H.face w b0 ∧ SameOrbit H.face (H.edge.f w) b2
    · exact h_touch
    · exfalso
      have h_fd3 : H.face.f d3 = d0 := quad_iter4 H darts h_mc d0 hd0_deg
      have ⟨hd01, hd02, hd03, hd12, hd13, hd23⟩ := quad_corners_distinct H darts d0 hd0_deg
      have h_d0_in : SameOrbit H.face d0 d0 := sameOrbit_refl _ _
      have h_d1_in : SameOrbit H.face d1 d0 :=
        sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 1 d0)
      have h_d2_in : SameOrbit H.face d2 d0 :=
        sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 2 d0)
      have h_d3_in : SameOrbit H.face d3 d0 :=
        sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 3 d0)
      have hb_ne_d : ∀ u v : H.Dart, SameOrbit H.face u d0 → SameOrbit H.face v d0 → u ≠ H.edge.f v := by
        intro u v hu hv h
        exact quad_outer_ne_inner H darts h_mc d0 u v hu hv (by rw [← h]; exact sameOrbit_refl _ _)
      have hb0_ne_d0 : b0 ≠ d0 := mc_edge_ne_self H darts h_mc d0
      have hb_inj_ne : ∀ u v : H.Dart, u ≠ v → H.edge.f u ≠ H.edge.f v := fun u v huv h =>
        huv (by have := congrArg H.edge.f h; simpa [H.edge_involution] using this)
      have hd2_nrem0 : d2 ∉ [d0, b0] := by
        intro h
        rcases List.mem_cons.mp h with h1 | h1
        · exact hd02 h1.symm
        · exact hb_ne_d d2 d0 h_d2_in h_d0_in (List.mem_singleton.mp h1)
      have hb2_nrem0 : b2 ∉ [d0, b0] := by
        intro h
        rcases List.mem_cons.mp h with h1 | h1
        · exact hb_ne_d d0 d2 h_d0_in h_d2_in h1.symm
        · exact hb_inj_ne d2 d0 hd02.symm (List.mem_singleton.mp h1)
      have hd1_nrem0 : d1 ∉ [d0, b0] := by
        intro h
        rcases List.mem_cons.mp h with h1 | h1
        · exact hd01 h1.symm
        · exact hb_ne_d d1 d0 h_d1_in h_d0_in (List.mem_singleton.mp h1)
      have hd3_nrem0 : d3 ∉ [d0, b0] := by
        intro h
        rcases List.mem_cons.mp h with h1 | h1
        · exact hd03 h1.symm
        · exact hb_ne_d d3 d0 h_d3_in h_d0_in (List.mem_singleton.mp h1)
      have hb1_nrem0 : b1 ∉ [d0, b0] := by
        intro h
        rcases List.mem_cons.mp h with h1 | h1
        · exact hb_ne_d d0 d1 h_d0_in h_d1_in h1.symm
        · exact hb_inj_ne d1 d0 hd01.symm (List.mem_singleton.mp h1)
      have hb3_nrem0 : b3 ∉ [d0, b0] := by
        intro h
        rcases List.mem_cons.mp h with h1 | h1
        · exact hb_ne_d d0 d3 h_d0_in h_d3_in h1.symm
        · exact hb_inj_ne d3 d0 hd03.symm (List.mem_singleton.mp h1)
      let H1 := H.deleteEdgeSubtype d0
      let d2' : H1.Dart := ⟨d2, hd2_nrem0⟩
      let b2' := H1.edge.f d2'
      have hb2'_val : b2'.val = b2 := deleteEdgeSubtype_edge_val H d0 d2'
      have hd2'_ne_b2' : d2' ≠ b2' := fun h =>
        hb_ne_d d2 d2 h_d2_in h_d2_in (by have := congrArg Subtype.val h; rwa [hb2'_val] at this)
      let d1' : H1.Dart := ⟨d1, hd1_nrem0⟩
      let d3' : H1.Dart := ⟨d3, hd3_nrem0⟩
      let b1' : H1.Dart := ⟨b1, hb1_nrem0⟩
      let b3' : H1.Dart := ⟨b3, hb3_nrem0⟩
      have h_nrem2 : ∀ z : H.Dart, (hz : z ∉ [d0, b0]) → z ≠ d2 → z ≠ b2 → (⟨z, hz⟩ : H1.Dart) ∉ [d2', b2'] := by
        intro z hz hzd hzb hmem
        rcases List.mem_cons.mp hmem with h1 | h1
        · exact hzd (congrArg Subtype.val h1)
        · have hv := congrArg Subtype.val (List.mem_singleton.mp h1)
          rw [hb2'_val] at hv
          exact hzb hv
      have hd1'_nrem : d1' ∉ [d2', b2'] := h_nrem2 d1 hd1_nrem0 hd12 (hb_ne_d d1 d2 h_d1_in h_d2_in)
      have hd3'_nrem : d3' ∉ [d2', b2'] := h_nrem2 d3 hd3_nrem0 hd23.symm (hb_ne_d d3 d2 h_d3_in h_d2_in)
      have hb1'_nrem : b1' ∉ [d2', b2'] := h_nrem2 b1 hb1_nrem0 (hb_ne_d d2 d1 h_d2_in h_d1_in).symm (hb_inj_ne d1 d2 hd12)
      have hb3'_nrem : b3' ∉ [d2', b2'] := h_nrem2 b3 hb3_nrem0 (hb_ne_d d2 d3 h_d2_in h_d3_in).symm (hb_inj_ne d3 d2 hd23.symm)
      let H02 := H1.deleteEdgeSubtype d2'
      let d1'' : H02.Dart := ⟨d1', hd1'_nrem⟩
      let d3'' : H02.Dart := ⟨d3', hd3'_nrem⟩
      let b1'' : H02.Dart := ⟨b1', hb1'_nrem⟩
      let b3'' : H02.Dart := ⟨b3', hb3'_nrem⟩
      let darts1 := subDarts darts [d0, b0]
      let darts2 := subDarts darts1 [d2', b2']
      have h_nd1 : darts1.Nodup := subDarts_nodup darts [d0, b0] h_mc.nodup
      have h_comp1 : ∀ x : H1.Dart, x ∈ darts1 := fun x => (mem_subDarts darts [d0, b0] x).mpr (h_mc.complete x.val)
      have h_len1 : darts1.length + 2 = darts.length :=
        subDarts_pair_length darts h_mc.nodup hb0_ne_d0.symm (h_mc.complete d0) (h_mc.complete b0)
      have h_nd2 : darts2.Nodup := subDarts_nodup darts1 [d2', b2'] h_nd1
      have h_comp2 : ∀ x : H02.Dart, x ∈ darts2 := fun x => (mem_subDarts darts1 [d2', b2'] x).mpr (h_comp1 x.val)
      have h_len2 : darts2.length + 2 = darts1.length :=
        subDarts_pair_length darts1 h_nd1 hd2'_ne_b2' (h_comp1 d2') (h_comp1 b2')
      have h_lt2 : darts2.length < darts.length := by omega
      have h_ne2 : darts2 ≠ [] := fun h => by
        have := h_comp2 d1''
        rw [h] at this
        cases this
      have h_planar1 : H1.isPlanar darts1.length darts1 = true :=
        deleteEdgeSubtype_isPlanar H darts h_mc.nodup h_mc.complete (Nat.le_refl _) h_mc.is_planar
          d0 hb0_ne_d0 darts1 h_nd1 h_comp1 (Nat.le_refl _)
      have hd2'_e : H1.edge.f d2' ≠ d2' := hd2'_ne_b2'.symm
      have h_planar2 : H02.isPlanar darts2.length darts2 = true :=
        deleteEdgeSubtype_isPlanar H1 darts1 h_nd1 h_comp1 (Nat.le_refl _) h_planar1
          d2' hd2'_e darts2 h_nd2 h_comp2 (Nat.le_refl _)
      have h_ndb0 : ¬ SameOrbit H.face d0 b0 := mc_not_sameOrbit_face_edge H darts h_mc d0
      have h_ndb2_1 : ¬ SameOrbit H1.face d2' b2' := by
        rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 d2' b2']
        intro h
        rcases h with h1 | ⟨_, h2⟩
        · exact quad_outer_ne_inner H darts h_mc d0 d2 d2 h_d2_in h_d2_in (by simpa [hb2'_val] using h1)
        · rcases h2 with h2d | h2b
          · apply quad_outer_ne_inner H darts h_mc d0 d0 d2 h_d0_in h_d2_in
            exact sameOrbit_symm_of_complete H.face darts h_mc.complete (by simpa [hb2'_val] using h2d)
          · apply hF02
            exact sameOrbit_symm_of_complete H.face darts h_mc.complete (by simpa [hb2'_val] using h2b)
      have h_lift_face_so : ∀ u w : H02.Dart, SameOrbit H.face u.val.val w.val.val →
          SameOrbit H02.face u w := by
        intro u w huw
        rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H1 darts1 h_comp1 d2' h_ndb2_1 u w]
        left
        rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 u.val w.val]
        left
        exact huw
      have h_edge_closed : ∀ z, z ∈ [d0, b0, d2, b2] → H.edge.f z ∈ [d0, b0, d2, b2] := by
        intro z hz
        rcases List.mem_cons.mp hz with h0 | h1
        · rw [h0]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))
        · rcases List.mem_cons.mp h1 with h1' | h2
          · rw [h1', show b0 = H.edge.f d0 from rfl, H.edge_involution]
            exact List.mem_cons.mpr (.inl rfl)
          · rcases List.mem_cons.mp h2 with h2' | h3
            · rw [h2']
              exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))
            · rw [List.mem_singleton.mp h3, show b2 = H.edge.f d2 from rfl, H.edge_involution]
              exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))
      have h_not_rem4 : ∀ x : H02.Dart, x.val.val ∉ [d0, b0, d2, b2] := by
        intro x hx
        rcases List.mem_cons.mp hx with h0 | h1
        · exact x.val.property (by rw [h0]; exact List.mem_cons.mpr (.inl rfl))
        · rcases List.mem_cons.mp h1 with h1' | h2
          · exact x.val.property (by rw [h1']; exact List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl)))
          · rcases List.mem_cons.mp h2 with h2' | h3
            · exact x.property (List.mem_cons.mpr (.inl (Subtype.ext h2')))
            · exact x.property (List.mem_cons.mpr (.inr (List.mem_singleton.mpr (Subtype.ext (by
                rw [hb2'_val]; exact List.mem_singleton.mp h3)))))
      have h_bridgeless2 : Math.Hypermap.isBridgeless H02 darts2 := by
        rw [isBridgeless_iff_no_sameOrbit_face_edge H02 darts2 h_comp2]
        intro x h_so
        let x0 := x.val.val
        let y0 := H.edge.f x0
        have hy0_val : (H02.edge.f x).val.val = y0 := by
          rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
        have hx0_nrem4 : x0 ∉ [d0, b0, d2, b2] := h_not_rem4 x
        have hy0_nrem4 : y0 ∉ [d0, b0, d2, b2] := fun h => hx0_nrem4 (by
          have := h_edge_closed y0 h; simpa [y0, H.edge_involution] using this)
        have h_inner_edge_bad : ∀ z0 : H.Dart, z0 ∉ [d0, b0, d2, b2] → SameOrbit H.face z0 d0 →
            ¬ (SameOrbit H.face (H.edge.f z0) d0 ∨ SameOrbit H.face (H.edge.f z0) b0 ∨
                SameOrbit H.face (H.edge.f z0) b2) := by
          intro z0 hz0_nrem hz0_in
          have hmem := (quad_face_mem_iff H darts h_mc d0 z0 hd0_deg).mp hz0_in
          have hz13 : z0 = d1 ∨ z0 = d3 := by
            rcases hmem with h0 | h1 | h2 | h3
            · exact absurd (by rw [h0]; exact List.mem_cons.mpr (.inl rfl)) hz0_nrem
            · exact .inl h1
            · exact absurd (by rw [h2]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))) hz0_nrem
            · exact .inr h3
          rcases hz13 with rfl | rfl
          · intro hbad
            rcases hbad with h0 | h0 | h0
            · exact quad_outer_ne_inner H darts h_mc d0 d0 d1 h_d0_in h_d1_in
                (sameOrbit_symm_of_complete H.face darts h_mc.complete h0)
            · exact adjacent_outer_faces_ne H darts h_mc d0
                (sameOrbit_symm_of_complete H.face darts h_mc.complete h0)
            · exact adjacent_outer_faces_ne H darts h_mc d1 h0
          · intro hbad
            rcases hbad with h0 | h0 | h0
            · exact quad_outer_ne_inner H darts h_mc d0 d0 d3 h_d0_in h_d3_in
                (sameOrbit_symm_of_complete H.face darts h_mc.complete h0)
            · have adj := adjacent_outer_faces_ne H darts h_mc d3
              rw [h_fd3] at adj
              exact adj h0
            · exact adjacent_outer_faces_ne H darts h_mc d2
                (sameOrbit_symm_of_complete H.face darts h_mc.complete h0)
        have h_in02 : ∀ u w : H02.Dart, SameOrbit H02.face u w →
            SameOrbit H.face u.val.val w.val.val ∨
              (SameOrbit H.face u.val.val d0 ∨ SameOrbit H.face u.val.val b0 ∨ SameOrbit H.face u.val.val b2) ∧
              (SameOrbit H.face w.val.val d0 ∨ SameOrbit H.face w.val.val b0 ∨ SameOrbit H.face w.val.val b2) := by
          intro u w huw
          rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H1 darts1 h_comp1 d2' h_ndb2_1 u w] at huw
          rcases huw with h1 | ⟨h2u, h2w⟩
          · rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 u.val w.val] at h1
            rcases h1 with h1' | ⟨h1u, h1w⟩
            · exact .inl h1'
            · exact .inr ⟨by rcases h1u with ha | hb; exact .inl ha; exact .inr (.inl hb),
                by rcases h1w with ha | hb; exact .inl ha; exact .inr (.inl hb)⟩
          · have h_1_to_3 : ∀ v : H1.Dart,
                SameOrbit H1.face v d2' ∨ SameOrbit H1.face v b2' →
                SameOrbit H.face v.val d0 ∨ SameOrbit H.face v.val b0 ∨ SameOrbit H.face v.val b2 := by
              intro v hv
              rcases hv with hvd | hvb
              · rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 v d2'] at hvd
                rcases hvd with h1 | ⟨h1v, _⟩
                · exact .inl (sameOrbit_trans H.face h1 h_d2_in)
                · rcases h1v with ha | hb
                  · exact .inl ha
                  · exact .inr (.inl hb)
              · rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 v b2'] at hvb
                rcases hvb with h1 | ⟨h1v, _⟩
                · exact .inr (.inr (by simpa [hb2'_val] using h1))
                · rcases h1v with ha | hb
                  · exact .inl ha
                  · exact .inr (.inl hb)
            exact .inr ⟨h_1_to_3 u.val h2u, h_1_to_3 w.val h2w⟩
        have h_exp := h_in02 x (H02.edge.f x) h_so
        rw [hy0_val] at h_exp
        rcases h_exp with h_same | ⟨hx_in, hy_in⟩
        · exact mc_not_sameOrbit_face_edge H darts h_mc x0 h_same
        · rcases hx_in with hxd0 | hxb0 | hxb2
          · exact h_inner_edge_bad x0 hx0_nrem4 hxd0 hy_in
          · rcases hy_in with hyd0 | hyb0 | hyb2
            · have hy_e : H.edge.f y0 = x0 := H.edge_involution x0
              exact h_inner_edge_bad y0 hy0_nrem4 hyd0 (by rw [hy_e]; exact .inr (.inl hxb0))
            · exact mc_not_sameOrbit_face_edge H darts h_mc x0
                (sameOrbit_trans H.face hxb0 (sameOrbit_symm_of_complete H.face darts h_mc.complete hyb0))
            · exact h_touch ⟨x0, hxb0, hyb2⟩
          · rcases hy_in with hyd0 | hyb0 | hyb2
            · have hy_e : H.edge.f y0 = x0 := H.edge_involution x0
              exact h_inner_edge_bad y0 hy0_nrem4 hyd0 (by rw [hy_e]; exact .inr (.inr hxb2))
            · exact h_touch ⟨y0, hyb0, by simpa [y0, H.edge_involution] using hxb2⟩
            · exact mc_not_sameOrbit_face_edge H darts h_mc x0
                (sameOrbit_trans H.face hxb2 (sameOrbit_symm_of_complete H.face darts h_mc.complete hyb2))
      obtain ⟨c2⟩ := h_mc.is_minimal H02 darts2 h_nd2 h_comp2 h_ne2 h_lt2 h_planar2 h_bridgeless2
      -- Lift coloring `c2` to `H`
      let col02 := c2.color d1''
      have h_col_d3 : c2.color d3'' = col02 := by
        apply sameOrbit_node_of_face_color_inv H02 c2
        exact h_lift_face_so d3'' d1''
          (sameOrbit_trans H.face h_d3_in (sameOrbit_symm_of_complete H.face darts h_mc.complete h_d1_in))
      have h_col_F0 : ∀ u : H02.Dart, SameOrbit H.face u.val.val b0 → c2.color u = col02 := by
        intro u hu
        apply sameOrbit_node_of_face_color_inv H02 c2
        rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H1 darts1 h_comp1 d2' h_ndb2_1 u d1'']
        left
        rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 u.val d1']
        right
        exact ⟨.inr hu, .inl h_d1_in⟩
      have h_col_F2 : ∀ u : H02.Dart, SameOrbit H.face u.val.val b2 → c2.color u = col02 := by
        intro u hu
        apply sameOrbit_node_of_face_color_inv H02 c2
        rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H1 darts1 h_comp1 d2' h_ndb2_1 u d1'']
        right
        refine ⟨.inr ?_, .inl ?_⟩
        · rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 u.val b2']
          left; simpa [hb2'_val] using hu
        · rw [deleteEdgeSubtype_face_sameOrbit_iff_ne H darts h_mc.complete d0 h_ndb0 d1' d2']
          left
          exact sameOrbit_trans H.face h_d1_in (sameOrbit_symm_of_complete H.face darts h_mc.complete h_d2_in)
      have h_edge_d1 : H02.edge.f d1'' = b1'' := by
        apply Subtype.ext; apply Subtype.ext
        rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
      have h_edge_d3 : H02.edge.f d3'' = b3'' := by
        apply Subtype.ext; apply Subtype.ext
        rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
      have h_c_b1_ne : c2.color b1'' ≠ col02 := by
        rw [← h_edge_d1]
        exact c2.edge_proper d1''
      have h_c_b3_ne : c2.color b3'' ≠ col02 := by
        rw [← h_col_d3, ← h_edge_d3]
        exact c2.edge_proper d3''
      obtain ⟨c4, hc4_02, hc4_b1, hc4_b3⟩ := exists_fourth_color col02 (c2.color b1'') (c2.color b3'')
      let lift (z : H.Dart) : Color :=
        if hzF : SameOrbit H.face z d0 then c4
        else if hz0 : z ∈ [d0, b0] then col02
        else if hz2 : (⟨z, hz0⟩ : H1.Dart) ∈ [d2', b2'] then col02
        else c2.color ⟨⟨z, hz0⟩, hz2⟩
      have h_lift_F : ∀ z : H.Dart, SameOrbit H.face z d0 → lift z = c4 := fun z hz => by
        simp only [lift, hz, ↓reduceDIte]
      have h_lift_b0 : lift b0 = col02 := by
        have h_nF : ¬ SameOrbit H.face b0 d0 := by
          intro h
          exact h_ndb0 (sameOrbit_symm_of_complete H.face darts h_mc.complete h)
        have h_in0 : b0 ∈ [d0, b0] := List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))
        simp only [lift, h_nF, h_in0, ↓reduceDIte]
      have h_lift_b2 : lift b2 = col02 := by
        have h_nF : ¬ SameOrbit H.face b2 d0 := by
          intro h
          exact quad_outer_ne_inner H darts h_mc d0 d0 d2 h_d0_in h_d2_in
            (sameOrbit_symm_of_complete H.face darts h_mc.complete h)
        have h_in2 : (⟨b2, hb2_nrem0⟩ : H1.Dart) ∈ [d2', b2'] :=
          List.mem_cons.mpr (.inr (List.mem_singleton.mpr (Subtype.ext hb2'_val.symm)))
        simp only [lift, h_nF, hb2_nrem0, h_in2, ↓reduceDIte]
      have h_lift_surv : ∀ z : H.Dart, ¬ SameOrbit H.face z d0 →
          (hz0 : z ∉ [d0, b0]) → (hz2 : (⟨z, hz0⟩ : H1.Dart) ∉ [d2', b2']) →
          lift z = c2.color ⟨⟨z, hz0⟩, hz2⟩ := by
        intro z hzF hz0 hz2
        simp only [lift, hzF, hz0, hz2, ↓reduceDIte]
      have h_lift_eq_col02_of_b02 : ∀ z : H.Dart, (SameOrbit H.face z b0 ∨ SameOrbit H.face z b2) →
          lift z = col02 := by
        intro z hz
        have hzF : ¬ SameOrbit H.face z d0 := by
          intro h
          rcases hz with hz0 | hz2
          · exact quad_outer_ne_inner H darts h_mc d0 d0 d0 h_d0_in h_d0_in
              (sameOrbit_trans H.face h_d0_in (sameOrbit_trans H.face
                (sameOrbit_symm_of_complete H.face darts h_mc.complete h) hz0))
          · exact quad_outer_ne_inner H darts h_mc d0 d0 d2 h_d0_in h_d2_in
              (sameOrbit_trans H.face h_d0_in (sameOrbit_trans H.face
                (sameOrbit_symm_of_complete H.face darts h_mc.complete h) hz2))
        by_cases hz0 : z ∈ [d0, b0]
        · simp only [lift, hzF, hz0, ↓reduceDIte]
        · by_cases hz2 : (⟨z, hz0⟩ : H1.Dart) ∈ [d2', b2']
          · simp only [lift, hzF, hz0, hz2, ↓reduceDIte]
          · rw [h_lift_surv z hzF hz0 hz2]
            rcases hz with hb0 | hb2
            · exact h_col_F0 ⟨⟨z, hz0⟩, hz2⟩ hb0
            · exact h_col_F2 ⟨⟨z, hz0⟩, hz2⟩ hb2
      have h_lift_face : ∀ z : H.Dart, lift (H.face.f z) = lift z := by
        intro z
        by_cases hzF : SameOrbit H.face z d0
        · have hfzF : SameOrbit H.face (H.face.f z) d0 :=
            sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete
              (perm_iter_sameOrbit H.face 1 z)) hzF
          rw [h_lift_F _ hfzF, h_lift_F _ hzF]
        · have hfzF : ¬ SameOrbit H.face (H.face.f z) d0 := fun h => hzF (sameOrbit_trans H.face
            (perm_iter_sameOrbit H.face 1 z) h)
          by_cases hzb0 : SameOrbit H.face z b0 ∨ SameOrbit H.face z b2
          · have hfzb0 : SameOrbit H.face (H.face.f z) b0 ∨ SameOrbit H.face (H.face.f z) b2 := by
              have step : SameOrbit H.face (H.face.f z) z :=
                sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 1 z)
              rcases hzb0 with h | h
              · exact .inl (sameOrbit_trans H.face step h)
              · exact .inr (sameOrbit_trans H.face step h)
            rw [h_lift_eq_col02_of_b02 _ hfzb0, h_lift_eq_col02_of_b02 _ hzb0]
          · have hz_nrem4 : z ∉ [d0, b0, d2, b2] := by
              intro hmem
              rcases List.mem_cons.mp hmem with h0 | h1
              · exact hzF (by rw [h0]; exact h_d0_in)
              · rcases List.mem_cons.mp h1 with h1' | h2
                · exact hzb0 (.inl (by rw [h1']; exact sameOrbit_refl _ _))
                · rcases List.mem_cons.mp h2 with h2' | h3
                  · exact hzF (by rw [h2']; exact h_d2_in)
                  · exact hzb0 (.inr (by rw [List.mem_singleton.mp h3]; exact sameOrbit_refl _ _))
            have hfz_nrem4 : H.face.f z ∉ [d0, b0, d2, b2] := by
              intro hmem
              have step : SameOrbit H.face (H.face.f z) z :=
                sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 1 z)
              rcases List.mem_cons.mp hmem with h0 | h1
              · exact hfzF (by rw [h0]; exact h_d0_in)
              · rcases List.mem_cons.mp h1 with h1' | h2
                · exact hzb0 (.inl (by rw [← h1']; exact sameOrbit_symm_of_complete H.face darts h_mc.complete step))
                · rcases List.mem_cons.mp h2 with h2' | h3
                  · exact hfzF (by rw [h2']; exact h_d2_in)
                  · exact hzb0 (.inr (by rw [← List.mem_singleton.mp h3]; exact sameOrbit_symm_of_complete H.face darts h_mc.complete step))
            have hz0 : z ∉ [d0, b0] := fun h => hz_nrem4 (by
              rcases List.mem_cons.mp h with h1 | h1
              · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
              · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
            have hfz0 : H.face.f z ∉ [d0, b0] := fun h => hfz_nrem4 (by
              rcases List.mem_cons.mp h with h1 | h1
              · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
              · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
            have hz2 : (⟨z, hz0⟩ : H1.Dart) ∉ [d2', b2'] := h_nrem2 z hz0
              (fun h => hz_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))))
              (fun h => hz_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))))
            have hfz2 : (⟨H.face.f z, hfz0⟩ : H1.Dart) ∉ [d2', b2'] := h_nrem2 (H.face.f z) hfz0
              (fun h => hfz_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))))
              (fun h => hfz_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))))
            rw [h_lift_surv (H.face.f z) hfzF hfz0 hfz2, h_lift_surv z hzF hz0 hz2]
            apply sameOrbit_node_of_face_color_inv H02 c2
            exact h_lift_face_so ⟨⟨H.face.f z, hfz0⟩, hfz2⟩ ⟨⟨z, hz0⟩, hz2⟩
              (sameOrbit_symm_of_complete H.face darts h_mc.complete (perm_iter_sameOrbit H.face 1 z))
      have h_lift_edge : ∀ z : H.Dart, lift (H.edge.f z) ≠ lift z := by
        intro z
        by_cases hzF : SameOrbit H.face z d0
        · rw [h_lift_F z hzF]
          rcases (quad_face_mem_iff H darts h_mc d0 z hd0_deg).mp hzF with hz0 | hz1 | hz2 | hz3
          · rw [hz0]; change lift b0 ≠ c4; rw [h_lift_b0]; exact hc4_02.symm
          · rw [hz1]
            have hb1_nF : ¬ SameOrbit H.face b1 d0 := fun h =>
              quad_outer_ne_inner H darts h_mc d0 d0 d1 h_d0_in h_d1_in
                (sameOrbit_symm_of_complete H.face darts h_mc.complete h)
            change lift b1 ≠ c4
            rw [h_lift_surv b1 hb1_nF hb1_nrem0 hb1'_nrem]
            exact hc4_b1.symm
          · rw [hz2]; change lift b2 ≠ c4; rw [h_lift_b2]; exact hc4_02.symm
          · rw [hz3]
            have hb3_nF : ¬ SameOrbit H.face b3 d0 := fun h =>
              quad_outer_ne_inner H darts h_mc d0 d0 d3 h_d0_in h_d3_in
                (sameOrbit_symm_of_complete H.face darts h_mc.complete h)
            change lift b3 ≠ c4
            rw [h_lift_surv b3 hb3_nF hb3_nrem0 hb3'_nrem]
            exact hc4_b3.symm
        · by_cases hezF : SameOrbit H.face (H.edge.f z) d0
          · rw [h_lift_F (H.edge.f z) hezF]
            rcases (quad_face_mem_iff H darts h_mc d0 (H.edge.f z) hd0_deg).mp hezF with he0 | he1 | he2 | he3
            · have hz_b0 : z = b0 := by
                have := congrArg H.edge.f he0
                simpa [H.edge_involution] using this
              rw [hz_b0, h_lift_b0]
              exact Ne.symm hc4_02.symm
            · have hz_b1 : z = b1 := by
                have := congrArg H.edge.f he1
                simpa [H.edge_involution] using this
              have hb1_nF : ¬ SameOrbit H.face b1 d0 := fun h =>
                quad_outer_ne_inner H darts h_mc d0 d0 d1 h_d0_in h_d1_in
                  (sameOrbit_symm_of_complete H.face darts h_mc.complete h)
              rw [hz_b1, h_lift_surv b1 hb1_nF hb1_nrem0 hb1'_nrem]
              exact hc4_b1
            · have hz_b2 : z = b2 := by
                have := congrArg H.edge.f he2
                simpa [H.edge_involution] using this
              rw [hz_b2, h_lift_b2]
              exact Ne.symm hc4_02.symm
            · have hz_b3 : z = b3 := by
                have := congrArg H.edge.f he3
                simpa [H.edge_involution] using this
              have hb3_nF : ¬ SameOrbit H.face b3 d0 := fun h =>
                quad_outer_ne_inner H darts h_mc d0 d0 d3 h_d0_in h_d3_in
                  (sameOrbit_symm_of_complete H.face darts h_mc.complete h)
              rw [hz_b3, h_lift_surv b3 hb3_nF hb3_nrem0 hb3'_nrem]
              exact hc4_b3
          · have hz_nrem4 : z ∉ [d0, b0, d2, b2] := by
              intro hmem
              rcases List.mem_cons.mp hmem with h0 | h1
              · exact hzF (by rw [h0]; exact h_d0_in)
              · rcases List.mem_cons.mp h1 with h1' | h2
                · apply hezF
                  rw [h1', show b0 = H.edge.f d0 from rfl, H.edge_involution]
                  exact h_d0_in
                · rcases List.mem_cons.mp h2 with h2' | h3
                  · exact hzF (by rw [h2']; exact h_d2_in)
                  · apply hezF
                    rw [List.mem_singleton.mp h3, show b2 = H.edge.f d2 from rfl, H.edge_involution]
                    exact h_d2_in
            have hez_nrem4 : H.edge.f z ∉ [d0, b0, d2, b2] := fun h => hz_nrem4 (by
              have := h_edge_closed _ h; rwa [H.edge_involution] at this)
            have hz0 : z ∉ [d0, b0] := fun h => hz_nrem4 (by
              rcases List.mem_cons.mp h with h1 | h1
              · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
              · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
            have hez0 : H.edge.f z ∉ [d0, b0] := fun h => hez_nrem4 (by
              rcases List.mem_cons.mp h with h1 | h1
              · rw [h1]; exact List.mem_cons.mpr (.inl rfl)
              · rw [List.mem_singleton.mp h1]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl))))
            have hz2 : (⟨z, hz0⟩ : H1.Dart) ∉ [d2', b2'] := h_nrem2 z hz0
              (fun h => hz_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))))
              (fun h => hz_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))))
            have hez2 : (⟨H.edge.f z, hez0⟩ : H1.Dart) ∉ [d2', b2'] := h_nrem2 (H.edge.f z) hez0
              (fun h => hez_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))))))
              (fun h => hez_nrem4 (by rw [h]; exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr rfl))))))))
            rw [h_lift_surv (H.edge.f z) hezF hez0 hez2, h_lift_surv z hzF hz0 hz2]
            have hev : H02.edge.f ⟨⟨z, hz0⟩, hz2⟩ = ⟨⟨H.edge.f z, hez0⟩, hez2⟩ := by
              apply Subtype.ext; apply Subtype.ext
              rw [deleteEdgeSubtype_edge_val H1 d2', deleteEdgeSubtype_edge_val H d0]
            rw [← hev]
            exact c2.edge_proper ⟨⟨z, hz0⟩, hz2⟩
      exact h_mc.not_colorable ⟨lift, h_lift_face, h_lift_edge⟩

private theorem reachENIn_dual_node_of_sameOrbit_face (H : Hypermap)
    (P : H.Dart → Prop) (hP_inv : ∀ z : H.Dart, P (H.face.f z) ↔ P z)
    {x y : H.Dart} (hx : P x) (hxy : SameOrbit H.face x y) :
    ReachENIn H.dual.edge H.dual.node P x y := by
  rcases hxy with ⟨k, rfl⟩
  have h_ind : ∀ m : Nat,
      ReachENIn H.dual.edge H.dual.node P x (Perm.iter H.face m x) ∧
      P (Perm.iter H.face m x) := by
    intro m
    induction m with
    | zero =>
      rw [Perm.iter_zero]
      exact ⟨ReachENIn.refl hx, hx⟩
    | succ j ih =>
      rw [Perm.iter_succ]
      have hP_next : P (H.face.f (Perm.iter H.face j x)) := (hP_inv _).mpr ih.2
      exact ⟨ReachENIn.step_n_bwd (e := H.dual.edge) (n := H.dual.node) (P := P) ih.1 hP_next,
        hP_next⟩
  exact (h_ind k).1

/-- No face in a minimal counterexample has size 4: otherwise the central 4-face and its four
outer faces `F0, F1, F2, F3` are pairwise distinct, `F0` touches `F2`, and `F1` touches `F3`,
yielding a `K5` minor in the planar dual `H.dual`. -/
private theorem quad_K5_contradiction (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart)
    (hd0_deg : Math.Hypermap.faceDegree H d0 darts.length = 4) : False := by
  let d1 : H.Dart := H.face.f d0
  let d2 : H.Dart := H.face.f d1
  let d3 : H.Dart := H.face.f d2
  let b0 : H.Dart := H.edge.f d0
  let b1 : H.Dart := H.edge.f d1
  let b2 : H.Dart := H.edge.f d2
  let b3 : H.Dart := H.edge.f d3
  have hd3_f : H.face.f d3 = d0 := quad_iter4 H darts h_mc d0 hd0_deg
  have h_d0_in : SameOrbit H.face d0 d0 := sameOrbit_refl H.face d0
  have h_d1_in : SameOrbit H.face d1 d0 := sameOrbit_symm_of_complete H.face darts h_mc.complete
    ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  have h_d2_in : SameOrbit H.face d2 d0 := sameOrbit_symm_of_complete H.face darts h_mc.complete
    ⟨2, by rw [Perm.iter_succ, Perm.iter_succ, Perm.iter_zero]⟩
  have h_d3_in : SameOrbit H.face d3 d0 := sameOrbit_symm_of_complete H.face darts h_mc.complete
    ⟨3, by rw [Perm.iter_succ, Perm.iter_succ, Perm.iter_succ, Perm.iter_zero]⟩
  have hd1_deg : Math.Hypermap.faceDegree H d1 darts.length = 4 :=
    quad_next_deg4 H darts h_mc d0 hd0_deg
  have hd2_deg : Math.Hypermap.faceDegree H d2 darts.length = 4 :=
    quad_next_deg4 H darts h_mc d1 hd1_deg
  -- Pairwise distinctness of the five face orbits `{d0, b0, b1, b2, b3}`:
  have h_n01 : ¬ SameOrbit H.face d0 b0 :=
    quad_outer_ne_inner H darts h_mc d0 d0 d0 h_d0_in h_d0_in
  have h_n02 : ¬ SameOrbit H.face d0 b1 :=
    quad_outer_ne_inner H darts h_mc d0 d0 d1 h_d0_in h_d1_in
  have h_n03 : ¬ SameOrbit H.face d0 b2 :=
    quad_outer_ne_inner H darts h_mc d0 d0 d2 h_d0_in h_d2_in
  have h_n04 : ¬ SameOrbit H.face d0 b3 :=
    quad_outer_ne_inner H darts h_mc d0 d0 d3 h_d0_in h_d3_in
  have h_n12 : ¬ SameOrbit H.face b0 b1 :=
    adjacent_outer_faces_ne H darts h_mc d0
  have h_n23 : ¬ SameOrbit H.face b1 b2 :=
    adjacent_outer_faces_ne H darts h_mc d1
  have h_n34 : ¬ SameOrbit H.face b2 b3 :=
    adjacent_outer_faces_ne H darts h_mc d2
  have h_n41 : ¬ SameOrbit H.face b3 b0 := by
    have h := adjacent_outer_faces_ne H darts h_mc d3
    simpa [b3, b0, hd3_f] using h
  have h_n14 : ¬ SameOrbit H.face b0 b3 := fun h =>
    h_n41 (sameOrbit_symm_of_complete H.face darts h_mc.complete h)
  have h_opp02_raw := quad_opp_touch_or_eq_of_deg4 H darts h_mc d0 hd0_deg
  have h_opp13_raw := quad_opp_touch_or_eq_of_deg4 H darts h_mc d1 hd1_deg
  have h_opp20_raw := quad_opp_touch_or_eq_of_deg4 H darts h_mc d2 hd2_deg
  have h_n13 : ¬ SameOrbit H.face b0 b2 := fun hF02 =>
    quad_H02_disconnected_of_F0_eq_F2 H darts h_mc d0 hd0_deg hF02 h_opp13_raw
  have h_n24 : ¬ SameOrbit H.face b1 b3 := fun hF13 =>
    quad_H02_disconnected_of_F0_eq_F2 H darts h_mc d1 hd1_deg hF13 h_opp20_raw
  rcases h_opp02_raw with h_eq02 | ⟨w02, hw02_0, hw02_2⟩
  · exact False.elim (h_n13 h_eq02)
  rcases h_opp13_raw with h_eq13 | ⟨w13, hw13_1, hw13_3⟩
  · exact False.elim (h_n24 h_eq13)
  -- Construct the K5 minor on `H.dual`:
  open Classical in
  let cls : H.Dart → Option (Fin 5) := fun z =>
    if SameOrbit H.face z d0 then some 0
    else if SameOrbit H.face z b0 then some 1
    else if SameOrbit H.face z b1 then some 2
    else if SameOrbit H.face z b2 then some 3
    else if SameOrbit H.face z b3 then some 4
    else none
  let rep : Fin 5 → H.Dart := fun i =>
    match i.1 with
    | 0 => d0
    | 1 => b0
    | 2 => b1
    | 3 => b2
    | _ => b3
  have h_not_both : ∀ {u v z : H.Dart}, ¬ SameOrbit H.face u v →
      SameOrbit H.face z v → ¬ SameOrbit H.face z u := fun hnuv hzv hzu =>
    hnuv (sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_mc.complete hzu) hzv)
  have h_cls0 : ∀ {z : H.Dart}, SameOrbit H.face z d0 → cls z = some 0 := fun hz => by
    dsimp only [cls]; exact if_pos hz
  have h_cls1 : ∀ {z : H.Dart}, SameOrbit H.face z b0 → cls z = some 1 := fun hz => by
    dsimp only [cls]
    rw [if_neg (h_not_both h_n01 hz), if_pos hz]
  have h_cls2 : ∀ {z : H.Dart}, SameOrbit H.face z b1 → cls z = some 2 := fun hz => by
    dsimp only [cls]
    rw [if_neg (h_not_both h_n02 hz), if_neg (h_not_both h_n12 hz), if_pos hz]
  have h_cls3 : ∀ {z : H.Dart}, SameOrbit H.face z b2 → cls z = some 3 := fun hz => by
    dsimp only [cls]
    rw [if_neg (h_not_both h_n03 hz), if_neg (h_not_both h_n13 hz),
      if_neg (h_not_both h_n23 hz), if_pos hz]
  have h_cls4 : ∀ {z : H.Dart}, SameOrbit H.face z b3 → cls z = some 4 := fun hz => by
    dsimp only [cls]
    rw [if_neg (h_not_both h_n04 hz), if_neg (h_not_both h_n14 hz),
      if_neg (h_not_both h_n24 hz), if_neg (h_not_both h_n34 hz), if_pos hz]
  have h_cls_to_rep : ∀ (i : Fin 5) (z : H.Dart), cls z = some i → SameOrbit H.face z (rep i) := by
    intro i z hzi
    dsimp only [cls] at hzi
    by_cases h0 : SameOrbit H.face z d0
    · rw [if_pos h0] at hzi; have h0i : (0 : Fin 5) = i := Option.some.inj hzi
      subst h0i; exact h0
    · rw [if_neg h0] at hzi
      by_cases h1 : SameOrbit H.face z b0
      · rw [if_pos h1] at hzi; have h1i : (1 : Fin 5) = i := Option.some.inj hzi
        subst h1i; exact h1
      · rw [if_neg h1] at hzi
        by_cases h2 : SameOrbit H.face z b1
        · rw [if_pos h2] at hzi; have h2i : (2 : Fin 5) = i := Option.some.inj hzi
          subst h2i; exact h2
        · rw [if_neg h2] at hzi
          by_cases h3 : SameOrbit H.face z b2
          · rw [if_pos h3] at hzi; have h3i : (3 : Fin 5) = i := Option.some.inj hzi
            subst h3i; exact h3
          · rw [if_neg h3] at hzi
            by_cases h4 : SameOrbit H.face z b3
            · rw [if_pos h4] at hzi; have h4i : (4 : Fin 5) = i := Option.some.inj hzi
              subst h4i; exact h4
            · rw [if_neg h4] at hzi; cases hzi
  have h_so_inv : ∀ z w : H.Dart, SameOrbit H.face (H.face.inv z) w ↔ SameOrbit H.face z w := by
    intro z w
    have h_step : SameOrbit H.face (H.face.inv z) z :=
      ⟨1, by rw [Perm.iter_succ, Perm.iter_zero, H.face.right_inv z]⟩
    have h_step_symm : SameOrbit H.face z (H.face.inv z) :=
      sameOrbit_symm_of_complete H.face darts h_mc.complete h_step
    exact ⟨fun h => sameOrbit_trans H.face h_step_symm h,
      fun h => sameOrbit_trans H.face h_step h⟩
  have h_so_face : ∀ z w : H.Dart, SameOrbit H.face (H.face.f z) w ↔ SameOrbit H.face z w := by
    intro z w
    have h_step : SameOrbit H.face z (H.face.f z) :=
      ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
    have h_step_symm : SameOrbit H.face (H.face.f z) z :=
      sameOrbit_symm_of_complete H.face darts h_mc.complete h_step
    exact ⟨fun h => sameOrbit_trans H.face h_step h,
      fun h => sameOrbit_trans H.face h_step_symm h⟩
  have h_cls_node : ∀ d : H.Dart, cls (H.dual.node.f d) = cls d := by
    intro d
    change cls (H.face.inv d) = cls d
    dsimp only [cls]
    simp only [h_so_inv]
  have h_cls_face : ∀ d : H.Dart, cls (H.face.f d) = cls d := by
    intro d
    dsimp only [cls]
    simp only [h_so_face]
  have h_conn : ∀ (i : Fin 5) (x y : H.Dart),
      cls x = some i → cls y = some i →
      ReachENIn H.dual.edge H.dual.node (fun z => cls z = some i) x y := by
    intro i x y hx hy
    have hxy : SameOrbit H.face x y := sameOrbit_trans H.face (h_cls_to_rep i x hx)
      (sameOrbit_symm_of_complete H.face darts h_mc.complete (h_cls_to_rep i y hy))
    refine reachENIn_dual_node_of_sameOrbit_face H (fun z => cls z = some i) ?_ hx hxy
    intro z
    rw [h_cls_face z]
  -- Adjacent outer face cross-edges via `node_edge_of_face_step`:
  have hstep0 := node_edge_of_face_step H darts h_mc d0
  have hstep1 := node_edge_of_face_step H darts h_mc d1
  have hstep2 := node_edge_of_face_step H darts h_mc d2
  have hstep3 := node_edge_of_face_step H darts h_mc d3
  have h_12_l : SameOrbit H.face (H.edge.f (H.face.f b1)) b0 := by
    have hfb1 : H.face.f b1 = H.node.inv d1 := hstep0.2.1
    have hfe : H.face.f (H.edge.f (H.face.f b1)) = b0 := by
      rw [hfb1]; exact hstep0.2.2
    rw [← hfe]; exact ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  have h_12_r : SameOrbit H.face (H.edge.f (H.edge.f (H.face.f b1))) b1 := by
    rw [H.edge_involution]
    exact sameOrbit_symm_of_complete H.face darts h_mc.complete
      ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  have h_23_l : SameOrbit H.face (H.edge.f (H.face.f b2)) b1 := by
    have hfb2 : H.face.f b2 = H.node.inv d2 := hstep1.2.1
    have hfe : H.face.f (H.edge.f (H.face.f b2)) = b1 := by
      rw [hfb2]; exact hstep1.2.2
    rw [← hfe]; exact ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  have h_23_r : SameOrbit H.face (H.edge.f (H.edge.f (H.face.f b2))) b2 := by
    rw [H.edge_involution]
    exact sameOrbit_symm_of_complete H.face darts h_mc.complete
      ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  have h_34_l : SameOrbit H.face (H.edge.f (H.face.f b3)) b2 := by
    have hfb3 : H.face.f b3 = H.node.inv d3 := hstep2.2.1
    have hfe : H.face.f (H.edge.f (H.face.f b3)) = b2 := by
      rw [hfb3]; exact hstep2.2.2
    rw [← hfe]; exact ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  have h_34_r : SameOrbit H.face (H.edge.f (H.edge.f (H.face.f b3))) b3 := by
    rw [H.edge_involution]
    exact sameOrbit_symm_of_complete H.face darts h_mc.complete
      ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  have h_14_l : SameOrbit H.face (H.face.f b0) b0 :=
    sameOrbit_symm_of_complete H.face darts h_mc.complete
      ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  have h_14_r : SameOrbit H.face (H.edge.f (H.face.f b0)) b3 := by
    have hfb0 : H.face.f b0 = H.node.inv d0 := by
      have htmp := hstep3.2.1
      change H.face.f (H.edge.f (H.face.f d3)) = H.node.inv (H.face.f d3) at htmp
      rw [hd3_f] at htmp; exact htmp
    have hfe : H.face.f (H.edge.f (H.face.f b0)) = b3 := by
      rw [hfb0]
      have htmp := hstep3.2.2
      change H.face.f (H.edge.f (H.node.inv (H.face.f d3))) = b3 at htmp
      rw [hd3_f] at htmp; exact htmp
    rw [← hfe]; exact ⟨1, by rw [Perm.iter_succ, Perm.iter_zero]⟩
  let e_dart : (i j : Fin 5) → i < j → H.Dart := fun i j _ =>
    match i.1, j.1 with
    | 0, 1 => d0
    | 0, 2 => d1
    | 0, 3 => d2
    | 0, 4 => d3
    | 1, 2 => H.edge.f (H.face.f b1)
    | 1, 3 => w02
    | 1, 4 => H.face.f b0
    | 2, 3 => H.edge.f (H.face.f b2)
    | 2, 4 => w13
    | 3, 4 => H.edge.f (H.face.f b3)
    | _, _ => d0
  have he_i : ∀ (i j : Fin 5) (h : i < j), cls (e_dart i j h) = some i := by
    intro i j hij
    rcases i with ⟨iv, hiv⟩
    rcases j with ⟨jv, hjv⟩
    change iv < jv at hij
    match iv, jv with
    | 0, 1 => exact h_cls0 h_d0_in
    | 0, 2 => exact h_cls0 h_d1_in
    | 0, 3 => exact h_cls0 h_d2_in
    | 0, 4 => exact h_cls0 h_d3_in
    | 1, 2 => exact h_cls1 h_12_l
    | 1, 3 => exact h_cls1 hw02_0
    | 1, 4 => exact h_cls1 h_14_l
    | 2, 3 => exact h_cls2 h_23_l
    | 2, 4 => exact h_cls2 hw13_1
    | 3, 4 => exact h_cls3 h_34_l
    | 0, 0 | 1, 0 | 1, 1 | 2, 0 | 2, 1 | 2, 2
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 4, _ => exact False.elim (by omega)
    | _ + 5, _ => exact False.elim (by omega)
    | _, _ + 5 => exact False.elim (by omega)
  have he_j : ∀ (i j : Fin 5) (h : i < j), cls (H.dual.edge.f (e_dart i j h)) = some j := by
    intro i j hij
    rcases i with ⟨iv, hiv⟩
    rcases j with ⟨jv, hjv⟩
    change iv < jv at hij
    change cls (H.edge.f (e_dart ⟨iv, hiv⟩ ⟨jv, hjv⟩ hij)) = some ⟨jv, hjv⟩
    match iv, jv with
    | 0, 1 => exact h_cls1 (sameOrbit_refl H.face b0)
    | 0, 2 => exact h_cls2 (sameOrbit_refl H.face b1)
    | 0, 3 => exact h_cls3 (sameOrbit_refl H.face b2)
    | 0, 4 => exact h_cls4 (sameOrbit_refl H.face b3)
    | 1, 2 => exact h_cls2 h_12_r
    | 1, 3 => exact h_cls3 hw02_2
    | 1, 4 => exact h_cls4 h_14_r
    | 2, 3 => exact h_cls3 h_23_r
    | 2, 4 => exact h_cls4 hw13_3
    | 3, 4 => exact h_cls4 h_34_r
    | 0, 0 | 1, 0 | 1, 1 | 2, 0 | 2, 1 | 2, 2
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 4, _ => exact False.elim (by omega)
    | _ + 5, _ => exact False.elim (by omega)
    | _, _ + 5 => exact False.elim (by omega)
  have h_dual_planar : H.dual.isPlanar darts.length darts = true := by
    rw [isPlanar_dual_of_complete H darts h_mc.complete (Nat.le_refl _)]
    exact h_mc.is_planar
  exact no_K5_minor_of_isPlanar H.dual darts h_mc.nodup h_mc.complete h_dual_planar
    cls h_cls_node h_conn e_dart he_i he_j

/-- No face in a minimal counterexample has size 4. -/
theorem mc_faceDegree_ne_four (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart) :
    Math.Hypermap.faceDegree H d0 darts.length ≠ 4 :=
  quad_K5_contradiction H darts h_mc d0

/-- Every face in a minimal counterexample has degree at least 5 (`girth ≥ 5` in the dual). -/
theorem mc_faceDegree_ge_five (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (d0 : H.Dart) :
    5 ≤ Math.Hypermap.faceDegree H d0 darts.length := by
  have h_pos : 0 < Math.Hypermap.faceDegree H d0 darts.length := by
    change 0 < (getOrbit H.face darts.length d0).length
    exact List.length_pos_of_mem (mem_getOrbit_self H.face darts.length d0)
  have h1 := mc_faceDegree_ne_one H darts h_mc d0
  have h2 := mc_faceDegree_ne_two H darts h_mc d0
  have h3 := mc_faceDegree_ne_three H darts h_mc d0
  have h4 := mc_faceDegree_ne_four H darts h_mc d0
  omega

end Hypermap
