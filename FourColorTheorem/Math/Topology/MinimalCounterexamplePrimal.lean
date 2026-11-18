module

public import FourColorTheorem.Math.Discharging
public import FourColorTheorem.Math.Topology.Genus

@[expose] public section

/-!
# Minimal Counterexample Primal Properties (`T.1`)

Eliminates disconnectedness and vertices of degree 1 or 2 from any minimal
counterexample to the 4-color theorem:
- `edge_ne_self_of_isBridgeless` / `mc_edge_ne_self`
- `mc_numComponents_eq_one`
- `mc_nodeDegree_ne_one`
- `mc_nodeDegree_ne_two`
- `mc_nodeDegree_ge_three`

No broken or legacy files (`Degree4.lean`) are imported.
-/

namespace Hypermap

/-- Standalone minimal counterexample specification for primal topological reductions.
    Matches the fields of `Math.MinimalCounterexample` without importing `MainTheorem.lean`. -/
structure PrimalMinimalCounterexample (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) : Prop where
  nodup : darts.Nodup
  complete : ∀ d : H.Dart, d ∈ darts
  nonempty : darts ≠ []
  is_planar : H.isPlanar darts.length darts = true
  is_bridgeless : Math.Hypermap.isBridgeless H darts darts.length
  not_colorable : ∀ _ : H.FaceColoring, False
  is_minimal : ∀ (H' : Hypermap) [DecidableEq H'.Dart] (darts' : List H'.Dart),
    darts'.Nodup → (∀ x : H'.Dart, x ∈ darts') → darts' ≠ [] →
    darts'.length < darts.length →
    H'.isPlanar darts'.length darts' = true →
    Math.Hypermap.isBridgeless H' darts' darts'.length →
    Nonempty H'.FaceColoring

/-- A bridgeless map has no self-paired edge darts (`H.edge.f d ≠ d`). -/
theorem edge_ne_self_of_isBridgeless (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_comp : ∀ d : H.Dart, d ∈ darts)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts darts.length)
    (d : H.Dart) : H.edge.f d ≠ d := by
  intro h_eq
  have hb := h_bridgeless d (h_comp d)
  change (getOrbit H.face darts.length d).contains (H.edge.f d) = false at hb
  rw [h_eq] at hb
  have hmem : (getOrbit H.face darts.length d).contains d = true :=
    List.contains_iff_mem.mpr (mem_getOrbit_self H.face darts.length d)
  rw [hmem] at hb
  exact Bool.false_ne_true hb.symm

theorem mc_edge_ne_self (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (d : H.Dart) : H.edge.f d ≠ d :=
  edge_ne_self_of_isBridgeless H darts h_mc.complete h_mc.is_bridgeless d

private theorem perm_iter_excise_face_val (H : Hypermap) (removed : List H.Dart)
    (h_edge : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ H.node.f d ∈ removed) :
    ∀ k (z : (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).Dart),
      (Perm.iter (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).face k z).val =
        Perm.iter H.face k z.val
  | 0, _ => rfl
  | k + 1, z => by
    change ((H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).face.f
      (Perm.iter (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).face k z)).val =
      H.face.f (Perm.iter H.face k z.val)
    have h_step : ((H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).face.f
        (Perm.iter (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).face k z)).val =
        H.face.f (Perm.iter (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).face k z).val := rfl
    rw [h_step, perm_iter_excise_face_val H removed h_edge h_node k z]

/-- Excising a union of connected components preserves bridgelessness. -/
private theorem exciseSubtype_id_isBridgeless (H : Hypermap) [DecidableEq H.Dart]
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
  intro u _
  rw [Bool.eq_false_iff]
  intro hb'
  change (getOrbit H'.face darts'.length u).contains (H'.edge.f u) = true at hb'
  have hmem' : H'.edge.f u ∈ getOrbit H'.face darts'.length u := List.contains_iff_mem.mp hb'
  have hcl' : orbitClosesWithin H'.face u u darts'.length :=
    orbitClosesWithin_of_complete H'.face darts' h_comp' u
  rcases (mem_getOrbit_iff_exists_iter H'.face darts'.length u (H'.edge.f u) hcl').mp hmem' with ⟨k, hk⟩
  have hval : H.edge.f u.val = Perm.iter H.face k u.val := by
    have h_edge_val : (H'.edge.f u).val = H.edge.f u.val := rfl
    rw [← h_edge_val, hk]
    exact perm_iter_excise_face_val H removed h_edge h_node k u
  have hcl : orbitClosesWithin H.face u.val u.val darts.length :=
    orbitClosesWithin_of_complete H.face darts h_comp u.val
  have hmem : H.edge.f u.val ∈ getOrbit H.face darts.length u.val :=
    (mem_getOrbit_iff_exists_iter H.face darts.length u.val (H.edge.f u.val) hcl).mpr ⟨k, hval⟩
  have hb := h_bridgeless u.val (h_comp u.val)
  change (getOrbit H.face darts.length u.val).contains (H.edge.f u.val) = false at hb
  rw [List.contains_iff_mem.mpr hmem] at hb
  exact Bool.false_ne_true hb.symm

/-- A minimal counterexample is connected (`numComponents = 1`). -/
theorem mc_numComponents_eq_one (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) :
    H.numComponents darts.length darts = 1 := by
  have h_comp := h_mc.complete
  have h_pos : 1 ≤ H.numComponents darts.length darts :=
    numComponents_pos_of_ne_nil H darts.length darts h_mc.nonempty
  rcases List.exists_mem_of_ne_nil darts h_mc.nonempty with ⟨d0, hd0_mem⟩
  let C := H.getComponent darts.length d0
  let Cbar := darts.filter (fun x => !C.contains x)
  by_cases h_eq1 : H.numComponents darts.length darts = 1
  · exact h_eq1
  · exfalso
    have h_gt1 : 1 < H.countComponents darts.length darts := by
      change 1 < H.numComponents darts.length darts
      omega
    have h_split := countComponents_eq_one_add_filter_of_mem H darts h_comp (Nat.le_refl _) darts d0 hd0_mem
    have h_rem_pos : 0 < H.countComponents darts.length Cbar := by
      dsimp only [Cbar, C]
      omega
    have h_Cbar_ne : Cbar ≠ [] := by
      intro h_nil
      rw [h_nil, countComponents_nil] at h_rem_pos
      omega
    rcases List.exists_mem_of_ne_nil Cbar h_Cbar_ne with ⟨d1, hd1_Cbar⟩
    have hd1_not_C : ¬ d1 ∈ C := by
      have hf := List.mem_filter.mp hd1_Cbar
      intro hmem
      have hc : C.contains d1 = true := List.contains_iff_mem.mpr hmem
      have hf2 := hf.2
      rw [hc] at hf2
      exact Bool.false_ne_true hf2
    have hd0_C : d0 ∈ C := mem_getComponent_self H darts.length d0
    have h_edge1 : ∀ d, d ∈ C ↔ H.edge.f d ∈ C := by
      intro d
      constructor
      · exact getComponent_step_closed_of_complete H darts h_comp (Nat.le_refl _) d0 (Step.edge rfl)
      · intro he
        have he2 := getComponent_step_closed_of_complete H darts h_comp (Nat.le_refl _) d0 (Step.edge rfl) he
        rwa [H.edge_involution d] at he2
    have h_node1 : ∀ d, d ∈ C ↔ H.node.f d ∈ C := by
      intro d
      constructor
      · exact getComponent_step_closed_of_complete H darts h_comp (Nat.le_refl _) d0 (Step.node rfl)
      · intro hn
        have hn2 := getComponent_step_closed_of_complete H darts h_comp (Nat.le_refl _) d0
          (Step.nodeInv (d := H.node.f d) (d' := d) (H.node.left_inv d).symm) hn
        exact hn2
    have h_mem_Cbar_iff : ∀ d, d ∈ Cbar ↔ ¬ d ∈ C := by
      intro d
      constructor
      · intro hm hc
        have hf := (List.mem_filter.mp hm).2
        rw [List.contains_iff_mem.mpr hc] at hf
        exact Bool.false_ne_true hf
      · intro hnc
        apply List.mem_filter.mpr
        refine ⟨h_comp d, ?_⟩
        by_cases hc : C.contains d = true
        · exfalso; exact hnc (List.contains_iff_mem.mp hc)
        · have hc_f : C.contains d = false := Bool.eq_false_iff.mpr hc
          rw [hc_f]
          rfl
    have h_edge2 : ∀ d, d ∈ Cbar ↔ H.edge.f d ∈ Cbar := by
      intro d
      rw [h_mem_Cbar_iff d, h_mem_Cbar_iff (H.edge.f d), h_edge1 d]
    have h_node2 : ∀ d, d ∈ Cbar ↔ H.node.f d ∈ Cbar := by
      intro d
      rw [h_mem_Cbar_iff d, h_mem_Cbar_iff (H.node.f d), h_node1 d]
    let H1 := H.exciseSubtype C H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge1 h_node1
    let darts1 := subDarts darts C
    let H2 := H.exciseSubtype Cbar H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge2 h_node2
    let darts2 := subDarts darts Cbar
    have h_comp1 := exciseSubtype_complete H darts C H.edge H.node H.face
      H.edge_involution H.edge_node_face_id h_edge1 h_node1 h_mc.nodup h_comp ⟨d1, h_comp d1, hd1_not_C⟩
    have h_lt1 : darts1.length < darts.length :=
      exciseSubtype_strictly_smaller darts C ⟨d0, hd0_mem, hd0_C⟩
    have h_planar1 : H1.isPlanar darts1.length darts1 = true :=
      exciseSubtype_isPlanar H darts C h_edge1 h_node1 h_mc.nodup h_comp
        (Nat.le_refl _) h_mc.is_planar darts1 h_comp1.1 h_comp1.2.1 (Nat.le_refl _)
    have h_bridgeless1 : Math.Hypermap.isBridgeless H1 darts1 darts1.length :=
      exciseSubtype_id_isBridgeless H darts C h_comp h_mc.is_bridgeless h_edge1 h_node1 darts1 h_comp1.2.1
    obtain ⟨c1⟩ := h_mc.is_minimal H1 darts1 h_comp1.1 h_comp1.2.1 h_comp1.2.2 h_lt1 h_planar1 h_bridgeless1
    have hd0_not_Cbar : ¬ d0 ∈ Cbar := fun hm => (h_mem_Cbar_iff d0).mp hm hd0_C
    have h_comp2 := exciseSubtype_complete H darts Cbar H.edge H.node H.face
      H.edge_involution H.edge_node_face_id h_edge2 h_node2 h_mc.nodup h_comp ⟨d0, hd0_mem, hd0_not_Cbar⟩
    have h_lt2 : darts2.length < darts.length :=
      exciseSubtype_strictly_smaller darts Cbar ⟨d1, h_comp d1, hd1_Cbar⟩
    have h_planar2 : H2.isPlanar darts2.length darts2 = true :=
      exciseSubtype_isPlanar H darts Cbar h_edge2 h_node2 h_mc.nodup h_comp
        (Nat.le_refl _) h_mc.is_planar darts2 h_comp2.1 h_comp2.2.1 (Nat.le_refl _)
    have h_bridgeless2 : Math.Hypermap.isBridgeless H2 darts2 darts2.length :=
      exciseSubtype_id_isBridgeless H darts Cbar h_comp h_mc.is_bridgeless h_edge2 h_node2 darts2 h_comp2.2.1
    obtain ⟨c2⟩ := h_mc.is_minimal H2 darts2 h_comp2.1 h_comp2.2.1 h_comp2.2.2 h_lt2 h_planar2 h_bridgeless2
    have h_face1 : ∀ d, d ∈ C ↔ H.face.f d ∈ C :=
      face_mem_removed_iff_of_edge_node C H.edge H.node H.face H.edge_node_face_id h_edge1 h_node1
    let col : H.Dart → Color := fun d =>
      if hd : C.contains d then
        c2.color ⟨d, fun hm => (h_mem_Cbar_iff d).mp hm (List.contains_iff_mem.mp hd)⟩
      else
        c1.color ⟨d, fun hm => hd (List.contains_iff_mem.mpr hm)⟩
    have h_face_inv : ∀ d : H.Dart, col (H.face.f d) = col d := by
      intro d
      dsimp only [col]
      by_cases hd : C.contains d = true
      · have hfd : C.contains (H.face.f d) = true :=
          List.contains_iff_mem.mpr ((h_face1 d).mp (List.contains_iff_mem.mp hd))
        rw [dif_pos hfd, dif_pos hd]
        exact c2.face_invariant ⟨d, fun hm => (h_mem_Cbar_iff d).mp hm (List.contains_iff_mem.mp hd)⟩
      · have hfd : ¬ C.contains (H.face.f d) = true := by
          intro hm
          exact hd (List.contains_iff_mem.mpr ((h_face1 d).mpr (List.contains_iff_mem.mp hm)))
        rw [dif_neg hfd, dif_neg hd]
        exact c1.face_invariant ⟨d, fun hm => hd (List.contains_iff_mem.mpr hm)⟩
    have h_edge_prop : ∀ d : H.Dart, col (H.edge.f d) ≠ col d := by
      intro d
      dsimp only [col]
      by_cases hd : C.contains d = true
      · have hed : C.contains (H.edge.f d) = true :=
          List.contains_iff_mem.mpr ((h_edge1 d).mp (List.contains_iff_mem.mp hd))
        rw [dif_pos hed, dif_pos hd]
        exact c2.edge_proper ⟨d, fun hm => (h_mem_Cbar_iff d).mp hm (List.contains_iff_mem.mp hd)⟩
      · have hed : ¬ C.contains (H.edge.f d) = true := by
          intro hm
          exact hd (List.contains_iff_mem.mpr ((h_edge1 d).mpr (List.contains_iff_mem.mp hm)))
        rw [dif_neg hed, dif_neg hd]
        exact c1.edge_proper ⟨d, fun hm => hd (List.contains_iff_mem.mpr hm)⟩
    exact h_mc.not_colorable ⟨col, h_face_inv, h_edge_prop⟩

/-- No dart in a minimal counterexample has `nodeDegree = 1`. -/
theorem mc_nodeDegree_ne_one (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (d : H.Dart) :
    Math.Hypermap.nodeDegree H d darts.length ≠ 1 := by
  intro h_deg1
  change (getOrbit H.node darts.length d).length = 1 at h_deg1
  have h_self : d ∈ getOrbit H.node darts.length d := mem_getOrbit_self H.node darts.length d
  have h_next : H.node.f d ∈ getOrbit H.node darts.length d :=
    getOrbit_closed_under_f_of_complete H.node darts h_mc.complete (Nat.le_refl _) h_self
  rcases List.length_eq_one_iff.mp h_deg1 with ⟨a, ha⟩
  rw [ha] at h_self h_next
  have hda : d = a := List.mem_singleton.mp h_self
  have hna : H.node.f d = a := List.mem_singleton.mp h_next
  have h_fix : H.node.f d = d := hna.trans hda.symm
  have h_enf : H.edge.f (H.node.f (H.face.f (H.face.inv d))) = H.face.inv d :=
    H.edge_node_face_id (H.face.inv d)
  rw [H.face.right_inv d, h_fix] at h_enf
  have h_f_self : d ∈ getOrbit H.face darts.length d := mem_getOrbit_self H.face darts.length d
  have h_f_inv : H.face.inv d ∈ getOrbit H.face darts.length d :=
    getOrbit_closed_under_inv_of_complete H.face darts h_mc.complete (Nat.le_refl _) h_f_self
  rw [← h_enf] at h_f_inv
  have hb := h_mc.is_bridgeless d (h_mc.complete d)
  change (getOrbit H.face darts.length d).contains (H.edge.f d) = false at hb
  rw [List.contains_iff_mem.mpr h_f_inv] at hb
  exact Bool.false_ne_true hb.symm

private theorem mem_two_orbit_eq_or {D : Type} (l : List D) (h_len : l.length = 2)
    {x y z : D} (hx : x ∈ l) (hy : y ∈ l) (hne : y ≠ x) (hz : z ∈ l) : z = x ∨ z = y := by
  cases l with
  | nil => simp at h_len
  | cons a t =>
    cases t with
    | nil => simp at h_len
    | cons b r =>
      cases r with
      | nil =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy hz
        rcases hx with rfl | rfl
        · rcases hy with rfl | rfl
          · exact False.elim (hne rfl)
          · exact hz
        · rcases hy with rfl | rfl
          · exact hz.symm
          · exact False.elim (hne rfl)
      | cons c r' => simp at h_len

private theorem smooth_two_cycle_loop_absurd (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (x : H.Dart)
    (hx_ne : H.node.f x ≠ x) (hy_back : H.node.f (H.node.f x) = x)
    (h_loop : H.edge.f x = H.node.f x) : False := by
  let y := H.node.f x
  have hey : H.edge.f y = x := by
    change H.edge.f (H.node.f x) = x
    rw [← h_loop, H.edge_involution x]
  have h_conn : H.numComponents darts.length darts = 1 := mc_numComponents_eq_one H darts h_mc
  have h_all_walk : ∀ u v : H.Dart, Nonempty (H.Walk u v) :=
    (numComponents_eq_one_iff_of_complete H darts h_mc.complete h_mc.nonempty (Nat.le_refl _)).mp h_conn
  have h_closed : ∀ z : H.Dart, z = x ∨ z = y := by
    intro z
    obtain ⟨w⟩ := h_all_walk x z
    apply pred_end_of_walk_of_closed H (fun u => u = x ∨ u = y) _ w (Or.inl rfl)
    apply step_closed_of_edge_node_closed H (fun u => u = x ∨ u = y)
    · intro u hu
      rcases hu with rfl | rfl
      · exact Or.inr h_loop
      · exact Or.inl hey
    · intro u hu
      have hinvol : H.edge.inv u = H.edge.f u := by
        have hi := H.edge_involution (H.edge.inv u)
        rw [H.edge.right_inv u] at hi
        exact hi.symm
      rw [hinvol]
      rcases hu with rfl | rfl
      · exact Or.inr h_loop
      · exact Or.inl hey
    · intro u hu
      rcases hu with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl hy_back
    · intro u hu
      rcases hu with hux | huy
      · have hnx : H.node.inv u = y := by
          rw [hux, ← hy_back]
          exact H.node.left_inv y
        exact Or.inr hnx
      · have hny : H.node.inv u = x := by
          rw [huy]
          exact H.node.left_inv x
        exact Or.inl hny
  have hfx : H.face.f x = x := by
    have h1 := H.edge_node_face_id x
    have h2 : H.edge.f (H.node.f x) = x := hey
    have h12 : H.edge.f (H.node.f (H.face.f x)) = H.edge.f (H.node.f x) := h1.trans h2.symm
    have h_e : H.node.f (H.face.f x) = H.node.f x := by
      have hi := congrArg H.edge.f h12
      rwa [H.edge_involution, H.edge_involution] at hi
    have hi := congrArg H.node.inv h_e
    rwa [H.node.left_inv, H.node.left_inv] at hi
  have hfy : H.face.f y = y := by
    have h1 := H.edge_node_face_id y
    have h2 : H.edge.f (H.node.f y) = y := by
      change H.edge.f (H.node.f (H.node.f x)) = H.node.f x
      rw [hy_back]; exact h_loop
    have h12 : H.edge.f (H.node.f (H.face.f y)) = H.edge.f (H.node.f y) := h1.trans h2.symm
    have h_e : H.node.f (H.face.f y) = H.node.f y := by
      have hi := congrArg H.edge.f h12
      rwa [H.edge_involution, H.edge_involution] at hi
    have hi := congrArg H.node.inv h_e
    rwa [H.node.left_inv, H.node.left_inv] at hi
  let col : H.Dart → Color := fun d => if d = x then Color.c0 else Color.c1
  refine h_mc.not_colorable ⟨col, ?_, ?_⟩
  · intro d
    dsimp only [col]
    rcases h_closed d with hdx | hdy
    · rw [hdx, hfx]
    · rw [hdy, hfy]
  · intro d
    dsimp only [col]
    rcases h_closed d with hdx | hdy
    · rw [hdx, h_loop, if_pos rfl, if_neg hx_ne]
      exact fun h => Color.noConfusion h
    · rw [hdy, hey, if_pos rfl, if_neg hx_ne]
      exact fun h => Color.noConfusion h

private theorem smoothDeg2_face_in_orbit (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_comp : ∀ d : H.Dart, d ∈ darts)
    (x : H.Dart) (hx_ne : H.node.f x ≠ x) (hy_back : H.node.f (H.node.f x) = x)
    (hx_efree : H.edge.f x ≠ x) (hy_efree : H.edge.f (H.node.f x) ≠ H.node.f x)
    (h_noloop : H.edge.f x ≠ H.node.f x) :
    let y := H.node.f x
    let ex := H.edge.f x
    let ey := H.edge.f y
    let H' := H.smoothDeg2Subtype x hx_ne hy_back hx_efree hy_efree h_noloop
    (H.face.f ey = x) ∧ (H.face.f ex = y) ∧
    (∀ z : H'.Dart, (H'.face.f z).val ∈ getOrbit H.face darts.length z.val) ∧
    (∀ k (u : H'.Dart), (Perm.iter H'.face k u).val ∈ getOrbit H.face darts.length u.val) := by
  intro y ex ey H'
  have hfey : H.face.f ey = x := by
    have h1 := H.edge_node_face_id ey
    have h2 : H.edge.f (H.node.f x) = ey := rfl
    have h12 : H.edge.f (H.node.f (H.face.f ey)) = H.edge.f (H.node.f x) := h1.trans h2.symm
    have he := congrArg H.edge.f h12
    rw [H.edge_involution, H.edge_involution] at he
    have hn := congrArg H.node.inv he
    rwa [H.node.left_inv, H.node.left_inv] at hn
  have hfex : H.face.f ex = y := by
    have h1 := H.edge_node_face_id ex
    have h2 : H.edge.f (H.node.f y) = ex := by
      change H.edge.f (H.node.f (H.node.f x)) = H.edge.f x
      rw [hy_back]
    have h12 : H.edge.f (H.node.f (H.face.f ex)) = H.edge.f (H.node.f y) := h1.trans h2.symm
    have he := congrArg H.edge.f h12
    rw [H.edge_involution, H.edge_involution] at he
    have hn := congrArg H.node.inv he
    rwa [H.node.left_inv, H.node.left_inv] at hn
  have hxy : x ≠ y := hx_ne.symm
  have hx_ey : x ≠ ey := fun h => h_noloop (by
    have h' := congrArg H.edge.f h
    rwa [H.edge_involution] at h')
  have hy_ex : y ≠ ex := h_noloop.symm
  have hex_ey : ex ≠ ey := fun h => hx_ne (by
    have h' := congrArg H.edge.f h
    rw [H.edge_involution, H.edge_involution] at h'
    exact h'.symm)
  have h_step_orb : ∀ z : H'.Dart, (H'.face.f z).val ∈ getOrbit H.face darts.length z.val := by
    intro z
    have hzx : z.val ≠ x := fun h => z.property (by simp [h])
    have hzy : z.val ≠ y := fun h => z.property (by simp [y, h])
    have hf_eval : (H'.face.f z).val = H.face.f (swapFun x ey (swapFun y ex z.val)) := rfl
    rw [hf_eval]
    by_cases hzex : z.val = ex
    · rw [hzex, swapFun_right, swapFun_of_ne hxy.symm hy_efree.symm]
      have hy_in : y ∈ getOrbit H.face darts.length ex := by
        rw [← hfex]
        exact getOrbit_closed_under_f_of_complete H.face darts h_comp (Nat.le_refl _)
          (mem_getOrbit_self H.face darts.length ex)
      exact getOrbit_closed_under_f_of_complete H.face darts h_comp (Nat.le_refl _) hy_in
    · by_cases hzey : z.val = ey
      · rw [hzey, swapFun_of_ne hy_efree hex_ey.symm, swapFun_right]
        have hx_in : x ∈ getOrbit H.face darts.length ey := by
          rw [← hfey]
          exact getOrbit_closed_under_f_of_complete H.face darts h_comp (Nat.le_refl _)
            (mem_getOrbit_self H.face darts.length ey)
        exact getOrbit_closed_under_f_of_complete H.face darts h_comp (Nat.le_refl _) hx_in
      · rw [swapFun_of_ne hzy hzex, swapFun_of_ne hzx hzey]
        exact getOrbit_closed_under_f_of_complete H.face darts h_comp (Nat.le_refl _)
          (mem_getOrbit_self H.face darts.length z.val)
  have h_iter_orb : ∀ k (u : H'.Dart), (Perm.iter H'.face k u).val ∈ getOrbit H.face darts.length u.val := by
    intro k
    induction k with
    | zero => intro u; exact mem_getOrbit_self H.face darts.length u.val
    | succ k ih =>
      intro u
      rw [Perm.iter_succ_right]
      have h1 : (H'.face.f u).val ∈ getOrbit H.face darts.length u.val := h_step_orb u
      have h2 := ih (H'.face.f u)
      have hcl : orbitClosesWithin H.face u.val u.val darts.length :=
        orbitClosesWithin_of_complete H.face darts h_comp u.val
      exact mem_getOrbit_trans H.face darts.length hcl h1 h2
  exact ⟨hfey, hfex, h_step_orb, h_iter_orb⟩

/-- No dart in a minimal counterexample has `nodeDegree = 2`. -/
theorem mc_nodeDegree_ne_two (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (x : H.Dart) :
    Math.Hypermap.nodeDegree H x darts.length ≠ 2 := by
  intro h_deg2
  change (getOrbit H.node darts.length x).length = 2 at h_deg2
  have hx_ne : H.node.f x ≠ x := by
    intro h_fix
    obtain ⟨m, hm⟩ : ∃ m, darts.length = m + 1 := by
      cases darts with
      | nil => exact False.elim (h_mc.nonempty rfl)
      | cons a t => exact ⟨t.length, rfl⟩
    rw [hm, getOrbit_fixed_point H.node x m h_fix] at h_deg2
    simp at h_deg2
  let y := H.node.f x
  have h_self : x ∈ getOrbit H.node darts.length x := mem_getOrbit_self H.node darts.length x
  have hy_in : y ∈ getOrbit H.node darts.length x :=
    getOrbit_closed_under_f_of_complete H.node darts h_mc.complete (Nat.le_refl _) h_self
  have hny_in : H.node.f y ∈ getOrbit H.node darts.length x :=
    getOrbit_closed_under_f_of_complete H.node darts h_mc.complete (Nat.le_refl _) hy_in
  have hy_back : H.node.f y = x := by
    rcases mem_two_orbit_eq_or (getOrbit H.node darts.length x) h_deg2 h_self hy_in hx_ne hny_in with h1 | h2
    · exact h1
    · exfalso
      have h2' := congrArg H.node.inv h2
      rw [H.node.left_inv y, H.node.left_inv x] at h2'
      exact hx_ne h2'
  have hx_efree : H.edge.f x ≠ x := mc_edge_ne_self H darts h_mc x
  have hy_efree : H.edge.f y ≠ y := mc_edge_ne_self H darts h_mc y
  have h_noloop : H.edge.f x ≠ y := by
    intro h_loop
    exact smooth_two_cycle_loop_absurd H darts h_mc x hx_ne hy_back h_loop
  let H' := H.smoothDeg2Subtype x hx_ne hy_back hx_efree hy_efree h_noloop
  let darts' := subDarts darts [x, y]
  let ex := H.edge.f x
  let ey := H.edge.f y
  have hxy : x ≠ y := hx_ne.symm
  have hx_ey : x ≠ ey := fun h => h_noloop (by
    have h' := congrArg H.edge.f h
    rwa [H.edge_involution] at h')
  have hy_ex : y ≠ ex := h_noloop.symm
  have hex_ey : ex ≠ ey := fun h => hx_ne (by
    have h' := congrArg H.edge.f h
    rw [H.edge_involution, H.edge_involution] at h'
    exact h'.symm)
  have hex_nmem : ¬ ex ∈ [x, y] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hx_efree h
    · exact h_noloop h
  have hey_nmem : ¬ ey ∈ [x, y] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro (h | h)
    · exact hx_ey h.symm
    · exact hy_efree h
  have h_nodup' : darts'.Nodup := subDarts_nodup darts [x, y] h_mc.nodup
  have h_comp' : ∀ z : H'.Dart, z ∈ darts' := fun z => (mem_subDarts darts [x, y] z).mpr (h_mc.complete z.val)
  have h_ne' : darts' ≠ [] := subDarts_nonempty darts [x, y] ⟨ex, h_mc.complete ex, hex_nmem⟩
  have h_lt' : darts'.length < darts.length :=
    exciseSubtype_strictly_smaller darts [x, y] ⟨x, h_mc.complete x, List.mem_cons_self⟩
  have h_planar' : H'.isPlanar darts'.length darts' = true :=
    smoothDeg2Subtype_isPlanar H darts h_mc.nodup h_mc.complete (Nat.le_refl _) h_mc.is_planar
      x hx_ne hy_back hx_efree hy_efree h_noloop darts' h_nodup' h_comp' (Nat.le_refl _)
  obtain ⟨hfey, hfex, _, h_iter_orb⟩ :=
    smoothDeg2_face_in_orbit H darts h_mc.complete x hx_ne hy_back hx_efree hy_efree h_noloop
  have h_edge'_eval : ∀ z : H'.Dart,
      (H'.edge.f z).val = if z.val = ex then ey else if z.val = ey then ex else H.edge.f z.val := by
    intro z
    have hzx : z.val ≠ x := fun h => z.property (by simp [h])
    have hzy : z.val ≠ y := fun h => z.property (by simp [y, h])
    have he_def : (H'.edge.f z).val = swapFun y ex (swapFun x ey (H.edge.f (swapFun x y z.val))) := rfl
    rw [he_def, swapFun_of_ne hzx hzy]
    by_cases hzex : z.val = ex
    · rw [if_pos hzex, hzex, show H.edge.f ex = x from H.edge_involution x, swapFun_left,
        swapFun_of_ne hy_efree hex_ey.symm]
    · rw [if_neg hzex]
      by_cases hzey : z.val = ey
      · rw [if_pos hzey, hzey, show H.edge.f ey = y from H.edge_involution y,
          swapFun_of_ne hxy.symm hy_efree.symm, swapFun_left]
      · rw [if_neg hzey]
        have hezx : H.edge.f z.val ≠ x := fun h => hzex (by
          have h' := congrArg H.edge.f h; rwa [H.edge_involution] at h')
        have hezy : H.edge.f z.val ≠ y := fun h => hzey (by
          have h' := congrArg H.edge.f h; rwa [H.edge_involution] at h')
        have hezex : H.edge.f z.val ≠ ex := fun h => hzx (by
          have h' := congrArg H.edge.f h; rwa [H.edge_involution, H.edge_involution] at h')
        have hezey : H.edge.f z.val ≠ ey := fun h => hzy (by
          have h' := congrArg H.edge.f h; rwa [H.edge_involution, H.edge_involution] at h')
        rw [swapFun_of_ne hezx hezey, swapFun_of_ne hezy hezex]
  have h_face'_eval : ∀ z : H'.Dart,
      (H'.face.f z).val = if z.val = ex then H.face.f y else if z.val = ey then H.face.f x else H.face.f z.val := by
    intro z
    have hzx : z.val ≠ x := fun h => z.property (by simp [h])
    have hzy : z.val ≠ y := fun h => z.property (by simp [y, h])
    have hf_def : (H'.face.f z).val = H.face.f (swapFun x ey (swapFun y ex z.val)) := rfl
    rw [hf_def]
    by_cases hzex : z.val = ex
    · rw [if_pos hzex, hzex, swapFun_right, swapFun_of_ne hxy.symm hy_efree.symm]
    · rw [if_neg hzex]
      by_cases hzey : z.val = ey
      · rw [if_pos hzey, hzey, swapFun_of_ne hy_efree hex_ey.symm, swapFun_right]
      · rw [if_neg hzey, swapFun_of_ne hzy hzex, swapFun_of_ne hzx hzey]
  have h_bridgeless' : Math.Hypermap.isBridgeless H' darts' darts'.length := by
    intro u _
    rw [Bool.eq_false_iff]
    intro hb'
    change (getOrbit H'.face darts'.length u).contains (H'.edge.f u) = true at hb'
    have hmem' : H'.edge.f u ∈ getOrbit H'.face darts'.length u := List.contains_iff_mem.mp hb'
    have hcl' : orbitClosesWithin H'.face u u darts'.length :=
      orbitClosesWithin_of_complete H'.face darts' h_comp' u
    rcases (mem_getOrbit_iff_exists_iter H'.face darts'.length u (H'.edge.f u) hcl').mp hmem' with ⟨k, hk⟩
    have h_val_in : (H'.edge.f u).val ∈ getOrbit H.face darts.length u.val := by
      rw [hk]; exact h_iter_orb k u
    have hcl : orbitClosesWithin H.face u.val u.val darts.length :=
      orbitClosesWithin_of_complete H.face darts h_mc.complete u.val
    rw [h_edge'_eval u] at h_val_in
    by_cases huex : u.val = ex
    · rw [if_pos huex, huex] at h_val_in
      have hy_in_ex : y ∈ getOrbit H.face darts.length ex := by
        change H.node.f x ∈ getOrbit H.face darts.length (H.edge.f x)
        rw [← hfex]
        exact getOrbit_closed_under_f_of_complete H.face darts h_mc.complete (Nat.le_refl _)
          (mem_getOrbit_self H.face darts.length ex)
      have hcl_ex : orbitClosesWithin H.face ex ex darts.length :=
        orbitClosesWithin_of_complete H.face darts h_mc.complete ex
      have hex_in_y : ex ∈ getOrbit H.face darts.length y :=
        mem_getOrbit_symm H.face darts.length hcl_ex hy_in_ex
      have hcl_y : orbitClosesWithin H.face y y darts.length :=
        orbitClosesWithin_of_complete H.face darts h_mc.complete y
      have hey_in_y : ey ∈ getOrbit H.face darts.length y :=
        mem_getOrbit_trans H.face darts.length hcl_y hex_in_y h_val_in
      have hb := h_mc.is_bridgeless y (h_mc.complete y)
      change (getOrbit H.face darts.length y).contains ey = false at hb
      rw [List.contains_iff_mem.mpr hey_in_y] at hb
      exact Bool.false_ne_true hb.symm
    · rw [if_neg huex] at h_val_in
      by_cases huey : u.val = ey
      · rw [if_pos huey, huey] at h_val_in
        have hx_in_ey : x ∈ getOrbit H.face darts.length ey := by
          rw [← hfey]
          exact getOrbit_closed_under_f_of_complete H.face darts h_mc.complete (Nat.le_refl _)
            (mem_getOrbit_self H.face darts.length ey)
        have hcl_ey : orbitClosesWithin H.face ey ey darts.length :=
          orbitClosesWithin_of_complete H.face darts h_mc.complete ey
        have hey_in_x : ey ∈ getOrbit H.face darts.length x :=
          mem_getOrbit_symm H.face darts.length hcl_ey hx_in_ey
        have hcl_x : orbitClosesWithin H.face x x darts.length :=
          orbitClosesWithin_of_complete H.face darts h_mc.complete x
        have hex_in_x : ex ∈ getOrbit H.face darts.length x :=
          mem_getOrbit_trans H.face darts.length hcl_x hey_in_x h_val_in
        have hb := h_mc.is_bridgeless x (h_mc.complete x)
        change (getOrbit H.face darts.length x).contains ex = false at hb
        rw [List.contains_iff_mem.mpr hex_in_x] at hb
        exact Bool.false_ne_true hb.symm
      · rw [if_neg huey] at h_val_in
        have hb := h_mc.is_bridgeless u.val (h_mc.complete u.val)
        change (getOrbit H.face darts.length u.val).contains (H.edge.f u.val) = false at hb
        rw [List.contains_iff_mem.mpr h_val_in] at hb
        exact Bool.false_ne_true hb.symm
  obtain ⟨c'⟩ := h_mc.is_minimal H' darts' h_nodup' h_comp' h_ne' h_lt' h_planar' h_bridgeless'
  let ex' : H'.Dart := ⟨ex, hex_nmem⟩
  let ey' : H'.Dart := ⟨ey, hey_nmem⟩
  let col : H.Dart → Color := fun d =>
    if hdx : d = x then c'.color ey'
    else if hdy : d = y then c'.color ex'
    else c'.color ⟨d, fun hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact hm.elim hdx hdy⟩
  have hcol_of_nmem : ∀ d (hd : ¬ d ∈ [x, y]), col d = c'.color ⟨d, hd⟩ := by
    intro d hd
    have hdx : d ≠ x := fun h => hd (h ▸ List.mem_cons_self)
    have hdy : d ≠ y := fun h => hd (by simp [y, h])
    dsimp only [col]
    rw [dif_neg hdx, dif_neg hdy]
  have h_face_inv : ∀ d : H.Dart, col (H.face.f d) = col d := by
    intro d
    by_cases hdx : d = x
    · rw [hdx]
      have hfx_nmem : ¬ H.face.f x ∈ [x, y] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro (h | h)
        · have h1 : H.face.f x = H.face.f ey := h.trans hfey.symm
          have h2 : x = ey := by
            have := congrArg H.face.inv h1
            rwa [H.face.left_inv, H.face.left_inv] at this
          exact hx_ey h2
        · have h1 : H.face.f x = H.face.f ex := h.trans hfex.symm
          have h2 : x = ex := by
            have := congrArg H.face.inv h1
            rwa [H.face.left_inv, H.face.left_inv] at this
          exact hx_efree h2.symm
      rw [hcol_of_nmem (H.face.f x) hfx_nmem]
      have hcolx : col x = c'.color ey' := by dsimp only [col]; rw [dif_pos rfl]
      rw [hcolx]
      have hfe : H'.face.f ey' = ⟨H.face.f x, hfx_nmem⟩ := by
        apply Subtype.ext
        rw [h_face'_eval ey']
        change (if ey = ex then H.face.f y else if ey = ey then H.face.f x else H.face.f ey) = H.face.f x
        rw [if_neg hex_ey.symm, if_pos rfl]
      rw [← hfe]
      exact c'.face_invariant ey'
    · by_cases hdy : d = y
      · rw [hdy]
        have hfy_nmem : ¬ H.face.f y ∈ [x, y] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | h)
          · have h1 : H.face.f y = H.face.f ey := h.trans hfey.symm
            have h2 : y = ey := by
              have := congrArg H.face.inv h1
              rwa [H.face.left_inv, H.face.left_inv] at this
            exact hy_efree h2.symm
          · have h1 : H.face.f y = H.face.f ex := h.trans hfex.symm
            have h2 : y = ex := by
              have := congrArg H.face.inv h1
              rwa [H.face.left_inv, H.face.left_inv] at this
            exact hy_ex h2
        rw [hcol_of_nmem (H.face.f y) hfy_nmem]
        have hcoly : col y = c'.color ex' := by dsimp only [col]; rw [dif_neg hxy.symm, dif_pos rfl]
        rw [hcoly]
        have hfe : H'.face.f ex' = ⟨H.face.f y, hfy_nmem⟩ := by
          apply Subtype.ext
          rw [h_face'_eval ex']
          change (if ex = ex then H.face.f y else if ex = ey then H.face.f x else H.face.f ex) = H.face.f y
          rw [if_pos rfl]
        rw [← hfe]
        exact c'.face_invariant ex'
      · have hd_nmem : ¬ d ∈ [x, y] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact fun h => h.elim hdx hdy
        let d' : H'.Dart := ⟨d, hd_nmem⟩
        rw [hcol_of_nmem d hd_nmem]
        by_cases hfx : H.face.f d = x
        · have hd_ey : d = ey := by
            have h1 := hfx.trans hfey.symm
            have := congrArg H.face.inv h1
            rwa [H.face.left_inv, H.face.left_inv] at this
          rw [hfx]
          have hcolx : col x = c'.color ey' := by dsimp only [col]; rw [dif_pos rfl]
          rw [hcolx]
          congr 1; exact Subtype.ext hd_ey.symm
        · by_cases hfy : H.face.f d = y
          · have hd_ex : d = ex := by
              have h1 := hfy.trans hfex.symm
              have := congrArg H.face.inv h1
              rwa [H.face.left_inv, H.face.left_inv] at this
            rw [hfy]
            have hcoly : col y = c'.color ex' := by dsimp only [col]; rw [dif_neg hxy.symm, dif_pos rfl]
            rw [hcoly]
            congr 1; exact Subtype.ext hd_ex.symm
          · have hfd_nmem : ¬ H.face.f d ∈ [x, y] := by
              simp only [List.mem_cons, List.not_mem_nil, or_false]
              exact fun h => h.elim hfx hfy
            rw [hcol_of_nmem (H.face.f d) hfd_nmem]
            have hd_nex : d ≠ ex := fun h => hfy (h ▸ hfex)
            have hd_ney : d ≠ ey := fun h => hfx (h ▸ hfey)
            have hfd' : H'.face.f d' = ⟨H.face.f d, hfd_nmem⟩ := by
              apply Subtype.ext
              rw [h_face'_eval d']
              change (if d = ex then H.face.f y else if d = ey then H.face.f x else H.face.f d) = H.face.f d
              rw [if_neg hd_nex, if_neg hd_ney]
            rw [← hfd']
            exact c'.face_invariant d'
  have h_edge_prop : ∀ d : H.Dart, col (H.edge.f d) ≠ col d := by
    intro d
    have h_e' : H'.edge.f ex' = ey' := by
      apply Subtype.ext
      rw [h_edge'_eval ex']
      change (if ex = ex then ey else if ex = ey then ex else H.edge.f ex) = ey
      rw [if_pos rfl]
    by_cases hdx : d = x
    · rw [hdx]
      have h1 : col (H.edge.f x) = c'.color ex' := hcol_of_nmem ex hex_nmem
      have h2 : col x = c'.color ey' := by dsimp only [col]; rw [dif_pos rfl]
      rw [h1, h2, ← h_e']
      exact fun h => (c'.edge_proper ex') h.symm
    · by_cases hdy : d = y
      · rw [hdy]
        have h1 : col (H.edge.f y) = c'.color ey' := hcol_of_nmem ey hey_nmem
        have h2 : col y = c'.color ex' := by dsimp only [col]; rw [dif_neg hxy.symm, dif_pos rfl]
        rw [h1, h2, ← h_e']
        exact c'.edge_proper ex'
      · have hd_nmem : ¬ d ∈ [x, y] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          exact fun h => h.elim hdx hdy
        let d' : H'.Dart := ⟨d, hd_nmem⟩
        rw [hcol_of_nmem d hd_nmem]
        by_cases hdex : d = ex
        · have h1 : H.edge.f d = x := hdex ▸ H.edge_involution x
          rw [h1]
          have hcolx : col x = c'.color ey' := by dsimp only [col]; rw [dif_pos rfl]
          rw [hcolx, ← h_e']
          have h_d'_ex : d' = ex' := Subtype.ext hdex
          change c'.color (H'.edge.f ex') ≠ c'.color d'
          rw [h_d'_ex]
          exact c'.edge_proper ex'
        · by_cases hdey : d = ey
          · have h1 : H.edge.f d = y := hdey ▸ H.edge_involution y
            rw [h1]
            have hcoly : col y = c'.color ex' := by dsimp only [col]; rw [dif_neg hxy.symm, dif_pos rfl]
            rw [hcoly]
            have h_d'_ey : d' = ey' := Subtype.ext hdey
            change c'.color ex' ≠ c'.color d'
            rw [h_d'_ey, ← h_e']
            exact fun h => (c'.edge_proper ex') h.symm
          · have hed_nmem : ¬ H.edge.f d ∈ [x, y] := by
              simp only [List.mem_cons, List.not_mem_nil, or_false]
              rintro (h | h)
              · apply hdex
                have h' := congrArg H.edge.f h
                rwa [H.edge_involution] at h'
              · apply hdey
                have h' := congrArg H.edge.f h
                rwa [H.edge_involution] at h'
            rw [hcol_of_nmem (H.edge.f d) hed_nmem]
            have hed' : H'.edge.f d' = ⟨H.edge.f d, hed_nmem⟩ := by
              apply Subtype.ext
              rw [h_edge'_eval d']
              change (if d = ex then ey else if d = ey then ex else H.edge.f d) = H.edge.f d
              rw [if_neg hdex, if_neg hdey]
            rw [← hed']
            exact c'.edge_proper d'
  exact h_mc.not_colorable ⟨col, h_face_inv, h_edge_prop⟩

/-- Every vertex in a minimal counterexample has `nodeDegree ≥ 3`. -/
theorem mc_nodeDegree_ge_three (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : PrimalMinimalCounterexample H darts) (d : H.Dart) :
    3 ≤ Math.Hypermap.nodeDegree H d darts.length := by
  have h_len_pos : 1 ≤ darts.length := by
    cases darts with
    | nil => exact False.elim (h_mc.nonempty rfl)
    | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  have h_pos : 1 ≤ Math.Hypermap.nodeDegree H d darts.length :=
    getOrbit_length_pos H.node h_len_pos d
  have h_ne1 : Math.Hypermap.nodeDegree H d darts.length ≠ 1 := mc_nodeDegree_ne_one H darts h_mc d
  have h_ne2 : Math.Hypermap.nodeDegree H d darts.length ≠ 2 := mc_nodeDegree_ne_two H darts h_mc d
  omega

end Hypermap
