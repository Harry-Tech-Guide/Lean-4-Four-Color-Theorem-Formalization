module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.CheckIsoSoundness
public import FourColorTheorem.Math.Unavoidability.ConfGeomCert
public import FourColorTheorem.Math.Reducibility
public import FourColorTheorem.Math.Coloring

@[expose] public section

/-!
# Stage R.3: Free-Completion Projection & Contracted Pullback (`RSST (3.3)–(3.6)`)

This module formalizes Robertson–Sanders–Seymour–Thomas (RSST) equations `(3.3)–(3.6)`
on top of the certified triangulation embeddings (`AppearsInTriangulation` and `MatchesConfCycle`
from `CheckIsoSoundness.lean`) and geometric/contract certificates (`ConfGeomCert.lean` and
`FastConfEquiv.lean`):

1. `CorrespondingProjection`: RSST `(3.3)–(3.4)` faithful projection of configuration `c` into
   a triangulation `T`, packaging `TriangulationEmbedding c T darts`, ring-cycle adjacency,
   bijective local dart star at every interior vertex `u` (`int_dart_bij`), symmetry, and
   RSST `(3.6)` contract safety.
2. `ring_fan_projection_consistent`: RSST `(3.4)` cyclic consistency along ring-interior fans
   and ring edges from `MatchesConfCycle` and `fastConf_geom_ring_fans`.
3. `appearsInTriangulation_implies_correspondingProjection` (and the matched variant
   `appearsInTriangulation_matched_implies_correspondingProjection`): lifts every
   `AppearsInTriangulation c T darts` (`c ∈ theUnavoidableSet`) to a `CorrespondingProjection`.
4. `mappedContractDarts`, `VertexColoringMod`, and `pullback_mod_coloring_extendsToContracted`:
   maps `c.contractEdges` into `T.Dart` and proves RSST `(3.5)` pullback — any 4-coloring of
   `T / mappedContractDarts` pulls back along `p.emb.rep` to `extendsToContracted c`.
5. `correspondingProjection_triangle_clique_and_contract_sparsity`, `contract_no_component_shortcut`,
   and `triad4_witness_in_triangulation`: lifts `fastConf_geom_tri_clique_in_cyc`,
   `fastConf_equiv_contract_safe`, and `fastConf_geom_triad4` into `T` for RSST `(3.5)–(3.6)`.
-/

namespace Math.Unavoidability

open Math Math.Discharging Math.Hypermap

section FinitePigeonholeAndContractHelpers

/-- Finite pigeonhole principle on duplicate-free lists: an injective subset of at least equal
    length covers every element of the ambient list. -/
private theorem list_sub_nodup_mem_of_length_le {α : Type} [DecidableEq α] :
    ∀ (l1 l2 : List α),
      l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l2.length ≤ l1.length →
      ∀ y ∈ l2, y ∈ l1
  | [], l2, _, _, hlen, y, hy => by
    have hpos : 0 < l2.length := List.length_pos_of_mem hy
    rw [List.length_nil] at hlen
    omega
  | x :: xs, l2, hnd, hsub, hlen, y, hy => by
    rw [List.nodup_cons] at hnd
    have hx_l2 : x ∈ l2 := hsub x List.mem_cons_self
    by_cases hyx : y = x
    · subst hyx; exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      have hxs_sub : ∀ z ∈ xs, z ∈ l2.erase x := by
        intro z hz
        have hzx : z ≠ x := fun h => hnd.1 (h ▸ hz)
        exact (List.mem_erase_of_ne hzx).mpr (hsub z (List.mem_cons_of_mem x hz))
      have hlen_er : (l2.erase x).length = l2.length - 1 := List.length_erase_of_mem hx_l2
      have hy_er : y ∈ l2.erase x := (List.mem_erase_of_ne hyx).mpr hy
      exact list_sub_nodup_mem_of_length_le xs (l2.erase x) hnd.2 hxs_sub
        (by simp only [List.length_cons] at hlen; omega) y hy_er

private theorem list_countP_eq_length_filter {α : Type} (p : α → Bool) (l : List α) :
    l.countP p = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.countP_cons, List.filter_cons]
    cases p a <;> simp [ih]

private theorem list_nodup_filter {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], h => h
  | a :: l, h => by
    have ha : a ∉ l := (List.nodup_cons.mp h).1
    have hl : l.Nodup := (List.nodup_cons.mp h).2
    rw [List.filter_cons]
    split
    · exact List.nodup_cons.mpr ⟨fun hm => ha (List.mem_filter.mp hm).1, list_nodup_filter p hl⟩
    · exact list_nodup_filter p hl

private theorem list_nodup_map_on {α β : Type} (f : α → β) :
    ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, h => by
    have ha : a ∉ l := (List.nodup_cons.mp h).1
    have hl : l.Nodup := (List.nodup_cons.mp h).2
    have hinj_l : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := fun x hx y hy =>
      hinj x (List.mem_cons.mpr (Or.inr hx)) y (List.mem_cons.mpr (Or.inr hy))
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, list_nodup_map_on f hinj_l hl⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨b, hb_mem, hb_eq⟩ := hm
    have hab : b = a :=
      hinj b (List.mem_cons.mpr (Or.inr hb_mem)) a (List.mem_cons.mpr (Or.inl rfl)) hb_eq
    subst hab
    exact ha hb_mem

private theorem mem_of_mem_dropLast {α : Type} {x : α} :
    ∀ {l : List α}, x ∈ l.dropLast → x ∈ l
  | [], h => by cases h
  | [_], h => by cases h
  | a :: b :: t, h => by
    change x ∈ a :: (b :: t).dropLast at h
    rcases List.mem_cons.mp h with rfl | ht
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (mem_of_mem_dropLast ht))

private theorem nat_pair_beq_swap (x1 x2 y1 y2 : Nat) :
    ((x1 == y1 && x2 == y2) || (x1 == y2 && x2 == y1)) =
    (((y1, y2) == (x1, x2)) || ((y2, y1) == (x1, x2))) := by
  by_cases h11 : x1 = y1 <;> by_cases h22 : x2 = y2 <;>
    by_cases h12 : x1 = y2 <;> by_cases h21 : x2 = y1 <;> by_cases hy : y1 = y2
  all_goals simp [h11, h22, h12, h21, hy, beq_false_of_ne, Ne.symm]

private theorem nat_beq_eq_beq (x y : Nat) : x.beq y = (x == y) := by
  by_cases h : x = y
  · subst h
    simp
  · have hf : x.beq y = false := Bool.eq_false_iff.mpr fun ht => h (Nat.beq_eq.mp ht)
    rw [hf, beq_false_of_ne h]

/-- `FastConfEquivBase.isContractPair` agrees pointwise with `Reducibility.isContractEdge`. -/
theorem isContractPair_eq_isContractEdge (ce : List (Nat × Nat)) (a b : Nat) :
    isContractPair ce a b = isContractEdge ce a b := by
  induction ce with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨p1, p2⟩
    have hL : isContractPair ((p1, p2) :: ps) a b =
        (((p1 == a && p2 == b) || (p1 == b && p2 == a)) || isContractPair ps a b) := by
      simp only [isContractPair, Bool.or_assoc, nat_beq_eq_beq]
    have hR : isContractEdge ((p1, p2) :: ps) a b =
        ((((a, b) == (p1, p2)) || ((b, a) == (p1, p2))) || isContractEdge ps a b) := by
      simp only [isContractEdge, List.contains_cons]
      cases (a, b) == (p1, p2) <;> cases (b, a) == (p1, p2) <;>
        cases ps.contains (a, b) <;> cases ps.contains (b, a) <;> rfl
    rw [hL, hR, nat_pair_beq_swap, ih]

private theorem node_invariant_iter_eq (T : Hypermap) (col : T.Dart → Color)
    (h_inv : ∀ d : T.Dart, col (T.node.f d) = col d) :
    ∀ (m : Nat) (y : T.Dart), col (Hypermap.Perm.iter T.node m y) = col y
  | 0, _ => rfl
  | m + 1, y => by
    rw [Hypermap.Perm.iter_succ_right, node_invariant_iter_eq T col h_inv m (T.node.f y), h_inv]

/-- If `col` is invariant under `T.node.f`, it takes identical colors on every pair of darts
    in the same `T.node` orbit. -/
theorem node_invariant_sameVertex_eq (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (col : T.Dart → Color) (h_inv : ∀ d : T.Dart, col (T.node.f d) = col d)
    {x y : T.Dart} (hsv : sameVertex T x y fuel = true) :
    col x = col y := by
  have hmem : x ∈ getOrbit T.node fuel y :=
    (sameVertex_iff_mem_getOrbit T darts h_all h_len y x).mp hsv
  obtain ⟨m, _, rfl⟩ := (mem_getOrbit_iff_exists_iter T darts h_all h_len T.node y x).mp hmem
  exact node_invariant_iter_eq T col h_inv m y

private theorem face_cube_of_faceDegree_eq_three
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_tri : ∀ d : T.Dart, d ∈ darts → faceDegree T d darts.length = 3)
    (x : T.Dart) :
    T.face.f (T.face.f (T.face.f x)) = x := by
  have h3 : (getOrbit T.face darts.length x).length = 3 := h_tri x (h_all x)
  have hper := _root_.Hypermap.perm_iter_length_getOrbit_eq_self_of_complete
    T.face darts h_all (Nat.le_refl darts.length) x
  rw [h3] at hper
  simpa [_root_.Hypermap.Perm.iter] using hper

end FinitePigeonholeAndContractHelpers

section CorrespondingProjectionSection

/-- RSST `(3.3)`–`(3.4)` & `(3.6)` faithful free-completion projection of configuration `c`
    into triangulation `T` enumerated by `darts`:
    - `emb` realizes every configuration vertex as a dart representative and every interior
      adjacency as an oriented edge dart;
    - `ring_edge_adj` witnesses adjacency along the boundary cycle of `c`;
    - `int_dart_bij` states that `emb.dart u` maps `c`-neighbors of any interior vertex `u`
      surjectively (hence bijectively) onto the full `T.node` orbit of `emb.rep u`;
    - `adj_symm` and `contract_*` record symmetry and RSST `(3.6)` contract safety. -/
structure CorrespondingProjection (c : Configuration) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) where
  emb : TriangulationEmbedding c T darts
  ring_edge_adj : ∀ x, x < c.ringSize → 0 < c.ringSize →
    areAdjacentVertices T (emb.rep x) (emb.rep ((x + 1) % c.ringSize)) darts.length = true
  int_dart_bij : ∀ u, c.ringSize ≤ u → u < c.totalNodes → ∀ d : T.Dart,
    sameVertex T d (emb.rep u) darts.length = true →
    ∃ v < c.totalNodes, c.adj u v = true ∧ emb.dart u v = d
  adj_symm : ∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = c.adj j i
  contract_valid : ∀ uv ∈ c.contractEdges,
    uv.1 < c.totalNodes ∧ uv.2 < c.totalNodes ∧ uv.1 ≠ uv.2 ∧
    c.adj uv.1 uv.2 = true ∧ ¬ (uv.1 < c.ringSize ∧ uv.2 < c.ringSize)
  contract_ring_deg : ∀ x < c.ringSize,
    (c.contractEdges.filter fun p => p.1 == x || p.2 == x).length ≤ 1
  contract_no_shortcut : ∀ x < c.totalNodes, ∀ y < c.totalNodes,
    ContractReach c.contractEdges x y → c.adj x y = true → isContractEdge c.contractEdges x y = true

/-- RSST `(3.4)` cyclic consistency of ring-interior fans along the boundary ring of `rc` in `T`. -/
def RingFanProjectionConsistent (rc : FastReducer.RConf) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (e : TriangulationEmbedding (configOfRConf rc) T darts) : Prop :=
  ∀ x (hx : x < rc.r) (hx_adj : x < rc.adj.size),
    let fans := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast
    let nextR := (x + 1) % rc.r
    fans ≠ [] ∧
    (∀ k (hk : k + 1 < fans.length),
      T.edge.f (e.dart (fans[k + 1]'(by omega)) x) =
        (nodePermOriented T e.orient).f (T.edge.f (e.dart (fans[k]'(by omega)) x))) ∧
    (∀ hf0 : 0 < fans.length,
      e.dart (fans[0]'hf0) nextR = (nodePermOriented T e.orient).f (e.dart (fans[0]'hf0) x)) ∧
    (∀ (hnext_adj : nextR < rc.adj.size) (hf0 : 0 < fans.length),
      ((rc.adj[nextR]'hnext_adj).toList.drop 1).dropLast.getLast? = some (fans[0]'hf0)) ∧
    areAdjacentVertices T (e.rep x) (e.rep nextR) darts.length = true

private theorem matchesConfCycle_adj_toList_length {h : Nat} (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (u : Nat) (hur : (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤ u)
    (hun : u < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes) :
    ∃ (hu_adj : u < (parsedRConfList[h]'hlen).adj.size),
      (parsedRConfList[h]'hlen).adj[u].toList.length ≥ 1 := by
  have hhdr := fastConf_equiv_header h hh
  have hadj := fastConf_equiv_adj h hh
  have hiv := fastConf_equiv_intVerts h hh
  have htot := hhdr.2.2.2.2.1
  have hu_adj : u < (parsedRConfList[h]'hlen).adj.size := by
    rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; exact hun
  refine ⟨hu_adj, ?_⟩
  have hiu : u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize <
      (configOfRConf (parsedRConfList[h]'hlen)).interiorSize := by
    have hhdr := fastConf_equiv_header h hh
    have hr := hhdr.2.2.1
    have hi := hhdr.2.2.2.1
    have hn := hhdr.2.2.2.2.1
    omega
  have hiv_u := hiv (u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize) hiu
  have hdeg_ge5 := hiv_u.2.1
  have hc_n : (configOfRConf (parsedRConfList[h]'hlen)).ringSize +
      (u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize) = u := by omega
  have hlen_eq : ((lookupFastConfRec h).intVerts[u -
      (configOfRConf (parsedRConfList[h]'hlen)).ringSize]'(by
        rw [hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hiu)).cyc.length =
      (parsedRConfList[h]'hlen).adj[u].toList.length := by
    simpa only [hc_n] using hiv_u.2.2.2.2.2.2.2.1
  omega

/-- RSST `(3.4)` ring-fan consistency theorem: every matched triangulation embedding of
    configuration `h < 633` satisfies `RingFanProjectionConsistent` along every ring edge
    and interior fan. -/
theorem ring_fan_projection_consistent (h : Nat) (hh : h < 633)
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_tri : ∀ d : T.Dart, d ∈ darts → faceDegree T d darts.length = 3)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (e : TriangulationEmbedding (configOfRConf (parsedRConfList[h]'hlen)) T darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) T darts e) :
    RingFanProjectionConsistent (parsedRConfList[h]'hlen) T darts e := by
  have h_tri3 : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x :=
    face_cube_of_faceDegree_eq_three T darts h_all h_tri
  have hhdr := fastConf_equiv_header h hh
  have hiv := fastConf_equiv_intVerts h hh
  have hring := fastConf_equiv_ring_and_fans h hh
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  have hr_eq : c.ringSize = rc.r := hhdr.2.2.1
  have hr6 : 6 ≤ c.ringSize := hhdr.2.2.2.2.2.1
  have hint_sz : (lookupFastConfRec h).intVerts.length = c.interiorSize :=
    hhdr.2.2.2.2.2.2.2.2.2.2.1
  intro x hx hx_adj
  let fans := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast
  let nextR := (x + 1) % rc.r
  have hrf := fastConf_geom_ring_fans h hh x hx
  have hfans_sub : ∀ v ∈ fans, c.ringSize ≤ v ∧ v < c.totalNodes := by
    intro v hv
    have hv_ge : c.ringSize ≤ v := (hring.2 x (hr_eq ▸ hx)).2.2.2.1 v hv
    have hv_adj : v ∈ (rc.adj[x]'hx_adj).toList := List.mem_of_mem_drop (mem_of_mem_dropLast hv)
    have hx_tot : x < c.totalNodes := Nat.lt_of_lt_of_le (hr_eq ▸ hx) (Nat.le_add_right _ _)
    have hv_tot : v < c.totalNodes := ((fastConf_equiv_adj h hh).1 x hx_tot).2 v hv_adj |>.1
    exact ⟨hv_ge, hv_tot⟩
  refine ⟨hrf.1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hk_lt : k < fans.length := Nat.lt_of_succ_lt hk
    obtain ⟨fk, hfk⟩ : ∃ fk, fk = fans[k]'hk_lt := ⟨_, rfl⟩
    obtain ⟨fk1, hfk1⟩ : ∃ fk1, fk1 = fans[k + 1]'hk := ⟨_, rfl⟩
    obtain ⟨ivk, hivk_mem, ivk1, hivk1_mem, hivk_u, hivk1_u, hcp_k, hcp_k1⟩ := hrf.2.2.2.2 k hk
    obtain ⟨jk, hjk_lt, hjk_eq⟩ := List.mem_iff_getElem.mp hivk_mem
    obtain ⟨jk1, hjk1_lt, hjk1_eq⟩ := List.mem_iff_getElem.mp hivk1_mem
    have hjk_c : jk < c.interiorSize := by rw [← hint_sz]; exact hjk_lt
    have hjk1_c : jk1 < c.interiorSize := by rw [← hint_sz]; exact hjk1_lt
    have hivk_spec := hiv jk hjk_c
    have hivk1_spec := hiv jk1 hjk1_c
    have hfk_bd : c.ringSize ≤ fk ∧ fk < c.totalNodes :=
      hfk ▸ hfans_sub (fans[k]'hk_lt) (List.getElem_mem _)
    have hfk1_bd : c.ringSize ≤ fk1 ∧ fk1 < c.totalNodes :=
      hfk1 ▸ hfans_sub (fans[k + 1]'hk) (List.getElem_mem _)
    have hfk_eq' : (List.drop 1 (parsedRConfList[h]'hlen).adj[x].toList).dropLast[k]'hk_lt = fk :=
      hfk.symm
    have hfk1_eq' : (List.drop 1 (parsedRConfList[h]'hlen).adj[x].toList).dropLast[k + 1]'hk = fk1 :=
      hfk1.symm
    rw [hfk_eq'] at hivk_u hcp_k1
    rw [hfk1_eq'] at hivk1_u hcp_k
    have hjk_c_val : c.ringSize + jk = fk := by
      have hu : (lookupFastConfRec h).intVerts[jk].u = c.ringSize + jk + 1 := hivk_spec.1
      rw [hjk_eq] at hu; rw [hu] at hivk_u; omega
    have hjk1_c_val : c.ringSize + jk1 = fk1 := by
      have hu : (lookupFastConfRec h).intVerts[jk1].u = c.ringSize + jk1 + 1 := hivk1_spec.1
      rw [hjk1_eq] at hu; rw [hu] at hivk1_u; omega
    have hcr : (configOfRConf (parsedRConfList[h]'hlen)).ringSize = c.ringSize := rfl
    have hturn_k := matchesConfCycle_of_mem_cyc hh hlen hmc hjk_c hjk_lt (hjk_eq ▸ hcp_k)
    have hturn_k1 := matchesConfCycle_of_mem_cyc hh hlen hmc hjk1_c hjk1_lt (hjk1_eq ▸ hcp_k1)
    rw [hcr, hjk_c_val, Nat.add_sub_cancel, Nat.add_sub_cancel] at hturn_k
    rw [hcr, hjk1_c_val, Nat.add_sub_cancel, Nat.add_sub_cancel] at hturn_k1
    have hadj_k_k1 : c.adj fk fk1 = true := by
      have hic := hivk_spec.2.2.2.2.2.2.2.2.2 { v := fk1 + 1, w := x + 1 } (hjk_eq ▸ hcp_k)
      have hic_adj := hic.2.2.2.2.1
      change c.adj (c.ringSize + jk) (fk1 + 1 - 1) = true at hic_adj
      rw [hjk_c_val, Nat.add_sub_cancel] at hic_adj
      exact hic_adj
    have hflip : T.edge.f (e.dart fk1 fk) = e.dart fk fk1 := by
      rw [← e.int_edge_flip fk fk1 hfk_bd.1 hfk_bd.2 hfk1_bd.1 hfk1_bd.2 hadj_k_k1, T.edge_edge]
    have htri_edge := tri_fan_turn_edge T h_tri3 e.orient (e.dart fk1 x)
    rw [← hturn_k1, hflip, ← hturn_k] at htri_edge
    have hinv_f := congrArg (nodePermOriented T e.orient).f htri_edge
    rw [(nodePermOriented T e.orient).right_inv] at hinv_f
    rw [← hfk, ← hfk1]
    exact hinv_f.symm
  · intro hf0
    obtain ⟨f0, hf0_eq⟩ : ∃ f0, f0 = fans[0]'hf0 := ⟨_, rfl⟩
    have hhd : fans.head? = some f0 := by
      have hhd' := List.head?_eq_some_head (hrf.1)
      rw [List.head_eq_getElem] at hhd'
      rw [hf0_eq]; exact hhd'
    obtain ⟨iv1, hiv1_mem, hiv1_u, hcp1⟩ := hrf.2.2.1 _ hhd
    obtain ⟨j1, hj1_lt, hj1_eq⟩ := List.mem_iff_getElem.mp hiv1_mem
    have hj1_c : j1 < c.interiorSize := by rw [← hint_sz]; exact hj1_lt
    have hiv1_spec := hiv j1 hj1_c
    have hj1_c_val : c.ringSize + j1 = f0 := by
      have hu : (lookupFastConfRec h).intVerts[j1].u = c.ringSize + j1 + 1 := hiv1_spec.1
      rw [hj1_eq] at hu; rw [hu] at hiv1_u; omega
    have hcr : (configOfRConf (parsedRConfList[h]'hlen)).ringSize = c.ringSize := rfl
    have hturn := matchesConfCycle_of_mem_cyc hh hlen hmc hj1_c hj1_lt (hj1_eq ▸ hcp1)
    rw [hcr, hj1_c_val, Nat.add_sub_cancel, Nat.add_sub_cancel] at hturn
    rw [← hf0_eq]
    exact hturn
  · intro hnext_adj hf0
    have hhd : fans.head? = some (fans[0]'hf0) := by
      have hhd' := List.head?_eq_some_head (hrf.1)
      rwa [List.head_eq_getElem] at hhd'
    exact hrf.2.1.trans hhd
  · have hx_c : x < c.ringSize := hr_eq ▸ hx
    have hnext_r : (x + 1) % rc.r < rc.r := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le x) hx)
    have hnext_c : nextR < c.ringSize := by
      change (x + 1) % rc.r < c.ringSize; rw [hr_eq]; exact hnext_r
    have hnext_tot : nextR < c.totalNodes := Nat.lt_of_lt_of_le hnext_c (Nat.le_add_right _ _)
    have hx_tot : x < c.totalNodes := Nat.lt_of_lt_of_le hx_c (Nat.le_add_right _ _)
    have hadj_x_next : c.adj x nextR = true := by
      rw [(hring.1 x hx_c nextR hnext_c)]
      right; change (x + 1) % rc.r = (x + 1) % c.ringSize; rw [hr_eq]
    exact e.adj_rep_edge x nextR hx_tot hnext_tot hadj_x_next

/-- Surjectivity/bijectivity of `e.dart u` onto `getOrbit T.node darts.length (e.rep u)`
    for any `TriangulationEmbedding e` of configuration `h < 633`. -/
theorem triangulationEmbedding_int_dart_bij (h : Nat) (hh : h < 633)
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (e : TriangulationEmbedding (configOfRConf (parsedRConfList[h]'hlen)) T darts) :
    let c := configOfRConf (parsedRConfList[h]'hlen)
    ∀ u, c.ringSize ≤ u → u < c.totalNodes → ∀ d : T.Dart,
      sameVertex T d (e.rep u) darts.length = true →
      ∃ v < c.totalNodes, c.adj u v = true ∧ e.dart u v = d := by
  intro c u hur hun d hsv_d
  let _ := hh
  let nbrs := (List.range c.totalNodes).filter (fun w => c.adj u w)
  have hnbrs_nodup : nbrs.Nodup := list_nodup_filter _ List.nodup_range
  have hinj_map : ∀ a ∈ nbrs, ∀ b ∈ nbrs, e.dart u a = e.dart u b → a = b := by
    intro a ha b hb heq
    rw [List.mem_filter, List.mem_range] at ha hb
    by_cases hab : a = b
    · exact hab
    · exact False.elim (e.int_inj_neighbor u hur hun a b ha.1 hb.1 ha.2 hb.2 hab heq)
  have hmap_nodup : (nbrs.map (e.dart u)).Nodup :=
    list_nodup_map_on (e.dart u) hinj_map hnbrs_nodup
  have hmap_sub : ∀ y ∈ nbrs.map (e.dart u), y ∈ getOrbit T.node darts.length (e.rep u) := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨w, hw_nbr, rfl⟩ := hy
    rw [List.mem_filter, List.mem_range] at hw_nbr
    have hsv_w := e.dart_same_vertex_rep u hur hun w hw_nbr.1 hw_nbr.2
    exact (sameVertex_iff_mem_getOrbit T darts h_all (Nat.le_refl _) (e.rep u) (e.dart u w)).mp hsv_w
  have hlen_orb : (getOrbit T.node darts.length (e.rep u)).length ≤
      (nbrs.map (e.dart u)).length := by
    have hdeg := e.int_degree_match u hur hun
    change (getOrbit T.node darts.length (e.rep u)).length =
      (List.range c.totalNodes).countP (fun w => c.adj u w) at hdeg
    rw [hdeg, list_countP_eq_length_filter, List.length_map]
    exact Nat.le_refl _
  have hd_orb : d ∈ getOrbit T.node darts.length (e.rep u) :=
    (sameVertex_iff_mem_getOrbit T darts h_all (Nat.le_refl _) (e.rep u) d).mp hsv_d
  have hd_map : d ∈ nbrs.map (e.dart u) :=
    list_sub_nodup_mem_of_length_le (nbrs.map (e.dart u))
      (getOrbit T.node darts.length (e.rep u)) hmap_nodup hmap_sub hlen_orb d hd_orb
  rw [List.mem_map] at hd_map
  obtain ⟨v, hv_nbr, hv_eq⟩ := hd_map
  rw [List.mem_filter, List.mem_range] at hv_nbr
  exact ⟨v, hv_nbr.1, hv_nbr.2, hv_eq⟩

/-- Constructive RSST `(3.3)–(3.4)` projection from any `TriangulationEmbedding` of `h < 633`. -/
def correspondingProjectionOfEmbedding (h : Nat) (hh : h < 633)
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (e : TriangulationEmbedding (configOfRConf (parsedRConfList[h]'hlen)) T darts) :
    CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) T darts :=
  let c := configOfRConf (parsedRConfList[h]'hlen)
  { emb := e
    ring_edge_adj := by
      intro x hx hrpos
      have hx_tot : x < c.totalNodes :=
        Nat.lt_of_lt_of_le (show x < c.ringSize from hx) (Nat.le_add_right _ _)
      have hnext_r : (x + 1) % c.ringSize < c.ringSize := Nat.mod_lt _ (by dsimp only [c]; exact hrpos)
      have hnext_tot : (x + 1) % c.ringSize < c.totalNodes :=
        Nat.lt_of_lt_of_le hnext_r (Nat.le_add_right _ _)
      have hadj_x_next : c.adj x ((x + 1) % c.ringSize) = true := by
        rw [(fastConf_equiv_ring_and_fans h hh).1 x hx _ hnext_r]
        exact Or.inr rfl
      exact e.adj_rep_edge x ((x + 1) % c.ringSize) hx_tot hnext_tot hadj_x_next
    int_dart_bij := triangulationEmbedding_int_dart_bij h hh T darts h_all hlen e
    adj_symm := fun i j hi hj => ((fastConf_equiv_adj h hh).2.2.1 i hi j hj).1
    contract_valid := by
      intro uv huv
      have hcs := (fastConf_equiv_contract_safe h hh).2.2.1 uv huv
      exact hcs
    contract_ring_deg := (fastConf_equiv_contract_safe h hh).2.2.2.1
    contract_no_shortcut := by
      intro x hx y hy hreach hadj_xy
      rw [← isContractPair_eq_isContractEdge]
      exact (fastConf_equiv_contract_safe h hh).2.2.2.2.2 x hx y hy hreach hadj_xy }

/-- Matched `TriangulationEmbedding` + `MatchesConfCycle` lifts directly to both
    `CorrespondingProjection` and `RingFanProjectionConsistent`. -/
theorem appearsInTriangulation_matched_implies_correspondingProjection
    (h : Nat) (hh : h < 633)
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_tri : ∀ d : T.Dart, d ∈ darts → faceDegree T d darts.length = 3)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (e : TriangulationEmbedding (configOfRConf (parsedRConfList[h]'hlen)) T darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) T darts e) :
    Nonempty (CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) T darts) ∧
    RingFanProjectionConsistent (parsedRConfList[h]'hlen) T darts e :=
  ⟨⟨correspondingProjectionOfEmbedding h hh T darts h_all hlen e⟩,
    ring_fan_projection_consistent h hh T darts h_all h_tri hlen e hmc⟩

/-- Any unavoidable configuration appearing via `AppearsInTriangulation` yields a faithful
    RSST `(3.3)–(3.4)` `CorrespondingProjection`. -/
theorem appearsInTriangulation_implies_correspondingProjection
    (c : Configuration) (hc : c ∈ theUnavoidableSet)
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts) :
    AppearsInTriangulation c T darts → Nonempty (CorrespondingProjection c T darts) := by
  intro ⟨e⟩
  obtain ⟨h, hlt, heq⟩ := Array.mem_iff_getElem.mp hc
  have hh : h < 633 := by rw [← theUnavoidableSet_size]; exact hlt
  have hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh
  have hc_eq : c = configOfRConf (parsedRConfList[h]'hlen) := by
    rw [← heq, theUnavoidableSet_getElem h hh]
  subst hc_eq
  exact ⟨correspondingProjectionOfEmbedding h hh T darts h_all hlen e⟩

end CorrespondingProjectionSection

section ContractionPullbackAndTriads

/-- Canonical dart in `T` representing a contracted configuration edge `p = (a, b)`: since
    `¬ (a < c.ringSize ∧ b < c.ringSize)`, at least one endpoint is interior. -/
def contractEdgeDart {c : Configuration} {T : Hypermap} [DecidableEq T.Dart]
    {darts : List T.Dart} (e : TriangulationEmbedding c T darts) (p : Nat × Nat) : T.Dart :=
  if c.ringSize ≤ p.1 then e.dart p.1 p.2 else e.dart p.2 p.1

/-- Image of `c.contractEdges` under `e` in `T.Dart`. -/
def mappedContractDarts {c : Configuration} {T : Hypermap} [DecidableEq T.Dart]
    {darts : List T.Dart} (e : TriangulationEmbedding c T darts) : List T.Dart :=
  c.contractEdges.map (contractEdgeDart e)

/-- A valid 4-coloring of the quotient triangulation `T / M`, where `M` is the list of
    contracted edge darts: constant on every vertex (`node_invariant`), equal across
    contracted edges (`contract_same`), and proper across all remaining edges (`edge_proper`). -/
structure VertexColoringMod (T : Hypermap) (M : List T.Dart) where
  color : T.Dart → Color
  node_invariant : ∀ d : T.Dart, color (T.node.f d) = color d
  contract_same : ∀ d ∈ M, color (T.edge.f d) = color d
  edge_proper : ∀ d : T.Dart, d ∉ M → T.edge.f d ∉ M → color (T.edge.f d) ≠ color d

/-- Every `VertexColoringMod H.dual M` determines a face-invariant, `M`-contracted, remaining-edge
    proper 4-coloring on the primal hypermap `H`. -/
theorem vertexColoringMod_to_faceColoringMod_dual {H : Hypermap} {M : List H.Dart}
    (col : VertexColoringMod H.dual M) :
    (∀ d : H.Dart, col.color (H.face.f d) = col.color d) ∧
    (∀ d ∈ M, col.color (H.edge.f d) = col.color d) ∧
    (∀ d : H.Dart, d ∉ M → H.edge.f d ∉ M → col.color (H.edge.f d) ≠ col.color d) := by
  refine ⟨?_, col.contract_same, col.edge_proper⟩
  intro d
  have h := col.node_invariant (H.face.f d)
  change col.color (H.face.inv (H.face.f d)) = col.color (H.face.f d) at h
  rw [H.face.left_inv] at h
  exact h.symm

theorem contractEdgeDart_canon
    {c : Configuration} {T : Hypermap} [DecidableEq T.Dart] {darts : List T.Dart}
    (p : CorrespondingProjection c T darts)
    {q : Nat × Nat} (hq_mem : q ∈ c.contractEdges) :
    ∃ qA qB : Nat, c.ringSize ≤ qA ∧ qA < c.totalNodes ∧ qB < c.totalNodes ∧
      c.adj qA qB = true ∧ ((qA, qB) ∈ c.contractEdges ∨ (qB, qA) ∈ c.contractEdges) ∧
      contractEdgeDart p.emb q = p.emb.dart qA qB := by
  rcases q with ⟨q1, q2⟩
  obtain ⟨hq1, hq2, _, hq_adj, hqnrr⟩ := p.contract_valid (q1, q2) hq_mem
  by_cases hq1r : c.ringSize ≤ q1
  · refine ⟨q1, q2, hq1r, hq1, hq2, hq_adj, Or.inl hq_mem, ?_⟩
    simp [contractEdgeDart, hq1r]
  · have hq2r : c.ringSize ≤ q2 := by omega
    have hq_adj21 : c.adj q2 q1 = true := by rw [p.adj_symm q2 q1 hq2 hq1]; exact hq_adj
    refine ⟨q2, q1, hq2r, hq2, hq1, hq_adj21, Or.inr hq_mem, ?_⟩
    simp [contractEdgeDart, hq1r]

private theorem int_dart_not_in_mappedContractDarts
    (c : Configuration) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (p : CorrespondingProjection c T darts)
    {u w : Nat} (hur : c.ringSize ≤ u) (hun : u < c.totalNodes)
    (hwn : w < c.totalNodes) (hadj_uw : c.adj u w = true)
    (hnc_uw : isContractEdge c.contractEdges u w = false) :
    p.emb.dart u w ∉ mappedContractDarts p.emb ∧
      T.edge.f (p.emb.dart u w) ∉ mappedContractDarts p.emb := by
  have h_not_contract_dart :
      ∀ {u0 w0 : Nat} (hu0r : c.ringSize ≤ u0) (hu0n : u0 < c.totalNodes) (hw0n : w0 < c.totalNodes)
        (hadj0 : c.adj u0 w0 = true) (hnc0 : isContractEdge c.contractEdges u0 w0 = false)
        {qA qB : Nat} (hqAr : c.ringSize ≤ qA) (hqAn : qA < c.totalNodes) (hqBn : qB < c.totalNodes)
        (hqAdj : c.adj qA qB = true) (hqpair : (qA, qB) ∈ c.contractEdges ∨ (qB, qA) ∈ c.contractEdges),
        p.emb.dart qA qB = p.emb.dart u0 w0 → False := by
    intro u0 w0 hu0r hu0n hw0n hadj0 hnc0 qA qB hqAr hqAn hqBn hqAdj hqpair hdart
    have hsv_u0 := p.emb.dart_same_vertex_rep u0 hu0r hu0n w0 hw0n hadj0
    have hsv_qA := p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
    rw [hdart] at hsv_qA
    have hsv_u0_sym : sameVertex T (p.emb.rep u0) (p.emb.dart u0 w0) darts.length = true := by
      rw [sameVertex_symm_of_complete T darts h_all (Nat.le_refl _)]
      exact hsv_u0
    have hsv_uq : sameVertex T (p.emb.rep u0) (p.emb.rep qA) darts.length = true :=
      sameVertex_trans_of_complete T darts h_all (Nat.le_refl _) hsv_u0_sym hsv_qA
    have huq : u0 = qA := by
      by_cases hne : u0 = qA
      · exact hne
      · have hf := p.emb.int_distinct u0 qA hu0r hu0n hqAr hqAn hne
        rw [hsv_uq] at hf; cases hf
    rw [huq] at hadj0 hnc0
    have hwq : w0 = qB := by
      by_cases hne : w0 = qB
      · exact hne
      · have hdart' : p.emb.dart qA w0 = p.emb.dart qA qB := by
          have := hdart.symm
          rwa [huq] at this
        exact False.elim (p.emb.int_inj_neighbor qA hqAr hqAn w0 qB hw0n hqBn hadj0 hqAdj hne hdart')
    rw [hwq] at hnc0
    have hce_t : isContractEdge c.contractEdges qA qB = true := by
      rcases hqpair with hm | hm <;>
        simp [isContractEdge, hm]
    rw [hnc0] at hce_t
    cases hce_t
  refine ⟨?_, ?_⟩
  · intro hmem
    rw [mappedContractDarts, List.mem_map] at hmem
    obtain ⟨q, hq_mem, hq_eq⟩ := hmem
    obtain ⟨qA, qB, hqAr, hqAn, hqBn, hqAdj, hqpair, hq_d⟩ := contractEdgeDart_canon p hq_mem
    rw [hq_d] at hq_eq
    exact h_not_contract_dart hur hun hwn hadj_uw hnc_uw hqAr hqAn hqBn hqAdj hqpair hq_eq
  · intro hmem
    rw [mappedContractDarts, List.mem_map] at hmem
    obtain ⟨q, hq_mem, hq_eq⟩ := hmem
    obtain ⟨qA, qB, hqAr, hqAn, hqBn, hqAdj, hqpair, hq_d⟩ := contractEdgeDart_canon p hq_mem
    rw [hq_d] at hq_eq
    have hsv_w := p.emb.dart_edge_same_vertex_rep u hur hun w hwn hadj_uw
    have hsv_qA := p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
    rw [hq_eq] at hsv_qA
    have hsv_w_sym : sameVertex T (p.emb.rep w) (T.edge.f (p.emb.dart u w)) darts.length = true := by
      rw [sameVertex_symm_of_complete T darts h_all (Nat.le_refl _)]
      exact hsv_w
    have hsv_wq : sameVertex T (p.emb.rep w) (p.emb.rep qA) darts.length = true :=
      sameVertex_trans_of_complete T darts h_all (Nat.le_refl _) hsv_w_sym hsv_qA
    have hwr : c.ringSize ≤ w := by
      by_cases hle : c.ringSize ≤ w
      · exact hle
      · have hwr' : w < c.ringSize := Nat.lt_of_not_le hle
        have hf := p.emb.int_ring_distinct qA w hqAr hqAn hwr'
        rw [sameVertex_symm_of_complete T darts h_all (Nat.le_refl _)] at hsv_wq
        rw [hsv_wq] at hf
        cases hf
    have hadj_wu : c.adj w u = true := by rw [p.adj_symm w u hwn hun]; exact hadj_uw
    have hnc_wu : isContractEdge c.contractEdges w u = false := by
      simp only [isContractEdge, Bool.or_eq_false_iff] at hnc_uw ⊢
      exact ⟨hnc_uw.2, hnc_uw.1⟩
    have hflip := p.emb.int_edge_flip u w hur hun hwr hwn hadj_uw
    rw [hflip] at hq_eq
    exact h_not_contract_dart hwr hwn hun hadj_wu hnc_wu hqAr hqAn hqBn hqAdj hqpair hq_eq

/-- RSST `(3.5)` pullback theorem: any valid 4-coloring `col` of `T / mappedContractDarts p.emb`
    pulls back along `p.emb.rep` to a boundary coloring of `c` satisfying `extendsToContracted`. -/
theorem pullback_mod_coloring_extendsToContracted
    (c : Configuration) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (p : CorrespondingProjection c T darts)
    (col : VertexColoringMod T (mappedContractDarts p.emb)) :
    extendsToContracted c (fun i => col.color (p.emb.rep i)) := by
  refine ⟨fun u => col.color (p.emb.rep u), fun _ _ => rfl, ?_, ?_⟩
  · intro uv huv
    obtain ⟨h1, h2, _, hadj12, hnrr⟩ := p.contract_valid uv huv
    refine ⟨h1, h2, ?_⟩
    have hd_mem : contractEdgeDart p.emb uv ∈ mappedContractDarts p.emb :=
      List.mem_map_of_mem huv
    have hcol_e := col.contract_same (contractEdgeDart p.emb uv) hd_mem
    dsimp only
    by_cases h1r : c.ringSize ≤ uv.1
    · have hsv1 := p.emb.dart_same_vertex_rep uv.1 h1r h1 uv.2 h2 hadj12
      have hsv2 := p.emb.dart_edge_same_vertex_rep uv.1 h1r h1 uv.2 h2 hadj12
      have hc1 : col.color (contractEdgeDart p.emb uv) = col.color (p.emb.rep uv.1) := by
        dsimp [contractEdgeDart]; rw [if_pos h1r]
        exact node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hsv1
      have hc2 : col.color (T.edge.f (contractEdgeDart p.emb uv)) = col.color (p.emb.rep uv.2) := by
        dsimp [contractEdgeDart]; rw [if_pos h1r]
        exact node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hsv2
      rw [← hc1, ← hc2, hcol_e]
    · have h2r : c.ringSize ≤ uv.2 := by omega
      have hadj21 : c.adj uv.2 uv.1 = true := by
        rw [p.adj_symm uv.2 uv.1 h2 h1]; exact hadj12
      have hsv2 := p.emb.dart_same_vertex_rep uv.2 h2r h2 uv.1 h1 hadj21
      have hsv1 := p.emb.dart_edge_same_vertex_rep uv.2 h2r h2 uv.1 h1 hadj21
      have hc2 : col.color (contractEdgeDart p.emb uv) = col.color (p.emb.rep uv.2) := by
        dsimp [contractEdgeDart]; rw [if_neg h1r]
        exact node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hsv2
      have hc1 : col.color (T.edge.f (contractEdgeDart p.emb uv)) = col.color (p.emb.rep uv.1) := by
        dsimp [contractEdgeDart]; rw [if_neg h1r]
        exact node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hsv1
      rw [← hc1, ← hc2, hcol_e]
  · intro i j hi hj hadj_ij hnc
    dsimp only
    by_cases hir : c.ringSize ≤ i
    · obtain ⟨hnot1, hnot2⟩ := int_dart_not_in_mappedContractDarts c T darts h_all p hir hi hj hadj_ij hnc
      have hprop := col.edge_proper (p.emb.dart i j) hnot1 hnot2
      have hsv1 := p.emb.dart_same_vertex_rep i hir hi j hj hadj_ij
      have hsv2 := p.emb.dart_edge_same_vertex_rep i hir hi j hj hadj_ij
      have hc1 := node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hsv1
      have hc2 := node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hsv2
      rw [hc1, hc2] at hprop
      exact hprop.symm
    · by_cases hjr : c.ringSize ≤ j
      · have hadj_ji : c.adj j i = true := by rw [p.adj_symm j i hj hi]; exact hadj_ij
        have hnc_ji : isContractEdge c.contractEdges j i = false := by
          simp only [isContractEdge, Bool.or_eq_false_iff] at hnc ⊢
          exact ⟨hnc.2, hnc.1⟩
        obtain ⟨hnot1, hnot2⟩ := int_dart_not_in_mappedContractDarts c T darts h_all p hjr hj hi hadj_ji hnc_ji
        have hprop := col.edge_proper (p.emb.dart j i) hnot1 hnot2
        have hsv1 := p.emb.dart_same_vertex_rep j hjr hj i hi hadj_ji
        have hsv2 := p.emb.dart_edge_same_vertex_rep j hjr hj i hi hadj_ji
        have hc1 := node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hsv1
        have hc2 := node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hsv2
        rw [hc1, hc2] at hprop
        exact hprop
      · have hi_r : i < c.ringSize := Nat.lt_of_not_le hir
        have hj_r : j < c.ringSize := Nat.lt_of_not_le hjr
        have hadj_rep := p.emb.adj_rep_edge i j hi hj hadj_ij
        obtain ⟨d, hd_i, hed_j⟩ := (areAdjacentVertices_iff T darts h_all (Nat.le_refl _) _ _).mp hadj_rep
        have hring_dart_not_M : ∀ x : T.Dart,
            (∃ r, r < c.ringSize ∧ sameVertex T x (p.emb.rep r) darts.length = true) →
            x ∉ mappedContractDarts p.emb := by
          intro x ⟨r1, hr1, hxr1⟩ hxM
          rw [mappedContractDarts, List.mem_map] at hxM
          obtain ⟨q, hq_mem, hq_eq⟩ := hxM
          obtain ⟨qA, qB, hqAr, hqAn, hqBn, hqAdj, _, hq_d⟩ := contractEdgeDart_canon p hq_mem
          rw [hq_d] at hq_eq
          have hsv_qA := p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
          rw [hq_eq] at hsv_qA
          have hsv_qA_sym : sameVertex T (p.emb.rep qA) x darts.length = true := by
            rw [sameVertex_symm_of_complete T darts h_all (Nat.le_refl _)]
            exact hsv_qA
          have hbad := sameVertex_trans_of_complete T darts h_all (Nat.le_refl _) hsv_qA_sym hxr1
          have hf := p.emb.int_ring_distinct qA r1 hqAr hqAn hr1
          rw [hbad] at hf
          cases hf
        have hnot1 : d ∉ mappedContractDarts p.emb := hring_dart_not_M d ⟨i, hi_r, hd_i⟩
        have hnot2 : T.edge.f d ∉ mappedContractDarts p.emb := hring_dart_not_M (T.edge.f d) ⟨j, hj_r, hed_j⟩
        have hprop := col.edge_proper d hnot1 hnot2
        have hc1 := node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hd_i
        have hc2 := node_invariant_sameVertex_eq T darts h_all (Nat.le_refl _) col.color col.node_invariant hed_j
        rw [hc1, hc2] at hprop
        exact hprop.symm

/-- RSST `(3.6)` size bound: every unavoidable configuration `h < 633` has at most 4 contract edges. -/
theorem contract_edges_le_four (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh) :
    (configOfRConf (parsedRConfList[h]'hlen)).contractEdges.length ≤ 4 :=
  (fastConf_equiv_contract_safe h hh).2.1

/-- RSST `(3.5)` triangle-clique and contract-sparsity lemma in `T`:
    every triangle `{a, b, d}` of `c` projects to mutually adjacent darts `p.emb.rep a`,
    `p.emb.rep b`, `p.emb.rep d` in `T`, with an interior apex witnessing the facial clique
    in `iv.cyc` and at most one contract edge among `(a, b)`, `(b, d)`, `(a, d)`. -/
theorem correspondingProjection_triangle_clique_and_contract_sparsity
    (h : Nat) (hh : h < 633)
    (T : Hypermap) [DecidableEq T.Dart] (darts : List T.Dart)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) T darts)
    {a b d : Nat}
    (ha : a < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hb : b < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hd : d < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hab : (configOfRConf (parsedRConfList[h]'hlen)).adj a b = true)
    (hbd : (configOfRConf (parsedRConfList[h]'hlen)).adj b d = true)
    (had : (configOfRConf (parsedRConfList[h]'hlen)).adj a d = true) :
    areAdjacentVertices T (p.emb.rep a) (p.emb.rep b) darts.length = true ∧
    areAdjacentVertices T (p.emb.rep b) (p.emb.rep d) darts.length = true ∧
    areAdjacentVertices T (p.emb.rep a) (p.emb.rep d) darts.length = true ∧
    (if isContractEdge (configOfRConf (parsedRConfList[h]'hlen)).contractEdges a b then 1 else 0) +
    (if isContractEdge (configOfRConf (parsedRConfList[h]'hlen)).contractEdges b d then 1 else 0) +
    (if isContractEdge (configOfRConf (parsedRConfList[h]'hlen)).contractEdges a d then 1 else 0) ≤ 1 := by
  have hhdr := fastConf_equiv_header h hh
  have htot : (configOfRConf (parsedRConfList[h]'hlen)).totalNodes = (parsedRConfList[h]'hlen).n :=
    hhdr.2.2.2.2.1
  have htri_cyc := fastConf_geom_tri_clique_in_cyc h hh (htot ▸ ha) (htot ▸ hb) (htot ▸ hd) hab hbd had
  obtain ⟨iv, hiv_mem, hcases⟩ := htri_cyc
  have hcs := (fastConf_equiv_contract_safe h hh).2.2.2.2.1 iv hiv_mem
  have hiv_spec := fastConf_equiv_intVerts h hh
  obtain ⟨iu, hiu_lt, hiu_eq⟩ := List.mem_iff_getElem.mp hiv_mem
  have hiu_c : iu < (configOfRConf (parsedRConfList[h]'hlen)).interiorSize := by
    rw [← hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hiu_lt
  have hiu_u : iv.u = (configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu + 1 := by
    rw [← hiu_eq]; exact (hiv_spec iu hiu_c).1
  have hadj_ab := p.emb.adj_rep_edge a b ha hb hab
  have hadj_bd := p.emb.adj_rep_edge b d hb hd hbd
  have hadj_ad := p.emb.adj_rep_edge a d ha hd had
  refine ⟨hadj_ab, hadj_bd, hadj_ad, ?_⟩
  obtain ⟨ce, hce_def⟩ : ∃ ce, ce = (configOfRConf (parsedRConfList[h]'hlen)).contractEdges :=
    ⟨_, rfl⟩
  have hsym_ce : ∀ u v, isContractPair ce u v = isContractPair ce v u := by
    intro u v
    rw [isContractPair_eq_isContractEdge, isContractPair_eq_isContractEdge]
    simp only [isContractEdge, Bool.or_comm]
  have hrew : ∀ x y, isContractEdge ce x y = isContractPair ce x y :=
    fun x y => (isContractPair_eq_isContractEdge ce x y).symm
  rw [← hce_def, hrew a b, hrew b d, hrew a d]
  rcases hcases with ⟨h_u, hcp⟩ | ⟨h_u, hcp⟩ | ⟨h_u, hcp⟩
  · have ha_eq : iv.u - 1 = a := by omega
    rcases hcp with h1 | h1
    · have hle := hcs _ h1
      dsimp only at hle
      rw [← hce_def, ha_eq, Nat.add_sub_cancel, Nat.add_sub_cancel] at hle
      omega
    · have hle := hcs _ h1
      dsimp only at hle
      rw [← hce_def, ha_eq, Nat.add_sub_cancel, Nat.add_sub_cancel, hsym_ce d b] at hle
      omega
  · have hb_eq : iv.u - 1 = b := by omega
    rcases hcp with h1 | h1
    · have hle := hcs _ h1
      dsimp only at hle
      rw [← hce_def, hb_eq, Nat.add_sub_cancel, Nat.add_sub_cancel, hsym_ce b a] at hle
      omega
    · have hle := hcs _ h1
      dsimp only at hle
      rw [← hce_def, hb_eq, Nat.add_sub_cancel, Nat.add_sub_cancel, hsym_ce b a, hsym_ce d a] at hle
      omega
  · have hd_eq : iv.u - 1 = d := by omega
    rcases hcp with h1 | h1
    · have hle := hcs _ h1
      dsimp only at hle
      rw [← hce_def, hd_eq, Nat.add_sub_cancel, Nat.add_sub_cancel, hsym_ce d a, hsym_ce d b] at hle
      omega
    · have hle := hcs _ h1
      dsimp only at hle
      rw [← hce_def, hd_eq, Nat.add_sub_cancel, Nat.add_sub_cancel, hsym_ce d b, hsym_ce d a, hsym_ce b a] at hle
      omega

/-- RSST `(3.6)` `|X| = 4` triad witness lifted to `T`: whenever `c.contractEdges.length = 4`,
    there exists an interior vertex `v_tri` whose image `p.emb.rep v_tri` is adjacent in `T` to
    at least 3 distinct vertices `w` appearing as contract-edge endpoints, via non-contracted darts
    outside `mappedContractDarts p.emb`. -/
theorem triad4_witness_in_triangulation
    (h : Nat) (hh : h < 633)
    (T : Hypermap) [DecidableEq T.Dart] (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) T darts)
    (hce : (configOfRConf (parsedRConfList[h]'hlen)).contractEdges.length = 4) :
    let rc := parsedRConfList[h]'hlen
    let c := configOfRConf rc
    ∃ v_tri : Nat, ∃ hv : v_tri < rc.adj.size,
      c.ringSize ≤ v_tri ∧ v_tri < c.totalNodes ∧
      let triNbrs := (rc.adj[v_tri]'hv).toList.filter
        (fun w => decide (∃ q ∈ c.contractEdges, w = q.1 ∨ w = q.2) && !isContractPair c.contractEdges v_tri w)
      triNbrs.Nodup ∧ 3 ≤ triNbrs.length ∧
      ∀ w ∈ triNbrs,
        w < c.totalNodes ∧ c.adj v_tri w = true ∧
        isContractEdge c.contractEdges v_tri w = false ∧
        areAdjacentVertices T (p.emb.rep v_tri) (p.emb.rep w) darts.length = true ∧
        p.emb.dart v_tri w ∉ mappedContractDarts p.emb := by
  intro rc c
  have hhdr := fastConf_equiv_header h hh
  have hadj := fastConf_equiv_adj h hh
  have htri4 := fastConf_geom_triad4 h hh hce
  obtain ⟨v_tri, hv_adj, hvr, hvn, hlen3⟩ := htri4
  have hvr_c : c.ringSize ≤ v_tri := by rw [hhdr.2.2.1]; exact hvr
  have hvn_c : v_tri < c.totalNodes := by rw [hhdr.2.2.2.2.1]; exact hvn
  let triNbrs := (rc.adj[v_tri]'hv_adj).toList.filter
    (fun w => decide (∃ q ∈ c.contractEdges, w = q.1 ∨ w = q.2) && !isContractPair c.contractEdges v_tri w)
  have hnd : triNbrs.Nodup := list_nodup_filter _ (hadj.1 v_tri hvn_c).1
  refine ⟨v_tri, hv_adj, hvr_c, hvn_c, hnd, hlen3, ?_⟩
  intro w hw
  rw [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hw
  have hw_adj_mem : w ∈ (rc.adj[v_tri]'hv_adj).toList := hw.1
  have hw_tot : w < c.totalNodes := ((hadj.1 v_tri hvn_c).2 w hw_adj_mem).1
  have hadj_vw : c.adj v_tri w = true := by
    rw [hadj.2.1 v_tri hvn_c w hw_tot, List.contains_eq_mem, decide_eq_true_eq]
    exact hw_adj_mem
  have hnc_pair : isContractPair c.contractEdges v_tri w = false := by
    have hnot := hw.2.2
    simp only [Bool.not_eq_true'] at hnot
    exact hnot
  have hnc : isContractEdge c.contractEdges v_tri w = false := by
    rw [← isContractPair_eq_isContractEdge]; exact hnc_pair
  have hadj_rep : areAdjacentVertices T (p.emb.rep v_tri) (p.emb.rep w) darts.length = true :=
    p.emb.adj_rep_edge v_tri w hvn_c hw_tot hadj_vw
  exact ⟨hw_tot, hadj_vw, hnc, hadj_rep,
    (int_dart_not_in_mappedContractDarts c T darts h_all p hvr_c hvn_c hw_tot hadj_vw hnc).1⟩

end ContractionPullbackAndTriads

end Math.Unavoidability
