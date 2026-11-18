module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Topology.CubicGirth5

@[expose] public section

/-!
# Discrete Jordan `k`-Cycle Separation & Subtype Cap Engine (`U.1`)

Proves discrete Jordan curve separation for any simple `k`-cycle (`k ≥ 2`) of faces
`(F₀, F₁, …, F_{k-1})` in a planar connected cubic bridgeless hypermap `H`:

1. **Reverse-Composition & `coupleEdge` Primitives (`swapCompRight`, `coupleEdge_diff`,
   `coupleEdge_sameFace`, `coupleNestedPairs`):**
   Exact orbit split/merge characterization of `swapCompRight` (`Perm.iter`), genus-deficit
   invariance under bridge and same-face edge coupling, and recursive rainbow-peeling for
   attaching arbitrary boundary-ordered planar gadgets without recomputing Euler sums.
2. **Equivalence Transport & Multi-Vertex Star Triples (`SimpleEquiv`, `PermTriple.mapEquiv`):**
   Genus deficit, orbit count, and component count invariance under bijections; planar
   degree-`m` vertex triples on borrowed dart lists.
3. **Discrete Jordan `k`-Cycle Separation (`FaceCycleCut`, `uncoupleCycle_two_components`):**
   Sequentially uncoupling the `k` cut edges `(aᵢ, bᵢ)` of a simple `k`-cycle of faces merges
   at steps `0..k-2` (`C = 1`) and splits at step `k-1` (`C = 2`), partitioning `H.Dart` into
   `D_L ⊔ D_R`, splitting each cycle face `Fᵢ = Lᵢ ⊔ Rᵢ`, enforcing cubic/even dart arithmetic
   `3 ∣ |D_*|` and `2 ∣ |D_*| + k`, providing `S₄` color alignment + gluing (`glueCycleColoring`),
   and constructing a reusable planar bridgeless single-vertex subtype cap (`capSingleVertex`) with
   `CyclicOrder4` on `dual.face`.
-/

namespace Hypermap

set_option linter.unusedSectionVars false

section BasicPermAndBridgeHelpers

theorem perm_f_inj_jcs {D : Type} (p : Perm D) {x y : D} (h : p.f x = p.f y) : x = y := by
  have hi := congrArg p.inv h
  rwa [p.left_inv, p.left_inv] at hi

theorem node_face_eq_edge_jcs (H : Hypermap) (x : H.Dart) :
    H.node.f (H.face.f x) = H.edge.f x := by
  have h := congrArg H.edge.f (H.edge_node_face_id x)
  rw [H.edge_involution] at h
  exact h

theorem face_edge_eq_node_inv_jcs (H : Hypermap) (x : H.Dart) :
    H.face.f (H.edge.f x) = H.node.inv x := by
  have h := congrArg H.node.inv (node_face_eq_edge_jcs H (H.edge.f x))
  rw [H.node.left_inv, H.edge_involution] at h
  exact h

theorem sameOrbit_face_color_eq (H : Hypermap) (c : H.FaceColoring)
    {x y : H.Dart} (h : SameOrbit H.face x y) : c.color x = c.color y := by
  rcases h with ⟨k, rfl⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    change c.color x = c.color (H.face.f (Perm.iter H.face k x))
    rw [c.face_invariant, ih]

theorem isBridgeless_iff_no_sameOrbit_face_edge_jcs (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_comp : ∀ d : H.Dart, d ∈ darts) :
    Math.Hypermap.isBridgeless H darts darts.length ↔
      ∀ d : H.Dart, ¬ SameOrbit H.face d (H.edge.f d) := by
  constructor
  · intro hb d hs
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

theorem sameOrbit_e_imp_reachEN {D : Type} {e n : Perm D} {x y : D}
    (h : SameOrbit e x y) : ReachEN e n x y := by
  rcases h with ⟨k, rfl⟩
  exact ⟨walkEN_of_permIter e n e (fun u => WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)) k x⟩

theorem sameOrbit_n_imp_reachEN {D : Type} {e n : Perm D} {x y : D}
    (h : SameOrbit n x y) : ReachEN e n x y := by
  rcases h with ⟨k, rfl⟩
  exact ⟨walkEN_of_permIter e n n (fun u => WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)) k x⟩

theorem exists_min_pos_of_iter_eq {D : Type} (p : Perm D) {a b : D}
    (h_ne : a ≠ b) :
    ∀ k : Nat, Perm.iter p k a = b →
      ∃ m : Nat, 1 ≤ m ∧ m ≤ k ∧ Perm.iter p m a = b ∧
        ∀ t : Nat, 1 ≤ t → t < m → Perm.iter p t a ≠ b := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk
    by_cases hk0 : k = 0
    · subst hk0; exact absurd hk h_ne
    · by_cases h_min : ∀ t : Nat, 1 ≤ t → t < k → Perm.iter p t a ≠ b
      · exact ⟨k, by omega, Nat.le_refl k, hk, h_min⟩
      · have h_ex : ∃ t : Nat, 1 ≤ t ∧ t < k ∧ Perm.iter p t a = b :=
          Classical.byContradiction fun hn => h_min fun t h1 h2 heq => hn ⟨t, h1, h2, heq⟩
        obtain ⟨t, ht1, htk, hteq⟩ := h_ex
        obtain ⟨m, hm1, hmt, hmeq, hmin'⟩ := ih t htk hteq
        exact ⟨m, hm1, by omega, hmeq, hmin'⟩

end BasicPermAndBridgeHelpers

section SwapCompRightAndCoupleEdge

variable {D : Type}

/-- Two-sided symmetry of `swapFun`. -/
theorem swapFun_comm [DecidableEq D] (a b x : D) : swapFun a b x = swapFun b a x := by
  dsimp [swapFun]
  by_cases h1 : x = a
  · rw [h1]; by_cases h2 : a = b <;> simp [h2]
  · by_cases h2 : x = b
    · have hba : b ≠ a := fun h => h1 (h2.trans h)
      rw [h2]; simp [hba]
    · simp [h1, h2]

/-- `uncoupleEdge T a b = uncoupleEdge T b a`. -/
theorem uncoupleEdge_symm [DecidableEq D] (T : PermTriple D) (a b : D) :
    uncoupleEdge T a b = uncoupleEdge T b a := by
  apply permTriple_eq_of_f_eq
  · intro x; dsimp [uncoupleEdge, swapCompLeft]; exact swapFun_comm a b _
  · intro _; rfl
  · intro x; dsimp [uncoupleEdge, swapCompRight]; rw [swapFun_comm a b x]

/-- Forward prefix agreement for `Perm.iter (swapCompRight p a b)` away from `a` and `b`. -/
theorem swapCompRight_iter_prefix [DecidableEq D] (p : Perm D) (a b : D)
    (m : Nat) (d : D)
    (h_bound : ∀ t : Nat, t < m → Perm.iter p t d ≠ a ∧ Perm.iter p t d ≠ b) :
    Perm.iter (swapCompRight p a b) m d = Perm.iter p m d := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [Perm.iter_succ, Perm.iter_succ]
    have h_ih := ih (fun t ht => h_bound t (Nat.lt_succ_of_lt ht))
    rw [h_ih]
    have hk := h_bound k (Nat.lt_succ_self k)
    dsimp [swapCompRight]
    rw [swapFun_of_ne hk.1 hk.2]

/-- Exact characterization of both split orbits when `b = Perm.iter p k a` (`1 ≤ k < L`)
    under `q = swapCompRight p a b`. -/
theorem swapCompRight_split_orbits [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (hab : a ≠ b) (hb : b ∈ getOrbit p fuel a) :
    let q := swapCompRight p a b
    let L := (getOrbit p fuel a).length
    ∃ k : Nat, 1 ≤ k ∧ k < L ∧ Perm.iter p k a = b ∧
      Perm.iter q k b = b ∧
      (∀ r : Nat, 1 ≤ r → r ≤ k → Perm.iter q r b = Perm.iter p r a) ∧
      (∀ x : D, x ∈ getOrbit q fuel b ↔ ∃ r : Nat, 1 ≤ r ∧ r ≤ k ∧ Perm.iter p r a = x) ∧
      (getOrbit q fuel b).length = k ∧
      Perm.iter q (L - k) a = a ∧
      (∀ r : Nat, 1 ≤ r → r ≤ L - k → Perm.iter q r a = Perm.iter p (k + r) a) ∧
      (∀ x : D, x ∈ getOrbit q fuel a ↔ ∃ r : Nat, 1 ≤ r ∧ r ≤ L - k ∧ Perm.iter p (k + r) a = x) ∧
      (getOrbit q fuel a).length = L - k := by
  intro q L
  have h_darts_ne : darts ≠ [] := fun hnil => by have := h_all a; rw [hnil] at this; cases this
  have h_fuel : 1 ≤ fuel := by
    cases darts with
    | nil => exact False.elim (h_darts_ne rfl)
    | cons _ _ => dsimp at h_le; omega
  have hca_p : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  have hca_q : orbitClosesWithin q a a fuel :=
    orbitClosesWithin_mono q a a (orbitClosesWithin_of_complete q darts h_all a) h_le
  have hcb_q : orbitClosesWithin q b b fuel :=
    orbitClosesWithin_mono q b b (orbitClosesWithin_of_complete q darts h_all b) h_le
  have hL_pos : 1 ≤ L := getOrbit_length_pos p h_fuel a
  have hL_per : Perm.iter p L a = a := perm_iter_length_getOrbit_eq_self p fuel a hca_p
  obtain ⟨k, hk_lt, hka⟩ := (mem_getOrbit_iff_exists_lt_length p h_fuel hca_p b).mp hb
  have hk_pos : 1 ≤ k := by
    by_cases hk0 : k = 0
    · subst hk0; exact absurd hka hab
    · omega
  refine ⟨k, hk_pos, hk_lt, hka, ?_⟩
  have hq_b_step1 : q.f b = p.f a := by dsimp [q, swapCompRight]; rw [swapFun_right]
  have hq_b_eq : ∀ r : Nat, 1 ≤ r → r ≤ k → Perm.iter q r b = Perm.iter p r a := by
    intro r hr1 hrk
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    rw [Perm.iter_succ_right, hq_b_step1]
    have h_p1 : Perm.iter p (m + 1) a = Perm.iter p m (p.f a) := Perm.iter_succ_right p m a
    rw [h_p1]
    apply swapCompRight_iter_prefix p a b m (p.f a)
    intro t ht
    rw [← Perm.iter_succ_right]
    have ht1_pos : 1 ≤ t + 1 := by omega
    have ht1_lt_k : t + 1 < k := by omega
    have ht1_lt_L : t + 1 < L := Nat.lt_trans ht1_lt_k hk_lt
    refine ⟨?_, ?_⟩
    · intro heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht1_lt_L hL_pos heq
      omega
    · intro heq
      rw [← hka] at heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht1_lt_L hk_lt heq
      omega
  have hq_b_per : Perm.iter q k b = b := by
    rw [hq_b_eq k hk_pos (Nat.le_refl k), hka]
  have hq_b_inj : ∀ r1 r2, 1 ≤ r1 → r1 ≤ k → 1 ≤ r2 → r2 ≤ k →
      Perm.iter q r1 b = Perm.iter q r2 b → r1 = r2 := by
    intro r1 r2 hr11 hr1k hr21 hr2k heq
    rw [hq_b_eq r1 hr11 hr1k, hq_b_eq r2 hr21 hr2k] at heq
    have h1L : r1 < L := Nat.lt_of_le_of_lt hr1k hk_lt
    have h2L : r2 < L := Nat.lt_of_le_of_lt hr2k hk_lt
    exact perm_iter_inj_of_lt_getOrbit_length p h1L h2L heq
  have h_qb_len_le : (getOrbit q fuel b).length ≤ k :=
    getOrbit_length_le_of_iter_eq_self q fuel hk_pos hq_b_per
  have h_qb_len : (getOrbit q fuel b).length = k := by
    apply Nat.le_antisymm h_qb_len_le
    by_cases hlt : (getOrbit q fuel b).length < k
    · exfalso
      let Lb := (getOrbit q fuel b).length
      have hLb_pos : 1 ≤ Lb := getOrbit_length_pos q h_fuel b
      have hLb_per : Perm.iter q Lb b = b := perm_iter_length_getOrbit_eq_self q fuel b hcb_q
      have := hq_b_inj Lb k hLb_pos (Nat.le_of_lt hlt) hk_pos (Nat.le_refl k) (hLb_per.trans hq_b_per.symm)
      omega
    · omega
  have h_mem_qb : ∀ x : D, x ∈ getOrbit q fuel b ↔ ∃ r : Nat, 1 ≤ r ∧ r ≤ k ∧ Perm.iter p r a = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨m, hm_lt, rfl⟩ := (mem_getOrbit_iff_exists_lt_length q h_fuel hcb_q x).mp hx
      rw [h_qb_len] at hm_lt
      by_cases hm0 : m = 0
      · subst hm0
        exact ⟨k, hk_pos, Nat.le_refl k, hka⟩
      · refine ⟨m, by omega, by omega, ?_⟩
        exact (hq_b_eq m (by omega) (by omega)).symm
    · rintro ⟨r, hr1, hrk, rfl⟩
      rw [← hq_b_eq r hr1 hrk]
      exact iter_mem_getOrbit_of_closes q fuel b hcb_q r
  have hq_a_step1 : q.f a = p.f b := by dsimp [q, swapCompRight]; rw [swapFun_left]
  have hq_a_eq : ∀ r : Nat, 1 ≤ r → r ≤ L - k → Perm.iter q r a = Perm.iter p (k + r) a := by
    intro r hr1 hrL
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    rw [Perm.iter_succ_right, hq_a_step1, ← hka, ← Perm.iter_succ]
    have h_eq : Perm.iter p (k + (m + 1)) a = Perm.iter p m (Perm.iter p (k + 1) a) := by
      rw [← Perm.iter_add, show m + (k + 1) = k + (m + 1) by omega]
    rw [h_eq]
    apply swapCompRight_iter_prefix p a b m (Perm.iter p (k + 1) a)
    intro t ht
    rw [← Perm.iter_add, show t + (k + 1) = k + t + 1 by omega]
    have ht_lt_L : k + t + 1 < L := by omega
    have ht_gt_k : k < k + t + 1 := by omega
    refine ⟨?_, ?_⟩
    · intro heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht_lt_L hL_pos heq
      omega
    · intro heq
      rw [← hka] at heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht_lt_L hk_lt heq
      omega
  have hq_a_per : Perm.iter q (L - k) a = a := by
    rw [hq_a_eq (L - k) (by omega) (Nat.le_refl _), show k + (L - k) = L by omega, hL_per]
  have hq_a_inj : ∀ r1 r2, 1 ≤ r1 → r1 ≤ L - k → 1 ≤ r2 → r2 ≤ L - k →
      Perm.iter q r1 a = Perm.iter q r2 a → r1 = r2 := by
    intro r1 r2 hr11 hr1L hr21 hr2L heq
    rw [hq_a_eq r1 hr11 hr1L, hq_a_eq r2 hr21 hr2L] at heq
    have hmod : ∀ u : Nat, 1 ≤ u → u ≤ L - k →
        Perm.iter p (k + u) a = Perm.iter p (if k + u < L then k + u else 0) a := by
      intro u hu1 huL
      split
      · rfl
      · have hku : k + u = L := by omega
        rw [hku, hL_per]; rfl
    have heq' := heq
    rw [hmod r1 hr11 hr1L, hmod r2 hr21 hr2L] at heq'
    have hidx := perm_iter_inj_of_lt_getOrbit_length p
      (by split <;> omega) (by split <;> omega) heq'
    split at hidx <;> split at hidx <;> omega
  have h_qa_len_le : (getOrbit q fuel a).length ≤ L - k :=
    getOrbit_length_le_of_iter_eq_self q fuel (by omega) hq_a_per
  have h_qa_len : (getOrbit q fuel a).length = L - k := by
    apply Nat.le_antisymm h_qa_len_le
    by_cases hlt : (getOrbit q fuel a).length < L - k
    · exfalso
      let La := (getOrbit q fuel a).length
      have hLa_pos : 1 ≤ La := getOrbit_length_pos q h_fuel a
      have hLa_per : Perm.iter q La a = a := perm_iter_length_getOrbit_eq_self q fuel a hca_q
      have := hq_a_inj La (L - k) hLa_pos (Nat.le_of_lt hlt) (by omega) (Nat.le_refl _) (hLa_per.trans hq_a_per.symm)
      omega
    · omega
  have h_mem_qa : ∀ x : D, x ∈ getOrbit q fuel a ↔ ∃ r : Nat, 1 ≤ r ∧ r ≤ L - k ∧ Perm.iter p (k + r) a = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨m, hm_lt, rfl⟩ := (mem_getOrbit_iff_exists_lt_length q h_fuel hca_q x).mp hx
      rw [h_qa_len] at hm_lt
      by_cases hm0 : m = 0
      · subst hm0
        exact ⟨L - k, by omega, Nat.le_refl _, by rw [show k + (L - k) = L by omega, hL_per]; rfl⟩
      · refine ⟨m, by omega, by omega, ?_⟩
        exact (hq_a_eq m (by omega) (by omega)).symm
    · rintro ⟨r, hr1, hrL, rfl⟩
      rw [← hq_a_eq r hr1 hrL]
      exact iter_mem_getOrbit_of_closes q fuel a hca_q r
  exact ⟨hq_b_per, hq_b_eq, h_mem_qb, h_qb_len, hq_a_per, hq_a_eq, h_mem_qa, h_qa_len⟩

/-- Exact characterization of the merged orbit when `b ∉ getOrbit p fuel a` under
    `q = swapCompRight p a b`. -/
theorem swapCompRight_merge_orbit [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (hab_not : b ∉ getOrbit p fuel a) :
    let q := swapCompRight p a b
    let La := (getOrbit p fuel a).length
    let Lb := (getOrbit p fuel b).length
    Perm.iter q (La + Lb) b = b ∧
    (∀ r : Nat, 1 ≤ r → r ≤ La → Perm.iter q r b = Perm.iter p r a) ∧
    (∀ s : Nat, 1 ≤ s → s ≤ Lb → Perm.iter q (La + s) b = Perm.iter p s b) ∧
    (∀ x : D, x ∈ getOrbit q fuel b ↔ x ∈ getOrbit p fuel a ∨ x ∈ getOrbit p fuel b) ∧
    (getOrbit q fuel b).length = La + Lb := by
  intro q La Lb
  have h_darts_ne : darts ≠ [] := fun hnil => by have := h_all a; rw [hnil] at this; cases this
  have h_fuel : 1 ≤ fuel := by
    cases darts with
    | nil => exact False.elim (h_darts_ne rfl)
    | cons _ _ => dsimp at h_le; omega
  have hab : a ≠ b := fun h => hab_not (h ▸ mem_getOrbit_self p fuel a)
  have hca_p : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  have hcb_p : orbitClosesWithin p b b fuel :=
    orbitClosesWithin_mono p b b (orbitClosesWithin_of_complete p darts h_all b) h_le
  have hcb_q : orbitClosesWithin q b b fuel :=
    orbitClosesWithin_mono q b b (orbitClosesWithin_of_complete q darts h_all b) h_le
  have ha_not_b : a ∉ getOrbit p fuel b := fun hm => hab_not (mem_getOrbit_symm p fuel hcb_p hm)
  have hLa_pos : 1 ≤ La := getOrbit_length_pos p h_fuel a
  have hLb_pos : 1 ≤ Lb := getOrbit_length_pos p h_fuel b
  have hLa_per : Perm.iter p La a = a := perm_iter_length_getOrbit_eq_self p fuel a hca_p
  have hLb_per : Perm.iter p Lb b = b := perm_iter_length_getOrbit_eq_self p fuel b hcb_p
  have hq_part1 : ∀ r : Nat, 1 ≤ r → r ≤ La → Perm.iter q r b = Perm.iter p r a := by
    intro r hr1 hrLa
    obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
    rw [Perm.iter_succ_right, show q.f b = p.f a from by dsimp [q, swapCompRight]; rw [swapFun_right]]
    rw [Perm.iter_succ_right p m a]
    apply swapCompRight_iter_prefix p a b m (p.f a)
    intro t ht
    rw [← Perm.iter_succ_right]
    have ht1_lt : t + 1 < La := by omega
    refine ⟨?_, ?_⟩
    · intro heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht1_lt hLa_pos heq
      omega
    · intro heq
      exact hab_not (heq ▸ iter_mem_getOrbit_of_closes p fuel a hca_p (t + 1))
  have hq_La : Perm.iter q La b = a := by rw [hq_part1 La hLa_pos (Nat.le_refl La), hLa_per]
  have hq_part2 : ∀ s : Nat, 1 ≤ s → s ≤ Lb → Perm.iter q (La + s) b = Perm.iter p s b := by
    intro s hs1 hsLb
    rw [Nat.add_comm La s, Perm.iter_add q s La b, hq_La]
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    rw [Perm.iter_succ_right, show q.f a = p.f b from by dsimp [q, swapCompRight]; rw [swapFun_left]]
    rw [Perm.iter_succ_right p m b]
    apply swapCompRight_iter_prefix p a b m (p.f b)
    intro t ht
    rw [← Perm.iter_succ_right]
    have ht1_lt : t + 1 < Lb := by omega
    refine ⟨?_, ?_⟩
    · intro heq
      exact ha_not_b (heq ▸ iter_mem_getOrbit_of_closes p fuel b hcb_p (t + 1))
    · intro heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht1_lt hLb_pos heq
      omega
  have hq_per : Perm.iter q (La + Lb) b = b := by
    rw [hq_part2 Lb hLb_pos (Nat.le_refl Lb), hLb_per]
  have h_len_le : (getOrbit q fuel b).length ≤ La + Lb :=
    getOrbit_length_le_of_iter_eq_self q fuel (by omega) hq_per
  have h_len : (getOrbit q fuel b).length = La + Lb := by
    apply Nat.le_antisymm h_len_le
    by_cases hlt : (getOrbit q fuel b).length < La + Lb
    · exfalso
      let Lq := (getOrbit q fuel b).length
      have hLq_pos : 1 ≤ Lq := getOrbit_length_pos q h_fuel b
      have hLq_per : Perm.iter q Lq b = b := perm_iter_length_getOrbit_eq_self q fuel b hcb_q
      by_cases hleLa : Lq ≤ La
      · have heq := hq_part1 Lq hLq_pos hleLa
        rw [hLq_per] at heq
        exact ha_not_b (heq.symm ▸ (mem_getOrbit_symm p fuel hca_p (iter_mem_getOrbit_of_closes p fuel a hca_p Lq)))
      · let s := Lq - La
        have hs1 : 1 ≤ s := by omega
        have hsLb : s < Lb := by omega
        have heq := hq_part2 s hs1 (Nat.le_of_lt hsLb)
        rw [show La + s = Lq by omega, hLq_per] at heq
        have := perm_iter_inj_of_lt_getOrbit_length p (by omega : 0 < Lb) hsLb (by simpa using heq)
        omega
    · omega
  have h_mem : ∀ x : D, x ∈ getOrbit q fuel b ↔ x ∈ getOrbit p fuel a ∨ x ∈ getOrbit p fuel b := by
    intro x
    constructor
    · intro hx
      obtain ⟨m, hm_lt, rfl⟩ := (mem_getOrbit_iff_exists_lt_length q h_fuel hcb_q x).mp hx
      rw [h_len] at hm_lt
      by_cases hm0 : m = 0
      · subst hm0; exact Or.inr (mem_getOrbit_self p fuel b)
      · by_cases hmLa : m ≤ La
        · rw [hq_part1 m (by omega) hmLa]
          exact Or.inl (iter_mem_getOrbit_of_closes p fuel a hca_p m)
        · let s := m - La
          have heq := hq_part2 s (by omega) (by omega)
          rw [show La + s = m by omega] at heq
          rw [heq]
          exact Or.inr (iter_mem_getOrbit_of_closes p fuel b hcb_p s)
    · rintro (hxa | hxb)
      · obtain ⟨r, hr_lt, rfl⟩ := (mem_getOrbit_iff_exists_lt_length p h_fuel hca_p x).mp hxa
        by_cases hr0 : r = 0
        · subst hr0
          rw [← hq_La]
          exact iter_mem_getOrbit_of_closes q fuel b hcb_q La
        · rw [← hq_part1 r (by omega) (Nat.le_of_lt hr_lt)]
          exact iter_mem_getOrbit_of_closes q fuel b hcb_q r
      · obtain ⟨s, hs_lt, rfl⟩ := (mem_getOrbit_iff_exists_lt_length p h_fuel hcb_p x).mp hxb
        by_cases hs0 : s = 0
        · subst hs0; exact mem_getOrbit_self q fuel b
        · rw [← hq_part2 s (by omega) (Nat.le_of_lt hs_lt)]
          exact iter_mem_getOrbit_of_closes q fuel b hcb_q (La + s)
  exact ⟨hq_per, hq_part1, hq_part2, h_mem, h_len⟩

theorem perm_iter_fixed {D : Type} (p : Perm D) {a : D} (ha : p.f a = a) :
    ∀ k : Nat, Perm.iter p k a = a
  | 0 => rfl
  | k + 1 => by rw [Perm.iter_succ, perm_iter_fixed p ha k, ha]

theorem mem_getOrbit_fixed_iff [DecidableEq D] (p : Perm D) {fuel : Nat} (h_fuel : 1 ≤ fuel)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) (h_le : darts.length ≤ fuel)
    (a : D) (ha : p.f a = a) (x : D) :
    x ∈ getOrbit p fuel a ↔ x = a := by
  have hc : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  constructor
  · intro hx
    obtain ⟨m, _, rfl⟩ := (mem_getOrbit_iff_exists_lt_length p h_fuel hc x).mp hx
    exact perm_iter_fixed p ha m
  · rintro rfl
    exact mem_getOrbit_self p fuel x

theorem mem_getOrbit_f_imp_reachEN [DecidableEq D] (T : PermTriple D) {fuel : Nat}
    {a b : D} (darts : List D) (h_all : ∀ x : D, x ∈ darts) (h_le : darts.length ≤ fuel)
    (hb : b ∈ getOrbit T.f fuel a) :
    ReachEN T.e T.n a b := by
  have h_fuel : 1 ≤ fuel := by
    cases darts with
    | nil => have := h_all a; contradiction
    | cons _ _ => dsimp at h_le; omega
  have hc : orbitClosesWithin T.f a a fuel :=
    orbitClosesWithin_mono T.f a a (orbitClosesWithin_of_complete T.f darts h_all a) h_le
  obtain ⟨m, _, rfl⟩ := (mem_getOrbit_iff_exists_lt_length T.f h_fuel hc b).mp hb
  exact ⟨walkEN_of_permIter T.e T.n T.f (fun u =>
    WalkEN.step (StepEN.e_bwd u)
      (WalkEN.step (StepEN.n_bwd (T.e.inv u))
        (by rw [← T.f_eq_n_inv_e_inv]; exact WalkEN.refl _))) m a⟩

theorem swapCompRight_iter_eq_of_not_mem_orbit [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b z : D} (hza : a ∉ getOrbit p fuel z) (hzb : b ∉ getOrbit p fuel z) :
    (∀ m : Nat, Perm.iter (swapCompRight p a b) m z = Perm.iter p m z) ∧
    getOrbit (swapCompRight p a b) fuel z = getOrbit p fuel z := by
  have hcz : orbitClosesWithin p z z fuel :=
    orbitClosesWithin_mono p z z (orbitClosesWithin_of_complete p darts h_all z) h_le
  have h_agree_iter : ∀ m : Nat, Perm.iter (swapCompRight p a b) m z = Perm.iter p m z := by
    intro m
    induction m with
    | zero => rfl
    | succ k ih =>
      rw [Perm.iter_succ, Perm.iter_succ, ih]
      have hk_mem : Perm.iter p k z ∈ getOrbit p fuel z :=
        iter_mem_getOrbit_of_closes p fuel z hcz k
      have hne_a : Perm.iter p k z ≠ a := fun h => hza (h ▸ hk_mem)
      have hne_b : Perm.iter p k z ≠ b := fun h => hzb (h ▸ hk_mem)
      dsimp [swapCompRight]
      rw [swapFun_of_ne hne_a hne_b]
  refine ⟨h_agree_iter, ?_⟩
  symm
  let S : D → Bool := fun x => decide (x ∈ getOrbit p fuel z)
  have hS_p : ∀ x : D, S (p.f x) = S x := by
    intro x
    dsimp [S]
    by_cases hx : x ∈ getOrbit p fuel z
    · have hfx : p.f x ∈ getOrbit p fuel z := getOrbit_closed_under_f_of_complete p darts h_all h_le hx
      simp [hx, hfx]
    · have hfx : p.f x ∉ getOrbit p fuel z := by
        intro hm
        have hi := getOrbit_closed_under_inv_of_complete p darts h_all h_le hm
        rw [p.left_inv] at hi
        exact hx hi
      simp [hx, hfx]
  have h_agree : ∀ x : D, S x = true → p.f x = (swapCompRight p a b).f x := by
    intro x hx
    have hmem : x ∈ getOrbit p fuel z := by simpa [S] using hx
    have hne_a : x ≠ a := fun h => hza (h ▸ hmem)
    have hne_b : x ≠ b := fun h => hzb (h ▸ hmem)
    dsimp [swapCompRight]
    rw [swapFun_of_ne hne_a hne_b]
  have hSz : S z = true := by simp [S, mem_getOrbit_self p fuel z]
  exact getOrbit_eq_of_agree_on_closed p (swapCompRight p a b) S hS_p h_agree fuel hSz

/-- Couple two fixed edge darts `(a, b)` into a paired edge `{a, b}` (`uncoupleEdge`). -/
abbrev coupleEdge [DecidableEq D] (T : PermTriple D) (a b : D) : PermTriple D :=
  uncoupleEdge T a b

theorem coupleEdge_symm [DecidableEq D] (T : PermTriple D) (a b : D) :
    coupleEdge T a b = coupleEdge T b a :=
  uncoupleEdge_symm T a b

theorem coupleEdge_n [DecidableEq D] (T : PermTriple D) (a b : D) :
    (coupleEdge T a b).n = T.n := rfl

theorem coupleEdge_e_eval [DecidableEq D] (T : PermTriple D) {a b : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) (x : D) :
    (coupleEdge T a b).e.f x = if x = a then b else if x = b then a else T.e.f x := by
  dsimp [coupleEdge, uncoupleEdge, swapCompLeft]
  by_cases hxa : x = a
  · subst hxa; rw [if_pos rfl, ha_fix, swapFun_left]
  · rw [if_neg hxa]
    by_cases hxb : x = b
    · subst hxb; rw [if_pos rfl, hb_fix, swapFun_right]
    · rw [if_neg hxb]
      have hfa : T.e.f x ≠ a := fun h => hxa (perm_f_inj_jcs T.e (h.trans ha_fix.symm))
      have hfb : T.e.f x ≠ b := fun h => hxb (perm_f_inj_jcs T.e (h.trans hb_fix.symm))
      exact swapFun_of_ne hfa hfb

theorem coupleEdge_e_left [DecidableEq D] (T : PermTriple D) {a b : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) :
    (coupleEdge T a b).e.f a = b := by
  rw [coupleEdge_e_eval T ha_fix hb_fix a, if_pos rfl]

theorem coupleEdge_e_right [DecidableEq D] (T : PermTriple D) {a b : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) :
    (coupleEdge T a b).e.f b = a := by
  rw [coupleEdge_e_eval T ha_fix hb_fix b]
  by_cases hba : b = a
  · rw [if_pos hba, hba]
  · rw [if_neg hba, if_pos rfl]

theorem coupleEdge_e_of_ne [DecidableEq D] (T : PermTriple D) {a b x : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) (hxa : x ≠ a) (hxb : x ≠ b) :
    (coupleEdge T a b).e.f x = T.e.f x := by
  rw [coupleEdge_e_eval T ha_fix hb_fix x, if_neg hxa, if_neg hxb]

theorem coupleEdge_e_inv_eval [DecidableEq D] (T : PermTriple D) {a b : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) (y : D) :
    (coupleEdge T a b).e.inv y = if y = a then b else if y = b then a else T.e.inv y := by
  have ha_inv : T.e.inv a = a := by
    have h := congrArg T.e.inv ha_fix; rw [T.e.left_inv] at h; exact h.symm
  have hb_inv : T.e.inv b = b := by
    have h := congrArg T.e.inv hb_fix; rw [T.e.left_inv] at h; exact h.symm
  dsimp [coupleEdge, uncoupleEdge, swapCompLeft]
  by_cases hya : y = a
  · rw [hya, if_pos rfl, swapFun_left, hb_inv]
  · rw [if_neg hya]
    by_cases hyb : y = b
    · rw [hyb, if_pos rfl, swapFun_right, ha_inv]
    · rw [if_neg hyb, swapFun_of_ne hya hyb]

theorem reachEN_mono_of_coupleEdge [DecidableEq D] (T : PermTriple D) {a b : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) {x y : D}
    (hxy : ReachEN T.e T.n x y) :
    ReachEN (coupleEdge T a b).e (coupleEdge T a b).n x y := by
  let T1 := coupleEdge T a b
  have h_step : ∀ {u v : D}, StepEN T.e T.n u v → ReachEN T1.e T1.n u v := by
    intro u v s
    cases s with
    | e_fwd =>
      by_cases hua : u = a
      · rw [hua, ha_fix]; exact reachEN_refl _ _ _
      · by_cases hub : u = b
        · rw [hub, hb_fix]; exact reachEN_refl _ _ _
        · rw [← coupleEdge_e_of_ne T ha_fix hb_fix hua hub]
          exact ⟨WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)⟩
    | e_bwd =>
      by_cases hua : u = a
      · have hi : T.e.inv a = a := by
          have h := congrArg T.e.inv ha_fix; rw [T.e.left_inv] at h; exact h.symm
        rw [hua, hi]; exact reachEN_refl _ _ _
      · by_cases hub : u = b
        · have hi : T.e.inv b = b := by
            have h := congrArg T.e.inv hb_fix; rw [T.e.left_inv] at h; exact h.symm
          rw [hub, hi]; exact reachEN_refl _ _ _
        · have hi : T1.e.inv u = T.e.inv u := by
            rw [coupleEdge_e_inv_eval T ha_fix hb_fix u, if_neg hua, if_neg hub]
          rw [← hi]
          exact ⟨WalkEN.step (StepEN.e_bwd u) (WalkEN.refl _)⟩
    | n_fwd => exact ⟨WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)⟩
    | n_bwd => exact ⟨WalkEN.step (StepEN.n_bwd u) (WalkEN.refl _)⟩
  rcases hxy with ⟨w⟩
  induction w with
  | refl z => exact reachEN_refl _ _ z
  | step s _ ih => exact reachEN_trans _ _ (h_step s) ih

private theorem stepEN_coupleEdge_reach [DecidableEq D] (T : PermTriple D) {a b : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) {u v : D}
    (s : StepEN (coupleEdge T a b).e (coupleEdge T a b).n u v) :
    ReachEN T.e T.n u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  cases s with
  | e_fwd =>
    rw [coupleEdge_e_eval T ha_fix hb_fix u]
    split
    · next hua => exact Or.inr (Or.inl ⟨hua, rfl⟩)
    · split
      · next hub => exact Or.inr (Or.inr ⟨hub, rfl⟩)
      · exact Or.inl ⟨WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)⟩
  | e_bwd =>
    rw [coupleEdge_e_inv_eval T ha_fix hb_fix u]
    split
    · next hua => exact Or.inr (Or.inl ⟨hua, rfl⟩)
    · split
      · next hub => exact Or.inr (Or.inr ⟨hub, rfl⟩)
      · exact Or.inl ⟨WalkEN.step (StepEN.e_bwd u) (WalkEN.refl _)⟩
  | n_fwd => exact Or.inl ⟨WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)⟩
  | n_bwd => exact Or.inl ⟨WalkEN.step (StepEN.n_bwd u) (WalkEN.refl _)⟩

theorem coupleEdge_reach_iff_or_bridge [DecidableEq D] (T : PermTriple D) {a b : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) {x y : D} :
    ReachEN (coupleEdge T a b).e (coupleEdge T a b).n x y ↔
      ReachEN T.e T.n x y ∨
        ((ReachEN T.e T.n x a ∧ ReachEN T.e T.n b y) ∨
         (ReachEN T.e T.n x b ∧ ReachEN T.e T.n a y)) := by
  let T1 := coupleEdge T a b
  constructor
  · rintro ⟨w⟩
    induction w with
    | refl z => exact Or.inl (reachEN_refl _ _ z)
    | step s _ ih =>
      rcases stepEN_coupleEdge_reach T ha_fix hb_fix s with hs' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with hyz | ⟨⟨hya, hbz⟩ | ⟨hyb, haz⟩⟩
        · exact Or.inl (reachEN_trans _ _ hs' hyz)
        · exact Or.inr (Or.inl ⟨reachEN_trans _ _ hs' hya, hbz⟩)
        · exact Or.inr (Or.inr ⟨reachEN_trans _ _ hs' hyb, haz⟩)
      · rcases ih with hbz | ⟨⟨_, hbz'⟩ | ⟨_, haz⟩⟩
        · exact Or.inr (Or.inl ⟨reachEN_refl _ _ _, hbz⟩)
        · exact Or.inr (Or.inl ⟨reachEN_refl _ _ _, hbz'⟩)
        · exact Or.inl haz
      · rcases ih with haz | ⟨⟨_, hbz⟩ | ⟨_, haz'⟩⟩
        · exact Or.inr (Or.inr ⟨reachEN_refl _ _ _, haz⟩)
        · exact Or.inl hbz
        · exact Or.inr (Or.inr ⟨reachEN_refl _ _ _, haz'⟩)
  · rintro (hxy | ⟨hxa, hby⟩ | ⟨hxb, hay⟩)
    · exact reachEN_mono_of_coupleEdge T ha_fix hb_fix hxy
    · have hab1 : ReachEN T1.e T1.n a b :=
        ⟨WalkEN.step (StepEN.e_fwd a) (by rw [coupleEdge_e_left T ha_fix hb_fix]; exact WalkEN.refl b)⟩
      exact reachEN_trans _ _ (reachEN_mono_of_coupleEdge T ha_fix hb_fix hxa)
        (reachEN_trans _ _ hab1 (reachEN_mono_of_coupleEdge T ha_fix hb_fix hby))
    · have hba1 : ReachEN T1.e T1.n b a :=
        ⟨WalkEN.step (StepEN.e_fwd b) (by rw [coupleEdge_e_right T ha_fix hb_fix]; exact WalkEN.refl a)⟩
      exact reachEN_trans _ _ (reachEN_mono_of_coupleEdge T ha_fix hb_fix hxb)
        (reachEN_trans _ _ hba1 (reachEN_mono_of_coupleEdge T ha_fix hb_fix hay))

/-- Coupling two fixed edge darts `(a, b)` in distinct `EN`-components merges those two
    components (`C - 1`), merges their edge orbits `{a}` and `{b}` (`E - 1`), merges their
    face orbits (`F - 1`), and **preserves `genusDeficit`**. -/
theorem coupleEdge_diff [DecidableEq D] (T : PermTriple D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b)
    (h_disj : ¬ ReachEN T.e T.n a b) :
    let T1 := coupleEdge T a b
    let S : D → Bool := fun x => decide (ReachEN T.e T.n a x ∨ ReachEN T.e T.n b x)
    (T1.e.f a = b ∧ T1.e.f b = a) ∧
    (b ∉ getOrbit T.f fuel a) ∧
    (∀ {x y : D}, ReachEN T.e T.n x y → S x = S y) ∧
    (∀ {x y : D}, ReachEN T1.e T1.n x y → S x = S y) ∧
    (countRelClasses (ReachEN T1.e T1.n) darts + 1 = countRelClasses (ReachEN T.e T.n) darts) ∧
    (countOrbits T1.e fuel darts + 1 = countOrbits T.e fuel darts) ∧
    (countOrbits T1.f fuel darts + 1 = countOrbits T.f fuel darts) ∧
    (genusDeficit T1 fuel darts = genusDeficit T fuel darts) := by
  intro T1 S
  have h_fuel : 1 ≤ fuel := by
    cases darts with
    | nil => have := h_all a; contradiction
    | cons _ _ => dsimp at h_le; omega
  have hab_ne : a ≠ b := fun h => h_disj (h ▸ reachEN_refl _ _ a)
  have he_lr : T1.e.f a = b ∧ T1.e.f b = a :=
    ⟨coupleEdge_e_left T ha_fix hb_fix, coupleEdge_e_right T ha_fix hb_fix⟩
  have hb_not_f : b ∉ getOrbit T.f fuel a :=
    fun hm => h_disj (mem_getOrbit_f_imp_reachEN T darts h_all h_le hm)
  have hb_not_e : b ∉ getOrbit T.e fuel a := by
    rw [mem_getOrbit_fixed_iff T.e h_fuel darts h_all h_le a ha_fix b]
    exact hab_ne.symm
  have hS_T : ∀ {x y : D}, ReachEN T.e T.n x y → S x = S y := by
    intro x y hxy
    dsimp [S]
    by_cases hx : ReachEN T.e T.n a x ∨ ReachEN T.e T.n b x
    · have hy : ReachEN T.e T.n a y ∨ ReachEN T.e T.n b y :=
        hx.elim (fun h => Or.inl (reachEN_trans _ _ h hxy)) (fun h => Or.inr (reachEN_trans _ _ h hxy))
      simp [hx, hy]
    · have hy : ¬(ReachEN T.e T.n a y ∨ ReachEN T.e T.n b y) := by
        rintro (hay | hby)
        · exact hx (Or.inl (reachEN_trans _ _ hay (reachEN_symm _ _ hxy)))
        · exact hx (Or.inr (reachEN_trans _ _ hby (reachEN_symm _ _ hxy)))
      simp [hx, hy]
  have hS_T1 : ∀ {x y : D}, ReachEN T1.e T1.n x y → S x = S y := by
    intro x y hxy
    rcases (coupleEdge_reach_iff_or_bridge T ha_fix hb_fix).mp hxy with hT | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
    · exact hS_T hT
    · have hxS : S x = true := by
        dsimp [S]; simp [Or.inl (reachEN_symm _ _ hxa)]
      have hyS : S y = true := by
        dsimp [S]; simp [Or.inr hby]
      exact hxS.trans hyS.symm
    · have hxS : S x = true := by
        dsimp [S]; simp [Or.inr (reachEN_symm _ _ hxb)]
      have hyS : S y = true := by
        dsimp [S]; simp [Or.inl hay]
      exact hxS.trans hyS.symm
  have hC1 : countRelClasses (ReachEN T1.e T1.n) darts + 1 = countRelClasses (ReachEN T.e T.n) darts := by
    rw [countRelClasses_partition_of_closed (ReachEN T1.e T1.n) (reachEN_refl _ _)
          (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS_T1 darts,
        countRelClasses_partition_of_closed (ReachEN T.e T.n) (reachEN_refl _ _)
          (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS_T darts]
    have ha_in : a ∈ darts.filter S := List.mem_filter.mpr ⟨h_all a, by simp [S, reachEN_refl]⟩
    have hb_in : b ∈ darts.filter S := List.mem_filter.mpr ⟨h_all b, by simp [S, reachEN_refl]⟩
    have hS1_T1 : countRelClasses (ReachEN T1.e T1.n) (darts.filter S) = 1 := by
      apply countRelClasses_eq_one_of_forall (ReachEN T1.e T1.n) a
      · intro x hx
        have hmx : ReachEN T.e T.n a x ∨ ReachEN T.e T.n b x := by
          simpa [S] using (List.mem_filter.mp hx).2
        rcases hmx with hax | hbx
        · exact reachEN_mono_of_coupleEdge T ha_fix hb_fix hax
        · have hab1 : ReachEN T1.e T1.n a b :=
            ⟨WalkEN.step (StepEN.e_fwd a) (by rw [he_lr.1]; exact WalkEN.refl b)⟩
          exact reachEN_trans _ _ hab1 (reachEN_mono_of_coupleEdge T ha_fix hb_fix hbx)
      · intro hnil; rw [hnil] at ha_in; cases ha_in
      · exact fun h => reachEN_symm _ _ h
      · exact fun h1 h2 => reachEN_trans _ _ h1 h2
    have hS2_T : countRelClasses (ReachEN T.e T.n) (darts.filter S) = 2 := by
      apply countRelClasses_eq_two_of_two_classes (ReachEN T.e T.n) (reachEN_refl _ _)
        (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) a b h_disj
        (darts.filter S) ha_in hb_in
      intro x hx
      simpa [S] using (List.mem_filter.mp hx).2
    have h_out : countRelClasses (ReachEN T1.e T1.n) (darts.filter (fun x => !S x)) =
        countRelClasses (ReachEN T.e T.n) (darts.filter (fun x => !S x)) := by
      apply countRelClasses_eq_of_rel_iff_on_mem (ReachEN T1.e T1.n) (ReachEN T.e T.n) _ _ (Nat.le_refl _)
      intro x hx y hy
      have hx_ns : ¬(ReachEN T.e T.n a x ∨ ReachEN T.e T.n b x) := by
        simpa [S] using (List.mem_filter.mp hx).2
      rw [coupleEdge_reach_iff_or_bridge T ha_fix hb_fix]
      constructor
      · rintro (hxy | ⟨hxa, _⟩ | ⟨hxb, _⟩)
        · exact hxy
        · exact False.elim (hx_ns (Or.inl (reachEN_symm _ _ hxa)))
        · exact False.elim (hx_ns (Or.inr (reachEN_symm _ _ hxb)))
      · exact Or.inl
    rw [hS1_T1, hS2_T, h_out]
    omega
  have hE1 : countOrbits T1.e fuel darts + 1 = countOrbits T.e fuel darts :=
    countOrbits_swapCompLeft_diff T.e darts h_all h_le hb_not_e
  have hF1 : countOrbits T1.f fuel darts + 1 = countOrbits T.f fuel darts :=
    countOrbits_swapCompRight_diff T.f darts h_all h_le hb_not_f
  have hV1 : countOrbits T1.n fuel darts = countOrbits T.n fuel darts := rfl
  have h_gen : genusDeficit T1 fuel darts = genusDeficit T fuel darts := by
    dsimp [genusDeficit]
    rw [hV1]
    omega
  exact ⟨he_lr, hb_not_f, hS_T, hS_T1, hC1, hE1, hF1, h_gen⟩

/-- Coupling two fixed edge darts `(a, b)` already in the same `T.f` orbit preserves `ReachEN`
    (`C` unchanged), decreases `E` by `1`, increases `F` by `1`, and **preserves `genusDeficit`**. -/
theorem coupleEdge_sameFace [DecidableEq D] (T : PermTriple D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b)
    (hab : a ≠ b) (hb_f : b ∈ getOrbit T.f fuel a) :
    let T1 := coupleEdge T a b
    (T1.e.f a = b ∧ T1.e.f b = a) ∧
    (∀ {x y : D}, ReachEN T1.e T1.n x y ↔ ReachEN T.e T.n x y) ∧
    (countRelClasses (ReachEN T1.e T1.n) darts = countRelClasses (ReachEN T.e T.n) darts) ∧
    (countOrbits T1.e fuel darts + 1 = countOrbits T.e fuel darts) ∧
    (countOrbits T1.f fuel darts = countOrbits T.f fuel darts + 1) ∧
    (genusDeficit T1 fuel darts = genusDeficit T fuel darts) := by
  intro T1
  have h_fuel : 1 ≤ fuel := by
    cases darts with
    | nil => have := h_all a; contradiction
    | cons _ _ => dsimp at h_le; omega
  have he_lr : T1.e.f a = b ∧ T1.e.f b = a :=
    ⟨coupleEdge_e_left T ha_fix hb_fix, coupleEdge_e_right T ha_fix hb_fix⟩
  have hab_reach : ReachEN T.e T.n a b := mem_getOrbit_f_imp_reachEN T darts h_all h_le hb_f
  have h_reach_iff : ∀ {x y : D}, ReachEN T1.e T1.n x y ↔ ReachEN T.e T.n x y := by
    intro x y
    rw [coupleEdge_reach_iff_or_bridge T ha_fix hb_fix]
    constructor
    · rintro (hxy | ⟨hxa, hby⟩ | ⟨hxb, hay⟩)
      · exact hxy
      · exact reachEN_trans _ _ hxa (reachEN_trans _ _ hab_reach hby)
      · exact reachEN_trans _ _ hxb (reachEN_trans _ _ (reachEN_symm _ _ hab_reach) hay)
    · exact Or.inl
  have hC1 : countRelClasses (ReachEN T1.e T1.n) darts = countRelClasses (ReachEN T.e T.n) darts :=
    countRelClasses_eq_of_rel_iff (ReachEN T1.e T1.n) (ReachEN T.e T.n)
      (fun x y => h_reach_iff) darts.length darts (Nat.le_refl _)
  have hb_not_e : b ∉ getOrbit T.e fuel a := by
    rw [mem_getOrbit_fixed_iff T.e h_fuel darts h_all h_le a ha_fix b]
    exact hab.symm
  have hE1 : countOrbits T1.e fuel darts + 1 = countOrbits T.e fuel darts :=
    countOrbits_swapCompLeft_diff T.e darts h_all h_le hb_not_e
  have hF1 : countOrbits T1.f fuel darts = countOrbits T.f fuel darts + 1 :=
    countOrbits_swapCompRight_same T.f darts h_all h_le hab hb_f
  have hV1 : countOrbits T1.n fuel darts = countOrbits T.n fuel darts := rfl
  have h_gen : genusDeficit T1 fuel darts = genusDeficit T fuel darts := by
    dsimp [genusDeficit]
    rw [hC1, hV1]
    omega
  exact ⟨he_lr, h_reach_iff, hC1, hE1, hF1, h_gen⟩

/-- Sequentially couple a list of pairs `(a, b)`. -/
def coupleList {D : Type} [DecidableEq D] (T : PermTriple D) : List (D × D) → PermTriple D
  | [] => T
  | (a, b) :: rest => coupleList (coupleEdge T a b) rest

/-- Dart pairs `(Perm.iter T.f p base, Perm.iter T.f q base)` extracted from nested position pairs. -/
def nestedPairs {D : Type} (T : PermTriple D) (base : D) (specs : List (Nat × Nat)) : List (D × D) :=
  specs.map fun pq => (Perm.iter T.f pq.1 base, Perm.iter T.f pq.2 base)

/-- Recursive rainbow-peeling engine: coupling nested pairs `(pᵢ, qᵢ)` on `T.f`'s orbit of `base`
    preserves `genusDeficit`, `ReachEN`, `n`, all faces disjoint from `base`, and partitions the
    `base`-orbit into explicit peeled faces plus the surviving outer `base`-orbit. -/
private theorem coupleNestedPairs_spec_aux [DecidableEq D]
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (base : D) :
    ∀ (n : Nat) (T : PermTriple D) (specs : List (Nat × Nat)),
      specs.length ≤ n →
      let L := (getOrbit T.f fuel base).length
      specs.Pairwise (fun x y => y.1 < x.1 ∧ x.2 < y.2) →
      (∀ pq ∈ specs, 1 ≤ pq.1 ∧ pq.1 < pq.2 ∧ pq.2 < L) →
      (∀ pq ∈ specs, T.e.f (Perm.iter T.f pq.1 base) = Perm.iter T.f pq.1 base ∧
                     T.e.f (Perm.iter T.f pq.2 base) = Perm.iter T.f pq.2 base) →
      let T' := coupleList T (nestedPairs T base specs)
      T'.n = T.n ∧
      (∀ d : D, (∀ pq ∈ specs, d ≠ Perm.iter T.f pq.1 base ∧ d ≠ Perm.iter T.f pq.2 base) →
        T'.e.f d = T.e.f d) ∧
      (∀ pq ∈ specs, T'.e.f (Perm.iter T.f pq.1 base) = Perm.iter T.f pq.2 base ∧
                     T'.e.f (Perm.iter T.f pq.2 base) = Perm.iter T.f pq.1 base) ∧
      (∀ {x y : D}, ReachEN T'.e T'.n x y ↔ ReachEN T.e T.n x y) ∧
      (genusDeficit T' fuel darts = genusDeficit T fuel darts) ∧
      (∀ z : D, z ∉ getOrbit T.f fuel base → getOrbit T'.f fuel z = getOrbit T.f fuel z) ∧
      (∀ x : D, x ∈ getOrbit T'.f fuel base ↔
        ∃ r : Nat, r < L ∧
          (∀ pq ∈ specs, ¬(pq.1 < r ∧ r ≤ pq.2)) ∧
          Perm.iter T.f r base = x) ∧
      (∀ i : Nat, (hi : i < specs.length) →
        ∀ x : D, x ∈ getOrbit T'.f fuel (Perm.iter T.f specs[i].2 base) ↔
          ∃ r : Nat, specs[i].1 < r ∧ r ≤ specs[i].2 ∧
            (∀ j : Nat, (hj : j < i) →
              ¬(specs[j].1 < r ∧ r ≤ specs[j].2)) ∧
            Perm.iter T.f r base = x) := by
  intro n
  induction n with
  | zero =>
    intro T specs hlen L _ h_bnd _
    have hnil : specs = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hnil
    have h_fuel : 1 ≤ fuel := by
      cases darts with
      | nil => have := h_all base; contradiction
      | cons _ _ => dsimp at h_le; omega
    have hcb : orbitClosesWithin T.f base base fuel :=
      orbitClosesWithin_mono T.f base base (orbitClosesWithin_of_complete T.f darts h_all base) h_le
    refine ⟨rfl, fun _ _ => rfl, ?_, fun {x y} => Iff.rfl, rfl,
            fun _ _ => rfl, ?_, fun i hi => False.elim (Nat.not_lt_zero i hi)⟩
    · intro pq hpq; cases hpq
    · intro x
      dsimp only [coupleList, nestedPairs, List.map]
      rw [mem_getOrbit_iff_exists_lt_length T.f h_fuel hcb x]
      constructor
      · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, (fun _ hm => nomatch hm), rfl⟩
      · rintro ⟨r, hr, _, rfl⟩; exact ⟨r, hr, rfl⟩
  | succ n ih =>
    intro T specs hlen L h_pw h_bnd h_fix
    have h_fuel : 1 ≤ fuel := by
      cases darts with
      | nil => have := h_all base; contradiction
      | cons _ _ => dsimp at h_le; omega
    have hcb : orbitClosesWithin T.f base base fuel :=
      orbitClosesWithin_mono T.f base base (orbitClosesWithin_of_complete T.f darts h_all base) h_le
    cases specs with
    | nil =>
      refine ⟨rfl, fun _ _ => rfl, ?_, fun {x y} => Iff.rfl, rfl,
              fun _ _ => rfl, ?_, fun i hi => False.elim (Nat.not_lt_zero i hi)⟩
      · intro pq hpq; cases hpq
      · intro x
        dsimp only [coupleList, nestedPairs, List.map]
        rw [mem_getOrbit_iff_exists_lt_length T.f h_fuel hcb x]
        constructor
        · rintro ⟨r, hr, rfl⟩; exact ⟨r, hr, (fun _ hm => nomatch hm), rfl⟩
        · rintro ⟨r, hr, _, rfl⟩; exact ⟨r, hr, rfl⟩
    | cons pq0 rest =>
      have hL_pos : 1 ≤ L := getOrbit_length_pos T.f h_fuel base
      have hpq0_bnd := h_bnd pq0 List.mem_cons_self
      have hpq0_fix := h_fix pq0 List.mem_cons_self
      have h_rel_rest : ∀ pq ∈ rest, pq.1 < pq0.1 ∧ pq0.2 < pq.2 :=
        (List.pairwise_cons.mp h_pw).1
      let a0 := Perm.iter T.f pq0.1 base
      let b0 := Perm.iter T.f pq0.2 base
      let T1 := coupleEdge T a0 b0
      have hab_ne : a0 ≠ b0 := fun heq => by
        have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
          (i := pq0.1) (j := pq0.2) (by omega) hpq0_bnd.2.2 heq
        omega
      have ha0_mem : a0 ∈ getOrbit T.f fuel base := iter_mem_getOrbit_of_closes T.f fuel base hcb pq0.1
      have hb0_mem : b0 ∈ getOrbit T.f fuel base := iter_mem_getOrbit_of_closes T.f fuel base hcb pq0.2
      have hca0 : orbitClosesWithin T.f a0 a0 fuel :=
        orbitClosesWithin_mono T.f a0 a0 (orbitClosesWithin_of_complete T.f darts h_all a0) h_le
      have hb0_a0 : b0 ∈ getOrbit T.f fuel a0 := by
        have hm1 := mem_getOrbit_symm T.f fuel hcb ha0_mem
        exact mem_getOrbit_trans T.f fuel hca0 hm1 hb0_mem
      have h_c1 := coupleEdge_sameFace T darts h_all h_le hpq0_fix.1 hpq0_fix.2 hab_ne hb0_a0
      have h_split := swapCompRight_split_orbits T.f darts h_all h_le hab_ne hb0_a0
      have h_len_a0 : (getOrbit T.f fuel a0).length = L :=
        getOrbit_length_eq_of_complete_mem T.f darts h_all h_le ha0_mem
      have hk_eq : ∃ k : Nat, 1 ≤ k ∧ k < L ∧ Perm.iter T.f k a0 = b0 ∧
          Perm.iter T1.f k b0 = b0 ∧
          (∀ r : Nat, 1 ≤ r → r ≤ k → Perm.iter T1.f r b0 = Perm.iter T.f r a0) ∧
          (∀ x : D, x ∈ getOrbit T1.f fuel b0 ↔ ∃ r : Nat, 1 ≤ r ∧ r ≤ k ∧ Perm.iter T.f r a0 = x) ∧
          (getOrbit T1.f fuel b0).length = k ∧
          Perm.iter T1.f (L - k) a0 = a0 ∧
          (∀ r : Nat, 1 ≤ r → r ≤ L - k → Perm.iter T1.f r a0 = Perm.iter T.f (k + r) a0) ∧
          (∀ x : D, x ∈ getOrbit T1.f fuel a0 ↔ ∃ r : Nat, 1 ≤ r ∧ r ≤ L - k ∧ Perm.iter T.f (k + r) a0 = x) ∧
          (getOrbit T1.f fuel a0).length = L - k := by
        simpa [h_len_a0, T1, coupleEdge, uncoupleEdge] using h_split
      obtain ⟨k, hk1, hkL, hka, hq_b_per, hq_b_eq, h_mem_qb, h_qb_len,
              hq_a_per, hq_a_eq, h_mem_qa, h_qa_len⟩ := hk_eq
      have hk_val : k = pq0.2 - pq0.1 := by
        have h_eq : Perm.iter T.f (k + pq0.1) base = Perm.iter T.f pq0.2 base := by
          rw [Perm.iter_add T.f k pq0.1 base]; exact hka
        by_cases h_sum : k + pq0.1 < L
        · have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := k + pq0.1) (j := pq0.2) h_sum hpq0_bnd.2.2 h_eq
          omega
        · exfalso
          have hL_per := perm_iter_length_getOrbit_eq_self T.f fuel base hcb
          have h_lt : k + pq0.1 - L < pq0.1 := by omega
          have h_mod : Perm.iter T.f (k + pq0.1 - L) base = Perm.iter T.f pq0.2 base := by
            have := Perm.iter_add T.f (k + pq0.1 - L) L base
            rw [hL_per, show k + pq0.1 - L + L = k + pq0.1 by omega] at this
            rw [← h_eq]; exact this.symm
          have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := k + pq0.1 - L) (j := pq0.2) (by omega) hpq0_bnd.2.2 h_mod
          omega
      subst hk_val
      let dlt := pq0.2 - pq0.1
      have hT1_prefix : ∀ r : Nat, r ≤ pq0.1 → Perm.iter T1.f r base = Perm.iter T.f r base := by
        intro r hr
        dsimp [T1, coupleEdge, uncoupleEdge]
        apply swapCompRight_iter_prefix T.f a0 b0 r base
        intro t ht
        refine ⟨?_, ?_⟩
        · intro heq
          have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := t) (j := pq0.1) (by omega) (by omega) heq
          omega
        · intro heq
          have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := t) (j := pq0.2) (by omega) hpq0_bnd.2.2 heq
          omega
      have hT1_suffix : ∀ r : Nat, pq0.1 < r → r ≤ L - dlt →
          Perm.iter T1.f r base = Perm.iter T.f (r + dlt) base := by
        intro r hr1 hr2
        let s := r - pq0.1
        have hs1 : 1 ≤ s := by omega
        have hs_le : s ≤ L - dlt := by omega
        have hr_eq : r = s + pq0.1 := by omega
        rw [hr_eq, Perm.iter_add T1.f s pq0.1 base, hT1_prefix pq0.1 (Nat.le_refl _)]
        rw [hq_a_eq s hs1 hs_le]
        rw [show a0 = Perm.iter T.f pq0.1 base from rfl, ← Perm.iter_add T.f (dlt + s) pq0.1 base]
        congr 1; omega
      have hcb1 : orbitClosesWithin T1.f base base fuel :=
        orbitClosesWithin_mono T1.f base base (orbitClosesWithin_of_complete T1.f darts h_all base) h_le
      have ha0_mem1 : a0 ∈ getOrbit T1.f fuel base := by
        have hm := iter_mem_getOrbit_of_closes T1.f fuel base hcb1 pq0.1
        rw [hT1_prefix pq0.1 (Nat.le_refl _)] at hm
        exact hm
      have h_len1 : (getOrbit T1.f fuel base).length = L - dlt := by
        rw [← getOrbit_length_eq_of_complete_mem T1.f darts h_all h_le ha0_mem1]
        exact h_qa_len
      let shift : Nat × Nat → Nat × Nat := fun pq => (pq.1, pq.2 - dlt)
      let rest1 := rest.map shift
      have hlen1 : rest1.length ≤ n := by
        dsimp [rest1]; rw [List.length_map]; dsimp at hlen; omega
      have h_pw1 : rest1.Pairwise (fun x y => y.1 < x.1 ∧ x.2 < y.2) := by
        rw [List.pairwise_map]
        apply List.Pairwise.imp_of_mem _ (List.pairwise_cons.mp h_pw).2
        intro x y hx hy hxy
        have hxb := h_rel_rest x hx
        have hyb := h_rel_rest y hy
        exact ⟨hxy.1, by dsimp [shift]; omega⟩
      have h_bnd1 : ∀ pq ∈ rest1, 1 ≤ pq.1 ∧ pq.1 < pq.2 ∧ pq.2 < (getOrbit T1.f fuel base).length := by
        intro pq hpq
        rw [List.mem_map] at hpq
        rcases hpq with ⟨⟨p, q⟩, hmem, rfl⟩
        have h_b := h_bnd (p, q) (List.mem_cons_of_mem pq0 hmem)
        have h_r := h_rel_rest (p, q) hmem
        rw [h_len1]
        dsimp [shift] at *
        omega
      have h_pairs_eq : nestedPairs T1 base rest1 = nestedPairs T base rest := by
        dsimp [nestedPairs, rest1]
        rw [List.map_map]
        apply List.map_congr_left
        intro ⟨p, q⟩ hmem
        have h_b := h_bnd (p, q) (List.mem_cons_of_mem pq0 hmem)
        have h_r := h_rel_rest (p, q) hmem
        dsimp [Function.comp, shift]
        ext
        · exact hT1_prefix p (Nat.le_of_lt h_r.1)
        · exact (hT1_suffix (q - dlt) (by omega) (by omega)).trans (by congr 1; omega)
      have h_fix1 : ∀ pq ∈ rest1,
          T1.e.f (Perm.iter T1.f pq.1 base) = Perm.iter T1.f pq.1 base ∧
          T1.e.f (Perm.iter T1.f pq.2 base) = Perm.iter T1.f pq.2 base := by
        intro pq hpq
        rw [List.mem_map] at hpq
        rcases hpq with ⟨⟨p, q⟩, hmem, rfl⟩
        have h_b := h_bnd (p, q) (List.mem_cons_of_mem pq0 hmem)
        have h_r := h_rel_rest (p, q) hmem
        have h_fx := h_fix (p, q) (List.mem_cons_of_mem pq0 hmem)
        have hp_eq : Perm.iter T1.f (shift (p, q)).1 base = Perm.iter T.f p base :=
          hT1_prefix p (Nat.le_of_lt h_r.1)
        have hq_eq : Perm.iter T1.f (shift (p, q)).2 base = Perm.iter T.f q base :=
          (hT1_suffix (q - dlt) (by omega) (by omega)).trans (by congr 1; omega)
        have hp_ne_a0 : Perm.iter T.f p base ≠ a0 := fun heq => by
          have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := p) (j := pq0.1) (by omega) (by omega) heq
          omega
        have hp_ne_b0 : Perm.iter T.f p base ≠ b0 := fun heq => by
          have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := p) (j := pq0.2) (by omega) hpq0_bnd.2.2 heq
          omega
        have hq_ne_a0 : Perm.iter T.f q base ≠ a0 := fun heq => by
          have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := q) (j := pq0.1) (by omega) (by omega) heq
          omega
        have hq_ne_b0 : Perm.iter T.f q base ≠ b0 := fun heq => by
          have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := q) (j := pq0.2) h_b.2.2 hpq0_bnd.2.2 heq
          omega
        refine ⟨?_, ?_⟩
        · rw [hp_eq, coupleEdge_e_of_ne T hpq0_fix.1 hpq0_fix.2 hp_ne_a0 hp_ne_b0]; exact h_fx.1
        · rw [hq_eq, coupleEdge_e_of_ne T hpq0_fix.1 hpq0_fix.2 hq_ne_a0 hq_ne_b0]; exact h_fx.2
      have h_ih := ih T1 rest1 hlen1 h_pw1 h_bnd1 h_fix1
      dsimp only [coupleList, nestedPairs, List.map] at h_ih ⊢
      have h_cl_eq : coupleList T1 ((rest.map (fun pq => (Perm.iter T.f pq.1 base, Perm.iter T.f pq.2 base)))) =
          coupleList T1 (rest1.map (fun pq => (Perm.iter T1.f pq.1 base, Perm.iter T1.f pq.2 base))) := by
        congr 1; exact h_pairs_eq.symm
      rcases h_ih with ⟨hn_ih, he_out_ih, he_in_ih, hreach_ih, hgen_ih, hz_ih, hbase_ih, hi_ih⟩
      rw [h_cl_eq]
      let T' := coupleList T1 (rest1.map (fun pq => (Perm.iter T1.f pq.1 base, Perm.iter T1.f pq.2 base)))
      change T'.n = T.n ∧ _
      have hca01 : orbitClosesWithin T1.f a0 a0 fuel :=
        orbitClosesWithin_mono T1.f a0 a0 (orbitClosesWithin_of_complete T1.f darts h_all a0) h_le
      have h_not_in_T1 : ∀ z : D, z ∉ getOrbit T.f fuel base → z ∉ getOrbit T1.f fuel base := by
        intro z hz hm1
        have hm_a0 : z ∈ getOrbit T1.f fuel a0 :=
          mem_getOrbit_trans T1.f fuel hca01 (mem_getOrbit_symm T1.f fuel hcb1 ha0_mem1) hm1
        rw [h_mem_qa] at hm_a0
        rcases hm_a0 with ⟨r, _, _, rfl⟩
        exact hz (by
          rw [show a0 = Perm.iter T.f pq0.1 base from rfl, ← Perm.iter_add T.f (dlt + r) pq0.1 base]
          exact iter_mem_getOrbit_of_closes T.f fuel base hcb (dlt + r + pq0.1))
      have hb0_not_base1 : b0 ∉ getOrbit T1.f fuel base := by
        intro hm1
        have hm_a0 : b0 ∈ getOrbit T1.f fuel a0 :=
          mem_getOrbit_trans T1.f fuel hca01 (mem_getOrbit_symm T1.f fuel hcb1 ha0_mem1) hm1
        rw [h_mem_qa] at hm_a0
        rcases hm_a0 with ⟨r, hr1, hrL, hreq⟩
        have h_eq' : Perm.iter T.f (dlt + r + pq0.1) base = Perm.iter T.f pq0.2 base := by
          rw [Perm.iter_add T.f (dlt + r) pq0.1 base]; exact hreq
        by_cases hsum : dlt + r + pq0.1 < L
        · have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := dlt + r + pq0.1) (j := pq0.2) hsum hpq0_bnd.2.2 h_eq'
          omega
        · have hL_per := perm_iter_length_getOrbit_eq_self T.f fuel base hcb
          have h_lt : dlt + r + pq0.1 - L < L := by omega
          have h_mod : Perm.iter T.f (dlt + r + pq0.1 - L) base = Perm.iter T.f pq0.2 base := by
            have := Perm.iter_add T.f (dlt + r + pq0.1 - L) L base
            rw [hL_per, show dlt + r + pq0.1 - L + L = dlt + r + pq0.1 by omega] at this
            rw [← h_eq']; exact this.symm
          have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
            (i := dlt + r + pq0.1 - L) (j := pq0.2) h_lt hpq0_bnd.2.2 h_mod
          omega
      refine ⟨hn_ih.trans rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro d hd
        have hd_out1 : ∀ pq1 ∈ rest1, d ≠ Perm.iter T1.f pq1.1 base ∧ d ≠ Perm.iter T1.f pq1.2 base := by
          intro pq1 hpq1
          rw [List.mem_map] at hpq1
          rcases hpq1 with ⟨⟨p, q⟩, hmem, rfl⟩
          have h_b := h_bnd (p, q) (List.mem_cons_of_mem pq0 hmem)
          have h_r := h_rel_rest (p, q) hmem
          have hd_pq := hd (p, q) (List.mem_cons_of_mem pq0 hmem)
          have hp_eq : Perm.iter T1.f (shift (p, q)).1 base = Perm.iter T.f p base :=
            hT1_prefix p (Nat.le_of_lt h_r.1)
          have hq_eq : Perm.iter T1.f (shift (p, q)).2 base = Perm.iter T.f q base :=
            (hT1_suffix (q - dlt) (by omega) (by omega)).trans (by congr 1; omega)
          rw [hp_eq, hq_eq]; exact hd_pq
        have hd0 := hd pq0 List.mem_cons_self
        rw [he_out_ih d hd_out1]
        exact coupleEdge_e_of_ne T hpq0_fix.1 hpq0_fix.2 hd0.1 hd0.2
      · intro pq hpq
        rcases List.mem_cons.mp hpq with hpq0 | hmem
        · rw [hpq0]
          have ha0_out : ∀ pq1 ∈ rest1, a0 ≠ Perm.iter T1.f pq1.1 base ∧ a0 ≠ Perm.iter T1.f pq1.2 base := by
            intro pq1 hpq1
            rw [List.mem_map] at hpq1
            rcases hpq1 with ⟨⟨p, q⟩, hmem, rfl⟩
            have h_b := h_bnd (p, q) (List.mem_cons_of_mem pq0 hmem)
            have h_r := h_rel_rest (p, q) hmem
            have h_qeq : Perm.iter T1.f (shift (p, q)).2 base = Perm.iter T.f q base :=
              (hT1_suffix (q - dlt) (by omega) (by omega)).trans (by congr 1; omega)
            rw [hT1_prefix p (Nat.le_of_lt h_r.1), h_qeq]
            refine ⟨?_, ?_⟩
            · intro heq
              have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
                (i := pq0.1) (j := p) (by omega) (by omega) heq
              omega
            · intro heq
              have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
                (i := pq0.1) (j := q) (by omega) h_b.2.2 heq
              omega
          have hb0_out : ∀ pq1 ∈ rest1, b0 ≠ Perm.iter T1.f pq1.1 base ∧ b0 ≠ Perm.iter T1.f pq1.2 base := by
            intro pq1 hpq1
            rw [List.mem_map] at hpq1
            rcases hpq1 with ⟨⟨p, q⟩, hmem, rfl⟩
            have h_b := h_bnd (p, q) (List.mem_cons_of_mem pq0 hmem)
            have h_r := h_rel_rest (p, q) hmem
            have h_qeq : Perm.iter T1.f (shift (p, q)).2 base = Perm.iter T.f q base :=
              (hT1_suffix (q - dlt) (by omega) (by omega)).trans (by congr 1; omega)
            rw [hT1_prefix p (Nat.le_of_lt h_r.1), h_qeq]
            refine ⟨?_, ?_⟩
            · intro heq
              have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
                (i := pq0.2) (j := p) hpq0_bnd.2.2 (by omega) heq
              omega
            · intro heq
              have hi := perm_iter_inj_of_lt_getOrbit_length T.f (fuel := fuel) (d := base)
                (i := pq0.2) (j := q) hpq0_bnd.2.2 h_b.2.2 heq
              omega
          exact ⟨(he_out_ih a0 ha0_out).trans h_c1.1.1, (he_out_ih b0 hb0_out).trans h_c1.1.2⟩
        · obtain ⟨p, q⟩ := pq
          have h_b := h_bnd (p, q) (List.mem_cons_of_mem pq0 hmem)
          have h_r := h_rel_rest (p, q) hmem
          have hsh : shift (p, q) ∈ rest1 := List.mem_map.mpr ⟨(p, q), hmem, rfl⟩
          have hp_eq : Perm.iter T1.f (shift (p, q)).1 base = Perm.iter T.f p base :=
            hT1_prefix p (Nat.le_of_lt h_r.1)
          have hq_eq : Perm.iter T1.f (shift (p, q)).2 base = Perm.iter T.f q base :=
            (hT1_suffix (q - dlt) (by omega) (by omega)).trans (by congr 1; omega)
          have hin := he_in_ih (shift (p, q)) hsh
          rwa [hp_eq, hq_eq] at hin
      · intro x y; exact (hreach_ih).trans (h_c1.2.1)
      · exact hgen_ih.trans h_c1.2.2.2.2.2
      · intro z hz
        rw [hz_ih z (h_not_in_T1 z hz)]
        have hcz : orbitClosesWithin T.f z z fuel :=
          orbitClosesWithin_mono T.f z z (orbitClosesWithin_of_complete T.f darts h_all z) h_le
        have hza : a0 ∉ getOrbit T.f fuel z := fun hm =>
          hz (mem_getOrbit_symm T.f fuel hcz
            (mem_getOrbit_trans T.f fuel hcz hm (mem_getOrbit_symm T.f fuel hcb ha0_mem)))
        have hzb : b0 ∉ getOrbit T.f fuel z := fun hm =>
          hz (mem_getOrbit_symm T.f fuel hcz
            (mem_getOrbit_trans T.f fuel hcz hm (mem_getOrbit_symm T.f fuel hcb hb0_mem)))
        exact (swapCompRight_iter_eq_of_not_mem_orbit T.f darts h_all h_le hza hzb).2
      · intro x
        rw [hbase_ih x, h_len1]
        constructor
        · rintro ⟨r1, hr1_lt, hr1_out, hreq⟩
          by_cases hr1_le : r1 ≤ pq0.1
          · refine ⟨r1, by omega, ?_, ?_⟩
            · intro pq hpq
              rcases List.mem_cons.mp hpq with rfl | hmem
              · omega
              · have h_r := h_rel_rest pq hmem
                have h_b := h_bnd pq (List.mem_cons_of_mem pq0 hmem)
                have hsh := hr1_out (shift pq) (List.mem_map.mpr ⟨pq, hmem, rfl⟩)
                dsimp [shift] at hsh
                omega
            · rw [← hT1_prefix r1 hr1_le]; exact hreq
          · refine ⟨r1 + dlt, by omega, ?_, ?_⟩
            · intro pq hpq
              rcases List.mem_cons.mp hpq with rfl | hmem
              · omega
              · have h_r := h_rel_rest pq hmem
                have h_b := h_bnd pq (List.mem_cons_of_mem pq0 hmem)
                have hsh := hr1_out (shift pq) (List.mem_map.mpr ⟨pq, hmem, rfl⟩)
                dsimp [shift] at hsh
                omega
            · rw [← hT1_suffix r1 (by omega) (by omega)]; exact hreq
        · rintro ⟨r, hr_lt, hr_out, hreq⟩
          have hr0 := hr_out pq0 List.mem_cons_self
          by_cases hr_le : r ≤ pq0.1
          · refine ⟨r, by omega, ?_, ?_⟩
            · intro pq1 hpq1
              rw [List.mem_map] at hpq1
              rcases hpq1 with ⟨pq, hmem, rfl⟩
              have h_r := h_rel_rest pq hmem
              have h_b := h_bnd pq (List.mem_cons_of_mem pq0 hmem)
              have hro := hr_out pq (List.mem_cons_of_mem pq0 hmem)
              dsimp [shift]
              omega
            · rw [hT1_prefix r hr_le]; exact hreq
          · refine ⟨r - dlt, by omega, ?_, ?_⟩
            · intro pq1 hpq1
              rw [List.mem_map] at hpq1
              rcases hpq1 with ⟨pq, hmem, rfl⟩
              have h_r := h_rel_rest pq hmem
              have h_b := h_bnd pq (List.mem_cons_of_mem pq0 hmem)
              have hro := hr_out pq (List.mem_cons_of_mem pq0 hmem)
              dsimp [shift]
              omega
            · rw [hT1_suffix (r - dlt) (by omega) (by omega), show r - dlt + dlt = r by omega]
              exact hreq
      · intro i hi x
        cases i with
        | zero =>
          dsimp
          rw [hz_ih b0 hb0_not_base1, h_mem_qb]
          constructor
          · rintro ⟨s, hs1, hsd, rfl⟩
            refine ⟨pq0.1 + s, by omega, by omega, fun j hj => by omega, ?_⟩
            rw [Nat.add_comm pq0.1 s, Perm.iter_add T.f s pq0.1 base]
          · rintro ⟨r, hr1, hr2, _, rfl⟩
            refine ⟨r - pq0.1, by omega, by omega, ?_⟩
            rw [show a0 = Perm.iter T.f pq0.1 base from rfl, ← Perm.iter_add T.f (r - pq0.1) pq0.1 base]
            congr 1; omega
        | succ i' =>
          dsimp at hi ⊢
          have hi' : i' < rest1.length := by dsimp [rest1]; rw [List.length_map]; omega
          have h_r := h_rel_rest rest[i'] (List.getElem_mem _)
          have h_b := h_bnd rest[i'] (List.mem_cons_of_mem pq0 (List.getElem_mem _))
          have h_tgt : Perm.iter T.f rest[i'].2 base = Perm.iter T1.f rest1[i'].2 base := by
            dsimp [rest1, shift]
            rw [List.getElem_map]
            exact ((hT1_suffix (rest[i'].2 - dlt) (by omega) (by omega)).trans (by congr 1; omega)).symm
          rw [h_tgt, hi_ih i' hi' x]
          have h_map_get : ∀ j (hj : j < i'), rest1[j] = shift rest[j] := fun j hj => by
            dsimp [rest1]; rw [List.getElem_map]
          have h_rel_j : ∀ j (hj : j < i'), rest[j].1 < pq0.1 ∧ pq0.2 < rest[j].2 := fun j hj =>
            h_rel_rest rest[j] (List.getElem_mem _)
          have h_bnd_j : ∀ j (hj : j < i'), 1 ≤ rest[j].1 ∧ rest[j].1 < rest[j].2 ∧ rest[j].2 < L := fun j hj =>
            h_bnd rest[j] (List.mem_cons_of_mem pq0 (List.getElem_mem _))
          constructor
          · rintro ⟨r1, hr1_lt, hr1_le, hr1_out, hreq⟩
            rw [List.getElem_map] at hr1_lt hr1_le
            dsimp [shift] at hr1_lt hr1_le
            by_cases hr1_p0 : r1 ≤ pq0.1
            · refine ⟨r1, hr1_lt, by omega, ?_, ?_⟩
              · intro j hj
                cases j with
                | zero => dsimp; omega
                | succ j' =>
                  dsimp
                  have hj' : j' < i' := by omega
                  have ho := hr1_out j' hj'
                  rw [h_map_get j' hj'] at ho
                  dsimp [shift] at ho
                  have hbj := h_bnd_j j' hj'
                  have hrj := h_rel_j j' hj'
                  omega
              · rw [← hT1_prefix r1 hr1_p0]; exact hreq
            · refine ⟨r1 + dlt, by omega, by omega, ?_, ?_⟩
              · intro j hj
                cases j with
                | zero => dsimp; omega
                | succ j' =>
                  dsimp
                  have hj' : j' < i' := by omega
                  have ho := hr1_out j' hj'
                  rw [h_map_get j' hj'] at ho
                  dsimp [shift] at ho
                  have hbj := h_bnd_j j' hj'
                  have hrj := h_rel_j j' hj'
                  omega
              · rw [← hT1_suffix r1 (by omega) (by omega)]; exact hreq
          · rintro ⟨r, hr_lt, hr_le, hr_out, hreq⟩
            have hr0 := hr_out 0 (Nat.zero_lt_succ i')
            dsimp at hr0
            rw [List.getElem_map]
            dsimp [shift]
            by_cases hr_p0 : r ≤ pq0.1
            · refine ⟨r, hr_lt, by omega, ?_, ?_⟩
              · intro j' hj'
                rw [h_map_get j' hj']
                dsimp [shift]
                have ho := hr_out (j' + 1) (by omega)
                dsimp at ho
                have hbj := h_bnd_j j' hj'
                have hrj := h_rel_j j' hj'
                omega
              · rw [hT1_prefix r hr_p0]; exact hreq
            · refine ⟨r - dlt, by omega, by omega, ?_, ?_⟩
              · intro j' hj'
                rw [h_map_get j' hj']
                dsimp [shift]
                have ho := hr_out (j' + 1) (by omega)
                dsimp at ho
                have hbj := h_bnd_j j' hj'
                have hrj := h_rel_j j' hj'
                omega
              · rw [hT1_suffix (r - dlt) (by omega) (by omega), show r - dlt + dlt = r by omega]
                exact hreq

/-- Recursive rainbow-peeling engine: coupling nested pairs `(pᵢ, qᵢ)` on `T.f`'s orbit of `base`
    preserves `genusDeficit`, `ReachEN`, `n`, all faces disjoint from `base`, and partitions the
    `base`-orbit into explicit peeled faces plus the surviving outer `base`-orbit. -/
theorem coupleNestedPairs_spec [DecidableEq D] (T : PermTriple D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (base : D) (specs : List (Nat × Nat)) :
    let L := (getOrbit T.f fuel base).length
    specs.Pairwise (fun x y => y.1 < x.1 ∧ x.2 < y.2) →
    (∀ pq ∈ specs, 1 ≤ pq.1 ∧ pq.1 < pq.2 ∧ pq.2 < L) →
    (∀ pq ∈ specs, T.e.f (Perm.iter T.f pq.1 base) = Perm.iter T.f pq.1 base ∧
                   T.e.f (Perm.iter T.f pq.2 base) = Perm.iter T.f pq.2 base) →
    let T' := coupleList T (nestedPairs T base specs)
    T'.n = T.n ∧
    (∀ d : D, (∀ pq ∈ specs, d ≠ Perm.iter T.f pq.1 base ∧ d ≠ Perm.iter T.f pq.2 base) →
      T'.e.f d = T.e.f d) ∧
    (∀ pq ∈ specs, T'.e.f (Perm.iter T.f pq.1 base) = Perm.iter T.f pq.2 base ∧
                   T'.e.f (Perm.iter T.f pq.2 base) = Perm.iter T.f pq.1 base) ∧
    (∀ {x y : D}, ReachEN T'.e T'.n x y ↔ ReachEN T.e T.n x y) ∧
    (genusDeficit T' fuel darts = genusDeficit T fuel darts) ∧
    (∀ z : D, z ∉ getOrbit T.f fuel base → getOrbit T'.f fuel z = getOrbit T.f fuel z) ∧
    (∀ x : D, x ∈ getOrbit T'.f fuel base ↔
      ∃ r : Nat, r < L ∧
        (∀ pq ∈ specs, ¬(pq.1 < r ∧ r ≤ pq.2)) ∧
        Perm.iter T.f r base = x) ∧
    (∀ i : Nat, (hi : i < specs.length) →
      ∀ x : D, x ∈ getOrbit T'.f fuel (Perm.iter T.f specs[i].2 base) ↔
        ∃ r : Nat, specs[i].1 < r ∧ r ≤ specs[i].2 ∧
          (∀ j : Nat, (hj : j < i) →
            ¬(specs[j].1 < r ∧ r ≤ specs[j].2)) ∧
          Perm.iter T.f r base = x) :=
  coupleNestedPairs_spec_aux darts h_all h_le base specs.length T specs (Nat.le_refl _)

end SwapCompRightAndCoupleEdge

section SimpleEquivAndSubtypeAssembly

/-- Explicit universe-`0` equivalence `α ≃ β` avoiding Mathlib dependencies. -/
structure SimpleEquiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x : α, invFun (toFun x) = x
  right_inv : ∀ y : β, toFun (invFun y) = y

def SimpleEquiv.symm {α β : Type} (e : SimpleEquiv α β) : SimpleEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

theorem SimpleEquiv.toFun_inj {α β : Type} (e : SimpleEquiv α β) {x y : α}
    (h : e.toFun x = e.toFun y) : x = y := by
  have hi := congrArg e.invFun h
  rwa [e.left_inv, e.left_inv] at hi

theorem SimpleEquiv.toFun_eq_iff {α β : Type} (e : SimpleEquiv α β) (x : α) (y : β) :
    e.toFun x = y ↔ x = e.invFun y := by
  constructor
  · rintro rfl; exact (e.left_inv x).symm
  · rintro rfl; exact e.right_inv y

/-- Identity permutation on a type `D`. -/
def permId {D : Type} : Perm D where
  f := id
  inv := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport a permutation along a `SimpleEquiv`. -/
def permMapEquiv {α β : Type} (p : Perm α) (e : SimpleEquiv α β) : Perm β where
  f y := e.toFun (p.f (e.invFun y))
  inv y := e.toFun (p.inv (e.invFun y))
  left_inv y := by simp only [e.left_inv, p.left_inv, e.right_inv]
  right_inv y := by simp only [e.left_inv, p.right_inv, e.right_inv]

theorem permMapEquiv_iter {α β : Type} (p : Perm α) (e : SimpleEquiv α β) :
    ∀ (k : Nat) (x : α), Perm.iter (permMapEquiv p e) k (e.toFun x) = e.toFun (Perm.iter p k x)
  | 0, _ => rfl
  | k + 1, x => by
    rw [Perm.iter_succ, Perm.iter_succ, permMapEquiv_iter p e k x]
    dsimp [permMapEquiv]
    rw [e.left_inv]

/-- Transport a `PermTriple` along a `SimpleEquiv`. -/
def PermTriple.mapEquiv {α β : Type} (T : PermTriple α) (φ : SimpleEquiv α β) : PermTriple β where
  e := permMapEquiv T.e φ
  n := permMapEquiv T.n φ
  f := permMapEquiv T.f φ
  enf_id y := by
    dsimp [permMapEquiv]
    simp only [φ.left_inv, T.enf_id, φ.right_inv]

def stepEN_mapEquiv_fwd {α β : Type} {e n : Perm α} (φ : SimpleEquiv α β) {u v : α}
    (s : StepEN e n u v) :
    StepEN (permMapEquiv e φ) (permMapEquiv n φ) (φ.toFun u) (φ.toFun v) := by
  cases s with
  | e_fwd =>
      simpa [permMapEquiv, φ.left_inv] using
        StepEN.e_fwd (e := permMapEquiv e φ) (n := permMapEquiv n φ) (φ.toFun u)
  | e_bwd =>
      simpa [permMapEquiv, φ.left_inv] using
        StepEN.e_bwd (e := permMapEquiv e φ) (n := permMapEquiv n φ) (φ.toFun u)
  | n_fwd =>
      simpa [permMapEquiv, φ.left_inv] using
        StepEN.n_fwd (e := permMapEquiv e φ) (n := permMapEquiv n φ) (φ.toFun u)
  | n_bwd =>
      simpa [permMapEquiv, φ.left_inv] using
        StepEN.n_bwd (e := permMapEquiv e φ) (n := permMapEquiv n φ) (φ.toFun u)

def stepEN_mapEquiv_bwd {α β : Type} {e n : Perm α} (φ : SimpleEquiv α β) {u v : β}
    (s : StepEN (permMapEquiv e φ) (permMapEquiv n φ) u v) :
    StepEN e n (φ.invFun u) (φ.invFun v) := by
  cases s with
  | e_fwd =>
    dsimp [permMapEquiv]; rw [φ.left_inv]; exact StepEN.e_fwd (φ.invFun u)
  | e_bwd =>
    dsimp [permMapEquiv]; rw [φ.left_inv]; exact StepEN.e_bwd (φ.invFun u)
  | n_fwd =>
    dsimp [permMapEquiv]; rw [φ.left_inv]; exact StepEN.n_fwd (φ.invFun u)
  | n_bwd =>
    dsimp [permMapEquiv]; rw [φ.left_inv]; exact StepEN.n_bwd (φ.invFun u)

private def walkEN_mapEquiv_bwd {α β : Type} {e n : Perm α} (φ : SimpleEquiv α β) :
    ∀ {u v : β}, WalkEN (permMapEquiv e φ) (permMapEquiv n φ) u v →
      WalkEN e n (φ.invFun u) (φ.invFun v)
  | _, _, WalkEN.refl _ => WalkEN.refl _
  | _, _, WalkEN.step s w => WalkEN.step (stepEN_mapEquiv_bwd φ s) (walkEN_mapEquiv_bwd φ w)

private def walkEN_mapEquiv_fwd {α β : Type} {e n : Perm α} (φ : SimpleEquiv α β) :
    ∀ {u v : α}, WalkEN e n u v →
      WalkEN (permMapEquiv e φ) (permMapEquiv n φ) (φ.toFun u) (φ.toFun v)
  | _, _, WalkEN.refl _ => WalkEN.refl _
  | _, _, WalkEN.step s w => WalkEN.step (stepEN_mapEquiv_fwd φ s) (walkEN_mapEquiv_fwd φ w)

theorem reachEN_mapEquiv_iff {α β : Type} (e n : Perm α) (φ : SimpleEquiv α β) (x y : α) :
    ReachEN (permMapEquiv e φ) (permMapEquiv n φ) (φ.toFun x) (φ.toFun y) ↔ ReachEN e n x y := by
  constructor
  · rintro ⟨w⟩
    have hw := walkEN_mapEquiv_bwd φ w
    rw [φ.left_inv, φ.left_inv] at hw
    exact ⟨hw⟩
  · rintro ⟨w⟩
    exact ⟨walkEN_mapEquiv_fwd φ w⟩

private theorem filter_map_not_decide {α β : Type}
    (R1 : α → α → Prop) [DecidableRel R1] (R2 : β → β → Prop) [DecidableRel R2]
    (φ : α → β) (h_iff : ∀ x y : α, R2 (φ x) (φ y) ↔ R1 x y) (a : α) :
    ∀ (as : List α),
      (as.map φ).filter (fun b => !decide (R2 (φ a) b)) =
        (as.filter (fun x => !decide (R1 a x))).map φ
  | [] => rfl
  | x :: xs => by
    dsimp [List.map, List.filter]
    by_cases h1 : R1 a x
    · have h2 : R2 (φ a) (φ x) := (h_iff a x).mpr h1
      simp [h1, h2, filter_map_not_decide R1 R2 φ h_iff a xs]
    · have h2 : ¬ R2 (φ a) (φ x) := fun hm => h1 ((h_iff a x).mp hm)
      simp [h1, h2, filter_map_not_decide R1 R2 φ h_iff a xs]

private theorem countRelClasses_map_aux {α β : Type}
    (R1 : α → α → Prop) [DecidableRel R1] (R2 : β → β → Prop) [DecidableRel R2]
    (φ : α → β) (h_iff : ∀ x y : α, R2 (φ x) (φ y) ↔ R1 x y) :
    ∀ (k : Nat) (l : List α), l.length ≤ k →
      countRelClasses R2 (l.map φ) = countRelClasses R1 l
  | 0, l, hlen => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hnil; rfl
  | _ + 1, [], _ => rfl
  | k + 1, a :: as, hlen => by
    rw [List.map_cons, countRelClasses_cons, countRelClasses_cons]
    rw [filter_map_not_decide R1 R2 φ h_iff a as]
    congr 1
    exact countRelClasses_map_aux R1 R2 φ h_iff k (as.filter (fun x => !decide (R1 a x)))
      (Nat.le_trans (List.length_filter_le _ as) (by dsimp at hlen; omega))

theorem countRelClasses_mapEquiv {α β : Type}
    (R1 : α → α → Prop) [DecidableRel R1] (R2 : β → β → Prop) [DecidableRel R2]
    (φ : α → β) (h_iff : ∀ x y : α, R2 (φ x) (φ y) ↔ R1 x y) (l : List α) :
    countRelClasses R2 (l.map φ) = countRelClasses R1 l :=
  countRelClasses_map_aux R1 R2 φ h_iff l.length l (Nat.le_refl _)

theorem countOrbits_mapEquiv {α β : Type} [DecidableEq α] [DecidableEq β]
    (p : Perm α) (φ : SimpleEquiv α β) (darts : List α) (h_all : ∀ x : α, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    countOrbits (permMapEquiv p φ) fuel (darts.map φ.toFun) = countOrbits p fuel darts := by
  have h_all_b : ∀ y : β, y ∈ darts.map φ.toFun := fun y =>
    List.mem_map.mpr ⟨φ.invFun y, h_all _, φ.right_inv y⟩
  have h_le_b : (darts.map φ.toFun).length ≤ fuel := by rw [List.length_map]; exact h_le
  have hid_a : permMapEquiv (permId : Perm α) φ = (permId : Perm β) := by
    apply perm_eq_of_f_eq
    intro y; dsimp [permMapEquiv, permId]; exact φ.right_inv y
  rw [← countRelClasses_reachEN_eq_countOrbits_of_edge_id (permId : Perm β) (permMapEquiv p φ)
        (fun _ => rfl) (darts.map φ.toFun) h_all_b h_le_b (darts.map φ.toFun),
      ← countRelClasses_reachEN_eq_countOrbits_of_edge_id (permId : Perm α) p
        (fun _ => rfl) darts h_all h_le darts]
  apply countRelClasses_mapEquiv
  intro x y
  rw [← hid_a]
  exact reachEN_mapEquiv_iff permId p φ x y

theorem genusDeficit_mapEquiv {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : PermTriple α) (φ : SimpleEquiv α β) (darts : List α)
    (h_all : ∀ x : α, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    genusDeficit (T.mapEquiv φ) fuel (darts.map φ.toFun) = genusDeficit T fuel darts := by
  have h_all_b : ∀ y : β, y ∈ darts.map φ.toFun := fun y =>
    List.mem_map.mpr ⟨φ.invFun y, h_all _, φ.right_inv y⟩
  have h_le_b : (darts.map φ.toFun).length ≤ fuel := by rw [List.length_map]; exact h_le
  have hlen : (darts.map φ.toFun).length = darts.length := List.length_map _
  have hC : countRelClasses (ReachEN (permMapEquiv T.e φ) (permMapEquiv T.n φ)) (darts.map φ.toFun) =
      countRelClasses (ReachEN T.e T.n) darts :=
    countRelClasses_mapEquiv _ _ φ.toFun (reachEN_mapEquiv_iff T.e T.n φ) darts
  have hV := countOrbits_mapEquiv T.n φ darts h_all h_le
  have hE := countOrbits_mapEquiv T.e φ darts h_all h_le
  have hF := countOrbits_mapEquiv T.f φ darts h_all h_le
  dsimp [genusDeficit, PermTriple.mapEquiv]
  rw [hlen, hC, hV, hE, hF]

theorem mem_getOrbit_mapEquiv_iff {α β : Type} [DecidableEq α] [DecidableEq β]
    (p : Perm α) (φ : SimpleEquiv α β) (darts : List α) (h_all : ∀ x : α, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (x : α) (y : β) :
    y ∈ getOrbit (permMapEquiv p φ) fuel (φ.toFun x) ↔ φ.invFun y ∈ getOrbit p fuel x := by
  have h_all_b : ∀ z : β, z ∈ darts.map φ.toFun := fun z =>
    List.mem_map.mpr ⟨φ.invFun z, h_all _, φ.right_inv z⟩
  have h_le_b : (darts.map φ.toFun).length ≤ fuel := by rw [List.length_map]; exact h_le
  have hcx : orbitClosesWithin p x x fuel :=
    orbitClosesWithin_mono p x x (orbitClosesWithin_of_complete p darts h_all x) h_le
  have hcy : orbitClosesWithin (permMapEquiv p φ) (φ.toFun x) (φ.toFun x) fuel :=
    orbitClosesWithin_mono (permMapEquiv p φ) (φ.toFun x) (φ.toFun x)
      (orbitClosesWithin_of_complete (permMapEquiv p φ) (darts.map φ.toFun) h_all_b (φ.toFun x)) h_le_b
  rw [mem_getOrbit_iff_exists_iter (permMapEquiv p φ) fuel (φ.toFun x) y hcy,
      mem_getOrbit_iff_exists_iter p fuel x (φ.invFun y) hcx]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [permMapEquiv_iter p φ k x] at hk
    have hi := congrArg φ.invFun hk
    rwa [φ.left_inv] at hi
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [permMapEquiv_iter p φ k x, ← hk, φ.right_inv]

/-- Index finder witnessing `a ∈ l` as a `Fin l.length` element. -/
def findFinIdx {α : Type} [DecidableEq α] (a : α) : ∀ (l : List α), a ∈ l → Fin l.length
  | [], h => False.elim (List.not_mem_nil h)
  | x :: xs, h =>
    if hxa : x = a then ⟨0, Nat.zero_lt_succ _⟩
    else
      have hxs : a ∈ xs := (List.mem_cons.mp h).resolve_left (Ne.symm hxa)
      let r := findFinIdx a xs hxs
      ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩

theorem getElem_findFinIdx {α : Type} [DecidableEq α] (a : α) :
    ∀ (l : List α) (ha : a ∈ l), l[(findFinIdx a l ha).val] = a
  | [], ha => False.elim (List.not_mem_nil ha)
  | x :: xs, ha => by
    dsimp [findFinIdx]
    split
    · next hxa => exact hxa
    · next hxa => exact getElem_findFinIdx a xs _

theorem findFinIdx_getElem {α : Type} [DecidableEq α] :
    ∀ (l : List α), l.Nodup → ∀ (i : Fin l.length),
      findFinIdx l[i.val] l (List.getElem_mem i.isLt) = i
  | [], _, i => Fin.elim0 i
  | x :: xs, hnd, i => by
    have hcons := List.nodup_cons.mp hnd
    cases i using Fin.cases with
    | zero =>
      simp [findFinIdx]
    | succ j =>
      have hne : x ≠ xs[j.val] := fun h => hcons.1 (h ▸ List.getElem_mem j.isLt)
      simp only [Fin.val_succ, List.getElem_cons_succ, findFinIdx, dif_neg hne]
      have ih := findFinIdx_getElem xs hcons.2 j
      apply Fin.ext
      dsimp at ih ⊢
      exact congrArg (· + 1) (congrArg Fin.val ih)

/-- Canonical equivalence `Fin xs.length ≃ { x : α // x ∈ xs }` for a `Nodup` list. -/
def finEquivOfNodup {α : Type} [DecidableEq α] (xs : List α) (hnd : xs.Nodup) :
    SimpleEquiv (Fin xs.length) { x : α // x ∈ xs } where
  toFun i := ⟨xs[i.val], List.getElem_mem i.isLt⟩
  invFun y := findFinIdx y.1 xs y.2
  left_inv i := findFinIdx_getElem xs hnd i
  right_inv y := by ext; exact getElem_findFinIdx y.1 xs y.2

/-- A single degree-`m` vertex with `m` fixed edge darts `(0, 1, …, m-1)`. -/
def singleCycleTriple (m : Nat) (hm : 1 ≤ m) : PermTriple (Fin m) where
  e := permId
  n := {
    f := fun i => ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩
    inv := fun i => ⟨(i.val + m - 1) % m, Nat.mod_lt _ hm⟩
    left_inv := fun i => by
      ext; dsimp
      have hi : i.val < m := i.isLt
      have : (i.val + 1) % m + m - 1 = i.val + m ∨ (i.val + 1) % m + m - 1 = i.val := by
        by_cases h : i.val + 1 < m
        · rw [Nat.mod_eq_of_lt h]; left; omega
        · have h1 : i.val + 1 = m := by omega
          rw [h1, Nat.mod_self]; right; omega
      rcases this with h | h <;> rw [h]
      · rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · exact Nat.mod_eq_of_lt hi
    right_inv := fun i => by
      ext; dsimp
      have hi : i.val < m := i.isLt
      by_cases h0 : i.val = 0
      · rw [h0, Nat.zero_add]
        have h1 : m - 1 < m := by omega
        rw [Nat.mod_eq_of_lt h1, show m - 1 + 1 = m by omega, Nat.mod_self]
      · have h1 : i.val + m - 1 = m + (i.val - 1) := by omega
        rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : i.val - 1 < m),
            show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]
  }
  f := {
    f := fun i => ⟨(i.val + m - 1) % m, Nat.mod_lt _ hm⟩
    inv := fun i => ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩
    left_inv := fun i => by
      ext; dsimp
      have hi : i.val < m := i.isLt
      by_cases h0 : i.val = 0
      · rw [h0, Nat.zero_add]
        have h1 : m - 1 < m := by omega
        rw [Nat.mod_eq_of_lt h1, show m - 1 + 1 = m by omega, Nat.mod_self]
      · have h1 : i.val + m - 1 = m + (i.val - 1) := by omega
        rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : i.val - 1 < m),
            show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]
    right_inv := fun i => by
      ext; dsimp
      have hi : i.val < m := i.isLt
      by_cases h : i.val + 1 < m
      · rw [Nat.mod_eq_of_lt h, show i.val + 1 + m - 1 = i.val + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have h1 : i.val + 1 = m := by omega
        rw [h1, Nat.mod_self, show 0 + m - 1 = m - 1 by omega, Nat.mod_eq_of_lt (by omega)]
        omega
  }
  enf_id := fun i => by
    ext; dsimp [permId]
    have hi : i.val < m := i.isLt
    by_cases h0 : i.val = 0
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m), show m - 1 + 1 = m by omega, Nat.mod_self]
    · rw [show i.val + m - 1 = m + (i.val - 1) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega : i.val - 1 < m), show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]

theorem singleCycleTriple_iter_n (m : Nat) (hm : 1 ≤ m) :
    ∀ k : Nat, Perm.iter (singleCycleTriple m hm).n k ⟨0, hm⟩ = ⟨k % m, Nat.mod_lt _ hm⟩
  | 0 => by ext; simp
  | k + 1 => by
    rw [Perm.iter_succ, singleCycleTriple_iter_n m hm k]
    ext; dsimp [singleCycleTriple]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

theorem singleCycleTriple_iter_f (m : Nat) (hm : 1 ≤ m) (k : Nat) (hk : k ≤ m) :
    Perm.iter (singleCycleTriple m hm).f k ⟨m - 1, by omega⟩ = ⟨m - 1 - (k % m), by omega⟩ := by
  induction k with
  | zero =>
    ext; simp
  | succ k ih =>
    by_cases hk_lt : k + 1 < m
    · rw [Perm.iter_succ, ih (by omega)]
      ext; dsimp [singleCycleTriple]
      rw [Nat.mod_eq_of_lt (by omega : k < m), Nat.mod_eq_of_lt hk_lt,
          show m - 1 - k + m - 1 = m + (m - 1 - (k + 1)) by omega, Nat.add_mod_left,
          Nat.mod_eq_of_lt (by omega)]
    · have hkm : k + 1 = m := by omega
      subst hkm
      rw [Perm.iter_succ, ih (by omega)]
      ext; dsimp [singleCycleTriple]
      rw [Nat.mod_eq_of_lt (by omega : k < k + 1), Nat.mod_self]
      have h_arith : k + 1 - 1 - k + (k + 1) - 1 = k := by omega
      rw [show (k - k + k) = k by omega, Nat.mod_eq_of_lt (by omega)]
      omega

theorem singleCycleTriple_spec (m : Nat) (hm : 1 ≤ m) :
    let T := singleCycleTriple m hm
    let darts := List.finRange m
    genusDeficit T m darts = 0 ∧
    countRelClasses (ReachEN T.e T.n) darts = 1 ∧
    countOrbits T.f m darts = 1 ∧
    (∀ i : Fin m, i ∈ getOrbit T.f m ⟨0, hm⟩) ∧
    (getOrbit T.f m ⟨0, hm⟩).length = m := by
  intro T darts
  have h_all : ∀ x : Fin m, x ∈ darts := fun x => List.mem_finRange x
  have h_nodup : darts.Nodup :=
    List.pairwise_iff_getElem.mpr (fun i j hi hj hlt h => by
      simp [darts, List.getElem_finRange] at h; omega)
  have h_le : darts.length ≤ m := by simp [darts]
  have h_reach : ∀ x y : Fin m, ReachEN T.e T.n x y := by
    have h0 : ∀ i : Fin m, ReachEN T.e T.n ⟨0, hm⟩ i := fun i => by
      have hi := singleCycleTriple_iter_n m hm i.val
      have heq : Perm.iter T.n i.val ⟨0, hm⟩ = i :=
        Fin.ext (by rw [congrArg Fin.val hi]; exact Nat.mod_eq_of_lt i.isLt)
      rw [← heq]
      exact sameOrbit_n_imp_reachEN ⟨i.val, rfl⟩
    intro x y
    exact reachEN_trans _ _ (reachEN_symm _ _ (h0 x)) (h0 y)
  have hne : darts ≠ [] := by
    intro h; have := h_all ⟨0, hm⟩; rw [h] at this; cases this
  have hC : countRelClasses (ReachEN T.e T.n) darts = 1 :=
    countRelClasses_eq_one_of_forall (ReachEN T.e T.n) ⟨0, hm⟩
      (fun x _ => h_reach ⟨0, hm⟩ x) hne (fun h => reachEN_symm _ _ h)
      (fun h1 h2 => reachEN_trans _ _ h1 h2)
  have hV : countOrbits T.n m darts = 1 := by
    rw [← countRelClasses_reachEN_eq_countOrbits_of_edge_id T.e T.n (fun _ => rfl) darts h_all h_le darts]
    exact hC
  have hE : countOrbits T.e m darts = m := by
    simpa [darts, T, singleCycleTriple] using
      countOrbits_eq_length_of_id T.e (fun _ => rfl) hm darts h_nodup
  have hf_reach : ∀ x y : Fin m, ReachEN T.e T.f x y := by
    have hf_0 : ∀ i : Fin m, Perm.iter T.f (m - 1 - i.val) ⟨m - 1, by omega⟩ = i := fun i => by
      have hi := singleCycleTriple_iter_f m hm (m - 1 - i.val) (by omega)
      apply Fin.ext
      rw [congrArg Fin.val hi]
      dsimp
      rw [Nat.mod_eq_of_lt (by omega : m - 1 - i.val < m)]
      omega
    intro x y
    have h0x : ReachEN T.e T.f ⟨m - 1, by omega⟩ x := by
      rw [← hf_0 x]; exact sameOrbit_n_imp_reachEN ⟨m - 1 - x.val, rfl⟩
    have h0y : ReachEN T.e T.f ⟨m - 1, by omega⟩ y := by
      rw [← hf_0 y]; exact sameOrbit_n_imp_reachEN ⟨m - 1 - y.val, rfl⟩
    exact reachEN_trans _ _ (reachEN_symm _ _ h0x) h0y
  have hF : countOrbits T.f m darts = 1 := by
    rw [← countRelClasses_reachEN_eq_countOrbits_of_edge_id T.e T.f (fun _ => rfl) darts h_all h_le darts]
    exact countRelClasses_eq_one_of_forall (ReachEN T.e T.f) ⟨0, hm⟩
      (fun x _ => hf_reach ⟨0, hm⟩ x) hne (fun h => reachEN_symm _ _ h)
      (fun h1 h2 => reachEN_trans _ _ h1 h2)
  have hgen : genusDeficit T m darts = 0 := by
    dsimp [genusDeficit]
    rw [show darts.length = m by simp [darts], hC, hV, hE, hF]
    omega
  have hc0 : orbitClosesWithin T.f ⟨0, hm⟩ ⟨0, hm⟩ m :=
    orbitClosesWithin_mono T.f ⟨0, hm⟩ ⟨0, hm⟩
      (orbitClosesWithin_of_complete T.f darts h_all ⟨0, hm⟩) h_le
  have h_mem_0 : ∀ i : Fin m, i ∈ getOrbit T.f m ⟨0, hm⟩ := by
    intro i
    have hm1 : ⟨m - 1, by omega⟩ ∈ getOrbit T.f m ⟨0, hm⟩ := by
      have hc_m : orbitClosesWithin T.f ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩ m :=
        orbitClosesWithin_mono T.f ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
          (orbitClosesWithin_of_complete T.f darts h_all _) h_le
      have h0m : (⟨0, hm⟩ : Fin m) ∈ getOrbit T.f m ⟨m - 1, by omega⟩ := by
        rw [mem_getOrbit_iff_exists_iter T.f m _ _ hc_m]
        refine ⟨m - 1, ?_⟩
        have hf := singleCycleTriple_iter_f m hm (m - 1) (by omega)
        apply Fin.ext
        rw [congrArg Fin.val hf]; dsimp
        rw [Nat.mod_eq_of_lt (by omega : m - 1 < m)]
        omega
      exact mem_getOrbit_symm T.f m hc_m h0m
    have hi_m : i ∈ getOrbit T.f m ⟨m - 1, by omega⟩ := by
      have hc_m : orbitClosesWithin T.f ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩ m :=
        orbitClosesWithin_mono T.f ⟨m - 1, by omega⟩ ⟨m - 1, by omega⟩
          (orbitClosesWithin_of_complete T.f darts h_all _) h_le
      rw [mem_getOrbit_iff_exists_iter T.f m _ _ hc_m]
      refine ⟨m - 1 - i.val, ?_⟩
      have hf := singleCycleTriple_iter_f m hm (m - 1 - i.val) (by omega)
      apply Fin.ext
      rw [congrArg Fin.val hf]; dsimp
      rw [Nat.mod_eq_of_lt (by omega : m - 1 - i.val < m)]
      omega
    exact mem_getOrbit_trans T.f m hc0 hm1 hi_m
  have h_len_0 : (getOrbit T.f m ⟨0, hm⟩).length = m := by
    let last : Fin m := ⟨m - 1, by omega⟩
    have hlast_mem : last ∈ getOrbit T.f m ⟨0, hm⟩ := h_mem_0 last
    have hcl : orbitClosesWithin T.f last last m :=
      orbitClosesWithin_mono T.f last last (orbitClosesWithin_of_complete T.f darts h_all last) h_le
    have hf_m : Perm.iter T.f m last = last := by
      have hi := singleCycleTriple_iter_f m hm m (Nat.le_refl m)
      apply Fin.ext
      rw [congrArg Fin.val hi]; dsimp [last]
      rw [Nat.mod_self]; omega
    have h_le_m : (getOrbit T.f m last).length ≤ m :=
      getOrbit_length_le_of_iter_eq_self T.f m hm hf_m
    have h_eq_len : (getOrbit T.f m last).length = (getOrbit T.f m ⟨0, hm⟩).length :=
      getOrbit_length_eq_of_complete_mem T.f darts h_all h_le hlast_mem
    rw [← h_eq_len]
    apply Nat.le_antisymm h_le_m
    by_cases hlt : (getOrbit T.f m last).length < m
    · exfalso
      let L := (getOrbit T.f m last).length
      have hL_pos : 1 ≤ L := getOrbit_length_pos T.f hm last
      have hL_per : Perm.iter T.f L last = last := perm_iter_length_getOrbit_eq_self T.f m last hcl
      have hi := singleCycleTriple_iter_f m hm L (Nat.le_of_lt hlt)
      have hv := (congrArg Fin.val hL_per).symm.trans (congrArg Fin.val hi)
      dsimp [last] at hv
      rw [Nat.mod_eq_of_lt hlt] at hv
      omega
    · omega
  exact ⟨hgen, hC, hF, h_mem_0, h_len_0⟩

/-- Disjoint union of two permutations defined on disjoint subtypes `P` and `Q`. -/
def unionPermPred {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (p1 : Perm { d : D // P d }) (p2 : Perm { d : D // Q d }) :
    Perm { d : D // P d ∨ Q d } where
  f x :=
    if hP : P x.1 then
      let y := p1.f ⟨x.1, hP⟩
      ⟨y.1, Or.inl y.2⟩
    else
      have hQ : Q x.1 := Or.resolve_left x.2 hP
      let y := p2.f ⟨x.1, hQ⟩
      ⟨y.1, Or.inr y.2⟩
  inv x :=
    if hP : P x.1 then
      let y := p1.inv ⟨x.1, hP⟩
      ⟨y.1, Or.inl y.2⟩
    else
      have hQ : Q x.1 := Or.resolve_left x.2 hP
      let y := p2.inv ⟨x.1, hQ⟩
      ⟨y.1, Or.inr y.2⟩
  left_inv x := by
    dsimp
    by_cases hP : P x.1
    · rw [dif_pos hP]
      have hPy : P (p1.f ⟨x.1, hP⟩).1 := (p1.f ⟨x.1, hP⟩).2
      rw [dif_pos hPy]
      apply Subtype.ext
      dsimp
      have hi := congrArg Subtype.val (p1.left_inv ⟨x.1, hP⟩)
      exact hi
    · rw [dif_neg hP]
      have hQ : Q x.1 := Or.resolve_left x.2 hP
      have hQy : Q (p2.f ⟨x.1, hQ⟩).1 := (p2.f ⟨x.1, hQ⟩).2
      have hPy : ¬ P (p2.f ⟨x.1, hQ⟩).1 := fun hp => h_disj _ ⟨hp, hQy⟩
      rw [dif_neg hPy]
      apply Subtype.ext
      dsimp
      have hi := congrArg Subtype.val (p2.left_inv ⟨x.1, hQ⟩)
      exact hi
  right_inv x := by
    dsimp
    by_cases hP : P x.1
    · rw [dif_pos hP]
      have hPy : P (p1.inv ⟨x.1, hP⟩).1 := (p1.inv ⟨x.1, hP⟩).2
      rw [dif_pos hPy]
      apply Subtype.ext
      dsimp
      have hi := congrArg Subtype.val (p1.right_inv ⟨x.1, hP⟩)
      exact hi
    · rw [dif_neg hP]
      have hQ : Q x.1 := Or.resolve_left x.2 hP
      have hQy : Q (p2.inv ⟨x.1, hQ⟩).1 := (p2.inv ⟨x.1, hQ⟩).2
      have hPy : ¬ P (p2.inv ⟨x.1, hQ⟩).1 := fun hp => h_disj _ ⟨hp, hQy⟩
      rw [dif_neg hPy]
      apply Subtype.ext
      dsimp
      have hi := congrArg Subtype.val (p2.right_inv ⟨x.1, hQ⟩)
      exact hi

theorem unionPermPred_inl {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d)) (p1 : Perm { d : D // P d }) (p2 : Perm { d : D // Q d })
    {d : D} (hd : P d) :
    (unionPermPred h_disj p1 p2).f ⟨d, Or.inl hd⟩ = ⟨(p1.f ⟨d, hd⟩).1, Or.inl (p1.f ⟨d, hd⟩).2⟩ := by
  dsimp [unionPermPred]; rw [dif_pos hd]

theorem unionPermPred_inl_val {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d)) (p1 : Perm { d : D // P d }) (p2 : Perm { d : D // Q d })
    {x : { d : D // P d ∨ Q d }} (hx : P x.1) :
    (unionPermPred h_disj p1 p2).f x = ⟨(p1.f ⟨x.1, hx⟩).1, Or.inl (p1.f ⟨x.1, hx⟩).2⟩ := by
  dsimp [unionPermPred]; rw [dif_pos hx]

theorem unionPermPred_inv_inl {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d)) (p1 : Perm { d : D // P d }) (p2 : Perm { d : D // Q d })
    {d : D} (hd : P d) :
    (unionPermPred h_disj p1 p2).inv ⟨d, Or.inl hd⟩ = ⟨(p1.inv ⟨d, hd⟩).1, Or.inl (p1.inv ⟨d, hd⟩).2⟩ := by
  dsimp [unionPermPred]; rw [dif_pos hd]

theorem unionPermPred_inv_inl_val {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d)) (p1 : Perm { d : D // P d }) (p2 : Perm { d : D // Q d })
    {x : { d : D // P d ∨ Q d }} (hx : P x.1) :
    (unionPermPred h_disj p1 p2).inv x = ⟨(p1.inv ⟨x.1, hx⟩).1, Or.inl (p1.inv ⟨x.1, hx⟩).2⟩ := by
  dsimp [unionPermPred]; rw [dif_pos hx]

theorem unionPermPred_inr {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d)) (p1 : Perm { d : D // P d }) (p2 : Perm { d : D // Q d })
    {d : D} (hd : Q d) :
    (unionPermPred h_disj p1 p2).f ⟨d, Or.inr hd⟩ = ⟨(p2.f ⟨d, hd⟩).1, Or.inr (p2.f ⟨d, hd⟩).2⟩ := by
  have hnp : ¬ P d := fun hp => h_disj d ⟨hp, hd⟩
  dsimp [unionPermPred]; rw [dif_neg hnp]

theorem unionPermPred_iter_inl {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d)) (p1 : Perm { d : D // P d }) (p2 : Perm { d : D // Q d })
    {d : D} (hd : P d) :
    ∀ k : Nat, Perm.iter (unionPermPred h_disj p1 p2) k ⟨d, Or.inl hd⟩ =
      ⟨(Perm.iter p1 k ⟨d, hd⟩).1, Or.inl (Perm.iter p1 k ⟨d, hd⟩).2⟩
  | 0 => rfl
  | k + 1 => by
    rw [Perm.iter_succ, Perm.iter_succ, unionPermPred_iter_inl h_disj p1 p2 hd k]
    exact unionPermPred_inl h_disj p1 p2 (Perm.iter p1 k ⟨d, hd⟩).2

theorem unionPermPred_iter_inr {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d)) (p1 : Perm { d : D // P d }) (p2 : Perm { d : D // Q d })
    {d : D} (hd : Q d) :
    ∀ k : Nat, Perm.iter (unionPermPred h_disj p1 p2) k ⟨d, Or.inr hd⟩ =
      ⟨(Perm.iter p2 k ⟨d, hd⟩).1, Or.inr (Perm.iter p2 k ⟨d, hd⟩).2⟩
  | 0 => rfl
  | k + 1 => by
    rw [Perm.iter_succ, Perm.iter_succ, unionPermPred_iter_inr h_disj p1 p2 hd k]
    exact unionPermPred_inr h_disj p1 p2 (Perm.iter p2 k ⟨d, hd⟩).2

/-- Disjoint union of two `PermTriple`s defined on disjoint subtypes `P` and `Q`. -/
def unionTriplePred {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (T1 : PermTriple { d : D // P d }) (T2 : PermTriple { d : D // Q d }) :
    PermTriple { d : D // P d ∨ Q d } where
  e := unionPermPred h_disj T1.e T2.e
  n := unionPermPred h_disj T1.n T2.n
  f := unionPermPred h_disj T1.f T2.f
  enf_id x := by
    by_cases hP : P x.1
    · rw [show x = ⟨x.1, Or.inl hP⟩ from Subtype.ext rfl]
      rw [unionPermPred_inl h_disj T1.f T2.f hP,
          unionPermPred_inl h_disj T1.n T2.n (T1.f.f ⟨x.1, hP⟩).2,
          unionPermPred_inl h_disj T1.e T2.e (T1.n.f (T1.f.f ⟨x.1, hP⟩)).2]
      apply Subtype.ext; dsimp
      exact congrArg Subtype.val (T1.enf_id ⟨x.1, hP⟩)
    · have hQ : Q x.1 := Or.resolve_left x.2 hP
      rw [show x = ⟨x.1, Or.inr hQ⟩ from Subtype.ext rfl]
      rw [unionPermPred_inr h_disj T1.f T2.f hQ,
          unionPermPred_inr h_disj T1.n T2.n (T2.f.f ⟨x.1, hQ⟩).2,
          unionPermPred_inr h_disj T1.e T2.e (T2.n.f (T2.f.f ⟨x.1, hQ⟩)).2]
      apply Subtype.ext; dsimp
      exact congrArg Subtype.val (T2.enf_id ⟨x.1, hQ⟩)

theorem unionTriplePred_preserves_P {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (T1 : PermTriple { d : D // P d }) (T2 : PermTriple { d : D // Q d }) :
    (∀ x : { d : D // P d ∨ Q d }, P x.1 ↔ P ((unionTriplePred h_disj T1 T2).e.f x).1) ∧
    (∀ x : { d : D // P d ∨ Q d }, P x.1 ↔ P ((unionTriplePred h_disj T1 T2).n.f x).1) := by
  constructor <;> intro x <;> constructor <;> intro hx
  · dsimp [unionTriplePred]
    rw [show x = ⟨x.1, Or.inl hx⟩ from Subtype.ext rfl,
        unionPermPred_inl h_disj T1.e T2.e hx]
    exact (T1.e.f ⟨x.1, hx⟩).2
  · by_cases hP : P x.1
    · exact hP
    · exfalso
      have hQ : Q x.1 := Or.resolve_left x.2 hP
      dsimp [unionTriplePred] at hx
      rw [show x = ⟨x.1, Or.inr hQ⟩ from Subtype.ext rfl,
          unionPermPred_inr h_disj T1.e T2.e hQ] at hx
      exact h_disj _ ⟨hx, (T2.e.f ⟨x.1, hQ⟩).2⟩
  · dsimp [unionTriplePred]
    rw [show x = ⟨x.1, Or.inl hx⟩ from Subtype.ext rfl,
        unionPermPred_inl h_disj T1.n T2.n hx]
    exact (T1.n.f ⟨x.1, hx⟩).2
  · by_cases hP : P x.1
    · exact hP
    · exfalso
      have hQ : Q x.1 := Or.resolve_left x.2 hP
      dsimp [unionTriplePred] at hx
      rw [show x = ⟨x.1, Or.inr hQ⟩ from Subtype.ext rfl,
          unionPermPred_inr h_disj T1.n T2.n hQ] at hx
      exact h_disj _ ⟨hx, (T2.n.f ⟨x.1, hQ⟩).2⟩

private theorem walkEN_unionTriplePred_inl_bwd {D : Type} {P Q : D → Prop}
    [DecidablePred P] [DecidablePred Q] (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (T1 : PermTriple { d : D // P d }) (T2 : PermTriple { d : D // Q d })
    {x y : { d : D // P d ∨ Q d }}
    (w : WalkEN (unionTriplePred h_disj T1 T2).e (unionTriplePred h_disj T1 T2).n x y) :
    ∀ (hx : P x.1) (hy : P y.1), ReachEN T1.e T1.n ⟨x.1, hx⟩ ⟨y.1, hy⟩ := by
  let T := unionTriplePred h_disj T1 T2
  have hpres := unionTriplePred_preserves_P h_disj T1 T2
  induction w with
  | refl z =>
    intro hx hy
    rw [show (⟨z.1, hx⟩ : { d : D // P d }) = ⟨z.1, hy⟩ from Subtype.ext rfl]
    exact reachEN_refl _ _ _
  | @step u _ z s _ ih =>
    intro hu hz
    cases s with
    | e_fwd =>
      have hv : P (T.e.f u).1 := (hpres.1 u).mp hu
      have hu_eq : T.e.f u = ⟨(T1.e.f ⟨u.1, hu⟩).1, Or.inl (T1.e.f ⟨u.1, hu⟩).2⟩ := by
        dsimp [T, unionTriplePred]; exact unionPermPred_inl_val h_disj T1.e T2.e hu
      have hev : (⟨(T.e.f u).1, hv⟩ : { d : D // P d }) = T1.e.f ⟨u.1, hu⟩ :=
        Subtype.ext (congrArg (fun q : { d : D // P d ∨ Q d } => q.1) hu_eq)
      have h1 : ReachEN T1.e T1.n ⟨u.1, hu⟩ ⟨(T.e.f u).1, hv⟩ := by
        rw [hev]; exact ⟨WalkEN.step (StepEN.e_fwd _) (WalkEN.refl _)⟩
      exact reachEN_trans _ _ h1 (ih hv hz)
    | e_bwd =>
      have hv : P (T.e.inv u).1 := (hpres.1 (T.e.inv u)).mpr (by rw [T.e.right_inv]; exact hu)
      have hu_eq : T.e.inv u = ⟨(T1.e.inv ⟨u.1, hu⟩).1, Or.inl (T1.e.inv ⟨u.1, hu⟩).2⟩ := by
        dsimp [T, unionTriplePred]; exact unionPermPred_inv_inl_val h_disj T1.e T2.e hu
      have hev : (⟨(T.e.inv u).1, hv⟩ : { d : D // P d }) = T1.e.inv ⟨u.1, hu⟩ :=
        Subtype.ext (congrArg (fun q : { d : D // P d ∨ Q d } => q.1) hu_eq)
      have h1 : ReachEN T1.e T1.n ⟨u.1, hu⟩ ⟨(T.e.inv u).1, hv⟩ := by
        rw [hev]; exact ⟨WalkEN.step (StepEN.e_bwd _) (WalkEN.refl _)⟩
      exact reachEN_trans _ _ h1 (ih hv hz)
    | n_fwd =>
      have hv : P (T.n.f u).1 := (hpres.2 u).mp hu
      have hu_eq : T.n.f u = ⟨(T1.n.f ⟨u.1, hu⟩).1, Or.inl (T1.n.f ⟨u.1, hu⟩).2⟩ := by
        dsimp [T, unionTriplePred]; exact unionPermPred_inl_val h_disj T1.n T2.n hu
      have hev : (⟨(T.n.f u).1, hv⟩ : { d : D // P d }) = T1.n.f ⟨u.1, hu⟩ :=
        Subtype.ext (congrArg (fun q : { d : D // P d ∨ Q d } => q.1) hu_eq)
      have h1 : ReachEN T1.e T1.n ⟨u.1, hu⟩ ⟨(T.n.f u).1, hv⟩ := by
        rw [hev]; exact ⟨WalkEN.step (StepEN.n_fwd _) (WalkEN.refl _)⟩
      exact reachEN_trans _ _ h1 (ih hv hz)
    | n_bwd =>
      have hv : P (T.n.inv u).1 := (hpres.2 (T.n.inv u)).mpr (by rw [T.n.right_inv]; exact hu)
      have hu_eq : T.n.inv u = ⟨(T1.n.inv ⟨u.1, hu⟩).1, Or.inl (T1.n.inv ⟨u.1, hu⟩).2⟩ := by
        dsimp [T, unionTriplePred]; exact unionPermPred_inv_inl_val h_disj T1.n T2.n hu
      have hev : (⟨(T.n.inv u).1, hv⟩ : { d : D // P d }) = T1.n.inv ⟨u.1, hu⟩ :=
        Subtype.ext (congrArg (fun q : { d : D // P d ∨ Q d } => q.1) hu_eq)
      have h1 : ReachEN T1.e T1.n ⟨u.1, hu⟩ ⟨(T.n.inv u).1, hv⟩ := by
        rw [hev]; exact ⟨WalkEN.step (StepEN.n_bwd _) (WalkEN.refl _)⟩
      exact reachEN_trans _ _ h1 (ih hv hz)

private theorem walkEN_unionTriplePred_inl_fwd {D : Type} {P Q : D → Prop}
    [DecidablePred P] [DecidablePred Q] (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (T1 : PermTriple { d : D // P d }) (T2 : PermTriple { d : D // Q d })
    {x y : { d : D // P d }} (w : WalkEN T1.e T1.n x y) :
    ReachEN (unionTriplePred h_disj T1 T2).e (unionTriplePred h_disj T1 T2).n
      ⟨x.1, Or.inl x.2⟩ ⟨y.1, Or.inl y.2⟩ := by
  let T := unionTriplePred h_disj T1 T2
  induction w with
  | refl z => exact reachEN_refl _ _ _
  | @step u y' _ s _ ih =>
    have hs : ReachEN T.e T.n ⟨u.1, Or.inl u.2⟩ ⟨y'.1, Or.inl y'.2⟩ := by
      cases s with
      | e_fwd =>
        have hu : T.e.f ⟨u.1, Or.inl u.2⟩ = ⟨(T1.e.f u).1, Or.inl (T1.e.f u).2⟩ := by
          dsimp [T, unionTriplePred]; exact unionPermPred_inl h_disj T1.e T2.e u.2
        rw [← hu]; exact ⟨WalkEN.step (StepEN.e_fwd _) (WalkEN.refl _)⟩
      | e_bwd =>
        have hu : T.e.inv ⟨u.1, Or.inl u.2⟩ = ⟨(T1.e.inv u).1, Or.inl (T1.e.inv u).2⟩ := by
          dsimp [T, unionTriplePred]; exact unionPermPred_inv_inl h_disj T1.e T2.e u.2
        rw [← hu]; exact ⟨WalkEN.step (StepEN.e_bwd _) (WalkEN.refl _)⟩
      | n_fwd =>
        have hu : T.n.f ⟨u.1, Or.inl u.2⟩ = ⟨(T1.n.f u).1, Or.inl (T1.n.f u).2⟩ := by
          dsimp [T, unionTriplePred]; exact unionPermPred_inl h_disj T1.n T2.n u.2
        rw [← hu]; exact ⟨WalkEN.step (StepEN.n_fwd _) (WalkEN.refl _)⟩
      | n_bwd =>
        have hu : T.n.inv ⟨u.1, Or.inl u.2⟩ = ⟨(T1.n.inv u).1, Or.inl (T1.n.inv u).2⟩ := by
          dsimp [T, unionTriplePred]; exact unionPermPred_inv_inl h_disj T1.n T2.n u.2
        rw [← hu]; exact ⟨WalkEN.step (StepEN.n_bwd _) (WalkEN.refl _)⟩
    exact reachEN_trans _ _ hs ih

theorem reachEN_unionTriplePred_inl {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (T1 : PermTriple { d : D // P d }) (T2 : PermTriple { d : D // Q d })
    {a b : D} (ha : P a) (hb : P b) :
    ReachEN (unionTriplePred h_disj T1 T2).e (unionTriplePred h_disj T1 T2).n
      ⟨a, Or.inl ha⟩ ⟨b, Or.inl hb⟩ ↔ ReachEN T1.e T1.n ⟨a, ha⟩ ⟨b, hb⟩ :=
  ⟨fun ⟨w⟩ => walkEN_unionTriplePred_inl_bwd h_disj T1 T2 w ha hb,
   fun ⟨w⟩ => walkEN_unionTriplePred_inl_fwd h_disj T1 T2 w⟩

theorem not_reachEN_unionTriplePred_inl_inr {D : Type} {P Q : D → Prop}
    [DecidablePred P] [DecidablePred Q] (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (T1 : PermTriple { d : D // P d }) (T2 : PermTriple { d : D // Q d })
    {a b : D} (ha : P a) (hb : Q b) :
    ¬ ReachEN (unionTriplePred h_disj T1 T2).e (unionTriplePred h_disj T1 T2).n
        ⟨a, Or.inl ha⟩ ⟨b, Or.inr hb⟩ := by
  let T := unionTriplePred h_disj T1 T2
  have hpres := unionTriplePred_preserves_P h_disj T1 T2
  rintro ⟨w⟩
  have hP := (reachEN_preserves_pred T.e T.n (fun x => P x.1) hpres.1 hpres.2 ⟨w⟩).mp ha
  exact h_disj b ⟨hP, hb⟩

theorem reachEN_unionTriplePred_inr {D : Type} {P Q : D → Prop} [DecidablePred P] [DecidablePred Q]
    (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (T1 : PermTriple { d : D // P d }) (T2 : PermTriple { d : D // Q d })
    {a b : D} (ha : Q a) (hb : Q b) :
    ReachEN (unionTriplePred h_disj T1 T2).e (unionTriplePred h_disj T1 T2).n
      ⟨a, Or.inr ha⟩ ⟨b, Or.inr hb⟩ ↔ ReachEN T2.e T2.n ⟨a, ha⟩ ⟨b, hb⟩ := by
  have h_disj' : ∀ d : D, ¬(Q d ∧ P d) := fun d ⟨hq, hp⟩ => h_disj d ⟨hp, hq⟩
  let φ : SimpleEquiv { d : D // P d ∨ Q d } { d : D // Q d ∨ P d } := {
    toFun := fun x => ⟨x.1, x.2.symm⟩
    invFun := fun x => ⟨x.1, x.2.symm⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl
  }
  have he : permMapEquiv (unionTriplePred h_disj T1 T2).e φ = (unionTriplePred h_disj' T2 T1).e := by
    apply perm_eq_of_f_eq; intro x; apply Subtype.ext
    by_cases hQ : Q x.1
    · have hnp : ¬ P x.1 := fun hp => h_disj x.1 ⟨hp, hQ⟩
      dsimp [permMapEquiv, φ, unionTriplePred, unionPermPred]
      rw [dif_neg hnp, dif_pos hQ]
    · have hP : P x.1 := Or.resolve_left x.2 hQ
      dsimp [permMapEquiv, φ, unionTriplePred, unionPermPred]
      rw [dif_pos hP, dif_neg hQ]
  have hn : permMapEquiv (unionTriplePred h_disj T1 T2).n φ = (unionTriplePred h_disj' T2 T1).n := by
    apply perm_eq_of_f_eq; intro x; apply Subtype.ext
    by_cases hQ : Q x.1
    · have hnp : ¬ P x.1 := fun hp => h_disj x.1 ⟨hp, hQ⟩
      dsimp [permMapEquiv, φ, unionTriplePred, unionPermPred]
      rw [dif_neg hnp, dif_pos hQ]
    · have hP : P x.1 := Or.resolve_left x.2 hQ
      dsimp [permMapEquiv, φ, unionTriplePred, unionPermPred]
      rw [dif_pos hP, dif_neg hQ]
  rw [← reachEN_mapEquiv_iff (unionTriplePred h_disj T1 T2).e (unionTriplePred h_disj T1 T2).n φ
        ⟨a, Or.inr ha⟩ ⟨b, Or.inr hb⟩, he, hn]
  exact reachEN_unionTriplePred_inl h_disj' T2 T1 ha hb

private theorem nodup_map_of_inj {α β : Type} (f : α → β)
    (hf : ∀ a b : α, f a = f b → a = b) : ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨hx, hxs⟩
    refine List.nodup_cons.mpr ⟨?_, nodup_map_of_inj f hf hxs⟩
    intro hm
    rcases List.mem_map.mp hm with ⟨y, hy, hyx⟩
    exact hx ((hf y x hyx) ▸ hy)

private theorem filter_map_eq_self_of_forall {α β : Type} (f : α → β) (p : β → Bool)
    (hp : ∀ x : α, p (f x) = true) :
    ∀ l : List α, (l.map f).filter p = l.map f
  | [] => rfl
  | x :: xs => by
    dsimp [List.map, List.filter]
    simp [hp x, filter_map_eq_self_of_forall f p hp xs]

private theorem filter_map_eq_nil_of_forall {α β : Type} (f : α → β) (p : β → Bool)
    (hp : ∀ x : α, p (f x) = false) :
    ∀ l : List α, (l.map f).filter p = []
  | [] => rfl
  | x :: xs => by
    dsimp [List.map, List.filter]
    simp [hp x, filter_map_eq_nil_of_forall f p hp xs]

theorem unionTriplePred_spec {D : Type} [DecidableEq D] {P Q : D → Prop}
    [DecidablePred P] [DecidablePred Q] (h_disj : ∀ d : D, ¬(P d ∧ Q d))
    (T1 : PermTriple { d : D // P d }) (T2 : PermTriple { d : D // Q d })
    (darts1 : List { d : D // P d }) (h1_nd : darts1.Nodup) (h1_comp : ∀ x, x ∈ darts1)
    (darts2 : List { d : D // Q d }) (h2_nd : darts2.Nodup) (h2_comp : ∀ x, x ∈ darts2)
    {fuel : Nat} (h_le : darts1.length + darts2.length ≤ fuel) :
    let T := unionTriplePred h_disj T1 T2
    let dartsU : List { d : D // P d ∨ Q d } :=
      (darts1.map fun x => ⟨x.1, Or.inl x.2⟩) ++ (darts2.map fun x => ⟨x.1, Or.inr x.2⟩)
    dartsU.Nodup ∧
    (∀ x, x ∈ dartsU) ∧
    genusDeficit T fuel dartsU = genusDeficit T1 fuel darts1 + genusDeficit T2 fuel darts2 ∧
    countRelClasses (ReachEN T.e T.n) dartsU =
      countRelClasses (ReachEN T1.e T1.n) darts1 + countRelClasses (ReachEN T2.e T2.n) darts2 := by
  intro T dartsU
  have hinj1 : ∀ a b : { d : D // P d },
      (⟨a.1, Or.inl a.2⟩ : { d : D // P d ∨ Q d }) = ⟨b.1, Or.inl b.2⟩ → a = b :=
    fun _ _ h => Subtype.ext (congrArg (fun z : { d : D // P d ∨ Q d } => z.1) h)
  have hinj2 : ∀ a b : { d : D // Q d },
      (⟨a.1, Or.inr a.2⟩ : { d : D // P d ∨ Q d }) = ⟨b.1, Or.inr b.2⟩ → a = b :=
    fun _ _ h => Subtype.ext (congrArg (fun z : { d : D // P d ∨ Q d } => z.1) h)
  have h_ndU : dartsU.Nodup := by
    rw [List.nodup_append]
    refine ⟨nodup_map_of_inj _ hinj1 h1_nd, nodup_map_of_inj _ hinj2 h2_nd, ?_⟩
    intro x hx1 y hy2 hxy
    rw [List.mem_map] at hx1 hy2
    rcases hx1 with ⟨a, _, rfl⟩
    rcases hy2 with ⟨b, _, rfl⟩
    have hv : a.1 = b.1 := congrArg Subtype.val hxy
    exact h_disj a.1 ⟨a.2, hv ▸ b.2⟩
  have h_compU : ∀ x : { d : D // P d ∨ Q d }, x ∈ dartsU := fun x => by
    rcases x.2 with hP | hQ
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨⟨x.1, hP⟩, h1_comp _, Subtype.ext rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨x.1, hQ⟩, h2_comp _, Subtype.ext rfl⟩)
  have h_leU : dartsU.length ≤ fuel := by
    dsimp [dartsU]; rw [List.length_append, List.length_map, List.length_map]; exact h_le
  have hpres := unionTriplePred_preserves_P h_disj T1 T2
  let P' : { d : D // P d ∨ Q d } → Prop := fun x => P x.1
  let φ1 : SimpleEquiv { x : { d : D // P d ∨ Q d } // P' x } { d : D // P d } := {
    toFun := fun x => ⟨x.1.1, x.2⟩
    invFun := fun x => ⟨⟨x.1, Or.inl x.2⟩, x.2⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext rfl
  }
  let φ2 : SimpleEquiv { x : { d : D // P d ∨ Q d } // ¬ P' x } { d : D // Q d } := {
    toFun := fun x => ⟨x.1.1, Or.resolve_left x.1.2 x.2⟩
    invFun := fun x => ⟨⟨x.1, Or.inr x.2⟩, fun hp => h_disj x.1 ⟨hp, x.2⟩⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext rfl
  }
  have h_r1_eq : (restrictTriplePred T P' hpres.1 hpres.2).mapEquiv φ1 = T1 := by
    apply permTriple_eq_of_f_eq
    · intro x; apply Subtype.ext
      dsimp [PermTriple.mapEquiv, permMapEquiv, restrictTriplePred, restrictPermPred, φ1, T, unionTriplePred]
      rw [unionPermPred_inl h_disj T1.e T2.e x.2]
    · intro x; apply Subtype.ext
      dsimp [PermTriple.mapEquiv, permMapEquiv, restrictTriplePred, restrictPermPred, φ1, T, unionTriplePred]
      rw [unionPermPred_inl h_disj T1.n T2.n x.2]
    · intro x; apply Subtype.ext
      dsimp [PermTriple.mapEquiv, permMapEquiv, restrictTriplePred, restrictPermPred, φ1, T, unionTriplePred]
      rw [unionPermPred_inl h_disj T1.f T2.f x.2]
  have h_nP_e : ∀ x : { d : D // P d ∨ Q d }, ¬ P' x ↔ ¬ P' (T.e.f x) :=
    fun x => not_congr (hpres.1 x)
  have h_nP_n : ∀ x : { d : D // P d ∨ Q d }, ¬ P' x ↔ ¬ P' (T.n.f x) :=
    fun x => not_congr (hpres.2 x)
  have h_r2_eq : (restrictTriplePred T (fun x => ¬ P' x) h_nP_e h_nP_n).mapEquiv φ2 = T2 := by
    apply permTriple_eq_of_f_eq
    · intro x; apply Subtype.ext
      dsimp [PermTriple.mapEquiv, permMapEquiv, restrictTriplePred, restrictPermPred, φ2, T, unionTriplePred]
      rw [unionPermPred_inr h_disj T1.e T2.e x.2]
    · intro x; apply Subtype.ext
      dsimp [PermTriple.mapEquiv, permMapEquiv, restrictTriplePred, restrictPermPred, φ2, T, unionTriplePred]
      rw [unionPermPred_inr h_disj T1.n T2.n x.2]
    · intro x; apply Subtype.ext
      dsimp [PermTriple.mapEquiv, permMapEquiv, restrictTriplePred, restrictPermPred, φ2, T, unionTriplePred]
      rw [unionPermPred_inr h_disj T1.f T2.f x.2]
  have h_genU : genusDeficit T fuel dartsU = genusDeficit T1 fuel darts1 + genusDeficit T2 fuel darts2 := by
    rw [genusDeficit_pred_split T fuel dartsU h_ndU h_compU h_leU P' hpres.1 hpres.2]
    have hpd1_nd : (predDarts P' dartsU).Nodup := nodup_predDarts P' h_ndU
    have hpd1_comp : ∀ x, x ∈ predDarts P' dartsU := fun x => (mem_predDarts_iff P' dartsU x).mpr (h_compU x.1)
    have hpd1_le : (predDarts P' dartsU).length ≤ fuel := by
      have hm := map_predDarts P' dartsU
      have hf : (dartsU.filter (fun d => decide (P' d))).length ≤ dartsU.length := List.length_filter_le _ _
      have hl : (predDarts P' dartsU).length = (dartsU.filter (fun d => decide (P' d))).length := by
        rw [← List.length_map (Subtype.val), hm]
      omega
    have hpd2_nd : (predDarts (fun x => ¬ P' x) dartsU).Nodup := nodup_predDarts _ h_ndU
    have hpd2_comp : ∀ x, x ∈ predDarts (fun x => ¬ P' x) dartsU :=
      fun x => (mem_predDarts_iff (fun x => ¬ P' x) dartsU x).mpr (h_compU x.1)
    have hpd2_le : (predDarts (fun x => ¬ P' x) dartsU).length ≤ fuel := by
      have hm := map_predDarts (fun x => ¬ P' x) dartsU
      have hf := List.length_filter_le (fun d => decide (¬ P' d)) dartsU
      have hl : (predDarts (fun x => ¬ P' x) dartsU).length =
          (dartsU.filter (fun d => decide (¬ P' d))).length := by
        rw [← List.length_map Subtype.val, hm]
      omega
    have hg1 : genusDeficit (restrictTriplePred T P' hpres.1 hpres.2) fuel (predDarts P' dartsU) =
        genusDeficit T1 fuel darts1 := by
      rw [← genusDeficit_mapEquiv (restrictTriplePred T P' hpres.1 hpres.2) φ1 (predDarts P' dartsU) hpd1_comp hpd1_le,
          h_r1_eq]
      exact genusDeficit_eq_of_complete T1 _ darts1 (nodup_map_of_inj φ1.toFun (fun _ _ h => φ1.toFun_inj h) hpd1_nd)
        (fun y => List.mem_map.mpr ⟨φ1.invFun y, hpd1_comp _, φ1.right_inv y⟩)
        h1_nd h1_comp (by rw [List.length_map]; exact hpd1_le) (by omega)
    have hg2 : genusDeficit (restrictTriplePred T (fun x => ¬ P' x) h_nP_e h_nP_n) fuel
          (predDarts (fun x => ¬ P' x) dartsU) = genusDeficit T2 fuel darts2 := by
      rw [← genusDeficit_mapEquiv (restrictTriplePred T (fun x => ¬ P' x) h_nP_e h_nP_n) φ2
            (predDarts (fun x => ¬ P' x) dartsU) hpd2_comp hpd2_le, h_r2_eq]
      exact genusDeficit_eq_of_complete T2 _ darts2 (nodup_map_of_inj φ2.toFun (fun _ _ h => φ2.toFun_inj h) hpd2_nd)
        (fun y => List.mem_map.mpr ⟨φ2.invFun y, hpd2_comp _, φ2.right_inv y⟩)
        h2_nd h2_comp (by rw [List.length_map]; exact hpd2_le) (by omega)
    rw [hg1, hg2]
  have hC_U : countRelClasses (ReachEN T.e T.n) dartsU =
      countRelClasses (ReachEN T1.e T1.n) darts1 + countRelClasses (ReachEN T2.e T2.n) darts2 := by
    let S : { d : D // P d ∨ Q d } → Bool := fun x => decide (P x.1)
    have hS : ∀ {x y : { d : D // P d ∨ Q d }}, ReachEN T.e T.n x y → S x = S y := by
      intro x y hxy
      dsimp [S]
      have hiff : P x.1 ↔ P y.1 := reachEN_preserves_pred T.e T.n P' hpres.1 hpres.2 hxy
      by_cases hx : P x.1
      · have hy : P y.1 := hiff.mp hx; simp [hx, hy]
      · have hny : ¬ P y.1 := fun hy => hx (hiff.mpr hy); simp [hx, hny]
    rw [countRelClasses_partition_of_closed (ReachEN T.e T.n) (reachEN_refl _ _)
          (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS dartsU]
    have h_flt1 : dartsU.filter S = darts1.map (fun x => ⟨x.1, Or.inl x.2⟩) := by
      dsimp [dartsU, S]
      rw [List.filter_append,
          filter_map_eq_self_of_forall (fun x : {d // P d} => (⟨x.1, Or.inl x.2⟩ : {d // P d ∨ Q d}))
            (fun x => decide (P x.1)) (fun x => decide_eq_true x.2) darts1,
          filter_map_eq_nil_of_forall (fun x : {d // Q d} => (⟨x.1, Or.inr x.2⟩ : {d // P d ∨ Q d}))
            (fun x => decide (P x.1)) (fun x => decide_eq_false (fun hp => h_disj x.1 ⟨hp, x.2⟩)) darts2,
          List.append_nil]
    have h_flt2 : dartsU.filter (fun x => !S x) = darts2.map (fun x => ⟨x.1, Or.inr x.2⟩) := by
      dsimp [dartsU, S]
      rw [List.filter_append,
          filter_map_eq_nil_of_forall (fun x : {d // P d} => (⟨x.1, Or.inl x.2⟩ : {d // P d ∨ Q d}))
            (fun x => !decide (P x.1)) (fun x => by simp [x.2]) darts1,
          filter_map_eq_self_of_forall (fun x : {d // Q d} => (⟨x.1, Or.inr x.2⟩ : {d // P d ∨ Q d}))
            (fun x => !decide (P x.1)) (fun x => by
              have hnp : ¬ P x.1 := fun hp => h_disj x.1 ⟨hp, x.2⟩
              simp [hnp]) darts2,
          List.nil_append]
    rw [h_flt1, h_flt2]
    congr 1
    · exact countRelClasses_mapEquiv (ReachEN T1.e T1.n) (ReachEN T.e T.n)
        (fun x => ⟨x.1, Or.inl x.2⟩) (fun x y => reachEN_unionTriplePred_inl h_disj T1 T2 x.2 y.2) darts1
    · exact countRelClasses_mapEquiv (ReachEN T2.e T2.n) (ReachEN T.e T.n)
        (fun x => ⟨x.1, Or.inr x.2⟩) (fun x y => reachEN_unionTriplePred_inr h_disj T1 T2 x.2 y.2) darts2
  exact ⟨h_ndU, h_compU, h_genU, hC_U⟩

theorem coupleEdge_edge_invol {D : Type} [DecidableEq D] (T : PermTriple D)
    (h_invol : ∀ d : D, T.e.f (T.e.f d) = d) {a b : D}
    (ha_fix : T.e.f a = a) (hb_fix : T.e.f b = b) :
    ∀ d : D, (coupleEdge T a b).e.f ((coupleEdge T a b).e.f d) = d := by
  intro d
  rw [coupleEdge_e_eval T ha_fix hb_fix d]
  by_cases hda : d = a
  · rw [if_pos hda, hda, coupleEdge_e_right T ha_fix hb_fix]
  · rw [if_neg hda]
    by_cases hdb : d = b
    · rw [if_pos hdb, hdb, coupleEdge_e_left T ha_fix hb_fix]
    · rw [if_neg hdb]
      have hfa : T.e.f d ≠ a := fun h => hda (by rw [← h_invol d, h, ha_fix])
      have hfb : T.e.f d ≠ b := fun h => hdb (by rw [← h_invol d, h, hb_fix])
      rw [coupleEdge_e_of_ne T ha_fix hb_fix hfa hfb, h_invol d]

theorem uncoupleEdge_edge_invol {D : Type} [DecidableEq D] (T : PermTriple D)
    (h_invol : ∀ d : D, T.e.f (T.e.f d) = d) {a b : D}
    (hab : T.e.f a = b) (hba : T.e.f b = a) :
    ∀ d : D, (uncoupleEdge T a b).e.f ((uncoupleEdge T a b).e.f d) = d := by
  intro d
  dsimp [uncoupleEdge, swapCompLeft]
  by_cases hda : d = a
  · rw [hda, hab, swapFun_right, hab, swapFun_right]
  · by_cases hdb : d = b
    · rw [hdb, hba, swapFun_left, hba, swapFun_left]
    · have hfa : T.e.f d ≠ b := fun h => hda (perm_f_inj_jcs T.e (h.trans hab.symm))
      have hfb : T.e.f d ≠ a := fun h => hdb (perm_f_inj_jcs T.e (h.trans hba.symm))
      rw [swapFun_of_ne hfb hfa, h_invol d, swapFun_of_ne hda hdb]

/-- Materialize a `PermTriple D` with involutive fixed-point-free edge permutation as a `Hypermap`. -/
abbrev tripleToHypermap {D : Type} (T : PermTriple D)
    (h_invol : ∀ d : D, T.e.f (T.e.f d) = d) : Hypermap where
  Dart := D
  edge := T.e
  node := T.n
  face := T.f
  edge_involution := h_invol
  edge_node_face_id := T.enf_id

theorem tripleToHypermap_isComplete {D : Type} (T : PermTriple D)
    (h_invol : ∀ d : D, T.e.f (T.e.f d) = d)
    (darts : List D) (h_nd : darts.Nodup) (h_comp : ∀ d : D, d ∈ darts) :
    darts.Nodup ∧ (∀ d : (tripleToHypermap T h_invol).Dart, d ∈ darts) :=
  ⟨h_nd, h_comp⟩

theorem tripleToHypermap_isPlanar {D : Type} [DecidableEq D] (T : PermTriple D)
    (h_invol : ∀ d : D, T.e.f (T.e.f d) = d)
    (darts : List D) (h_nd : darts.Nodup) (h_comp : ∀ d : D, d ∈ darts)
    (h_gen : genusDeficit T darts.length darts = 0)
    (h_no_fix : ∀ d : D, T.e.f d ≠ d) :
    (tripleToHypermap T h_invol).isPlanar darts.length darts = true := by
  let H' := tripleToHypermap T h_invol
  have hec := (eulerChar_le_two_mul_numComponents H' darts h_nd h_comp (Nat.le_refl _)).2
  exact hec.mpr ⟨h_gen, h_no_fix⟩

theorem tripleToHypermap_numComponents_eq_one {D : Type} [DecidableEq D] (T : PermTriple D)
    (h_invol : ∀ d : D, T.e.f (T.e.f d) = d)
    (darts : List D) (h_comp : ∀ d : D, d ∈ darts)
    (h_c1 : countRelClasses (ReachEN T.e T.n) darts = 1) :
    (tripleToHypermap T h_invol).numComponents darts.length darts = 1 := by
  let H' := tripleToHypermap T h_invol
  dsimp [Hypermap.numComponents]
  rw [← countRelClasses_reachEN_eq_countComponents H' darts h_comp (Nat.le_refl _) darts]
  exact h_c1

end SimpleEquivAndSubtypeAssembly

section ReverseUncoupleAndDisjointPairs

theorem perm_mk_eq {D : Type} (p q : Perm D)
    (hf : p.f = q.f) (hi : p.inv = q.inv) : p = q := by
  cases p; cases q
  dsimp at hf hi
  subst hf hi
  rfl

theorem permTriple_mk_eq {D : Type} (T1 T2 : PermTriple D)
    (he : T1.e = T2.e) (hn : T1.n = T2.n) (hf : T1.f = T2.f) : T1 = T2 := by
  cases T1; cases T2
  dsimp at he hn hf
  subst he hn hf
  rfl

theorem swapCompLeft_invol_op [DecidableEq D] (p : Perm D) (a b : D) :
    swapCompLeft (swapCompLeft p a b) a b = p := by
  apply perm_mk_eq
  · funext x; dsimp [swapCompLeft]; exact swapFun_invol a b (p.f x)
  · funext x; dsimp [swapCompLeft]; rw [swapFun_invol a b x]

theorem swapCompRight_invol_op [DecidableEq D] (p : Perm D) (a b : D) :
    swapCompRight (swapCompRight p a b) a b = p := by
  apply perm_mk_eq
  · funext x; dsimp [swapCompRight]; rw [swapFun_invol a b x]
  · funext x; dsimp [swapCompRight]; exact swapFun_invol a b (p.inv x)

theorem coupleEdge_uncoupleEdge_eq [DecidableEq D] (T : PermTriple D) (a b : D) :
    coupleEdge (uncoupleEdge T a b) a b = T := by
  apply permTriple_mk_eq
  · exact swapCompLeft_invol_op T.e a b
  · rfl
  · exact swapCompRight_invol_op T.f a b

theorem uncoupleEdge_e_fixed [DecidableEq D] (T : PermTriple D)
    {a b : D} (hab : T.e.f a = b) (hba : T.e.f b = a) :
    (uncoupleEdge T a b).e.f a = a ∧
      (uncoupleEdge T a b).e.f b = b ∧
      (∀ x : D, x ≠ a → x ≠ b → (uncoupleEdge T a b).e.f x = T.e.f x) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [uncoupleEdge, swapCompLeft]; rw [hab, swapFun_right]
  · dsimp [uncoupleEdge, swapCompLeft]; rw [hba, swapFun_left]
  · intro x hxa hxb
    dsimp [uncoupleEdge, swapCompLeft]
    have hfa : T.e.f x ≠ a := fun h => hxb (perm_f_inj_jcs T.e (h.trans hba.symm))
    have hfb : T.e.f x ≠ b := fun h => hxa (perm_f_inj_jcs T.e (h.trans hab.symm))
    exact swapFun_of_ne hfa hfb

theorem uncoupleEdge_e_of_ne_targets [DecidableEq D] (T : PermTriple D)
    {a b x : D} (ha : T.e.f x ≠ a) (hb : T.e.f x ≠ b) :
    (uncoupleEdge T a b).e.f x = T.e.f x := by
  dsimp [uncoupleEdge, swapCompLeft]
  exact swapFun_of_ne ha hb

theorem swapFun_comm_disjoint [DecidableEq D] {a b c d : D}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (x : D) :
    swapFun a b (swapFun c d x) = swapFun c d (swapFun a b x) := by
  by_cases hxc : x = c
  · rw [hxc, swapFun_left, swapFun_of_ne had.symm hbd.symm, swapFun_of_ne hac.symm hbc.symm,
      swapFun_left]
  · by_cases hxd : x = d
    · rw [hxd, swapFun_right, swapFun_of_ne hac.symm hbc.symm, swapFun_of_ne had.symm hbd.symm,
        swapFun_right]
    · rw [swapFun_of_ne hxc hxd]
      by_cases hxa : x = a
      · rw [hxa, swapFun_left, swapFun_of_ne hbc hbd]
      · by_cases hxb : x = b
        · rw [hxb, swapFun_right, swapFun_of_ne hac had]
        · rw [swapFun_of_ne hxa hxb, swapFun_of_ne hxc hxd]

theorem uncoupleEdge_comm [DecidableEq D] (T : PermTriple D) {a b c d : D}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    uncoupleEdge (uncoupleEdge T a b) c d = uncoupleEdge (uncoupleEdge T c d) a b := by
  apply permTriple_mk_eq
  · apply perm_mk_eq
    · funext x; dsimp [uncoupleEdge, swapCompLeft]
      exact (swapFun_comm_disjoint hac had hbc hbd (T.e.f x)).symm
    · funext x; dsimp [uncoupleEdge, swapCompLeft]
      rw [swapFun_comm_disjoint hac had hbc hbd x]
  · rfl
  · apply perm_mk_eq
    · funext x; dsimp [uncoupleEdge, swapCompRight]
      rw [swapFun_comm_disjoint hac had hbc hbd x]
    · funext x; dsimp [uncoupleEdge, swapCompRight]
      exact (swapFun_comm_disjoint hac had hbc hbd (T.f.inv x)).symm

abbrev uncoupleList {D : Type} [DecidableEq D] (T : PermTriple D) :
    List (D × D) → PermTriple D :=
  coupleList T

theorem coupleList_append [DecidableEq D] (T : PermTriple D) (ps qs : List (D × D)) :
    coupleList T (ps ++ qs) = coupleList (coupleList T ps) qs := by
  induction ps generalizing T with
  | nil => rfl
  | cons p ps ih => exact ih (coupleEdge T p.1 p.2)

theorem uncoupleList_n [DecidableEq D] (T : PermTriple D) (ps : List (D × D)) :
    (uncoupleList T ps).n = T.n := by
  induction ps generalizing T with
  | nil => rfl
  | cons p ps ih => exact ih (coupleEdge T p.1 p.2)

theorem uncoupleList_map_swap [DecidableEq D] (T : PermTriple D) (ps : List (D × D)) :
    uncoupleList T (ps.map Prod.swap) = uncoupleList T ps := by
  induction ps generalizing T with
  | nil => rfl
  | cons p ps ih =>
    dsimp [uncoupleList, coupleList, List.map]
    rw [coupleEdge_symm T p.2 p.1]
    exact ih (coupleEdge T p.1 p.2)

def PairwiseDisjointPairs {D : Type} : List (D × D) → Prop
  | [] => True
  | p :: ps =>
    p.1 ≠ p.2 ∧
      (∀ q ∈ ps, p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      PairwiseDisjointPairs ps

theorem uncoupleEdge_uncoupleList_comm [DecidableEq D] (T : PermTriple D)
    {p : D × D} {qs : List (D × D)}
    (h_disj : ∀ q ∈ qs, p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    uncoupleList (uncoupleEdge T p.1 p.2) qs = uncoupleEdge (uncoupleList T qs) p.1 p.2 := by
  induction qs generalizing T with
  | nil => rfl
  | cons q qs ih =>
    have hq := h_disj q (by simp)
    have htail : ∀ r ∈ qs, p.1 ≠ r.1 ∧ p.1 ≠ r.2 ∧ p.2 ≠ r.1 ∧ p.2 ≠ r.2 :=
      fun r hr => h_disj r (by simp [hr])
    dsimp [uncoupleList, coupleList, coupleEdge]
    rw [uncoupleEdge_comm T hq.1 hq.2.1 hq.2.2.1 hq.2.2.2]
    exact ih (uncoupleEdge T q.1 q.2) htail

theorem pairwiseDisjointPairs_reverse {D : Type} :
    ∀ ps : List (D × D), PairwiseDisjointPairs ps → PairwiseDisjointPairs ps.reverse
  | [], _ => trivial
  | p :: ps, ⟨hp_ne, h_pq, h_ps⟩ => by
    have ih := pairwiseDisjointPairs_reverse ps h_ps
    have aux : ∀ qs rs : List (D × D), PairwiseDisjointPairs qs → PairwiseDisjointPairs rs →
        (∀ q ∈ qs, ∀ r ∈ rs, q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2) →
        PairwiseDisjointPairs (qs ++ rs) := by
      intro qs rs hq hr hqr
      induction qs with
      | nil => simpa using hr
      | cons q qs ihq =>
        rcases hq with ⟨hq1, hq2, hq3⟩
        refine ⟨hq1, ?_, ihq hq3 (fun a ha r hr => hqr a (by simp [ha]) r hr)⟩
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hq2 x hx
        · exact hqr q (by simp) x hx
    rw [List.reverse_cons]
    refine aux ps.reverse [p] ih ⟨hp_ne, fun _ h => by simp at h, trivial⟩ ?_
    intro q hq r hr
    simp at hr; subst hr
    have hq' := List.mem_reverse.mp hq
    have h := h_pq q hq'
    exact ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

theorem uncoupleList_reverse [DecidableEq D] (T : PermTriple D) (ps : List (D × D))
    (h_pd : PairwiseDisjointPairs ps) :
    uncoupleList T ps.reverse = uncoupleList T ps := by
  induction ps generalizing T with
  | nil => rfl
  | cons p ps ih =>
    rcases h_pd with ⟨_, h_pq, h_ps⟩
    rw [List.reverse_cons, uncoupleList, coupleList_append]
    dsimp [coupleList]
    have hcomm := uncoupleEdge_uncoupleList_comm T h_pq
    dsimp [uncoupleList] at hcomm
    change coupleEdge (coupleList T ps.reverse) p.1 p.2 = coupleList (coupleEdge T p.1 p.2) ps
    have ih' := ih T h_ps
    dsimp [uncoupleList] at ih'
    rw [ih']
    exact hcomm.symm

theorem uncoupleList_f_eval [DecidableEq D] (T : PermTriple D) (ps : List (D × D))
    (h_pd : PairwiseDisjointPairs ps) (x : D) :
    ((∀ q ∈ ps, x ≠ q.1 ∧ x ≠ q.2) → (uncoupleList T ps).f.f x = T.f.f x) ∧
      (∀ q ∈ ps, (x = q.1 → (uncoupleList T ps).f.f x = T.f.f q.2) ∧
        (x = q.2 → (uncoupleList T ps).f.f x = T.f.f q.1)) := by
  induction ps generalizing T with
  | nil =>
    exact ⟨fun _ => rfl, fun _ h => by simp at h⟩
  | cons p ps ih =>
    rcases h_pd with ⟨hp_ne, h_pq, h_ps⟩
    have ih' := ih (coupleEdge T p.1 p.2) h_ps
    have hp_swap : (coupleEdge T p.1 p.2).f.f p.1 = T.f.f p.2 ∧
        (coupleEdge T p.1 p.2).f.f p.2 = T.f.f p.1 := by
      dsimp [coupleEdge, uncoupleEdge, swapCompRight]
      exact ⟨by rw [swapFun_left], by rw [swapFun_right]⟩
    constructor
    · intro hx
      have hxp1 : x ≠ p.1 := (hx p (by simp)).1
      have hxp2 : x ≠ p.2 := (hx p (by simp)).2
      rw [uncoupleList, coupleList, ih'.1 (fun q hq => hx q (by simp [hq]))]
      dsimp [coupleEdge, uncoupleEdge, swapCompRight]
      rw [swapFun_of_ne hxp1 hxp2]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · constructor
        · intro hxq1; subst hxq1
          have h_not : ∀ r ∈ ps, q.1 ≠ r.1 ∧ q.1 ≠ r.2 :=
            fun r hr => ⟨(h_pq r hr).1, (h_pq r hr).2.1⟩
          rw [uncoupleList, coupleList, ih'.1 h_not]
          exact hp_swap.1
        · intro hxq2; subst hxq2
          have h_not : ∀ r ∈ ps, q.2 ≠ r.1 ∧ q.2 ≠ r.2 :=
            fun r hr => ⟨(h_pq r hr).2.2.1, (h_pq r hr).2.2.2⟩
          rw [uncoupleList, coupleList, ih'.1 h_not]
          exact hp_swap.2
      · constructor
        · intro hxq1; subst hxq1
          have hq1_ne : q.1 ≠ p.1 ∧ q.1 ≠ p.2 :=
            ⟨(h_pq q hq).1.symm, (h_pq q hq).2.2.1.symm⟩
          have hq2_ne : q.2 ≠ p.1 ∧ q.2 ≠ p.2 :=
            ⟨(h_pq q hq).2.1.symm, (h_pq q hq).2.2.2.symm⟩
          rw [uncoupleList, coupleList, (ih'.2 q hq).1 rfl]
          dsimp [coupleEdge, uncoupleEdge, swapCompRight]
          rw [swapFun_of_ne hq2_ne.1 hq2_ne.2]
        · intro hxq2; subst hxq2
          have hq1_ne : q.1 ≠ p.1 ∧ q.1 ≠ p.2 :=
            ⟨(h_pq q hq).1.symm, (h_pq q hq).2.2.1.symm⟩
          rw [uncoupleList, coupleList, (ih'.2 q hq).2 rfl]
          dsimp [coupleEdge, uncoupleEdge, swapCompRight]
          rw [swapFun_of_ne hq1_ne.1 hq1_ne.2]

theorem uncoupleList_e_eval [DecidableEq D] (T : PermTriple D)
    (h_invol : ∀ d : D, T.e.f (T.e.f d) = d) (ps : List (D × D))
    (h_pd : PairwiseDisjointPairs ps) (h_pairs : ∀ q ∈ ps, T.e.f q.1 = q.2) (x : D) :
    ((∀ q ∈ ps, x ≠ q.1 ∧ x ≠ q.2) → (uncoupleList T ps).e.f x = T.e.f x) ∧
      (∀ q ∈ ps, (x = q.1 → (uncoupleList T ps).e.f x = x) ∧
        (x = q.2 → (uncoupleList T ps).e.f x = x)) := by
  induction ps generalizing T with
  | nil =>
    exact ⟨fun _ => rfl, fun _ h => by simp at h⟩
  | cons p ps ih =>
    rcases h_pd with ⟨hp_ne, h_pq, h_ps⟩
    have hp12 : T.e.f p.1 = p.2 := h_pairs p (by simp)
    have hp21 : T.e.f p.2 = p.1 := by rw [← hp12, h_invol p.1]
    have hfix := uncoupleEdge_e_fixed T hp12 hp21
    have h_invol' : ∀ d, (coupleEdge T p.1 p.2).e.f ((coupleEdge T p.1 p.2).e.f d) = d :=
      uncoupleEdge_edge_invol T h_invol hp12 hp21
    have h_pairs' : ∀ q ∈ ps, (coupleEdge T p.1 p.2).e.f q.1 = q.2 := by
      intro q hq
      have hqp := h_pq q hq
      change (uncoupleEdge T p.1 p.2).e.f q.1 = q.2
      rw [hfix.2.2 q.1 hqp.1.symm hqp.2.2.1.symm]
      exact h_pairs q (by simp [hq])
    have ih' := ih (coupleEdge T p.1 p.2) h_invol' h_ps h_pairs'
    constructor
    · intro hx
      have hxp1 : x ≠ p.1 := (hx p (by simp)).1
      have hxp2 : x ≠ p.2 := (hx p (by simp)).2
      rw [uncoupleList, coupleList, ih'.1 (fun q hq => hx q (by simp [hq]))]
      exact hfix.2.2 x hxp1 hxp2
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · constructor
        · intro hxq1; subst hxq1
          have h_not : ∀ r ∈ ps, q.1 ≠ r.1 ∧ q.1 ≠ r.2 :=
            fun r hr => ⟨(h_pq r hr).1, (h_pq r hr).2.1⟩
          rw [uncoupleList, coupleList, ih'.1 h_not]
          exact hfix.1
        · intro hxq2; subst hxq2
          have h_not : ∀ r ∈ ps, q.2 ≠ r.1 ∧ q.2 ≠ r.2 :=
            fun r hr => ⟨(h_pq r hr).2.2.1, (h_pq r hr).2.2.2⟩
          rw [uncoupleList, coupleList, ih'.1 h_not]
          exact hfix.2.1
      · constructor
        · intro hxq1; subst hxq1
          exact (ih'.2 q hq).1 rfl
        · intro hxq2; subst hxq2
          exact (ih'.2 q hq).2 rfl

theorem getOrbit_eq_of_agree_on_orbit [DecidableEq D] (p q : Perm D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) (z : D)
    (h_agree : ∀ u : D, u ∈ getOrbit p fuel z → p.f u = q.f u) :
    getOrbit q fuel z = getOrbit p fuel z := by
  let S : D → Bool := fun x => decide (x ∈ getOrbit p fuel z)
  have hS_p : ∀ x : D, S (p.f x) = S x := by
    intro x
    dsimp [S]
    by_cases hx : x ∈ getOrbit p fuel z
    · have hfx := getOrbit_closed_under_f_of_complete p darts h_all h_le hx
      simp [hx, hfx]
    · have hfx : p.f x ∉ getOrbit p fuel z := by
        intro hm
        have hi := getOrbit_closed_under_inv_of_complete p darts h_all h_le hm
        rw [p.left_inv] at hi
        exact hx hi
      simp [hx, hfx]
  have hSz : S z = true := by simp [S, mem_getOrbit_self p fuel z]
  exact (getOrbit_eq_of_agree_on_closed p q S hS_p (fun x hx => h_agree x (by simpa [S] using hx))
    fuel hSz).symm

theorem mem_getOrbit_symm_complete [DecidableEq D] (p : Perm D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) {a b : D}
    (hb : b ∈ getOrbit p fuel a) : a ∈ getOrbit p fuel b :=
  mem_getOrbit_symm p fuel
    (orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le) hb

theorem mem_getOrbit_trans_complete [DecidableEq D] (p : Perm D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) {a b c : D}
    (hab : b ∈ getOrbit p fuel a) (hbc : c ∈ getOrbit p fuel b) : c ∈ getOrbit p fuel a :=
  mem_getOrbit_trans p fuel
    (orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le) hab hbc

theorem mem_getOrbit_of_iter_complete [DecidableEq D] (p : Perm D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (d : D) (k : Nat) : Perm.iter p k d ∈ getOrbit p fuel d :=
  iter_mem_getOrbit_of_closes p fuel d
    (orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le) k

/-- Uncoupling an edge `{a, b}` whose two darts lie in DIFFERENT faces (`b ∉ getOrbit T.f fuel a`)
    merges those two face orbits into `getOrbit T.f fuel a ∪ getOrbit T.f fuel b`,
    leaves all other faces intact, and **preserves components (`ReachEN`) and `genusDeficit`**. -/
theorem uncoupleEdge_diff [DecidableEq D] (T : PermTriple D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (hab : a ≠ b) (ha_b : T.e.f a = b) (hb_a : T.e.f b = a)
    (h_not : ¬ b ∈ getOrbit T.f fuel a) :
    have T1 := uncoupleEdge T a b
    (T1.e.f a = a ∧ T1.e.f b = b) ∧
      b ∈ getOrbit T1.f fuel a ∧
      (∀ {x y : D}, ReachEN T1.e T1.n x y ↔ ReachEN T.e T.n x y) ∧
      countRelClasses (ReachEN T1.e T1.n) darts = countRelClasses (ReachEN T.e T.n) darts ∧
      countOrbits T.e fuel darts + 1 = countOrbits T1.e fuel darts ∧
      countOrbits T.f fuel darts = countOrbits T1.f fuel darts + 1 ∧
      genusDeficit T1 fuel darts = genusDeficit T fuel darts ∧
      (∀ x : D, x ∈ getOrbit T1.f fuel b ↔ x ∈ getOrbit T.f fuel a ∨ x ∈ getOrbit T.f fuel b) ∧
      (∀ z : D, ¬ z ∈ getOrbit T.f fuel a → ¬ z ∈ getOrbit T.f fuel b →
        getOrbit T1.f fuel z = getOrbit T.f fuel z) := by
  dsimp only
  let T1 := uncoupleEdge T a b
  have hfix := uncoupleEdge_e_fixed T ha_b hb_a
  have h_merge := swapCompRight_merge_orbit T.f darts h_all h_le h_not
  have h_a_orb : a ∈ getOrbit T1.f fuel b :=
    (h_merge.2.2.2.1 a).mpr (Or.inl (mem_getOrbit_self T.f fuel a))
  have hb_T1 : b ∈ getOrbit T1.f fuel a :=
    mem_getOrbit_symm_complete T1.f darts h_all h_le h_a_orb
  have hcs := coupleEdge_sameFace T1 darts h_all h_le hfix.1 hfix.2.1 hab hb_T1
  rw [coupleEdge_uncoupleEdge_eq T a b] at hcs
  refine ⟨⟨hfix.1, hfix.2.1⟩, hb_T1, ?_, ?_, hcs.2.2.2.1, hcs.2.2.2.2.1, hcs.2.2.2.2.2.symm,
    h_merge.2.2.2.1, ?_⟩
  · intro x y; exact hcs.2.1.symm
  · exact hcs.2.2.1.symm
  · intro z hza hzb
    have ha_not_z : a ∉ getOrbit T.f fuel z := fun h => hza (mem_getOrbit_symm_complete T.f darts h_all h_le h)
    have hb_not_z : b ∉ getOrbit T.f fuel z := fun h => hzb (mem_getOrbit_symm_complete T.f darts h_all h_le h)
    exact (swapCompRight_iter_eq_of_not_mem_orbit T.f darts h_all h_le ha_not_z hb_not_z).2

/-- Uncoupling an edge `{a, b}` whose two darts lie in the SAME face (`b ∈ getOrbit T.f fuel a`)
    of a planar triple (`genusDeficit = 0`) MUST disconnect `a` and `b` (`¬ ReachEN T1.e T1.n a b`),
    splitting the face orbit of `a` into two, increasing `countRelClasses` by `1`, preserving
    `genusDeficit = 0`, and leaving all other faces untouched. -/
theorem uncoupleEdge_sameFace_separates [DecidableEq D] (T : PermTriple D) (darts : List D)
    (h_nd : darts.Nodup) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_gen : genusDeficit T fuel darts = 0)
    {a b : D} (hab : a ≠ b) (ha_b : T.e.f a = b) (hb_a : T.e.f b = a)
    (hb_Tf : b ∈ getOrbit T.f fuel a) :
    have T1 := uncoupleEdge T a b
    (T1.e.f a = a ∧ T1.e.f b = b) ∧
      ¬ ReachEN T1.e T1.n a b ∧
      ¬ b ∈ getOrbit T1.f fuel a ∧
      (∀ {x y : D}, ReachEN T1.e T1.n x y → ReachEN T.e T.n x y) ∧
      (∀ x : D, ReachEN T.e T.n a x → ReachEN T1.e T1.n a x ∨ ReachEN T1.e T1.n b x) ∧
      countRelClasses (ReachEN T1.e T1.n) darts = countRelClasses (ReachEN T.e T.n) darts + 1 ∧
      countOrbits T1.e fuel darts = countOrbits T.e fuel darts + 1 ∧
      countOrbits T1.f fuel darts = countOrbits T.f fuel darts + 1 ∧
      genusDeficit T1 fuel darts = 0 ∧
      (∀ z : D, ¬ z ∈ getOrbit T.f fuel a → getOrbit T1.f fuel z = getOrbit T.f fuel z) := by
  dsimp only
  let T1 := uncoupleEdge T a b
  have hfix := uncoupleEdge_e_fixed T ha_b hb_a
  have hb_Te : b ∈ getOrbit T.e fuel a := by
    have h1 := mem_getOrbit_of_iter_complete T.e darts h_all h_le a 1
    simpa [Perm.iter, ha_b] using h1
  have hE1 : countOrbits T1.e fuel darts = countOrbits T.e fuel darts + 1 :=
    countOrbits_swapCompLeft_same T.e darts h_all h_le hab hb_Te
  have hF1 : countOrbits T1.f fuel darts = countOrbits T.f fuel darts + 1 :=
    countOrbits_swapCompRight_same T.f darts h_all h_le hab hb_Tf
  have hN1 : countOrbits T1.n fuel darts = countOrbits T.n fuel darts := rfl
  have h_disj : ¬ ReachEN T1.e T1.n a b := by
    intro h_ab
    have h_rel_iff : ∀ x y : D, ReachEN T1.e T1.n x y ↔ ReachEN T.e T.n x y := by
      intro x y
      have hcb := coupleEdge_reach_iff_or_bridge T1 hfix.1 hfix.2.1 (x := x) (y := y)
      rw [coupleEdge_uncoupleEdge_eq T a b] at hcb
      constructor
      · intro hxy; exact hcb.mpr (Or.inl hxy)
      · intro hxy
        rcases hcb.mp hxy with h | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
        · exact h
        · exact reachEN_trans T1.e T1.n (reachEN_trans T1.e T1.n hxa h_ab) hby
        · exact reachEN_trans T1.e T1.n (reachEN_trans T1.e T1.n hxb (reachEN_symm T1.e T1.n h_ab)) hay
    have hC1 : countRelClasses (ReachEN T1.e T1.n) darts = countRelClasses (ReachEN T.e T.n) darts :=
      countRelClasses_eq_of_rel_iff (ReachEN T1.e T1.n) (ReachEN T.e T.n) h_rel_iff fuel darts h_le
    have h_neg := genusDeficit_nonneg T1 darts h_nd h_all h_le
    dsimp [genusDeficit] at h_neg h_gen
    rw [hC1, hN1, hE1, hF1] at h_neg
    omega
  have hcd := coupleEdge_diff T1 darts h_all h_le hfix.1 hfix.2.1 h_disj
  rw [coupleEdge_uncoupleEdge_eq T a b] at hcd
  refine ⟨⟨hfix.1, hfix.2.1⟩, h_disj, hcd.2.1, ?_, ?_, hcd.2.2.2.2.1.symm, hE1, hF1, ?_, ?_⟩
  · intro x y hxy
    exact reachEN_uncouple_mono T.e T.n ha_b.symm hxy
  · intro x hax
    have hS := hcd.2.2.2.1 hax
    dsimp only at hS
    have hSa : decide (ReachEN T1.e T1.n a a ∨ ReachEN T1.e T1.n b a) = true :=
      decide_eq_true (Or.inl (reachEN_refl T1.e T1.n a))
    exact of_decide_eq_true (hS.symm.trans hSa)
  · rw [← hcd.2.2.2.2.2.2.2]; exact h_gen
  · intro z hza
    have ha_not_z : a ∉ getOrbit T.f fuel z := fun h => hza (mem_getOrbit_symm_complete T.f darts h_all h_le h)
    have hb_not_z : b ∉ getOrbit T.f fuel z := fun h =>
      hza (mem_getOrbit_trans_complete T.f darts h_all h_le hb_Tf (mem_getOrbit_symm_complete T.f darts h_all h_le h))
    exact (swapCompRight_iter_eq_of_not_mem_orbit T.f darts h_all h_le ha_not_z hb_not_z).2

end ReverseUncoupleAndDisjointPairs

section FaceCycleSeparation

/-- A `k`-cycle of edges separating faces in a planar hypermap `H` (equivalently a simple `k`-cycle
    in `H.dual`), with `2 ≤ k`, distinct ring faces `F_0, …, F_{k-1}`, and edge darts
    `cutDart i ∈ F_i` mapped across `H.edge` to `F_{(i + 1) % k}`. -/
structure FaceCycleCut (H : Hypermap) (k : Nat) where
  hk : 2 ≤ k
  ringFace : Fin k → H.Dart
  cutDart : Fin k → H.Dart
  h_diff : ∀ i j : Fin k, i ≠ j → ¬ SameOrbit H.face (ringFace i) (ringFace j)
  h_a : ∀ i : Fin k, SameOrbit H.face (ringFace i) (cutDart i)
  h_b : ∀ i : Fin k, SameOrbit H.face (ringFace ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩)
    (H.edge.f (cutDart i))
  h_disj_edge : ∀ i j : Fin k, H.edge.f (cutDart i) ≠ cutDart j

/-- Reverse orientation of a `FaceCycleCut` (swapping the roles of `D_L` and `D_R`). -/
def FaceCycleCut.rev {H : Hypermap} {k : Nat} (cut : FaceCycleCut H k) : FaceCycleCut H k where
  hk := cut.hk
  ringFace := fun i => cut.ringFace ⟨(k - i.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  cutDart := fun i => H.edge.f (cut.cutDart ⟨k - 1 - i.val, by have := i.isLt; omega⟩)
  h_diff := by
    have hk := cut.hk
    intro i j hij hsame
    apply cut.h_diff ⟨(k - i.val) % k, Nat.mod_lt _ (by omega)⟩
      ⟨(k - j.val) % k, Nat.mod_lt _ (by omega)⟩ _ hsame
    intro heq
    have hv : (k - i.val) % k = (k - j.val) % k := congrArg Fin.val heq
    apply hij; apply Fin.ext
    have hi := i.isLt; have hj := j.isLt
    by_cases hi0 : i.val = 0 <;> by_cases hj0 : j.val = 0
    · omega
    · rw [hi0, Nat.sub_zero, Nat.mod_self] at hv
      rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
    · rw [hj0, Nat.sub_zero, Nat.mod_self] at hv
      rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
      omega
  h_a := by
    have hk := cut.hk
    intro i
    have hi := i.isLt
    have hidx : ((k - 1 - i.val) + 1) % k = (k - i.val) % k := by
      have : (k - 1 - i.val) + 1 = k - i.val := by omega
      rw [this]
    have hb := cut.h_b ⟨k - 1 - i.val, by omega⟩
    have hfin : (⟨((k - 1 - i.val) + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) =
        ⟨(k - i.val) % k, Nat.mod_lt _ (by omega)⟩ := Fin.ext hidx
    rw [hfin] at hb
    exact hb
  h_b := by
    have hk := cut.hk
    intro i
    have hi := i.isLt
    rw [H.edge_involution]
    have hidx : (k - ((i.val + 1) % k)) % k = k - 1 - i.val := by
      by_cases h1 : i.val + 1 < k
      · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]; omega
      · have heq : i.val + 1 = k := by omega
        rw [heq, Nat.mod_self, Nat.sub_zero, Nat.mod_self]; omega
    have ha := cut.h_a ⟨k - 1 - i.val, by omega⟩
    have hfin : (⟨(k - ((i.val + 1) % k)) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) =
        ⟨k - 1 - i.val, by omega⟩ := Fin.ext hidx
    rw [hfin]
    exact ha
  h_disj_edge := by
    intro i j
    rw [H.edge_involution]
    intro heq
    exact cut.h_disj_edge ⟨k - 1 - j.val, by have := j.isLt; have := cut.hk; omega⟩
      ⟨k - 1 - i.val, by have := i.isLt; have := cut.hk; omega⟩ heq.symm

theorem FaceCycleCut.rev_rev {H : Hypermap} {k : Nat} (cut : FaceCycleCut H k) :
    cut.rev.rev = cut := by
  have hk := cut.hk
  cases cut with
  | mk hk' rf cd hdiff ha hb hdisj =>
    dsimp [FaceCycleCut.rev]
    congr 1
    · funext i; congr 1; apply Fin.ext
      have hi := i.isLt
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · have hmod1 : (k - i.val) % k = k - i.val := Nat.mod_eq_of_lt (by omega)
        dsimp
        rw [hmod1, show k - (k - i.val) = i.val by omega, Nat.mod_eq_of_lt hi]
    · funext i; rw [H.edge_involution]; congr 1; apply Fin.ext
      have hi := i.isLt; dsimp; omega

theorem FaceCycleCut.cut_inj {H : Hypermap} (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) :
    ∀ {i j : Fin k}, cut.cutDart i = cut.cutDart j → i = j := by
  classical
  intro i j heq
  by_cases hij : i = j
  · exact hij
  · exfalso
    have hi := cut.h_a i
    have hj := cut.h_a j
    rw [heq] at hi
    exact cut.h_diff i j hij
      (sameOrbit_trans H.face hi (sameOrbit_symm_of_complete H.face darts h_all hj))

theorem FaceCycleCut.edge_cut_inj {H : Hypermap} (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) :
    ∀ {i j : Fin k}, H.edge.f (cut.cutDart i) = H.edge.f (cut.cutDart j) → i = j :=
  fun heq => cut.cut_inj darts h_all (perm_f_inj_jcs H.edge heq)

def FaceCycleCut.cutPairs {H : Hypermap} {k : Nat} (cut : FaceCycleCut H k) :
    List (H.Dart × H.Dart) :=
  (List.finRange k).map (fun i => (cut.cutDart i, H.edge.f (cut.cutDart i)))

theorem FaceCycleCut.mem_cutPairs_iff {H : Hypermap} {k : Nat} (cut : FaceCycleCut H k)
    (q : H.Dart × H.Dart) :
    q ∈ cut.cutPairs ↔ ∃ i : Fin k, q = (cut.cutDart i, H.edge.f (cut.cutDart i)) := by
  dsimp [FaceCycleCut.cutPairs]
  constructor
  · intro h; rcases List.mem_map.mp h with ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact List.mem_map.mpr ⟨i, List.mem_iff_getElem.mpr ⟨i.val, by simp [List.length_finRange],
      by simp [List.getElem_finRange]⟩, rfl⟩

theorem FaceCycleCut.pairwiseDisjoint_cutPairs {H : Hypermap} (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) :
    PairwiseDisjointPairs cut.cutPairs := by
  have hnod : (List.finRange k).Nodup :=
    List.pairwise_iff_getElem.mpr (fun i j hi hj hij h => by
      simp [List.getElem_finRange] at h; omega)
  have aux : ∀ l : List (Fin k), l.Nodup →
      PairwiseDisjointPairs (l.map (fun i => (cut.cutDart i, H.edge.f (cut.cutDart i)))) := by
    intro l hnd
    induction l with
    | nil => exact trivial
    | cons i ls ih =>
      rcases List.nodup_cons.mp hnd with ⟨hi_mem, hnd_ls⟩
      refine ⟨(cut.h_disj_edge i i).symm, ?_, ih hnd_ls⟩
      intro q hq
      rcases List.mem_map.mp hq with ⟨j, hj, rfl⟩
      have hij : i ≠ j := fun h => hi_mem (h ▸ hj)
      refine ⟨fun h => hij (cut.cut_inj darts h_all h), (cut.h_disj_edge j i).symm,
        cut.h_disj_edge i j, fun h => hij (cut.edge_cut_inj darts h_all h)⟩
  exact aux (List.finRange k) hnod

noncomputable def FaceCycleCut.uncoupleTriple {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : FaceCycleCut H k) : PermTriple H.Dart :=
  uncoupleList H.hypermapToTriple cut.cutPairs

theorem FaceCycleCut.uncoupleTriple_rev_eq {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) :
    cut.rev.uncoupleTriple = cut.uncoupleTriple := by
  have hk := cut.hk
  have hrev_eq : cut.rev.cutPairs = (cut.cutPairs.map Prod.swap).reverse := by
    dsimp [FaceCycleCut.cutPairs, FaceCycleCut.rev]
    rw [List.map_map, ← List.map_reverse]
    apply List.ext_getElem
    · simp [List.length_finRange]
    · intro idx h1 h2
      have hk_len : idx < k := by simpa [List.length_finRange] using h1
      simp only [List.getElem_map, List.getElem_reverse, List.getElem_finRange,
        List.length_finRange, Function.comp_apply, Prod.swap, H.edge_involution]
      congr 1; all_goals (congr 1; apply Fin.ext; dsimp; omega)
  dsimp [FaceCycleCut.uncoupleTriple]
  rw [hrev_eq, uncoupleList_reverse _ _ (by
    have hpd : PairwiseDisjointPairs (cut.cutPairs.map Prod.swap) := by
      have aux : ∀ l : List (H.Dart × H.Dart), PairwiseDisjointPairs l →
          PairwiseDisjointPairs (l.map Prod.swap) := by
        intro l hl
        induction l with
        | nil => exact trivial
        | cons p ps ih =>
          rcases hl with ⟨h1, h2, h3⟩
          refine ⟨h1.symm, ?_, ih h3⟩
          intro q hq
          rcases List.mem_map.mp hq with ⟨r, hr, rfl⟩
          have hr' := h2 r hr
          exact ⟨hr'.2.2.2, hr'.2.2.1, hr'.2.1, hr'.1⟩
      exact aux cut.cutPairs (cut.pairwiseDisjoint_cutPairs darts h_all)
    exact hpd)]
  exact uncoupleList_map_swap H.hypermapToTriple cut.cutPairs

theorem sameOrbit_face_iff_mem_getOrbit [DecidableEq D] (p : Perm D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) (x y : D) :
    SameOrbit p x y ↔ y ∈ getOrbit p fuel x := by
  constructor
  · rintro ⟨m, rfl⟩; exact mem_getOrbit_of_iter_complete p darts h_all h_le x m
  · intro hy
    rcases mem_getOrbit_imp_exists_iter p fuel x y hy with ⟨m, _, rfl⟩
    exact ⟨m, rfl⟩

/-- First positive iterate along `H.face` from incoming cut-dart `b_{i-1}` to outgoing `a_i`
    on face `F_i`. Returns exact length `s_i` with `1 ≤ s_i < |F_i|`. -/
theorem FaceCycleCut.face_arc_len {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) :
    let b_prev := H.edge.f (cut.cutDart ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
    let a_i := cut.cutDart i
    ∃ s : Nat, 1 ≤ s ∧ s < (getOrbit H.face darts.length (cut.ringFace i)).length ∧
      Perm.iter H.face s b_prev = a_i ∧
      (∀ t : Nat, 1 ≤ t → t < s → Perm.iter H.face t b_prev ≠ a_i) ∧
      (∀ x : H.Dart, x ∈ getOrbit H.face darts.length b_prev ↔ x ∈ getOrbit H.face darts.length (cut.ringFace i)) ∧
      (getOrbit H.face darts.length b_prev).length =
        (getOrbit H.face darts.length (cut.ringFace i)).length := by
  have hk := cut.hk
  have hi := i.isLt
  dsimp only
  let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  let b_prev := H.edge.f (cut.cutDart i_prev)
  let a_i := cut.cutDart i
  have hmod_succ : (i_prev.val + 1) % k = i.val := by
    dsimp [i_prev]
    by_cases hi0 : i.val = 0
    · rw [hi0, Nat.zero_add, show (k - 1) % k = k - 1 from Nat.mod_eq_of_lt (by omega),
        show k - 1 + 1 = k by omega, Nat.mod_self]
    · have hred : (i.val + k - 1) % k = i.val - 1 := by
        rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hred, show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]
  have hb_same : SameOrbit H.face (cut.ringFace i) b_prev := by
    have hb' := cut.h_b i_prev
    have hfin : (⟨(i_prev.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = i := Fin.ext hmod_succ
    rw [hfin] at hb'
    exact hb'
  have ha_same : SameOrbit H.face (cut.ringFace i) a_i := cut.h_a i
  have hba_same : SameOrbit H.face b_prev a_i :=
    sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_all hb_same) ha_same
  have h_ne : b_prev ≠ a_i := cut.h_disj_edge i_prev i
  have ha_mem : a_i ∈ getOrbit H.face darts.length b_prev :=
    (sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) b_prev a_i).mp hba_same
  have h_fuel : 1 ≤ darts.length := by
    have ha_m := h_all a_i
    cases darts with | nil => cases ha_m | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  have h_close_b : orbitClosesWithin H.face b_prev b_prev darts.length :=
    orbitClosesWithin_of_complete H.face darts h_all b_prev
  rcases (mem_getOrbit_iff_exists_lt_length H.face h_fuel h_close_b a_i).mp ha_mem with ⟨m, hm_lt, hm_eq⟩
  rcases exists_min_pos_of_iter_eq H.face h_ne m hm_eq with ⟨s, hs1, hsm, hs_eq, hs_min⟩
  have h_close_r : orbitClosesWithin H.face (cut.ringFace i) (cut.ringFace i) darts.length :=
    orbitClosesWithin_of_complete H.face darts h_all (cut.ringFace i)
  have hb_mem_r : b_prev ∈ getOrbit H.face darts.length (cut.ringFace i) :=
    (sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) (cut.ringFace i) b_prev).mp hb_same
  have h_len_eq : (getOrbit H.face darts.length b_prev).length =
      (getOrbit H.face darts.length (cut.ringFace i)).length :=
    getOrbit_length_eq_of_mem H.face darts.length h_close_r hb_mem_r
  have h_iff : ∀ x : H.Dart, x ∈ getOrbit H.face darts.length b_prev ↔
      x ∈ getOrbit H.face darts.length (cut.ringFace i) := by
    intro x
    rw [← sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) b_prev x,
        ← sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) (cut.ringFace i) x]
    exact ⟨fun h => sameOrbit_trans H.face hb_same h,
      fun h => sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_all hb_same) h⟩
  exact ⟨s, hs1, by omega, hs_eq, hs_min, h_iff, h_len_eq⟩

theorem mod_pred_succ {k : Nat} (hk : 2 ≤ k) (i : Nat) (hi : i < k) :
    ((i + k - 1) % k + 1) % k = i := by
  by_cases hi0 : i = 0
  · rw [hi0, Nat.zero_add, show (k - 1) % k = k - 1 from Nat.mod_eq_of_lt (by omega),
      show k - 1 + 1 = k by omega, Nat.mod_self]
  · have hred : (i + k - 1) % k = i - 1 := by
      rw [show i + k - 1 = (i - 1) + k by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hred, show i - 1 + 1 = i by omega, Nat.mod_eq_of_lt hi]

theorem mod_succ_pred {k : Nat} (hk : 2 ≤ k) (i : Nat) (hi : i < k) :
    ((i + 1) % k + k - 1) % k = i := by
  by_cases h1 : i + 1 < k
  · rw [Nat.mod_eq_of_lt h1, show i + 1 + k - 1 = i + k by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hi
  · have heq : i + 1 = k := by omega
    rw [heq, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega

/-- Length `s_i` (`1 ≤ s_i < |F_i|`) of the `L`-side face arc on face `F_i` from `b_{i-1}` to `a_i`. -/
noncomputable def FaceCycleCut.arcLen {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) : Nat :=
  Classical.choose (cut.face_arc_len darts h_all i)

theorem FaceCycleCut.arcLen_spec {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) :
    let b_prev := H.edge.f (cut.cutDart ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
    let a_i := cut.cutDart i
    let s := cut.arcLen darts h_all i
    1 ≤ s ∧ s < (getOrbit H.face darts.length (cut.ringFace i)).length ∧
      Perm.iter H.face s b_prev = a_i ∧
      (∀ t : Nat, 1 ≤ t → t < s → Perm.iter H.face t b_prev ≠ a_i) ∧
      (∀ x : H.Dart, x ∈ getOrbit H.face darts.length b_prev ↔ x ∈ getOrbit H.face darts.length (cut.ringFace i)) ∧
      (getOrbit H.face darts.length b_prev).length =
        (getOrbit H.face darts.length (cut.ringFace i)).length :=
  Classical.choose_spec (cut.face_arc_len darts h_all i)

/-- The `L`-side arc `L_i` of face `F_i`: `{ H.face^t (b_{i-1}) | 1 ≤ t ≤ s_i }`, ending at `a_i`. -/
def FaceCycleCut.inArcL {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k)
    (x : H.Dart) : Prop :=
  let b_prev := H.edge.f (cut.cutDart ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
  ∃ t : Nat, 1 ≤ t ∧ t ≤ cut.arcLen darts h_all i ∧ Perm.iter H.face t b_prev = x

/-- The `R`-side arc `R_i` of face `F_i`: `{ H.face^u (a_i) | 1 ≤ u ≤ |F_i| - s_i }`, ending at `b_{i-1}`. -/
def FaceCycleCut.inArcR {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k)
    (x : H.Dart) : Prop :=
  ∃ u : Nat, 1 ≤ u ∧
    u ≤ (getOrbit H.face darts.length (cut.ringFace i)).length - cut.arcLen darts h_all i ∧
    Perm.iter H.face u (cut.cutDart i) = x

theorem FaceCycleCut.inArcL_sub_face {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) {i : Fin k} {x : H.Dart}
    (hx : cut.inArcL darts h_all i x) : SameOrbit H.face (cut.ringFace i) x := by
  have hk := cut.hk
  rcases hx with ⟨t, _, _, rfl⟩
  let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  have hb := cut.h_b i_prev
  have hfin : (⟨(i_prev.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = i :=
    Fin.ext (mod_pred_succ hk i.val i.isLt)
  rw [hfin] at hb
  exact sameOrbit_trans H.face hb ⟨t, rfl⟩

theorem FaceCycleCut.inArcR_sub_face {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) {i : Fin k} {x : H.Dart}
    (hx : cut.inArcR darts h_all i x) : SameOrbit H.face (cut.ringFace i) x := by
  rcases hx with ⟨u, _, _, rfl⟩
  exact sameOrbit_trans H.face (cut.h_a i) ⟨u, rfl⟩

theorem FaceCycleCut.cutDart_mem_inArcL {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) :
    cut.inArcL darts h_all i (cut.cutDart i) := by
  have hs := cut.arcLen_spec darts h_all i
  exact ⟨cut.arcLen darts h_all i, hs.1, Nat.le_refl _, hs.2.2.1⟩

theorem FaceCycleCut.edgePrev_mem_inArcR {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) :
    let b_prev := H.edge.f (cut.cutDart ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
    cut.inArcR darts h_all i b_prev := by
  have hs := cut.arcLen_spec darts h_all i
  let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  let b_prev := H.edge.f (cut.cutDart i_prev)
  let s := cut.arcLen darts h_all i
  let L := (getOrbit H.face darts.length (cut.ringFace i)).length
  refine ⟨L - s, by omega, Nat.le_refl _, ?_⟩
  rw [← hs.2.2.1, ← Perm.iter_add]
  have hsum : L - s + s = L := by omega
  rw [hsum]; dsimp only [L]; rw [← hs.2.2.2.2.2]
  exact perm_iter_length_getOrbit_eq_self_of_complete H.face darts h_all (Nat.le_refl _) b_prev

theorem FaceCycleCut.face_partition_arcs {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) (x : H.Dart) :
    (SameOrbit H.face (cut.ringFace i) x ↔
      cut.inArcL darts h_all i x ∨ cut.inArcR darts h_all i x) ∧
      ¬ (cut.inArcL darts h_all i x ∧ cut.inArcR darts h_all i x) := by
  have hs := cut.arcLen_spec darts h_all i
  let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  let b_prev := H.edge.f (cut.cutDart i_prev)
  let s := cut.arcLen darts h_all i
  let L := (getOrbit H.face darts.length (cut.ringFace i)).length
  have h_len_b : (getOrbit H.face darts.length b_prev).length = L := hs.2.2.2.2.2
  have h_close_b : orbitClosesWithin H.face b_prev b_prev darts.length :=
    orbitClosesWithin_of_complete H.face darts h_all b_prev
  have h_fuel : 1 ≤ darts.length := by
    have ha := h_all (cut.cutDart i)
    cases darts with | nil => cases ha | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  constructor
  · constructor
    · intro hx
      have hx_mem : x ∈ getOrbit H.face darts.length b_prev :=
        (hs.2.2.2.2.1 x).mpr ((sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _)
          (cut.ringFace i) x).mp hx)
      rcases (mem_getOrbit_iff_exists_lt_length H.face h_fuel h_close_b x).mp hx_mem with
        ⟨r, hr_lt, hr_eq⟩
      by_cases hr0 : r = 0
      · right
        rw [hr0, Perm.iter_zero] at hr_eq
        subst hr_eq
        exact cut.edgePrev_mem_inArcR darts h_all i
      · by_cases hrs : r ≤ s
        · left; exact ⟨r, by omega, hrs, hr_eq⟩
        · right
          refine ⟨r - s, by omega, by omega, ?_⟩
          rw [← hs.2.2.1, ← Perm.iter_add, show r - s + s = r by omega]
          exact hr_eq
    · rintro (hl | hr)
      · exact cut.inArcL_sub_face darts h_all hl
      · exact cut.inArcR_sub_face darts h_all hr
  · rintro ⟨⟨t, ht1, hts, ht_eq⟩, ⟨u, hu1, hus, hu_eq⟩⟩
    have hu_b : Perm.iter H.face (u + s) b_prev = x := by
      rw [Perm.iter_add, hs.2.2.1]; exact hu_eq
    by_cases hus_L : u + s = L
    · have ht_lt : t < (getOrbit H.face darts.length b_prev).length := by omega
      have hx_b : x = b_prev := by
        rw [← hu_b, hus_L, ← h_len_b]
        exact perm_iter_length_getOrbit_eq_self_of_complete H.face darts h_all (Nat.le_refl _) b_prev
      have ht0 : Perm.iter H.face t b_prev = Perm.iter H.face 0 b_prev := ht_eq.trans hx_b
      have heq := perm_iter_inj_of_lt_getOrbit_length H.face ht_lt (by omega) ht0
      omega
    · have ht_lt : t < (getOrbit H.face darts.length b_prev).length := by omega
      have hus_lt : u + s < (getOrbit H.face darts.length b_prev).length := by omega
      have heq := perm_iter_inj_of_lt_getOrbit_length H.face ht_lt hus_lt (ht_eq.trans hu_b.symm)
      omega

theorem FaceCycleCut.inArcL_interior_not_cut {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) {t : Nat}
    (ht1 : 1 ≤ t) (ht_lt : t < cut.arcLen darts h_all i) :
    let b_prev := H.edge.f (cut.cutDart ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
    let y := Perm.iter H.face t b_prev
    ∀ q ∈ cut.cutPairs, y ≠ q.1 ∧ y ≠ q.2 := by
  have hk := cut.hk
  have hs := cut.arcLen_spec darts h_all i
  let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  let b_prev := H.edge.f (cut.cutDart i_prev)
  let y := Perm.iter H.face t b_prev
  have hy_inL : cut.inArcL darts h_all i y := ⟨t, ht1, by omega, rfl⟩
  have hy_Fi : SameOrbit H.face (cut.ringFace i) y := cut.inArcL_sub_face darts h_all hy_inL
  dsimp only
  intro q hq
  rcases (cut.mem_cutPairs_iff q).mp hq with ⟨j, rfl⟩
  constructor
  · intro heq
    by_cases hji : j = i
    · subst hji; exact hs.2.2.2.1 t ht1 ht_lt heq
    · have hj := cut.h_a j
      dsimp only at heq; rw [← heq] at hj
      exact cut.h_diff j i hji (sameOrbit_trans H.face hj (sameOrbit_symm_of_complete H.face darts h_all hy_Fi))
  · intro heq
    by_cases hjp : j = i_prev
    · subst hjp
      have hy0 : Perm.iter H.face t b_prev = Perm.iter H.face 0 b_prev := heq
      have hlb : (getOrbit H.face darts.length b_prev).length =
          (getOrbit H.face darts.length (cut.ringFace i)).length := hs.2.2.2.2.2
      have hs_lt : arcLen darts h_all cut i <
          (getOrbit H.face darts.length (cut.ringFace i)).length := hs.2.1
      have h_eq0 := perm_iter_inj_of_lt_getOrbit_length H.face (fuel := darts.length)
        (by omega) (by omega) hy0
      omega
    · have hb := cut.h_b j
      dsimp only at heq; rw [← heq] at hb
      have h_ne : (⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) ≠ i := by
        intro hfin; apply hjp; apply Fin.ext
        have hv : (j.val + 1) % k = i.val := congrArg Fin.val hfin
        have := mod_succ_pred hk j.val j.isLt
        rw [hv] at this; exact this.symm
      exact cut.h_diff _ i h_ne (sameOrbit_trans H.face hb (sameOrbit_symm_of_complete H.face darts h_all hy_Fi))

theorem FaceCycleCut.inArcR_interior_not_cut {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) {u : Nat}
    (hu1 : 1 ≤ u)
    (hu_lt : u < (getOrbit H.face darts.length (cut.ringFace i)).length - cut.arcLen darts h_all i) :
    let y := Perm.iter H.face u (cut.cutDart i)
    ∀ q ∈ cut.cutPairs, y ≠ q.1 ∧ y ≠ q.2 := by
  have hk := cut.hk
  have hs := cut.arcLen_spec darts h_all i
  let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  let b_prev := H.edge.f (cut.cutDart i_prev)
  let s := cut.arcLen darts h_all i
  let L := (getOrbit H.face darts.length (cut.ringFace i)).length
  have h_len_b : (getOrbit H.face darts.length b_prev).length = L := hs.2.2.2.2.2
  let y := Perm.iter H.face u (cut.cutDart i)
  have hy_inR : cut.inArcR darts h_all i y := ⟨u, hu1, by omega, rfl⟩
  have hy_Fi : SameOrbit H.face (cut.ringFace i) y := cut.inArcR_sub_face darts h_all hy_inR
  have hy_b : Perm.iter H.face (u + s) b_prev = y := by
    rw [Perm.iter_add, hs.2.2.1]
  dsimp only
  intro q hq
  rcases (cut.mem_cutPairs_iff q).mp hq with ⟨j, rfl⟩
  constructor
  · intro heq
    by_cases hji : j = i
    · subst hji
      have heq' : Perm.iter H.face (u + s) b_prev = Perm.iter H.face s b_prev :=
        hy_b.trans (heq.trans hs.2.2.1.symm)
      have hinj := perm_iter_inj_of_lt_getOrbit_length H.face (fuel := darts.length) (by omega) (by omega) heq'
      omega
    · have hj := cut.h_a j
      dsimp only at heq; rw [← heq] at hj
      exact cut.h_diff j i hji (sameOrbit_trans H.face hj (sameOrbit_symm_of_complete H.face darts h_all hy_Fi))
  · intro heq
    by_cases hjp : j = i_prev
    · subst hjp
      have heq' : Perm.iter H.face (u + s) b_prev = Perm.iter H.face 0 b_prev := hy_b.trans heq
      have hinj := perm_iter_inj_of_lt_getOrbit_length H.face (fuel := darts.length) (by omega) (by omega) heq'
      omega
    · have hb := cut.h_b j
      dsimp only at heq; rw [← heq] at hb
      have h_ne : (⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) ≠ i := by
        intro hfin; apply hjp; apply Fin.ext
        have hv : (j.val + 1) % k = i.val := congrArg Fin.val hfin
        have := mod_succ_pred hk j.val j.isLt
        rw [hv] at this; exact this.symm
      exact cut.h_diff _ i h_ne (sameOrbit_trans H.face hb (sameOrbit_symm_of_complete H.face darts h_all hy_Fi))

theorem FaceCycleCut.uncoupleTriple_step_arcL {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) :
    let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
    let a_prev := cut.cutDart i_prev
    let b_prev := H.edge.f a_prev
    ∀ t : Nat, 1 ≤ t → t ≤ cut.arcLen darts h_all i →
      Perm.iter cut.uncoupleTriple.f t a_prev = Perm.iter H.face t b_prev := by
  have hk := cut.hk
  dsimp only
  let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  let a_prev := cut.cutDart i_prev
  let b_prev := H.edge.f a_prev
  let T := cut.uncoupleTriple
  have hpd := cut.pairwiseDisjoint_cutPairs darts h_all
  intro t ht1 hts
  induction t with
  | zero => omega
  | succ t' ih =>
    cases t' with
    | zero =>
      rw [Perm.iter_succ, Perm.iter_zero, Perm.iter_succ, Perm.iter_zero]
      have hmem : (a_prev, b_prev) ∈ cut.cutPairs :=
        (cut.mem_cutPairs_iff (a_prev, b_prev)).mpr ⟨i_prev, rfl⟩
      exact ((uncoupleList_f_eval H.hypermapToTriple cut.cutPairs hpd a_prev).2
        (a_prev, b_prev) hmem).1 rfl
    | succ t'' =>
      rw [Perm.iter_succ T.f (t'' + 1), Perm.iter_succ H.face (t'' + 1)]
      have hprev := ih (by omega) (by omega)
      rw [hprev]
      have hnot := cut.inArcL_interior_not_cut darts h_all i (t := t'' + 1) (by omega) (by omega); dsimp only at hnot
      exact (uncoupleList_f_eval H.hypermapToTriple cut.cutPairs hpd _).1 hnot

theorem FaceCycleCut.uncoupleTriple_step_arcR {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) :
    let L := (getOrbit H.face darts.length (cut.ringFace i)).length
    let s := cut.arcLen darts h_all i
    let b_i := H.edge.f (cut.cutDart i)
    ∀ u : Nat, 1 ≤ u → u ≤ L - s →
      Perm.iter cut.uncoupleTriple.f u b_i = Perm.iter H.face u (cut.cutDart i) := by
  dsimp only
  let T := cut.uncoupleTriple
  have hpd := cut.pairwiseDisjoint_cutPairs darts h_all
  intro u hu1 hu_le
  induction u with
  | zero => omega
  | succ u' ih =>
    cases u' with
    | zero =>
      rw [Perm.iter_succ, Perm.iter_zero, Perm.iter_succ, Perm.iter_zero]
      have hmem : (cut.cutDart i, H.edge.f (cut.cutDart i)) ∈ cut.cutPairs :=
        (cut.mem_cutPairs_iff _).mpr ⟨i, rfl⟩
      exact ((uncoupleList_f_eval H.hypermapToTriple cut.cutPairs hpd _).2
        (cut.cutDart i, H.edge.f (cut.cutDart i)) hmem).2 rfl
    | succ u'' =>
      rw [Perm.iter_succ T.f (u'' + 1), Perm.iter_succ H.face (u'' + 1)]
      rw [ih (by omega) (by omega)]
      have hnot := cut.inArcR_interior_not_cut darts h_all i (u := u'' + 1) (by omega) (by omega); dsimp only at hnot
      exact (uncoupleList_f_eval H.hypermapToTriple cut.cutPairs hpd _).1 hnot

noncomputable def FaceCycleCut.posL {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) : Nat → Nat
  | 0 => 0
  | m + 1 =>
    cut.posL darts h_all m +
      cut.arcLen darts h_all ⟨(m + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩

theorem FaceCycleCut.posL_strictMono {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) :
    ∀ {m n : Nat}, m < n → cut.posL darts h_all m < cut.posL darts h_all n := by
  intro m n hmn
  induction n with
  | zero => omega
  | succ n ih =>
    have hs := (cut.arcLen_spec darts h_all ⟨(n + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩).1
    dsimp [FaceCycleCut.posL]
    by_cases hmn' : m = n
    · subst hmn'; omega
    · have := ih (by omega); omega

theorem FaceCycleCut.uncoupleTriple_iter_posL {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k) (m : Nat) :
    Perm.iter cut.uncoupleTriple.f (cut.posL darts h_all m) (cut.cutDart ⟨0, by have := cut.hk; omega⟩) =
      cut.cutDart ⟨m % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ := by
  have hk := cut.hk
  induction m with
  | zero => simp [FaceCycleCut.posL, Nat.zero_mod]
  | succ m ih =>
    dsimp [FaceCycleCut.posL]
    rw [Nat.add_comm, Perm.iter_add, ih]
    let i_next : Fin k := ⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩
    have hstep := cut.uncoupleTriple_step_arcL darts h_all i_next
      (cut.arcLen darts h_all i_next) (cut.arcLen_spec darts h_all i_next).1 (Nat.le_refl _)
    have hidx : ((m + 1) % k + k - 1) % k = m % k := by
      rw [show (m + 1) % k = (m % k + 1) % k from by simp [Nat.add_mod]]
      exact mod_succ_pred hk (m % k) (Nat.mod_lt _ (by omega))
    have hfin : (⟨((m + 1) % k + k - 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) =
        ⟨m % k, Nat.mod_lt _ (by omega)⟩ := Fin.ext hidx
    have h_arc := (cut.arcLen_spec darts h_all i_next).2.2.1
    rw [hfin] at hstep h_arc
    rw [hstep]
    exact h_arc

theorem FaceCycleCut.uncoupleTriple_a_all_sameOrbit_f {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k)
    (i : Fin k) :
    SameOrbit cut.uncoupleTriple.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩) (cut.cutDart i) := by
  refine ⟨cut.posL darts h_all i.val, ?_⟩
  rw [cut.uncoupleTriple_iter_posL darts h_all i.val]
  congr 1; apply Fin.ext; exact Nat.mod_eq_of_lt i.isLt

theorem FaceCycleCut.uncoupleTriple_b_all_sameOrbit_f {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k)
    (i : Fin k) :
    SameOrbit cut.uncoupleTriple.f (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩))
      (H.edge.f (cut.cutDart i)) := by
  have hk := cut.hk
  let j : Fin k := ⟨k - 1 - i.val, by omega⟩
  have heq_f := (cut.rev).uncoupleTriple_a_all_sameOrbit_f darts h_all j
  rw [cut.uncoupleTriple_rev_eq darts h_all] at heq_f
  dsimp [FaceCycleCut.rev] at heq_f
  have hfin1 : (⟨k - 1 - 0, by omega⟩ : Fin k) = ⟨k - 1, by omega⟩ := rfl
  have hfin2 : (⟨k - 1 - j.val, by omega⟩ : Fin k) = i := Fin.ext (by dsimp [j]; omega)
  rw [hfin2] at heq_f
  exact heq_f

theorem FaceCycleCut.uncoupleTriple_outerL_orbit {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k)
    (x : H.Dart) :
    x ∈ getOrbit cut.uncoupleTriple.f darts.length (cut.cutDart ⟨0, by have := cut.hk; omega⟩) ↔
      ∃ i : Fin k, cut.inArcL darts h_all i x := by
  have hk := cut.hk
  let a0 := cut.cutDart ⟨0, by omega⟩
  let T := cut.uncoupleTriple
  have hL : Perm.iter T.f (cut.posL darts h_all k) a0 = a0 := by
    rw [cut.uncoupleTriple_iter_posL darts h_all k]
    congr 1; apply Fin.ext; simp
  constructor
  · intro hx
    rcases mem_getOrbit_imp_exists_iter T.f darts.length a0 x hx with ⟨r, _, rfl⟩
    let r' := r % cut.posL darts h_all k
    have hpos_k : 0 < cut.posL darts h_all k := by
      have := cut.posL_strictMono darts h_all (m := 0) (n := k) (by omega)
      dsimp [FaceCycleCut.posL] at this; omega
    have hr'_lt : r' < cut.posL darts h_all k := Nat.mod_lt _ hpos_k
    have h_mod_eq : Perm.iter T.f r a0 = Perm.iter T.f r' a0 := by
      have hdiv := Nat.div_add_mod r (cut.posL darts h_all k)
      have hiter_mul : ∀ q : Nat, Perm.iter T.f (cut.posL darts h_all k * q) a0 = a0 := by
        intro q; induction q with
        | zero => rfl
        | succ q ih =>
          rw [Nat.mul_succ, Nat.add_comm, Perm.iter_add, ih, hL]
      rw [← hdiv, Nat.add_comm, Perm.iter_add, hiter_mul (r / cut.posL darts h_all k)]
    rw [h_mod_eq]
    by_cases hr'0 : r' = 0
    · rw [hr'0, Perm.iter_zero]
      exact ⟨⟨0, by omega⟩, cut.cutDart_mem_inArcL darts h_all ⟨0, by omega⟩⟩
    · -- Find unique block `m < k` with `posL m < r' ≤ posL (m + 1)`
      have hex_m : ∃ m : Nat, m < k ∧ cut.posL darts h_all m < r' ∧
          r' ≤ cut.posL darts h_all (m + 1) := by
        -- Largest `m < k` with `posL m < r'`
        have aux : ∀ B : Nat, B ≤ k → r' ≤ cut.posL darts h_all B → r' > 0 →
            ∃ m, m < B ∧ cut.posL darts h_all m < r' ∧ r' ≤ cut.posL darts h_all (m + 1) := by
          intro B hBk hrB hpos
          induction B with
          | zero => dsimp [FaceCycleCut.posL] at hrB; omega
          | succ B ih =>
            by_cases hlt : r' ≤ cut.posL darts h_all B
            · rcases ih (by omega) hlt with ⟨m, hmB, h1, h2⟩
              exact ⟨m, by omega, h1, h2⟩
            · exact ⟨B, by omega, by omega, hrB⟩
        exact aux k (Nat.le_refl k) (Nat.le_of_lt hr'_lt) (Nat.pos_of_ne_zero hr'0)
      rcases hex_m with ⟨m, hm_k, hm_lo, hm_hi⟩
      let i_next : Fin k := ⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩
      let t := r' - cut.posL darts h_all m
      have ht1 : 1 ≤ t := by omega
      have ht_arc : t ≤ cut.arcLen darts h_all i_next := by
        dsimp only [FaceCycleCut.posL, i_next, t] at hm_hi ⊢; omega
      have hr'_eq : r' = t + cut.posL darts h_all m := by omega
      rw [hr'_eq, Perm.iter_add, cut.uncoupleTriple_iter_posL darts h_all m]
      have hstep := cut.uncoupleTriple_step_arcL darts h_all i_next t ht1 ht_arc
      have hidx : ((m + 1) % k + k - 1) % k = m := by
        rw [show (m + 1) % k = (m % k + 1) % k from by simp [Nat.add_mod]]
        rw [mod_succ_pred hk (m % k) (Nat.mod_lt _ (by omega)), Nat.mod_eq_of_lt hm_k]
      have hfin : (⟨((m + 1) % k + k - 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) =
          ⟨m, hm_k⟩ := Fin.ext hidx
      have hfin_m : (⟨m % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨m, hm_k⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hm_k)
      rw [hfin_m]
      refine ⟨i_next, t, ht1, ht_arc, ?_⟩
      rw [← hstep, hfin]
  · rintro ⟨i, t, ht1, ht_arc, rfl⟩
    let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
    have hstep := cut.uncoupleTriple_step_arcL darts h_all i t ht1 ht_arc
    rw [← hstep]
    have ha_orb : cut.cutDart i_prev ∈ getOrbit T.f darts.length a0 :=
      (sameOrbit_face_iff_mem_getOrbit T.f darts h_all (Nat.le_refl _) a0 (cut.cutDart i_prev)).mp
        (cut.uncoupleTriple_a_all_sameOrbit_f darts h_all i_prev)
    exact mem_getOrbit_trans_complete T.f darts h_all (Nat.le_refl _) ha_orb
      (mem_getOrbit_of_iter_complete T.f darts h_all (Nat.le_refl _) (cut.cutDart i_prev) t)

theorem FaceCycleCut.uncoupleTriple_outerR_orbit {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k)
    (x : H.Dart) :
    x ∈ getOrbit cut.uncoupleTriple.f darts.length
        (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩)) ↔
      ∃ i : Fin k, cut.inArcR darts h_all i x := by
  have hk := cut.hk
  let T := cut.uncoupleTriple
  let b_last := H.edge.f (cut.cutDart ⟨k - 1, by omega⟩)
  have hS_closed : ∀ y : H.Dart, (∃ i : Fin k, cut.inArcR darts h_all i y) →
      ∃ i : Fin k, cut.inArcR darts h_all i (T.f.f y) := by
    rintro y ⟨i, u, hu1, hu_le, rfl⟩
    let L := (getOrbit H.face darts.length (cut.ringFace i)).length
    let s := cut.arcLen darts h_all i
    have hs := cut.arcLen_spec darts h_all i
    by_cases hu_lt : u < L - s
    · have hnot := cut.inArcR_interior_not_cut darts h_all i hu1 hu_lt
      have hf : T.f.f (Perm.iter H.face u (cut.cutDart i)) =
          H.face.f (Perm.iter H.face u (cut.cutDart i)) :=
        (uncoupleList_f_eval H.hypermapToTriple cut.cutPairs
          (cut.pairwiseDisjoint_cutPairs darts h_all) _).1 hnot
      rw [hf, ← Perm.iter_succ]
      exact ⟨i, u + 1, by omega, by omega, rfl⟩
    · have hu_eq : u = L - s := by omega
      subst hu_eq
      have h_eq_bprev : Perm.iter H.face (L - s) (cut.cutDart i) =
          H.edge.f (cut.cutDart ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩) := by
        rw [← hs.2.2.1, ← Perm.iter_add, show L - s + s = L by omega]; dsimp only [L]; rw [← hs.2.2.2.2.2]
        exact perm_iter_length_getOrbit_eq_self_of_complete H.face darts h_all (Nat.le_refl _) _
      rw [h_eq_bprev]
      let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
      have hmem : (cut.cutDart i_prev, H.edge.f (cut.cutDart i_prev)) ∈ cut.cutPairs :=
        (cut.mem_cutPairs_iff _).mpr ⟨i_prev, rfl⟩
      have hf := ((uncoupleList_f_eval H.hypermapToTriple cut.cutPairs
        (cut.pairwiseDisjoint_cutPairs darts h_all) (H.edge.f (cut.cutDart i_prev))).2
        (cut.cutDart i_prev, H.edge.f (cut.cutDart i_prev)) hmem).2 rfl
      dsimp only [T, FaceCycleCut.uncoupleTriple, i_prev] at hf ⊢; rw [hf]
      have hs_p := cut.arcLen_spec darts h_all i_prev
      refine ⟨i_prev, 1, Nat.le_refl _, by omega, ?_⟩
      rfl
  constructor
  · intro hx
    rcases mem_getOrbit_imp_exists_iter T.f darts.length b_last x hx with ⟨m, _, rfl⟩
    induction m with
    | zero =>
      rw [Perm.iter_zero]
      have hb0 := cut.edgePrev_mem_inArcR darts h_all ⟨0, by omega⟩
      have hidx : (0 + k - 1) % k = k - 1 := by
        rw [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
      have hfin : (⟨(0 + k - 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨k - 1, by omega⟩ :=
        Fin.ext hidx
      dsimp only at hb0; rw [hfin] at hb0
      exact ⟨⟨0, by omega⟩, hb0⟩
    | succ m ih =>
      rw [Perm.iter_succ]
      exact hS_closed _ (ih (by omega)
        (mem_getOrbit_of_iter_complete T.f darts h_all (Nat.le_refl _) b_last m))
  · rintro ⟨i, u, hu1, hu_le, rfl⟩
    have hstep := cut.uncoupleTriple_step_arcR darts h_all i u hu1 hu_le
    rw [← hstep]
    have hb_orb : H.edge.f (cut.cutDart i) ∈ getOrbit T.f darts.length b_last :=
      (sameOrbit_face_iff_mem_getOrbit T.f darts h_all (Nat.le_refl _) _ _).mp
        (cut.uncoupleTriple_b_all_sameOrbit_f darts h_all i)
    exact mem_getOrbit_trans_complete T.f darts h_all (Nat.le_refl _) hb_orb
      (mem_getOrbit_of_iter_complete T.f darts h_all (Nat.le_refl _) _ u)

private theorem forall_rel_of_countRelClasses_eq_one {D : Type} (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    (l : List D) (h_one : countRelClasses R l = 1) (a b : D) (ha : a ∈ l) (hb : b ∈ l) : R a b := by
  have hsplit := countRelClasses_eq_one_add_filter_of_mem R h_refl h_symm h_trans l a ha
  rw [h_one] at hsplit
  have h0 : countRelClasses R (l.filter (fun x => !decide (R a x))) = 0 := by omega
  by_cases hR : R a b
  · exact hR
  · exfalso
    have hmem : b ∈ l.filter (fun x => !decide (R a x)) :=
      List.mem_filter.mpr ⟨hb, by simp [hR]⟩
    cases hfl : l.filter (fun x => !decide (R a x)) with
    | nil => rw [hfl] at hmem; cases hmem
    | cons z zs => rw [hfl, countRelClasses_cons] at h0; omega

theorem list_take_succ_of_lt {α : Type} :
    ∀ (l : List α) (m : Nat) (hm : m < l.length),
      l.take (m + 1) = l.take m ++ [l[m]]
  | [], _, hm => by simp at hm
  | a :: as, 0, _ => rfl
  | a :: as, m + 1, hm => by
    simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
    congr 1
    exact list_take_succ_of_lt as m (by simp at hm; omega)

/-- **Discrete Jordan `k`-Cycle Separation Theorem**:
    Uncoupling all `k` edges (`k ≥ 2`) along a `FaceCycleCut` in a connected planar hypermap `H`
    splits `H` into a planar (`genusDeficit = 0`) two-component triple `T_k` with `C(T_k) = 2`,
    exact component partition `D = D_L ⊔ D_R`, all `a_i ∈ D_L` and `b_i ∈ D_R`, exact face-arc
    orbits `⋃ L_i` and `⋃ R_i`, untouched interior faces, and `T_k.n = H.node`. -/
theorem uncoupleCycle_two_components (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) :
    let T_k := cut.uncoupleTriple
    let a0 := cut.cutDart ⟨0, by have := cut.hk; omega⟩
    let b0 := H.edge.f a0
    let DL := fun x : H.Dart => ReachEN T_k.e T_k.n a0 x
    let DR := fun x : H.Dart => ReachEN T_k.e T_k.n b0 x
    T_k.n = H.node ∧
      (∀ d : H.Dart, T_k.e.f (T_k.e.f d) = d) ∧
      genusDeficit T_k darts.length darts = 0 ∧
      countRelClasses (ReachEN T_k.e T_k.n) darts = 2 ∧
      ¬ ReachEN T_k.e T_k.n a0 b0 ∧
      (∀ x : H.Dart, DL x ∨ DR x) ∧
      (∀ x : H.Dart, ¬ (DL x ∧ DR x)) ∧
      (∀ i : Fin k, DL (cut.cutDart i) ∧ DR (H.edge.f (cut.cutDart i))) ∧
      (∀ i : Fin k, T_k.e.f (cut.cutDart i) = cut.cutDart i ∧
        T_k.e.f (H.edge.f (cut.cutDart i)) = H.edge.f (cut.cutDart i)) ∧
      (∀ x : H.Dart, (∀ i : Fin k, x ≠ cut.cutDart i ∧ x ≠ H.edge.f (cut.cutDart i)) →
        T_k.e.f x = H.edge.f x ∧ T_k.f.f x = H.face.f x) ∧
      (∀ x : H.Dart, x ∈ getOrbit T_k.f darts.length a0 ↔ ∃ i : Fin k, cut.inArcL darts h_all i x) ∧
      (∀ x : H.Dart, x ∈ getOrbit T_k.f darts.length (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩)) ↔
        ∃ i : Fin k, cut.inArcR darts h_all i x) ∧
      (∀ z : H.Dart, (∀ i : Fin k, ¬ SameOrbit H.face (cut.ringFace i) z) →
        getOrbit T_k.f darts.length z = getOrbit H.face darts.length z) := by
  have hk := cut.hk
  have hpd := cut.pairwiseDisjoint_cutPairs darts h_all
  let T_k := cut.uncoupleTriple
  let rf0 := cut.ringFace ⟨0, by omega⟩
  let a0 := cut.cutDart ⟨0, by omega⟩
  let b0 := H.edge.f a0
  have h_gen0 : genusDeficit H.hypermapToTriple darts.length darts = 0 :=
    ((eulerChar_le_two_mul_numComponents H darts h_nd h_all (Nat.le_refl _)).2.mp h_planar).1
  have h_C1 : countRelClasses (ReachEN H.hypermapToTriple.e H.hypermapToTriple.n) darts = 1 := by
    change countRelClasses (ReachEN H.edge H.node) darts = 1
    rw [countRelClasses_reachEN_eq_countComponents H darts h_all (Nat.le_refl _) darts]
    exact h_conn
  have hlen_pairs : cut.cutPairs.length = k := by
    dsimp [FaceCycleCut.cutPairs]; simp [List.length_finRange]
  let T_pref : Nat → PermTriple H.Dart := fun m =>
    uncoupleList H.hypermapToTriple (cut.cutPairs.take m)
  have h_pref_step : ∀ m : Nat, (hm : m < k) →
      T_pref (m + 1) = uncoupleEdge (T_pref m)
        (cut.cutDart ⟨m, hm⟩) (H.edge.f (cut.cutDart ⟨m, hm⟩)) := by
    intro m hm
    dsimp [T_pref, uncoupleList]
    rw [list_take_succ_of_lt cut.cutPairs m (by rw [hlen_pairs]; exact hm), coupleList_append]
    have helem : cut.cutPairs[m]'(by rw [hlen_pairs]; exact hm) =
        (cut.cutDart ⟨m, hm⟩, H.edge.f (cut.cutDart ⟨m, hm⟩)) := by
      simp [FaceCycleCut.cutPairs, List.getElem_map, List.getElem_finRange]
    rw [helem]
    rfl
  let Inv : Nat → Prop := fun m =>
    countRelClasses (ReachEN (T_pref m).e (T_pref m).n) darts = 1 ∧
      genusDeficit (T_pref m) darts.length darts = 0 ∧
      (T_pref m).n = H.node ∧
      (∀ x : H.Dart, x ∈ getOrbit (T_pref m).f darts.length rf0 ↔
        ∃ j : Fin k, j.val ≤ m ∧ SameOrbit H.face (cut.ringFace j) x) ∧
      (∀ z : H.Dart, (∀ j : Fin k, j.val ≤ m → ¬ SameOrbit H.face (cut.ringFace j) z) →
        getOrbit (T_pref m).f darts.length z = getOrbit H.face darts.length z) ∧
      (∀ x : H.Dart, (∀ j : Fin k, j.val < m → x ≠ cut.cutDart j ∧ x ≠ H.edge.f (cut.cutDart j)) →
        (T_pref m).e.f x = H.edge.f x)
  have hInv : ∀ m : Nat, m < k → Inv m := by
    intro m hm
    induction m with
    | zero =>
      refine ⟨h_C1, h_gen0, rfl, ?_, ?_, fun _ _ => rfl⟩
      · intro x
        change x ∈ getOrbit H.face darts.length rf0 ↔ _
        rw [← sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) rf0 x]
        constructor
        · intro h; exact ⟨⟨0, by omega⟩, Nat.le_refl _, h⟩
        · rintro ⟨j, hj0, h⟩
          have hjeq : j = ⟨0, hm⟩ := Fin.ext (Nat.le_zero.mp hj0)
          rw [hjeq] at h; exact h
      · intro _ _; rfl
    | succ m ih =>
      rcases ih (by omega) with ⟨hC_m, hg_m, hn_m, hM_m, hU_m, he_m⟩
      let im : Fin k := ⟨m, by omega⟩
      let ip : Fin k := ⟨m + 1, hm⟩
      let am := cut.cutDart im
      let bm := H.edge.f am
      have hab : am ≠ bm := (cut.h_disj_edge im im).symm
      have ham_fresh : ∀ j : Fin k, j.val < m →
          am ≠ cut.cutDart j ∧ am ≠ H.edge.f (cut.cutDart j) := by
        intro j hj
        refine ⟨fun h => ?_, fun h => cut.h_disj_edge j im h.symm⟩
        have heqj := cut.cut_inj darts h_all h
        have hv := congrArg Fin.val heqj; dsimp [im] at hv; omega
      have hbm_fresh : ∀ j : Fin k, j.val < m →
          bm ≠ cut.cutDart j ∧ bm ≠ H.edge.f (cut.cutDart j) := by
        intro j hj
        refine ⟨fun h => cut.h_disj_edge im j h, fun h => ?_⟩
        have heqj := cut.edge_cut_inj darts h_all h
        have hv := congrArg Fin.val heqj; dsimp [im] at hv; omega
      have ham_e : (T_pref m).e.f am = bm := he_m am ham_fresh
      have hbm_e : (T_pref m).e.f bm = am := by
        rw [he_m bm hbm_fresh]; exact H.edge_involution am
      have ham_in_M : am ∈ getOrbit (T_pref m).f darts.length rf0 :=
        (hM_m am).mpr ⟨im, Nat.le_refl _, cut.h_a im⟩
      have hbm_same_Fip : SameOrbit H.face (cut.ringFace ip) bm := by
        have hb := cut.h_b im
        have hfin : (⟨(im.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ip :=
          Fin.ext (Nat.mod_eq_of_lt hm)
        rw [hfin] at hb; exact hb
      have hbm_not_le : ∀ j : Fin k, j.val ≤ m → ¬ SameOrbit H.face (cut.ringFace j) bm := by
        intro j hj hsame
        exact cut.h_diff j ip (by intro heq; have hv := congrArg Fin.val heq; dsimp [ip] at hv; omega)
          (sameOrbit_trans H.face hsame (sameOrbit_symm_of_complete H.face darts h_all hbm_same_Fip))
      have hbm_not_am : ¬ bm ∈ getOrbit (T_pref m).f darts.length am := by
        intro hmem
        have h_rf0 := mem_getOrbit_trans_complete (T_pref m).f darts h_all (Nat.le_refl _) ham_in_M hmem
        rcases (hM_m bm).mp h_rf0 with ⟨j, hj, hbj⟩
        exact hbm_not_le j hj hbj
      have hud := uncoupleEdge_diff (T_pref m) darts h_all (Nat.le_refl _) hab ham_e hbm_e hbm_not_am
      rw [← h_pref_step m (by omega)] at hud
      have hbm_orb_eq : getOrbit (T_pref m).f darts.length bm =
          getOrbit H.face darts.length bm := hU_m bm hbm_not_le
      have h_rf0_in_succ : rf0 ∈ getOrbit (T_pref (m + 1)).f darts.length bm := by
        have h_rf0_am : rf0 ∈ getOrbit (T_pref m).f darts.length am :=
          mem_getOrbit_symm_complete (T_pref m).f darts h_all (Nat.le_refl _) ham_in_M
        exact (hud.2.2.2.2.2.2.2.1 rf0).mpr (Or.inl h_rf0_am)
      refine ⟨hud.2.2.2.1.trans hC_m, hud.2.2.2.2.2.2.1.trans hg_m,
        (by rw [h_pref_step m (by omega)]; exact hn_m), ?_, ?_, ?_⟩
      · intro x
        have h_eq_bm : x ∈ getOrbit (T_pref (m + 1)).f darts.length rf0 ↔
            x ∈ getOrbit (T_pref (m + 1)).f darts.length bm := by
          constructor
          · intro hx
            exact mem_getOrbit_trans_complete (T_pref (m + 1)).f darts h_all (Nat.le_refl _)
              h_rf0_in_succ hx
          · intro hx
            exact mem_getOrbit_trans_complete (T_pref (m + 1)).f darts h_all (Nat.le_refl _)
              (mem_getOrbit_symm_complete (T_pref (m + 1)).f darts h_all (Nat.le_refl _) h_rf0_in_succ)
              hx
        rw [h_eq_bm, hud.2.2.2.2.2.2.2.1 x, hbm_orb_eq]
        constructor
        · rintro (hx | hx)
          · have h_rf0_x := mem_getOrbit_trans_complete (T_pref m).f darts h_all (Nat.le_refl _)
              ham_in_M hx
            rcases (hM_m x).mp h_rf0_x with ⟨j, hj, hxj⟩
            exact ⟨j, by omega, hxj⟩
          · have hsx := (sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) bm x).mpr hx
            exact ⟨ip, Nat.le_refl _, sameOrbit_trans H.face hbm_same_Fip hsx⟩
        · rintro ⟨j, hj, hxj⟩
          by_cases hjm : j.val ≤ m
          · left
            exact mem_getOrbit_trans_complete (T_pref m).f darts h_all (Nat.le_refl _)
              (mem_getOrbit_symm_complete (T_pref m).f darts h_all (Nat.le_refl _) ham_in_M)
              ((hM_m x).mpr ⟨j, hjm, hxj⟩)
          · right
            have hjip : j = ip := Fin.ext (by dsimp [ip]; omega)
            rw [hjip] at hxj
            have hbx : SameOrbit H.face bm x :=
              sameOrbit_trans H.face (sameOrbit_symm_of_complete H.face darts h_all hbm_same_Fip) hxj
            exact (sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) bm x).mp hbx
      · intro z hz
        have hz_le : ∀ j : Fin k, j.val ≤ m → ¬ SameOrbit H.face (cut.ringFace j) z :=
          fun j hj => hz j (by omega)
        have hza : ¬ z ∈ getOrbit (T_pref m).f darts.length am := by
          intro hmem
          have hrf := mem_getOrbit_trans_complete (T_pref m).f darts h_all (Nat.le_refl _) ham_in_M hmem
          rcases (hM_m z).mp hrf with ⟨j, hj, hzj⟩
          exact hz_le j hj hzj
        have hzb : ¬ z ∈ getOrbit (T_pref m).f darts.length bm := by
          rw [hbm_orb_eq]
          intro hmem
          have hbz := (sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) bm z).mpr hmem
          exact hz ip (Nat.le_refl _) (sameOrbit_trans H.face hbm_same_Fip hbz)
        rw [hud.2.2.2.2.2.2.2.2 z hza hzb]
        exact hU_m z hz_le
      · intro x hx
        rw [h_pref_step m (by omega)]
        have hfix := uncoupleEdge_e_fixed (T_pref m) ham_e hbm_e
        have hx_m := hx im (Nat.lt_succ_self m)
        rw [hfix.2.2 x hx_m.1 hx_m.2]
        exact he_m x (fun j hj => hx j (Nat.lt_succ_of_lt hj))
  -- Apply final uncoupling step at `m = k - 1`
  rcases hInv (k - 1) (by omega) with ⟨hC_prev, hg_prev, hn_prev, hM_prev, hU_prev, he_prev⟩
  let i_last : Fin k := ⟨k - 1, by omega⟩
  let alast := cut.cutDart i_last
  let blast := H.edge.f alast
  have hT_k_eq : T_k = uncoupleEdge (T_pref (k - 1)) alast blast := by
    dsimp [T_k, FaceCycleCut.uncoupleTriple]
    have htake : cut.cutPairs = cut.cutPairs.take ((k - 1) + 1) :=
      (List.take_of_length_le (by rw [hlen_pairs]; omega : cut.cutPairs.length ≤ (k - 1) + 1)).symm
    rw [congrArg (uncoupleList H.hypermapToTriple) htake]
    exact h_pref_step (k - 1) (by omega)
  have hab_last : alast ≠ blast := (cut.h_disj_edge i_last i_last).symm
  have hal_fresh : ∀ j : Fin k, j.val < k - 1 →
      alast ≠ cut.cutDart j ∧ alast ≠ H.edge.f (cut.cutDart j) := by
    intro j hj
    refine ⟨fun h => ?_, fun h => cut.h_disj_edge j i_last h.symm⟩
    have hv := congrArg Fin.val (cut.cut_inj darts h_all h); dsimp [i_last] at hv; omega
  have hbl_fresh : ∀ j : Fin k, j.val < k - 1 →
      blast ≠ cut.cutDart j ∧ blast ≠ H.edge.f (cut.cutDart j) := by
    intro j hj
    refine ⟨fun h => cut.h_disj_edge i_last j h, fun h => ?_⟩
    have hv := congrArg Fin.val (cut.edge_cut_inj darts h_all h); dsimp [i_last] at hv; omega
  have hal_e : (T_pref (k - 1)).e.f alast = blast := he_prev alast hal_fresh
  have hbl_e : (T_pref (k - 1)).e.f blast = alast := by
    rw [he_prev blast hbl_fresh]; exact H.edge_involution alast
  have hal_M : alast ∈ getOrbit (T_pref (k - 1)).f darts.length rf0 :=
    (hM_prev alast).mpr ⟨i_last, Nat.le_refl _, cut.h_a i_last⟩
  have hbl_F0 : SameOrbit H.face rf0 blast := by
    have hb := cut.h_b i_last
    have hfin : (⟨(i_last.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨0, by omega⟩ :=
      Fin.ext (by dsimp [i_last]; rw [show k - 1 + 1 = k by omega, Nat.mod_self])
    rw [hfin] at hb; exact hb
  have hbl_M : blast ∈ getOrbit (T_pref (k - 1)).f darts.length rf0 :=
    (hM_prev blast).mpr ⟨⟨0, by omega⟩, Nat.zero_le _, hbl_F0⟩
  have hbl_al : blast ∈ getOrbit (T_pref (k - 1)).f darts.length alast :=
    mem_getOrbit_trans_complete (T_pref (k - 1)).f darts h_all (Nat.le_refl _)
      (mem_getOrbit_symm_complete (T_pref (k - 1)).f darts h_all (Nat.le_refl _) hal_M) hbl_M
  have hsep := uncoupleEdge_sameFace_separates (T_pref (k - 1)) darts h_nd h_all (Nat.le_refl _)
    hg_prev hab_last hal_e hbl_e hbl_al
  rw [← hT_k_eq] at hsep
  -- Connect `a0` with `alast` and `b0` with `blast` inside `T_k`
  have ha_reach : ∀ i : Fin k, ReachEN T_k.e T_k.n a0 (cut.cutDart i) :=
    fun i => sameOrbit_f_imp_reachEN T_k (cut.uncoupleTriple_a_all_sameOrbit_f darts h_all i)
  have hb_reach : ∀ i : Fin k, ReachEN T_k.e T_k.n blast (H.edge.f (cut.cutDart i)) :=
    fun i => sameOrbit_f_imp_reachEN T_k (cut.uncoupleTriple_b_all_sameOrbit_f darts h_all i)
  have ha0_alast : ReachEN T_k.e T_k.n a0 alast := ha_reach i_last
  have hbl_b0 : ReachEN T_k.e T_k.n blast b0 := hb_reach ⟨0, by omega⟩
  have h_not_a0b0 : ¬ ReachEN T_k.e T_k.n a0 b0 := fun hab0 =>
    hsep.2.1 (reachEN_trans T_k.e T_k.n (reachEN_symm T_k.e T_k.n ha0_alast)
      (reachEN_trans T_k.e T_k.n hab0 (reachEN_symm T_k.e T_k.n hbl_b0)))
  have he_pairs : ∀ q ∈ cut.cutPairs, H.hypermapToTriple.e.f q.1 = q.2 := by
    intro q hq; rcases (cut.mem_cutPairs_iff q).mp hq with ⟨j, rfl⟩; rfl
  have he_ev := uncoupleList_e_eval H.hypermapToTriple H.edge_involution cut.cutPairs hpd he_pairs
  have hf_ev := uncoupleList_f_eval H.hypermapToTriple cut.cutPairs hpd
  refine ⟨uncoupleList_n H.hypermapToTriple cut.cutPairs, ?_, hsep.2.2.2.2.2.2.2.2.1,
    by rw [hsep.2.2.2.2.2.1, hC_prev], h_not_a0b0, ?_, ?_, ?_, ?_, ?_,
    cut.uncoupleTriple_outerL_orbit darts h_all,
    cut.uncoupleTriple_outerR_orbit darts h_all, ?_⟩
  · intro d
    by_cases hu_mem : ∃ q ∈ cut.cutPairs, d = q.1 ∨ d = q.2
    · rcases hu_mem with ⟨q, hq, rfl | rfl⟩
      · have hq1 := (he_ev q.1).2 q hq |>.1 rfl
        change T_k.e.f q.1 = q.1 at hq1
        change T_k.e.f (T_k.e.f q.1) = q.1
        rw [hq1, hq1]
      · have hq2 := (he_ev q.2).2 q hq |>.2 rfl
        change T_k.e.f q.2 = q.2 at hq2
        change T_k.e.f (T_k.e.f q.2) = q.2
        rw [hq2, hq2]
    · have h_not : ∀ q ∈ cut.cutPairs, d ≠ q.1 ∧ d ≠ q.2 :=
        fun q hq => ⟨fun h => hu_mem ⟨q, hq, Or.inl h⟩, fun h => hu_mem ⟨q, hq, Or.inr h⟩⟩
      have hu_eq : T_k.e.f d = H.edge.f d := (he_ev d).1 h_not
      have hfu_not : ∀ q ∈ cut.cutPairs, H.edge.f d ≠ q.1 ∧ H.edge.f d ≠ q.2 := by
        intro q hq
        rcases (cut.mem_cutPairs_iff q).mp hq with ⟨j, rfl⟩
        constructor
        · intro h; apply h_not (cut.cutDart j, H.edge.f (cut.cutDart j)) hq |>.2
          dsimp only at h ⊢; rw [← h, H.edge_involution]
        · intro h; apply h_not (cut.cutDart j, H.edge.f (cut.cutDart j)) hq |>.1
          exact perm_f_inj_jcs H.edge h
      have hfu_eq : T_k.e.f (H.edge.f d) = H.edge.f (H.edge.f d) := (he_ev (H.edge.f d)).1 hfu_not
      change T_k.e.f (T_k.e.f d) = d
      rw [hu_eq, hfu_eq, H.edge_involution]
  · intro x
    have h_all_reach : ReachEN (T_pref (k - 1)).e (T_pref (k - 1)).n alast x :=
      forall_rel_of_countRelClasses_eq_one
        (ReachEN (T_pref (k - 1)).e (T_pref (k - 1)).n)
        (reachEN_refl _ _)
        (fun {_ _} h => reachEN_symm _ _ h)
        (fun {_ _ _} h1 h2 => reachEN_trans _ _ h1 h2)
        darts hC_prev alast x (h_all alast) (h_all x)
    rcases hsep.2.2.2.2.1 x h_all_reach with halx | hblx
    · left; exact reachEN_trans T_k.e T_k.n ha0_alast halx
    · right; exact reachEN_trans T_k.e T_k.n (reachEN_symm T_k.e T_k.n hbl_b0) hblx
  · rintro x ⟨hxL, hxR⟩
    exact h_not_a0b0 (reachEN_trans T_k.e T_k.n hxL (reachEN_symm T_k.e T_k.n hxR))
  · intro i
    exact ⟨ha_reach i, reachEN_trans T_k.e T_k.n (reachEN_symm T_k.e T_k.n hbl_b0) (hb_reach i)⟩
  · intro i
    have hmem : (cut.cutDart i, H.edge.f (cut.cutDart i)) ∈ cut.cutPairs :=
      (cut.mem_cutPairs_iff _).mpr ⟨i, rfl⟩
    exact ⟨(he_ev (cut.cutDart i)).2 _ hmem |>.1 rfl,
      (he_ev (H.edge.f (cut.cutDart i))).2 _ hmem |>.2 rfl⟩
  · intro x hx
    have h_not : ∀ q ∈ cut.cutPairs, x ≠ q.1 ∧ x ≠ q.2 := by
      intro q hq; rcases (cut.mem_cutPairs_iff q).mp hq with ⟨j, rfl⟩; exact hx j
    exact ⟨(he_ev x).1 h_not, (hf_ev x).1 h_not⟩
  · intro z hz
    have hz_le : ∀ j : Fin k, j.val ≤ k - 1 → ¬ SameOrbit H.face (cut.ringFace j) z :=
      fun j _ => hz j
    have hz_not_al : ¬ z ∈ getOrbit (T_pref (k - 1)).f darts.length alast := by
      intro hmem
      have hrf := mem_getOrbit_trans_complete (T_pref (k - 1)).f darts h_all (Nat.le_refl _) hal_M hmem
      rcases (hM_prev z).mp hrf with ⟨j, _, hzj⟩
      exact hz j hzj
    rw [hsep.2.2.2.2.2.2.2.2.2 z hz_not_al, hU_prev z hz_le]

end FaceCycleSeparation

section ParityAndColorGluing

open Math.Hypermap

/-- In a bridgeless hypermap on a complete dart list, `H.edge` has no fixed points. -/
theorem edge_no_fix_of_isBridgeless (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts darts.length) :
    ∀ d : H.Dart, H.edge.f d ≠ d := by
  intro d hfix
  have hbr := h_bridgeless d (h_all d)
  dsimp [Math.Hypermap.isBridge, Math.Hypermap.sameFace] at hbr
  rw [hfix, List.contains_iff_mem.mpr (mem_getOrbit_self H.face darts.length d)] at hbr
  cases hbr

/-- Any `Nodup` list closed under `H.node`-orbits in a hypermap where every node has degree 3
    has length divisible by 3. -/
theorem three_dvd_of_uniform_nodeDegree_three (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_deg3 : ∀ d : H.Dart, Math.Hypermap.nodeDegree H d darts.length = 3)
    (L : List H.Dart) (h_nd : L.Nodup)
    (h_sub : ∀ d ∈ L, ∀ x ∈ getOrbit H.node darts.length d, x ∈ L) :
    3 ∣ L.length := by
  have h_closes : ∀ d ∈ L, orbitClosesWithin H.node d d darts.length :=
    fun d _ => orbitClosesWithin_of_complete H.node darts h_all d
  have h_unif : ∀ d ∈ L, (getOrbit H.node darts.length d).length = 3 := by
    intro d _
    have h3 := h_deg3 d
    dsimp [Math.Hypermap.nodeDegree] at h3
    exact h3
  have hlen := length_eq_mul_countOrbits_of_uniform H.node darts.length 3 L
    h_nd h_closes h_sub h_unif
  exact ⟨countOrbits H.node darts.length L, hlen⟩

private theorem perm_iter_ne_of_invol {D : Type} (p : Perm D)
    (h_invol : ∀ x : D, p.f (p.f x) = x) {d : D} (_hne : p.f d ≠ d) :
    ∀ r : Nat, Perm.iter p r d = d ∨ Perm.iter p r d = p.f d := by
  intro r
  induction r with
  | zero => left; rfl
  | succ r ih =>
    rw [Perm.iter_succ]
    rcases ih with h | h
    · right; rw [h]
    · left; rw [h, h_invol d]

private theorem reachEN_f_step {D : Type} (T : PermTriple D) (d : D) :
    ReachEN T.e T.n d (T.f.f d) := by
  rw [T.f_eq_n_inv_e_inv]
  exact ⟨WalkEN.step (StepEN.e_bwd d) (WalkEN.step (StepEN.n_bwd (T.e.inv d)) (WalkEN.refl _))⟩

private theorem side_divisibility_aux (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_deg3 : ∀ d : H.Dart, Math.Hypermap.nodeDegree H d darts.length = 3)
    (T : PermTriple H.Dart) (h_Tn : T.n = H.node)
    (h_Te_invol : ∀ d : H.Dart, T.e.f (T.e.f d) = d)
    (P : H.Dart → Prop) [DecidablePred P]
    (h_Pe : ∀ d : H.Dart, P d ↔ P (T.e.f d))
    (h_Pn : ∀ d : H.Dart, P d ↔ P (T.n.f d))
    {k : Nat} (hk : 1 ≤ k) (bdy : Fin k → H.Dart)
    (h_bdy_inj : ∀ {i j : Fin k}, bdy i = bdy j → i = j)
    (h_bdy_mem : ∀ i : Fin k, P (bdy i))
    (h_fix_iff : ∀ d : H.Dart, P d → (T.e.f d = d ↔ ∃ i : Fin k, d = bdy i)) :
    let dartsP := darts.filter (fun d => decide (P d))
    3 ∣ dartsP.length ∧ k ≤ dartsP.length ∧
      (∃ m : Nat, dartsP.length = 2 * m + k) ∧ 2 ∣ dartsP.length + k := by
  intro dartsP
  have hP_nd : dartsP.Nodup := h_nd.filter _
  have hP_mem_iff : ∀ d : H.Dart, d ∈ dartsP ↔ P d := by
    intro d
    simp [dartsP, h_all d]
  have hP_node_closed : ∀ d ∈ dartsP, ∀ x ∈ getOrbit H.node darts.length d, x ∈ dartsP := by
    intro d hd x hx
    have hPd : P d := (hP_mem_iff d).mp hd
    rcases mem_getOrbit_imp_exists_iter H.node darts.length d x hx with ⟨r, _, rfl⟩
    apply (hP_mem_iff _).mpr
    rw [← h_Tn]
    have hstep : ∀ s : Nat, P (Perm.iter T.n s d) := by
      intro s
      induction s with
      | zero => exact hPd
      | succ s ih => rw [Perm.iter_succ]; exact (h_Pn _).mp ih
    exact hstep r
  have h3 : 3 ∣ dartsP.length :=
    three_dvd_of_uniform_nodeDegree_three H darts h_all h_deg3 dartsP hP_nd hP_node_closed
  let bdyList : List H.Dart := (List.finRange k).map bdy
  have hbdy_nd : bdyList.Nodup := by
    dsimp [bdyList]
    refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij heq => ?_)
    simp only [List.getElem_map, List.getElem_finRange] at heq
    have hfin := h_bdy_inj heq
    have hv := congrArg Fin.val hfin
    simp only [Fin.val_cast] at hv
    omega
  have hbdy_sub : ∀ x ∈ bdyList, x ∈ dartsP := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, _, rfl⟩
    exact (hP_mem_iff _).mpr (h_bdy_mem i)
  have h_le : k ≤ dartsP.length := by
    have hsub := nodup_length_le_of_subset bdyList dartsP hbdy_nd hbdy_sub
    simpa [bdyList] using hsub
  let isFix : H.Dart → Bool := fun d => decide (T.e.f d = d)
  have hsplit := length_eq_filter_add_filter_not isFix dartsP
  let dartsFix := dartsP.filter isFix
  let dartsFree := dartsP.filter (fun d => !isFix d)
  have hfix_iff_bdy : ∀ d : H.Dart, d ∈ dartsFix ↔ d ∈ bdyList := by
    intro d
    constructor
    · intro hd
      rcases List.mem_filter.mp hd with ⟨hdP, hdf⟩
      have hPd : P d := (hP_mem_iff d).mp hdP
      have hTeq : T.e.f d = d := of_decide_eq_true hdf
      rcases (h_fix_iff d hPd).mp hTeq with ⟨i, rfl⟩
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    · intro hd
      rcases List.mem_map.mp hd with ⟨i, _, rfl⟩
      apply List.mem_filter.mpr
      refine ⟨(hP_mem_iff _).mpr (h_bdy_mem i), decide_eq_true ?_⟩
      exact (h_fix_iff (bdy i) (h_bdy_mem i)).mpr ⟨i, rfl⟩
  have hfix_len : dartsFix.length = k := by
    have h1 := nodup_length_eq_of_iff_mem (hP_nd.filter isFix) hbdy_nd hfix_iff_bdy
    simpa [bdyList] using h1
  have h_pos_darts : 1 ≤ darts.length := by
    have h0 : bdy ⟨0, hk⟩ ∈ darts := h_all _
    exact List.length_pos_of_mem h0
  have hfree_closes : ∀ d ∈ dartsFree, orbitClosesWithin T.e d d darts.length :=
    fun d _ => orbitClosesWithin_of_complete T.e darts h_all d
  have hfree_sub : ∀ d ∈ dartsFree, ∀ x ∈ getOrbit T.e darts.length d, x ∈ dartsFree := by
    intro d hd x hx
    rcases List.mem_filter.mp hd with ⟨hdP, hdFree⟩
    have hPd : P d := (hP_mem_iff d).mp hdP
    have hd_ne : T.e.f d ≠ d := by
      intro h
      rw [show isFix d = true from decide_eq_true h] at hdFree
      cases hdFree
    rcases mem_getOrbit_imp_exists_iter T.e darts.length d x hx with ⟨r, _, rfl⟩
    apply List.mem_filter.mpr
    rcases perm_iter_ne_of_invol T.e h_Te_invol hd_ne r with h | h
    · rw [h]; exact ⟨hdP, hdFree⟩
    · rw [h]
      refine ⟨(hP_mem_iff _).mpr ((h_Pe d).mp hPd), ?_⟩
      have hf_false : isFix (T.e.f d) = false := by
        dsimp [isFix]
        exact decide_eq_false (fun heq => by rw [h_Te_invol d] at heq; exact hd_ne heq.symm)
      simp [hf_false]
  have hfree_unif : ∀ d ∈ dartsFree, (getOrbit T.e darts.length d).length = 2 := by
    intro d hd
    have hdFree := (List.mem_filter.mp hd).2
    have hd_ne : T.e.f d ≠ d := by
      intro h
      rw [show isFix d = true from decide_eq_true h] at hdFree
      cases hdFree
    exact getOrbit_involution_length_two T.e h_Te_invol d hd_ne h_pos_darts
  have hfree_len := length_eq_mul_countOrbits_of_uniform T.e darts.length 2 dartsFree
    (hP_nd.filter _) hfree_closes hfree_sub hfree_unif
  have h_eq : dartsP.length = 2 * countOrbits T.e darts.length dartsFree + k := by
    have hs : dartsP.length = dartsFix.length + dartsFree.length := hsplit
    rw [hfix_len, hfree_len] at hs
    omega
  refine ⟨h3, h_le, ⟨countOrbits T.e darts.length dartsFree, h_eq⟩, ?_⟩
  refine ⟨countOrbits T.e darts.length dartsFree + k, ?_⟩
  omega

/-- **Divisibility & Parity Along a Separating `k`-Cycle**:
    In a connected planar cubic bridgeless hypermap `H`, separating along a `FaceCycleCut` of
    length `k ≥ 2` yields two sides `D_L`, `D_R` satisfying `3 ∣ |D_*|`, `k ≤ |D_*|`,
    `|D_*| = 2 * m_* + k`, and `2 ∣ |D_*| + k`. -/
theorem side_parity_divisibility (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts darts.length)
    (h_deg3 : ∀ d : H.Dart, Math.Hypermap.nodeDegree H d darts.length = 3)
    {k : Nat} (cut : H.FaceCycleCut k) :
    let T_k := cut.uncoupleTriple
    let a0 := cut.cutDart ⟨0, by have := cut.hk; omega⟩
    let b0 := H.edge.f a0
    let DL := fun x => ReachEN T_k.e T_k.n a0 x
    let DR := fun x => ReachEN T_k.e T_k.n b0 x
    let dartsL := darts.filter (fun x => decide (DL x))
    let dartsR := darts.filter (fun x => decide (DR x))
    (3 ∣ dartsL.length ∧ k ≤ dartsL.length ∧
      (∃ mL : Nat, dartsL.length = 2 * mL + k) ∧ 2 ∣ dartsL.length + k) ∧
    (3 ∣ dartsR.length ∧ k ≤ dartsR.length ∧
      (∃ mR : Nat, dartsR.length = 2 * mR + k) ∧ 2 ∣ dartsR.length + k) := by
  intro T_k a0 b0 DL DR
  have hk := cut.hk
  have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hTn : T_k.n = H.node := hsep.1
  have hTe_invol : ∀ d : H.Dart, T_k.e.f (T_k.e.f d) = d := hsep.2.1
  have h_disj : ∀ x : H.Dart, ¬ (DL x ∧ DR x) := hsep.2.2.2.2.2.2.1
  have h_bdy := hsep.2.2.2.2.2.2.2.1
  have h_fix_bdy := hsep.2.2.2.2.2.2.2.2.1
  have h_away := hsep.2.2.2.2.2.2.2.2.2.1
  have h_no_fix := edge_no_fix_of_isBridgeless H darts h_all h_bridgeless
  have hDL_e : ∀ d : H.Dart, DL d ↔ DL (T_k.e.f d) := by
    intro d
    constructor
    · intro hd
      exact reachEN_trans T_k.e T_k.n hd ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩
    · intro hd
      have h1 : ReachEN T_k.e T_k.n d (T_k.e.f d) :=
        ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩
      exact reachEN_trans T_k.e T_k.n hd (reachEN_symm T_k.e T_k.n h1)
  have hDL_n : ∀ d : H.Dart, DL d ↔ DL (T_k.n.f d) := by
    intro d
    constructor
    · intro hd
      exact reachEN_trans T_k.e T_k.n hd ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩
    · intro hd
      have h1 : ReachEN T_k.e T_k.n d (T_k.n.f d) :=
        ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩
      exact reachEN_trans T_k.e T_k.n hd (reachEN_symm T_k.e T_k.n h1)
  have hDR_e : ∀ d : H.Dart, DR d ↔ DR (T_k.e.f d) := by
    intro d
    constructor
    · intro hd
      exact reachEN_trans T_k.e T_k.n hd ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩
    · intro hd
      have h1 : ReachEN T_k.e T_k.n d (T_k.e.f d) :=
        ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩
      exact reachEN_trans T_k.e T_k.n hd (reachEN_symm T_k.e T_k.n h1)
  have hDR_n : ∀ d : H.Dart, DR d ↔ DR (T_k.n.f d) := by
    intro d
    constructor
    · intro hd
      exact reachEN_trans T_k.e T_k.n hd ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩
    · intro hd
      have h1 : ReachEN T_k.e T_k.n d (T_k.n.f d) :=
        ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩
      exact reachEN_trans T_k.e T_k.n hd (reachEN_symm T_k.e T_k.n h1)
  have hL : _ := side_divisibility_aux H darts h_nd h_all h_deg3 T_k hTn hTe_invol DL hDL_e hDL_n
    (by omega) cut.cutDart (fun hij => cut.cut_inj darts h_all hij)
    (fun i => (h_bdy i).1)
    (fun d hd => by
      constructor
      · intro hTeq
        by_cases hcut : ∃ i : Fin k, d = cut.cutDart i
        · exact hcut
        · have hedge : ∀ i : Fin k, d ≠ H.edge.f (cut.cutDart i) := by
            intro i heq
            exact h_disj d ⟨hd, heq ▸ (h_bdy i).2⟩
          have hnot : ∀ i : Fin k, d ≠ cut.cutDart i ∧ d ≠ H.edge.f (cut.cutDart i) :=
            fun i => ⟨fun h => hcut ⟨i, h⟩, hedge i⟩
          have heqH := (h_away d hnot).1
          rw [heqH] at hTeq
          exact False.elim (h_no_fix d hTeq)
      · rintro ⟨i, rfl⟩
        exact (h_fix_bdy i).1)
  have hR : _ := side_divisibility_aux H darts h_nd h_all h_deg3 T_k hTn hTe_invol DR hDR_e hDR_n
    (by omega) (fun i => H.edge.f (cut.cutDart i)) (fun hij => cut.edge_cut_inj darts h_all hij)
    (fun i => (h_bdy i).2)
    (fun d hd => by
      constructor
      · intro hTeq
        by_cases hedge : ∃ i : Fin k, d = H.edge.f (cut.cutDart i)
        · exact hedge
        · have hcut : ∀ i : Fin k, d ≠ cut.cutDart i := by
            intro i heq
            exact h_disj d ⟨heq ▸ (h_bdy i).1, hd⟩
          have hnot : ∀ i : Fin k, d ≠ cut.cutDart i ∧ d ≠ H.edge.f (cut.cutDart i) :=
            fun i => ⟨hcut i, fun h => hedge ⟨i, h⟩⟩
          have heqH := (h_away d hnot).1
          rw [heqH] at hTeq
          exact False.elim (h_no_fix d hTeq)
      · rintro ⟨i, rfl⟩
        exact (h_fix_bdy i).2)
  exact ⟨hL, hR⟩

/-- Any two `Fin k → Color` boundary tuples with the same equality pattern (`f i = f j ↔ g i = g j`)
    are related by a color permutation `π : Perm Color`. -/
theorem exists_color_bij_of_eq_iff (k : Nat) (f g : Fin k → Color)
    (h_eq_iff : ∀ i j : Fin k, f i = f j ↔ g i = g j) :
    ∃ π : Perm Color, ∀ i : Fin k, π.f (g i) = f i := by
  have h_aux : ∀ n : Nat, n ≤ k → ∃ p : Perm Color, ∀ i : Fin k, i.val < n → p.f (g i) = f i := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨permId, fun _ hi => by omega⟩
    | succ n ih =>
      intro hn
      rcases ih (Nat.le_of_lt hn) with ⟨p, hp⟩
      let i0 : Fin k := ⟨n, hn⟩
      refine ⟨swapCompLeft p (p.f (g i0)) (f i0), ?_⟩
      intro j hj
      by_cases hjn : j.val = n
      · have hji0 : j = i0 := Fin.ext hjn
        rw [hji0]
        dsimp [swapCompLeft]
        exact swapFun_left (p.f (g i0)) (f i0)
      · have hjlt : j.val < n := by omega
        have hpj : p.f (g j) = f j := hp j hjlt
        dsimp [swapCompLeft]
        rw [hpj]
        by_cases hfj : f j = f i0
        · have hgj : g j = g i0 := (h_eq_iff j i0).mp hfj
          rw [← hgj, hpj, hfj]
          exact swapFun_right (f i0) (f i0)
        · have hne_g : g j ≠ g i0 := fun h => hfj ((h_eq_iff j i0).mpr h)
          have hne_p : f j ≠ p.f (g i0) := by
            intro heq
            rw [← hpj] at heq
            exact hne_g (perm_f_inj_jcs p heq)
          exact swapFun_of_ne hne_p hfj
  rcases h_aux k (Nat.le_refl k) with ⟨π, hπ⟩
  exact ⟨π, fun i => hπ i i.isLt⟩

theorem FaceCycleCut.inArcL_imp_DL {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (i : Fin k) (x : H.Dart)
    (hx : cut.inArcL darts h_all i x) :
    ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
      (cut.cutDart ⟨0, by have := cut.hk; omega⟩) x := by
  have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have horb := (hsep.2.2.2.2.2.2.2.2.2.2.1 x).mpr ⟨i, hx⟩
  rcases mem_getOrbit_imp_exists_iter cut.uncoupleTriple.f darts.length
      (cut.cutDart ⟨0, by have := cut.hk; omega⟩) x horb with ⟨r, _, rfl⟩
  have hstep : ∀ s : Nat, ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
      (cut.cutDart ⟨0, by have := cut.hk; omega⟩)
      (Perm.iter cut.uncoupleTriple.f s (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) := by
    intro s
    induction s with
    | zero => exact reachEN_refl _ _ _
    | succ s ih =>
      rw [Perm.iter_succ]
      exact reachEN_trans _ _ ih (reachEN_f_step cut.uncoupleTriple _)
  exact hstep r

theorem FaceCycleCut.inArcR_imp_DR {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (i : Fin k) (x : H.Dart)
    (hx : cut.inArcR darts h_all i x) :
    ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
      (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) x := by
  have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hb_last : ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
      (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩))
      (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩)) :=
    (hsep.2.2.2.2.2.2.2.1 ⟨k - 1, by have := cut.hk; omega⟩).2
  have horb := (hsep.2.2.2.2.2.2.2.2.2.2.2.1 x).mpr ⟨i, hx⟩
  rcases mem_getOrbit_imp_exists_iter cut.uncoupleTriple.f darts.length
      (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩)) x horb with ⟨r, _, rfl⟩
  refine reachEN_trans _ _ hb_last ?_
  have hstep : ∀ s : Nat, ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
      (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩))
      (Perm.iter cut.uncoupleTriple.f s
        (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩))) := by
    intro s
    induction s with
    | zero => exact reachEN_refl _ _ _
    | succ s ih =>
      rw [Perm.iter_succ]
      exact reachEN_trans _ _ ih (reachEN_f_step cut.uncoupleTriple _)
  exact hstep r

/-- **Cycle Color-Gluing Theorem**:
    Given partial colorings `cL` on `D_L` and `cR` on `D_R` that are constant on each arc `inArcL i`
    (with value `f i`) and `inArcR i` (with value `g i`), satisfy `f i ≠ f (i+1)`, and share the
    same equality equivalence relation `f i = f j ↔ g i = g j`, permuting `cR` by `exists_color_bij_of_eq_iff`
    and splicing along `D_L ⊔ D_R` yields a valid `H.FaceColoring`. -/
theorem glueCycleFaceColoring (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k)
    (cL cR : H.Dart → Color) (f g : Fin k → Color)
    (hL_arc : ∀ i : Fin k, ∀ d : H.Dart, cut.inArcL darts h_all i d → cL d = f i)
    (hL_face : ∀ d : H.Dart,
      ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (cut.cutDart ⟨0, by have := cut.hk; omega⟩) d →
      (∀ i : Fin k, ¬ SameOrbit H.face (cut.ringFace i) d) → cL (H.face.f d) = cL d)
    (hL_edge : ∀ d : H.Dart,
      ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (cut.cutDart ⟨0, by have := cut.hk; omega⟩) d →
      ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (cut.cutDart ⟨0, by have := cut.hk; omega⟩) (H.edge.f d) →
      cL (H.edge.f d) ≠ cL d)
    (hR_arc : ∀ i : Fin k, ∀ d : H.Dart, cut.inArcR darts h_all i d → cR d = g i)
    (hR_face : ∀ d : H.Dart,
      ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) d →
      (∀ i : Fin k, ¬ SameOrbit H.face (cut.ringFace i) d) → cR (H.face.f d) = cR d)
    (hR_edge : ∀ d : H.Dart,
      ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) d →
      ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) (H.edge.f d) →
      cR (H.edge.f d) ≠ cR d)
    (hf_adj : ∀ i : Fin k, f ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ ≠ f i)
    (h_eq_iff : ∀ i j : Fin k, f i = f j ↔ g i = g j) :
    Nonempty H.FaceColoring := by
  classical
  rcases exists_color_bij_of_eq_iff k f g h_eq_iff with ⟨π, hπ⟩
  have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  let T_k := cut.uncoupleTriple
  let a0 := cut.cutDart ⟨0, by have := cut.hk; omega⟩
  let b0 := H.edge.f a0
  let DL : H.Dart → Prop := fun x => ReachEN T_k.e T_k.n a0 x
  let DR : H.Dart → Prop := fun x => ReachEN T_k.e T_k.n b0 x
  have h_part : ∀ x : H.Dart, DL x ∨ DR x := hsep.2.2.2.2.2.1
  have h_disj : ∀ x : H.Dart, ¬ (DL x ∧ DR x) := hsep.2.2.2.2.2.2.1
  have h_bdy := hsep.2.2.2.2.2.2.2.1
  have h_away := hsep.2.2.2.2.2.2.2.2.2.1
  let col : H.Dart → Color := fun d => if decide (DL d) then cL d else π.f (cR d)
  have hcol_ring : ∀ i : Fin k, ∀ d : H.Dart,
      SameOrbit H.face (cut.ringFace i) d → col d = f i := by
    intro i d hsame
    rcases (cut.face_partition_arcs darts h_all i d).1.mp hsame with hL | hR
    · have hdL : DL d := cut.inArcL_imp_DL darts h_nd h_all h_planar h_conn i d hL
      change (if decide (DL d) = true then cL d else π.f (cR d)) = f i
      rw [if_pos (decide_eq_true hdL), hL_arc i d hL]
    · have hdR : DR d := cut.inArcR_imp_DR darts h_nd h_all h_planar h_conn i d hR
      have hd_notL : ¬ DL d := fun h => h_disj d ⟨h, hdR⟩
      change (if decide (DL d) = true then cL d else π.f (cR d)) = f i
      rw [if_neg (fun hm => hd_notL (of_decide_eq_true hm)), hR_arc i d hR, hπ i]
  have h_face_inv : ∀ d : H.Dart, col (H.face.f d) = col d := by
    intro d
    by_cases hring : ∃ i : Fin k, SameOrbit H.face (cut.ringFace i) d
    · rcases hring with ⟨i, hi⟩
      have hi' : SameOrbit H.face (cut.ringFace i) (H.face.f d) :=
        sameOrbit_trans H.face hi (sameOrbit_step H.face rfl)
      rw [hcol_ring i (H.face.f d) hi', hcol_ring i d hi]
    · have h_nonring : ∀ i : Fin k, ¬ SameOrbit H.face (cut.ringFace i) d :=
        fun i h => hring ⟨i, h⟩
      have h_not_cut : ∀ i : Fin k, d ≠ cut.cutDart i ∧ d ≠ H.edge.f (cut.cutDart i) := by
        intro i
        refine ⟨fun heq => h_nonring i ?_, fun heq => h_nonring ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ ?_⟩
        · rw [heq]; exact cut.h_a i
        · rw [heq]; exact cut.h_b i
      have hf_eq : T_k.f.f d = H.face.f d := (h_away d h_not_cut).2
      have hreach_fd : ReachEN T_k.e T_k.n d (H.face.f d) := by
        rw [← hf_eq]; exact reachEN_f_step T_k d
      rcases h_part d with hdL | hdR
      · have hfdL : DL (H.face.f d) := reachEN_trans T_k.e T_k.n hdL hreach_fd
        change (if decide (DL (H.face.f d)) = true then cL (H.face.f d) else π.f (cR (H.face.f d))) =
               (if decide (DL d) = true then cL d else π.f (cR d))
        rw [if_pos (decide_eq_true hfdL), if_pos (decide_eq_true hdL)]
        exact hL_face d hdL h_nonring
      · have hfdR : DR (H.face.f d) := reachEN_trans T_k.e T_k.n hdR hreach_fd
        have hd_notL : ¬ DL d := fun h => h_disj d ⟨h, hdR⟩
        have hfd_notL : ¬ DL (H.face.f d) := fun h => h_disj (H.face.f d) ⟨h, hfdR⟩
        change (if decide (DL (H.face.f d)) = true then cL (H.face.f d) else π.f (cR (H.face.f d))) =
               (if decide (DL d) = true then cL d else π.f (cR d))
        rw [if_neg (fun hm => hfd_notL (of_decide_eq_true hm)),
          if_neg (fun hm => hd_notL (of_decide_eq_true hm)),
          hR_face d hdR h_nonring]
  have h_edge_prop : ∀ d : H.Dart, col (H.edge.f d) ≠ col d := by
    intro d
    rcases h_part d with hdL | hdR <;> rcases h_part (H.edge.f d) with hedL | hedR
    · change (if decide (DL (H.edge.f d)) = true then cL (H.edge.f d) else π.f (cR (H.edge.f d))) ≠
             (if decide (DL d) = true then cL d else π.f (cR d))
      rw [if_pos (decide_eq_true hedL), if_pos (decide_eq_true hdL)]
      exact hL_edge d hdL hedL
    · have hcut : ∃ i : Fin k, d = cut.cutDart i := by
        by_cases hcut : ∃ i : Fin k, d = cut.cutDart i
        · exact hcut
        · exfalso
          have h_away_d : ∀ i : Fin k, d ≠ cut.cutDart i ∧ d ≠ H.edge.f (cut.cutDart i) := by
            intro i
            refine ⟨fun h => hcut ⟨i, h⟩, fun h => h_disj d ⟨hdL, h ▸ (h_bdy i).2⟩⟩
          have heq_e : T_k.e.f d = H.edge.f d := (h_away d h_away_d).1
          have hedL' : DL (H.edge.f d) := by
            rw [← heq_e]
            exact reachEN_trans T_k.e T_k.n hdL ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩
          exact h_disj (H.edge.f d) ⟨hedL', hedR⟩
      rcases hcut with ⟨i, rfl⟩
      rw [hcol_ring i (cut.cutDart i) (cut.h_a i),
        hcol_ring ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
          (H.edge.f (cut.cutDart i)) (cut.h_b i)]
      exact hf_adj i
    · have hcut : ∃ i : Fin k, H.edge.f d = cut.cutDart i := by
        by_cases hcut : ∃ i : Fin k, H.edge.f d = cut.cutDart i
        · exact hcut
        · exfalso
          have h_away_ed : ∀ i : Fin k, H.edge.f d ≠ cut.cutDart i ∧ H.edge.f d ≠ H.edge.f (cut.cutDart i) := by
            intro i
            refine ⟨fun h => hcut ⟨i, h⟩, fun h => h_disj (H.edge.f d) ⟨hedL, h ▸ (h_bdy i).2⟩⟩
          have heq_e : T_k.e.f (H.edge.f d) = H.edge.f (H.edge.f d) := (h_away (H.edge.f d) h_away_ed).1
          rw [H.edge_involution] at heq_e
          have hdL' : DL d := by
            rw [← heq_e]
            exact reachEN_trans T_k.e T_k.n hedL ⟨WalkEN.step (StepEN.e_fwd (H.edge.f d)) (WalkEN.refl _)⟩
          exact h_disj d ⟨hdL', hdR⟩
      rcases hcut with ⟨i, hi_eq⟩
      have hd_eq : d = H.edge.f (cut.cutDart i) := by
        rw [← H.edge_involution d, hi_eq]
      rw [hi_eq, hd_eq, hcol_ring i (cut.cutDart i) (cut.h_a i),
        hcol_ring ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
          (H.edge.f (cut.cutDart i)) (cut.h_b i)]
      exact (hf_adj i).symm
    · have hd_notL : ¬ DL d := fun h => h_disj d ⟨h, hdR⟩
      have hed_notL : ¬ DL (H.edge.f d) := fun h => h_disj (H.edge.f d) ⟨h, hedR⟩
      change (if decide (DL (H.edge.f d)) = true then cL (H.edge.f d) else π.f (cR (H.edge.f d))) ≠
             (if decide (DL d) = true then cL d else π.f (cR d))
      rw [if_neg (fun hm => hed_notL (of_decide_eq_true hm)),
        if_neg (fun hm => hd_notL (of_decide_eq_true hm))]
      intro heq
      exact hR_edge d hdR hedR (perm_f_inj_jcs π heq)
  exact ⟨⟨col, h_face_inv, h_edge_prop⟩⟩

end ParityAndColorGluing

section CapSingleVertex

/-! ### Sum of Permutation Triples and Single-Vertex Cycle Capping

Given a connected planar cubic bridgeless hypermap `H` and a `FaceCycleCut` `cut` of length `k ≥ 2`,
we take the disjoint union of the `L`-side restricted triple `T_L` on `{ d : H.Dart // DL d }` and
the single degree-`k` vertex `singleCycleTriple k hk` on `Fin k`, couple `(cutDart 0, 0)` via
`coupleEdge_diff` (merging the two components and splicing both boundary face orbits into one cycle
of length `La + k`), and then couple `(cutDart (k-1), k-1), …, (cutDart 1, 1)` in nested rainbow
order via `coupleNestedPairs_spec` to obtain the planar, connected, bridgeless capped hypermap
`cut.capSingleVertexHypermap` on `{ d // DL d } ⊕ Fin k`.
-/

/-- Disjoint sum of two permutations on `α ⊕ β`. -/
def sumPerm {α β : Type} (p1 : Perm α) (p2 : Perm β) : Perm (α ⊕ β) where
  f := Sum.map p1.f p2.f
  inv := Sum.map p1.inv p2.inv
  left_inv x := by cases x <;> simp [p1.left_inv, p2.left_inv]
  right_inv x := by cases x <;> simp [p1.right_inv, p2.right_inv]

theorem sumPerm_iter_inl {α β : Type} (p1 : Perm α) (p2 : Perm β) (m : Nat) (x : α) :
    Perm.iter (sumPerm p1 p2) m (Sum.inl x) = Sum.inl (Perm.iter p1 m x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Perm.iter_succ, ih]; rfl

theorem sumPerm_iter_inr {α β : Type} (p1 : Perm α) (p2 : Perm β) (m : Nat) (y : β) :
    Perm.iter (sumPerm p1 p2) m (Sum.inr y) = Sum.inr (Perm.iter p2 m y) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Perm.iter_succ, ih]; rfl

private theorem beq_eq_of_iff {D : Type} {b1 b2 : BEq D}
    (hb : ∀ x y : D, b1.beq x y = true ↔ b2.beq x y = true) : b1 = b2 := by
  cases b1; cases b2
  congr 1; funext x; funext y
  exact Bool.eq_iff_iff.mpr (hb x y)

private theorem getOrbitAux_beq_congr {D : Type} {b1 b2 : BEq D}
    (hb : ∀ x y : D, b1.beq x y = true ↔ b2.beq x y = true)
    (p : Perm D) (start current : D) (acc : List D) (fuel : Nat) :
    @getOrbitAux D b1 p start current acc fuel =
      @getOrbitAux D b2 p start current acc fuel := by
  induction fuel generalizing current acc with
  | zero => rfl
  | succ f ih =>
    dsimp [getOrbitAux]
    have hbeq : b1.beq (p.f current) start = b2.beq (p.f current) start :=
      Bool.eq_iff_iff.mpr (hb _ _)
    rw [hbeq]
    cases b2.beq (p.f current) start
    · exact ih (p.f current) (current :: acc)
    · rfl

theorem getOrbit_beq_congr {D : Type} {b1 b2 : BEq D}
    (hb : ∀ x y : D, b1.beq x y = true ↔ b2.beq x y = true)
    (p : Perm D) (fuel : Nat) (x : D) :
    @getOrbit D b1 p fuel x = @getOrbit D b2 p fuel x :=
  getOrbitAux_beq_congr hb p x x [] fuel

private theorem deceq_beq_iff_eq {D : Type} [DecidableEq D] (x y : D) :
    (@instBEqOfDecidableEq D _).beq x y = true ↔ x = y := by
  change decide (x = y) = true ↔ x = y
  exact ⟨of_decide_eq_true, decide_eq_true⟩

private theorem sum_instBEq_iff_eq {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (u v : α ⊕ β) :
    ((@Sum.instBEq α β _ _).beq u v = true ↔ u = v) := by
  cases u with
  | inl a =>
    cases v with
    | inl a' =>
      change (a == a') = true ↔ Sum.inl a = Sum.inl a'
      rw [beq_iff_eq]
      exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
    | inr b' =>
      change false = true ↔ Sum.inl a = Sum.inr b'
      exact Iff.intro (fun h => by cases h) (fun h => by cases h)
  | inr b =>
    cases v with
    | inl a' =>
      change false = true ↔ Sum.inr b = Sum.inl a'
      exact Iff.intro (fun h => by cases h) (fun h => by cases h)
    | inr b' =>
      change (b == b') = true ↔ Sum.inr b = Sum.inr b'
      rw [beq_iff_eq]
      exact ⟨congrArg Sum.inr, Sum.inr.inj⟩

private theorem getOrbitAux_sumPerm_inl_gen {α β : Type}
    {bSum : BEq (α ⊕ β)} (hbSum : ∀ u v : α ⊕ β, bSum.beq u v = true ↔ u = v)
    {b1 : BEq α} (hb1 : ∀ x y : α, b1.beq x y = true ↔ x = y)
    (p1 : Perm α) (p2 : Perm β) (start current : α) (acc : List α) (fuel : Nat) :
    @getOrbitAux (α ⊕ β) bSum (sumPerm p1 p2) (Sum.inl start) (Sum.inl current) (acc.map Sum.inl) fuel =
      (@getOrbitAux α b1 p1 start current acc fuel).map Sum.inl := by
  induction fuel generalizing current acc with
  | zero => rfl
  | succ f ih =>
    have hsf : (sumPerm p1 p2).f (Sum.inl current) = Sum.inl (p1.f current) := rfl
    have hbeq : (@BEq.beq (α ⊕ β) bSum (Sum.inl (p1.f current)) (Sum.inl start)) =
        (@BEq.beq α b1 (p1.f current) start) := by
      apply Bool.eq_iff_iff.mpr
      rw [hbSum, hb1]
      exact ⟨fun h => Sum.inl.inj h, fun h => congrArg Sum.inl h⟩
    rw [getOrbitAux, getOrbitAux, hsf, hbeq]
    cases @BEq.beq α b1 (p1.f current) start
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← List.map_cons]
      exact ih (p1.f current) (current :: acc)
    · simp

private theorem getOrbitAux_sumPerm_inr_gen {α β : Type}
    {bSum : BEq (α ⊕ β)} (hbSum : ∀ u v : α ⊕ β, bSum.beq u v = true ↔ u = v)
    {b2 : BEq β} (hb2 : ∀ x y : β, b2.beq x y = true ↔ x = y)
    (p1 : Perm α) (p2 : Perm β) (start current : β) (acc : List β) (fuel : Nat) :
    @getOrbitAux (α ⊕ β) bSum (sumPerm p1 p2) (Sum.inr start) (Sum.inr current) (acc.map Sum.inr) fuel =
      (@getOrbitAux β b2 p2 start current acc fuel).map Sum.inr := by
  induction fuel generalizing current acc with
  | zero => rfl
  | succ f ih =>
    have hsf : (sumPerm p1 p2).f (Sum.inr current) = Sum.inr (p2.f current) := rfl
    have hbeq : (@BEq.beq (α ⊕ β) bSum (Sum.inr (p2.f current)) (Sum.inr start)) =
        (@BEq.beq β b2 (p2.f current) start) := by
      apply Bool.eq_iff_iff.mpr
      rw [hbSum, hb2]
      exact ⟨fun h => Sum.inr.inj h, fun h => congrArg Sum.inr h⟩
    rw [getOrbitAux, getOrbitAux, hsf, hbeq]
    cases @BEq.beq β b2 (p2.f current) start
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← List.map_cons]
      exact ih (p2.f current) (current :: acc)
    · simp

theorem getOrbit_sumPerm_inl_gen {α β : Type}
    {bSum : BEq (α ⊕ β)} (hbSum : ∀ u v : α ⊕ β, bSum.beq u v = true ↔ u = v)
    {b1 : BEq α} (hb1 : ∀ x y : α, b1.beq x y = true ↔ x = y)
    (p1 : Perm α) (p2 : Perm β) (fuel : Nat) (x : α) :
    @getOrbit (α ⊕ β) bSum (sumPerm p1 p2) fuel (Sum.inl x) =
      (@getOrbit α b1 p1 fuel x).map Sum.inl :=
  getOrbitAux_sumPerm_inl_gen hbSum hb1 p1 p2 x x [] fuel

theorem getOrbit_sumPerm_inr_gen {α β : Type}
    {bSum : BEq (α ⊕ β)} (hbSum : ∀ u v : α ⊕ β, bSum.beq u v = true ↔ u = v)
    {b2 : BEq β} (hb2 : ∀ x y : β, b2.beq x y = true ↔ x = y)
    (p1 : Perm α) (p2 : Perm β) (fuel : Nat) (y : β) :
    @getOrbit (α ⊕ β) bSum (sumPerm p1 p2) fuel (Sum.inr y) =
      (@getOrbit β b2 p2 fuel y).map Sum.inr :=
  getOrbitAux_sumPerm_inr_gen hbSum hb2 p1 p2 y y [] fuel

theorem getOrbit_sumPerm_inl_deceq {α β : Type} [DecidableEq α] [DecidableEq β]
    (p1 : Perm α) (p2 : Perm β) (fuel : Nat) (x : α) :
    @getOrbit (α ⊕ β) (@instBEqOfDecidableEq (α ⊕ β) _) (sumPerm p1 p2) fuel (Sum.inl x) =
      (@getOrbit α (@instBEqOfDecidableEq α _) p1 fuel x).map Sum.inl :=
  getOrbit_sumPerm_inl_gen deceq_beq_iff_eq deceq_beq_iff_eq p1 p2 fuel x

theorem getOrbit_sumPerm_inr_deceq {α β : Type} [DecidableEq α] [DecidableEq β]
    (p1 : Perm α) (p2 : Perm β) (fuel : Nat) (y : β) :
    @getOrbit (α ⊕ β) (@instBEqOfDecidableEq (α ⊕ β) _) (sumPerm p1 p2) fuel (Sum.inr y) =
      (@getOrbit β (@instBEqOfDecidableEq β _) p2 fuel y).map Sum.inr :=
  getOrbit_sumPerm_inr_gen deceq_beq_iff_eq deceq_beq_iff_eq p1 p2 fuel y

private theorem walkEN_sumPerm_inl {α β : Type} (e1 n1 : Perm α) (e2 n2 : Perm β) :
    ∀ {u v : α ⊕ β}, WalkEN (sumPerm e1 e2) (sumPerm n1 n2) u v →
      (∃ x : α, u = Sum.inl x) → ∃ x' : α, v = Sum.inl x'
  | _, _, WalkEN.refl _, h => h
  | _, _, WalkEN.step s w, h => by
    rcases h with ⟨x, rfl⟩
    apply walkEN_sumPerm_inl e1 n1 e2 n2 w
    cases s with
    | e_fwd => exact ⟨e1.f x, rfl⟩
    | e_bwd => exact ⟨e1.inv x, rfl⟩
    | n_fwd => exact ⟨n1.f x, rfl⟩
    | n_bwd => exact ⟨n1.inv x, rfl⟩

theorem reachEN_sumPerm_inl_inr_false {α β : Type} (e1 n1 : Perm α) (e2 n2 : Perm β)
    (x : α) (y : β) :
    ¬ ReachEN (sumPerm e1 e2) (sumPerm n1 n2) (Sum.inl x) (Sum.inr y) := by
  rintro ⟨w⟩
  rcases walkEN_sumPerm_inl e1 n1 e2 n2 w ⟨x, rfl⟩ with ⟨x', heq⟩
  cases heq

/-- Disjoint sum of two permutation triples on `α ⊕ β`. -/
def sumTriple {α β : Type} (T1 : PermTriple α) (T2 : PermTriple β) : PermTriple (α ⊕ β) where
  e := sumPerm T1.e T2.e
  n := sumPerm T1.n T2.n
  f := sumPerm T1.f T2.f
  enf_id x := by cases x <;> simp [sumPerm, T1.enf_id, T2.enf_id]

private theorem perm_eq_of_f_inv {D : Type} {p1 p2 : Perm D}
    (hf : p1.f = p2.f) (hinv : p1.inv = p2.inv) : p1 = p2 := by
  cases p1; cases p2; dsimp at hf hinv; subst hf hinv; rfl

private theorem permTriple_eq_of_enf {D : Type} {T1 T2 : PermTriple D}
    (he : T1.e = T2.e) (hn : T1.n = T2.n) (hf : T1.f = T2.f) : T1 = T2 := by
  cases T1; cases T2; dsimp at he hn hf; subst he hn hf; rfl

/-- Exact Euler/genus-deficit and component-count additivity for `sumTriple`. -/
theorem sumTriple_spec {α β : Type} [DecidableEq α] [DecidableEq β]
    (T1 : PermTriple α) (T2 : PermTriple β)
    (darts1 : List α) (h1_nd : darts1.Nodup) (h1_comp : ∀ x : α, x ∈ darts1)
    (darts2 : List β) (h2_nd : darts2.Nodup) (h2_comp : ∀ y : β, y ∈ darts2)
    {fuel : Nat} (h_le : darts1.length + darts2.length ≤ fuel) :
    let dartsU : List (α ⊕ β) := darts1.map Sum.inl ++ darts2.map Sum.inr
    dartsU.Nodup ∧ (∀ z : α ⊕ β, z ∈ dartsU) ∧
      genusDeficit (sumTriple T1 T2) fuel dartsU =
        genusDeficit T1 fuel darts1 + genusDeficit T2 fuel darts2 ∧
      countRelClasses (ReachEN (sumTriple T1 T2).e (sumTriple T1 T2).n) dartsU =
        countRelClasses (ReachEN T1.e T1.n) darts1 +
          countRelClasses (ReachEN T2.e T2.n) darts2 := by
  intro dartsU
  let P : α ⊕ β → Prop := fun z => Sum.isLeft z = true
  let Q : α ⊕ β → Prop := fun z => Sum.isRight z = true
  have h_disj : ∀ z : α ⊕ β, ¬ (P z ∧ Q z) := by
    intro z ⟨hP, hQ⟩
    cases z <;> simp [P, Q] at hP hQ
  let φ1 : SimpleEquiv α { z : α ⊕ β // P z } :=
    { toFun := fun a => ⟨Sum.inl a, rfl⟩
      invFun := fun z => match z with | ⟨Sum.inl a, _⟩ => a | ⟨Sum.inr _, h⟩ => absurd h (by simp [P])
      left_inv := fun _ => rfl
      right_inv := fun z => by cases z with | mk v h => cases v <;> simp [P] at h ⊢ }
  let φ2 : SimpleEquiv β { z : α ⊕ β // Q z } :=
    { toFun := fun b => ⟨Sum.inr b, rfl⟩
      invFun := fun z => match z with | ⟨Sum.inl _, h⟩ => absurd h (by simp [Q]) | ⟨Sum.inr b, _⟩ => b
      left_inv := fun _ => rfl
      right_inv := fun z => by cases z with | mk v h => cases v <;> simp [Q] at h ⊢ }
  let φU : SimpleEquiv { z : α ⊕ β // P z ∨ Q z } (α ⊕ β) :=
    { toFun := fun z => z.val
      invFun := fun z => ⟨z, by cases z <;> simp [P, Q]⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  let T_P := T1.mapEquiv φ1
  let T_Q := T2.mapEquiv φ2
  let T_U := unionTriplePred h_disj T_P T_Q
  let darts_P : List { z : α ⊕ β // P z } := darts1.map φ1.toFun
  let darts_Q : List { z : α ⊕ β // Q z } := darts2.map φ2.toFun
  have hP_nd : darts_P.Nodup := by
    refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij heq => ?_)
    simp only [darts_P, List.getElem_map] at heq
    have heq' : darts1[i]'(by simpa [darts_P] using hi) = darts1[j]'(by simpa [darts_P] using hj) := by
      simpa [φ1] using congrArg φ1.invFun heq
    exact List.pairwise_iff_getElem.mp h1_nd i j (by simpa [darts_P] using hi) (by simpa [darts_P] using hj) hij heq'
  have hP_comp : ∀ z : { z : α ⊕ β // P z }, z ∈ darts_P := by
    intro z
    rw [← φ1.right_inv z]
    exact List.mem_map.mpr ⟨φ1.invFun z, h1_comp _, rfl⟩
  have hQ_nd : darts_Q.Nodup := by
    refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij heq => ?_)
    simp only [darts_Q, List.getElem_map] at heq
    have heq' : darts2[i]'(by simpa [darts_Q] using hi) = darts2[j]'(by simpa [darts_Q] using hj) := by
      simpa [φ2] using congrArg φ2.invFun heq
    exact List.pairwise_iff_getElem.mp h2_nd i j (by simpa [darts_Q] using hi) (by simpa [darts_Q] using hj) hij heq'
  have hQ_comp : ∀ z : { z : α ⊕ β // Q z }, z ∈ darts_Q := by
    intro z
    rw [← φ2.right_inv z]
    exact List.mem_map.mpr ⟨φ2.invFun z, h2_comp _, rfl⟩
  have h_le' : darts_P.length + darts_Q.length ≤ fuel := by
    simpa [darts_P, darts_Q] using h_le
  have hU := unionTriplePred_spec h_disj T_P T_Q darts_P hP_nd hP_comp darts_Q hQ_nd hQ_comp h_le'
  dsimp only at hU
  let dartsU' : List { z : α ⊕ β // P z ∨ Q z } :=
    List.map (fun x => ⟨x.val, Or.inl x.property⟩) darts_P ++
      List.map (fun x => ⟨x.val, Or.inr x.property⟩) darts_Q
  have hTU_eq : T_U.mapEquiv φU = sumTriple T1 T2 := by
    refine permTriple_eq_of_enf ?_ ?_ ?_
    · refine perm_eq_of_f_inv ?_ ?_ <;> funext z <;> cases z <;>
        simp [T_U, T_P, T_Q, unionTriplePred, unionPermPred, PermTriple.mapEquiv, permMapEquiv, sumTriple, sumPerm, φU, φ1, φ2, P, Q]
    · refine perm_eq_of_f_inv ?_ ?_ <;> funext z <;> cases z <;>
        simp [T_U, T_P, T_Q, unionTriplePred, unionPermPred, PermTriple.mapEquiv, permMapEquiv, sumTriple, sumPerm, φU, φ1, φ2, P, Q]
    · refine perm_eq_of_f_inv ?_ ?_ <;> funext z <;> cases z <;>
        simp [T_U, T_P, T_Q, unionTriplePred, unionPermPred, PermTriple.mapEquiv, permMapEquiv, sumTriple, sumPerm, φU, φ1, φ2, P, Q]
  have hdarts_eq : List.map φU.toFun dartsU' = dartsU := by
    simp [dartsU', dartsU, darts_P, darts_Q, φU, φ1, φ2, List.map_append, List.map_map, Function.comp_def]
  have hU_len_eq : dartsU'.length = darts_P.length + darts_Q.length := by
    simp [dartsU']
  have hU_nd : dartsU.Nodup := by
    rw [← hdarts_eq]
    refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij heq => ?_)
    simp only [List.getElem_map] at heq
    have hi' : i < dartsU'.length := by simpa using hi
    have hj' : j < dartsU'.length := by simpa using hj
    have heq' : dartsU'[i]'hi' = dartsU'[j]'hj' := Subtype.ext heq
    exact List.pairwise_iff_getElem.mp hU.1 i j
      (by simpa [hU_len_eq] using hi') (by simpa [hU_len_eq] using hj') hij heq'
  have hU_comp : ∀ z : α ⊕ β, z ∈ dartsU := by
    intro z
    rw [← hdarts_eq]
    exact List.mem_map.mpr ⟨φU.invFun z, hU.2.1 (φU.invFun z), φU.right_inv z⟩
  have h_leU : dartsU'.length ≤ fuel := by omega
  have hgenU := genusDeficit_mapEquiv T_U φU dartsU' hU.2.1 h_leU
  rw [hTU_eq, hdarts_eq] at hgenU
  have hgen1 := genusDeficit_mapEquiv T1 φ1 darts1 h1_comp (by omega : darts1.length ≤ fuel)
  have hgen2 := genusDeficit_mapEquiv T2 φ2 darts2 h2_comp (by omega : darts2.length ≤ fuel)
  have hgen_tot : genusDeficit (sumTriple T1 T2) fuel dartsU =
      genusDeficit T1 fuel darts1 + genusDeficit T2 fuel darts2 := by
    rw [hgenU, hU.2.2.1, ← hgen1, ← hgen2]
  have hC_U : countRelClasses (ReachEN (sumTriple T1 T2).e (sumTriple T1 T2).n) dartsU =
      countRelClasses (ReachEN T_U.e T_U.n) dartsU' := by
    rw [← hdarts_eq, ← hTU_eq]
    apply countRelClasses_mapEquiv (ReachEN T_U.e T_U.n)
      (ReachEN (T_U.mapEquiv φU).e (T_U.mapEquiv φU).n) φU.toFun
    intro x y
    exact reachEN_mapEquiv_iff T_U.e T_U.n φU x y
  have hC_1 : countRelClasses (ReachEN T_P.e T_P.n) darts_P =
      countRelClasses (ReachEN T1.e T1.n) darts1 := by
    apply countRelClasses_mapEquiv (ReachEN T1.e T1.n)
      (ReachEN (T1.mapEquiv φ1).e (T1.mapEquiv φ1).n) φ1.toFun
    intro x y
    exact reachEN_mapEquiv_iff T1.e T1.n φ1 x y
  have hC_2 : countRelClasses (ReachEN T_Q.e T_Q.n) darts_Q =
      countRelClasses (ReachEN T2.e T2.n) darts2 := by
    apply countRelClasses_mapEquiv (ReachEN T2.e T2.n)
      (ReachEN (T2.mapEquiv φ2).e (T2.mapEquiv φ2).n) φ2.toFun
    intro x y
    exact reachEN_mapEquiv_iff T2.e T2.n φ2 x y
  refine ⟨hU_nd, hU_comp, hgen_tot, ?_⟩
  rw [hC_U, hU.2.2.2, hC_1, hC_2]

private theorem getOrbitAux_restrictPermPred {D : Type} [DecidableEq D]
    (p : Perm D) (P : D → Prop) (h_inv : ∀ d : D, P d ↔ P (p.f d))
    (start current : { d : D // P d }) (acc : List { d : D // P d }) (fuel : Nat) :
    (getOrbitAux (restrictPermPred p P h_inv) start current acc fuel).map Subtype.val =
      getOrbitAux p start.val current.val (acc.map Subtype.val) fuel := by
  induction fuel generalizing current acc with
  | zero => rfl
  | succ f ih =>
    dsimp [getOrbitAux, restrictPermPred]
    by_cases h : p.f current.val = start.val
    · have hb1 : ((⟨p.f current.val, (h_inv current.val).mp current.property⟩ : { d : D // P d }) == start) = true :=
        beq_iff_eq.mpr (Subtype.ext h)
      have hb2 : (p.f current.val == start.val) = true := beq_iff_eq.mpr h
      rw [hb1, hb2]; rfl
    · have hb1 : ((⟨p.f current.val, (h_inv current.val).mp current.property⟩ : { d : D // P d }) == start) = false :=
        beq_eq_false_iff_ne.mpr (fun heq => h (congrArg Subtype.val heq))
      have hb2 : (p.f current.val == start.val) = false :=
        Bool.eq_false_iff.mpr (fun heq => h (beq_iff_eq.mp heq))
      rw [hb1, hb2]
      exact ih ⟨p.f current.val, (h_inv current.val).mp current.property⟩ (current :: acc)

theorem getOrbit_restrictPermPred {D : Type} [DecidableEq D]
    (p : Perm D) (P : D → Prop) (h_inv : ∀ d : D, P d ↔ P (p.f d))
    (fuel : Nat) (x : { d : D // P d }) :
    (getOrbit (restrictPermPred p P h_inv) fuel x).map Subtype.val = getOrbit p fuel x.val :=
  getOrbitAux_restrictPermPred p P h_inv x x [] fuel

theorem getOrbit_restrictPermPred_length {D : Type} [DecidableEq D]
    (p : Perm D) (P : D → Prop) (h_inv : ∀ d : D, P d ↔ P (p.f d))
    (fuel : Nat) (x : { d : D // P d }) :
    (getOrbit (restrictPermPred p P h_inv) fuel x).length = (getOrbit p fuel x.val).length := by
  have := congrArg List.length (getOrbit_restrictPermPred p P h_inv fuel x)
  simpa using this

private theorem FaceCycleCut.posL_block {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k)
    {r : Nat} (_hr0 : 0 < r) (hrk : r ≤ cut.posL darts h_all k) :
    ∃ m : Nat, m < k ∧ cut.posL darts h_all m < r ∧ r ≤ cut.posL darts h_all (m + 1) := by
  have aux : ∀ B : Nat, r ≤ cut.posL darts h_all B →
      ∃ m : Nat, m < B ∧ cut.posL darts h_all m < r ∧ r ≤ cut.posL darts h_all (m + 1) := by
    intro B hrB
    induction B with
    | zero =>
      dsimp [FaceCycleCut.posL] at hrB
      omega
    | succ B ih =>
      by_cases hlt : r ≤ cut.posL darts h_all B
      · rcases ih hlt with ⟨m, hm, hlo, hhi⟩
        exact ⟨m, by omega, hlo, hhi⟩
      · exact ⟨B, Nat.lt_succ_self B, Nat.lt_of_not_ge hlt, hrB⟩
  exact aux k hrk

/-- Exact block bijection between `(posL m, posL (m + 1)]` along `T_k.f` and `cut.inArcL (m + 1)`. -/
theorem FaceCycleCut.inArcL_iff_posL_block {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {k : Nat} (cut : FaceCycleCut H k)
    {m : Nat} (hm : m < k) (d : H.Dart) :
    cut.inArcL darts h_all ⟨(m + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d ↔
      ∃ r : Nat, cut.posL darts h_all m < r ∧ r ≤ cut.posL darts h_all (m + 1) ∧
        Perm.iter cut.uncoupleTriple.f r (cut.cutDart ⟨0, by have := cut.hk; omega⟩) = d := by
  have hk := cut.hk
  let m_next : Fin k := ⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩
  let m_prev : Fin k := ⟨(m_next.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  have hm_prev_eq : m_prev = ⟨m, hm⟩ := by
    apply Fin.ext
    dsimp [m_prev, m_next]
    exact mod_succ_pred hk m hm
  have hm_mod : (⟨m % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨m, hm⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hm)
  have hpos_step : cut.posL darts h_all (m + 1) =
      cut.posL darts h_all m + cut.arcLen darts h_all m_next := rfl
  have hm_prev_unfold : ∀ (hlt1 : (m + 1) % k < k) (hlt2 : ((⟨(m + 1) % k, hlt1⟩ : Fin k).val + k - 1) % k < k),
      (⟨((⟨(m + 1) % k, hlt1⟩ : Fin k).val + k - 1) % k, hlt2⟩ : Fin k) = ⟨m, hm⟩ :=
    fun _ _ => Fin.ext (mod_succ_pred hk m hm)
  constructor
  · intro hd
    rcases hd with ⟨t, ht1, ht_le, ht_eq⟩
    refine ⟨cut.posL darts h_all m + t, by omega, by rw [hpos_step]; dsimp only [m_next]; omega, ?_⟩
    rw [Nat.add_comm, Perm.iter_add, cut.uncoupleTriple_iter_posL darts h_all m, hm_mod]
    have hstep := cut.uncoupleTriple_step_arcL darts h_all m_next t ht1 ht_le
    change Perm.iter cut.uncoupleTriple.f t (cut.cutDart m_prev) =
      Perm.iter H.face t (H.edge.f (cut.cutDart m_prev)) at hstep
    rw [hm_prev_eq] at hstep
    rw [hstep]
    simpa [hm_prev_unfold] using ht_eq
  · rintro ⟨r, hr_gt, hr_le, hr_eq⟩
    let t := r - cut.posL darts h_all m
    have ht1 : 1 ≤ t := by omega
    have ht_le : t ≤ cut.arcLen darts h_all m_next := by
      dsimp only [t, m_next]
      rw [hpos_step] at hr_le
      dsimp only [m_next] at hr_le
      omega
    refine ⟨t, ht1, ht_le, ?_⟩
    have hr_add : r = t + cut.posL darts h_all m := by omega
    rw [hr_add, Perm.iter_add, cut.uncoupleTriple_iter_posL darts h_all m, hm_mod] at hr_eq
    have hstep := cut.uncoupleTriple_step_arcL darts h_all m_next t ht1 ht_le
    change Perm.iter cut.uncoupleTriple.f t (cut.cutDart m_prev) =
      Perm.iter H.face t (H.edge.f (cut.cutDart m_prev)) at hstep
    rw [hm_prev_eq] at hstep
    have heq' : Perm.iter H.face t (H.edge.f (cut.cutDart ⟨m, hm⟩)) = d := by
      rw [← hstep]; exact hr_eq
    simpa [hm_prev_unfold] using heq'

/-- The `T_k.f`-orbit of `cutDart 0` has exact length `cut.posL darts h_all k`. -/
theorem FaceCycleCut.uncoupleTriple_posL_orbit_length {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {k : Nat} (cut : FaceCycleCut H k) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    (getOrbit cut.uncoupleTriple.f fuel (cut.cutDart ⟨0, by have := cut.hk; omega⟩)).length =
      cut.posL darts h_all k := by
  have hk := cut.hk
  let T_k := cut.uncoupleTriple
  let a0 := cut.cutDart ⟨0, by omega⟩
  let P := cut.posL darts h_all k
  have hfuel : getOrbit T_k.f fuel a0 = getOrbit T_k.f darts.length a0 :=
    getOrbit_fuel_eq_of_complete T_k.f darts h_all a0 h_le
  rw [hfuel]
  let La := (getOrbit T_k.f darts.length a0).length
  have hP_pos : 0 < P := by
    have hlt := cut.posL_strictMono darts h_all (m := 0) (n := k) (by omega)
    dsimp [FaceCycleCut.posL] at hlt
    omega
  have hP_per : Perm.iter T_k.f P a0 = a0 := by
    have h := cut.uncoupleTriple_iter_posL darts h_all k
    have h0 : (⟨k % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨0, by omega⟩ := Fin.ext (Nat.mod_self k)
    rwa [h0] at h
  have hmul_per : ∀ q : Nat, Perm.iter T_k.f (P * q) a0 = a0 := by
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [Nat.mul_succ, Perm.iter_add, hP_per, ih]
  let pts : List H.Dart := (List.range P).map (fun r => Perm.iter T_k.f r a0)
  have hsub : ∀ x ∈ getOrbit T_k.f darts.length a0, x ∈ pts := by
    intro x hx
    rcases mem_getOrbit_imp_exists_iter T_k.f darts.length a0 x hx with ⟨q, _, rfl⟩
    have hdiv := Nat.div_add_mod q P
    have hq_eq : Perm.iter T_k.f q a0 = Perm.iter T_k.f (q % P) a0 := by
      have h_split : q = q % P + P * (q / P) := by omega
      calc Perm.iter T_k.f q a0
          = Perm.iter T_k.f (q % P + P * (q / P)) a0 := by rw [← h_split]
        _ = Perm.iter T_k.f (q % P) (Perm.iter T_k.f (P * (q / P)) a0) := Perm.iter_add T_k.f _ _ a0
        _ = Perm.iter T_k.f (q % P) a0 := by rw [hmul_per (q / P)]
    rw [hq_eq]
    exact List.mem_map.mpr ⟨q % P, List.mem_range.mpr (Nat.mod_lt _ hP_pos), rfl⟩
  have hLa_le : La ≤ P := by
    have hle := nodup_length_le_of_subset (getOrbit T_k.f darts.length a0) pts
      (getOrbit_nodup T_k.f darts.length a0) hsub
    simpa [pts, La] using hle
  have hLa_pos : 1 ≤ La := List.length_pos_of_mem (mem_getOrbit_self T_k.f darts.length a0)
  by_cases hlt : La < P
  · exfalso
    have hLa_per : Perm.iter T_k.f La a0 = a0 :=
      perm_iter_length_getOrbit_eq_self_of_complete T_k.f darts h_all (Nat.le_refl _) a0
    rcases cut.posL_block darts h_all hLa_pos (by omega) with ⟨m, hm_lt, hm_gt, hm_le⟩
    have hin : cut.inArcL darts h_all ⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩ a0 :=
      (cut.inArcL_iff_posL_block darts h_all hm_lt a0).mpr ⟨La, hm_gt, hm_le, hLa_per⟩
    have hsame_next := cut.inArcL_sub_face darts h_all hin
    have hsame0 := cut.h_a ⟨0, by omega⟩
    have heq_idx : (⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨0, by omega⟩ := by
      by_cases hne : (⟨(m + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨0, by omega⟩
      · exact hne
      · exfalso
        exact cut.h_diff _ _ hne (sameOrbit_trans H.face hsame_next (sameOrbit_symm_of_complete H.face darts h_all hsame0))
    have hm_succ_mod : (m + 1) % k = 0 := congrArg Fin.val heq_idx
    have hm_eq : m = k - 1 := by
      by_cases h1 : m + 1 < k
      · rw [Nat.mod_eq_of_lt h1] at hm_succ_mod; omega
      · omega
    subst hm_eq
    have hk_eq : k - 1 + 1 = k := by omega
    have h_pos_k : cut.posL darts h_all k =
        cut.posL darts h_all (k - 1) + cut.arcLen darts h_all ⟨0, by omega⟩ := by
      have hfin : (⟨k % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨0, by omega⟩ :=
        Fin.ext (Nat.mod_self k)
      have hd : cut.posL darts h_all (k - 1 + 1) =
          cut.posL darts h_all (k - 1) + cut.arcLen darts h_all ⟨(k - 1 + 1) % k, Nat.mod_lt _ (by omega)⟩ := rfl
      rw [hk_eq] at hd
      rw [hd, hfin]
    let t := La - cut.posL darts h_all (k - 1)
    have ht1 : 1 ≤ t := by omega
    have ht_lt : t < cut.arcLen darts h_all ⟨0, by omega⟩ := by
      dsimp only [t, P] at hlt ⊢; omega
    have hstep := cut.uncoupleTriple_step_arcL darts h_all ⟨0, by omega⟩ t ht1 (by omega)
    have hidx0 : (⟨(0 + k - 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨k - 1, by omega⟩ := by
      apply Fin.ext; simp only [Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    change Perm.iter T_k.f t (cut.cutDart ⟨(0 + k - 1) % k, _⟩) =
      Perm.iter H.face t (H.edge.f (cut.cutDart ⟨(0 + k - 1) % k, _⟩)) at hstep
    rw [hidx0] at hstep
    have h_iter_eq : Perm.iter H.face t (H.edge.f (cut.cutDart ⟨k - 1, by omega⟩)) = a0 := by
      rw [← hstep]
      have hpos_last := cut.uncoupleTriple_iter_posL darts h_all (k - 1)
      have hk1_mod : (⟨(k - 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = ⟨k - 1, by omega⟩ :=
        Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [hk1_mod] at hpos_last
      have hLa_add : La = t + cut.posL darts h_all (k - 1) := by omega
      calc
        Perm.iter T_k.f t (cut.cutDart ⟨k - 1, by omega⟩)
            = Perm.iter T_k.f t (Perm.iter T_k.f (cut.posL darts h_all (k - 1)) a0) := by rw [hpos_last]
        _ = Perm.iter T_k.f La a0 := by rw [← Perm.iter_add, ← hLa_add]
        _ = a0 := hLa_per
    exact (cut.arcLen_spec darts h_all ⟨0, by omega⟩).2.2.2.1 t ht1 ht_lt
      (by simpa [hidx0] using h_iter_eq)
  · omega

/-- Predicate identifying the `L`-component darts `{ d : H.Dart // DL d }` of a `FaceCycleCut`. -/
def FaceCycleCut.capSingleVertex_DL {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : FaceCycleCut H k) (d : H.Dart) : Prop :=
  ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
    (cut.cutDart ⟨0, by have := cut.hk; omega⟩) d

theorem FaceCycleCut.capSingleVertex_DL_e {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : FaceCycleCut H k) (d : H.Dart) :
    cut.capSingleVertex_DL d ↔ cut.capSingleVertex_DL (cut.uncoupleTriple.e.f d) :=
  ⟨fun hd => reachEN_trans _ _ hd ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩,
   fun hd => reachEN_trans _ _ hd (reachEN_symm _ _ ⟨WalkEN.step (StepEN.e_fwd d) (WalkEN.refl _)⟩)⟩

theorem FaceCycleCut.capSingleVertex_DL_n {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : FaceCycleCut H k) (d : H.Dart) :
    cut.capSingleVertex_DL d ↔ cut.capSingleVertex_DL (cut.uncoupleTriple.n.f d) :=
  ⟨fun hd => reachEN_trans _ _ hd ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩,
   fun hd => reachEN_trans _ _ hd (reachEN_symm _ _ ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩)⟩

/-- Restricted `L`-side permutation triple on `{ d : H.Dart // cut.capSingleVertex_DL d }`. -/
noncomputable def FaceCycleCut.capSingleVertex_TL {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : FaceCycleCut H k) : PermTriple { d : H.Dart // cut.capSingleVertex_DL d } :=
  restrictTriplePred cut.uncoupleTriple cut.capSingleVertex_DL
    cut.capSingleVertex_DL_e cut.capSingleVertex_DL_n

noncomputable def FaceCycleCut.capSumTriple {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : FaceCycleCut H k) :
    PermTriple ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) :=
  sumTriple cut.capSingleVertex_TL (singleCycleTriple k (by have := cut.hk; omega))

noncomputable def FaceCycleCut.capBaseTriple {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : FaceCycleCut H k) :
    PermTriple ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) :=
  let a0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k :=
    Sum.inl ⟨cut.cutDart ⟨0, by have := cut.hk; omega⟩, reachEN_refl _ _ _⟩
  let v0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k :=
    Sum.inr ⟨0, by have := cut.hk; omega⟩
  coupleEdge cut.capSumTriple a0_sum v0_sum

noncomputable def FaceCycleCut.capSpecs {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {k : Nat} (cut : FaceCycleCut H k) : List (Nat × Nat) :=
  let La := cut.posL darts h_all k
  (List.finRange (k - 1)).map (fun i => (cut.posL darts h_all (k - 1 - i.val), La + 1 + i.val))

/-- Permutation triple obtained by capping the `L`-side of a `FaceCycleCut` with a single
    degree-`k` vertex (`Fin k`), pairing each `cutDart i` with `Sum.inr i`. -/
noncomputable def FaceCycleCut.capSingleVertexTriple {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {k : Nat} (cut : FaceCycleCut H k) :
    PermTriple ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) :=
  let v0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k :=
    Sum.inr ⟨0, by have := cut.hk; omega⟩
  coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all))

noncomputable def FaceCycleCut.capDartsL_sub {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) {k : Nat} (cut : FaceCycleCut H k) :
    List { d : H.Dart // cut.capSingleVertex_DL d } :=
  @predDarts H.Dart cut.capSingleVertex_DL (fun _ => Classical.propDecidable _) darts

/-- Complete dart list for `cut.capSingleVertexHypermap`: `{ d ∈ DL } ⊕ Fin k`. -/
noncomputable def FaceCycleCut.capSingleVertexDarts {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) {k : Nat} (cut : FaceCycleCut H k) :
    List ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) :=
  (cut.capDartsL_sub darts).map Sum.inl ++ (List.finRange k).map Sum.inr

theorem FaceCycleCut.capSingleVertexDarts_nodup_complete {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {k : Nat} (cut : FaceCycleCut H k) :
    let darts_cap := cut.capSingleVertexDarts darts
    darts_cap.Nodup ∧ (∀ x, x ∈ darts_cap) ∧ darts_cap ≠ [] ∧
      ∃ dartsL : List H.Dart, dartsL.Nodup ∧ (∀ d, d ∈ dartsL ↔ cut.capSingleVertex_DL d) ∧
        darts_cap.length = dartsL.length + k ∧ dartsL.length ≤ darts.length := by
  intro darts_cap
  letI decDL : DecidablePred cut.capSingleVertex_DL := fun d => Classical.propDecidable _
  let dartsL_sub := cut.capDartsL_sub darts
  have hsub_nd : dartsL_sub.Nodup := @nodup_predDarts H.Dart cut.capSingleVertex_DL decDL darts h_nd
  have hsub_mem : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d }, x ∈ dartsL_sub :=
    fun x => (@mem_predDarts_iff H.Dart cut.capSingleVertex_DL decDL darts x).mpr (h_all x.val)
  have hk := cut.hk
  have h_nd_cap : darts_cap.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij heq => ?_)
      simp only [List.getElem_map] at heq
      have heq' : dartsL_sub[i]'(by simpa using hi) = dartsL_sub[j]'(by simpa using hj) :=
        Sum.inl.inj heq
      exact List.pairwise_iff_getElem.mp hsub_nd i j (by simpa using hi) (by simpa using hj) hij heq'
    · refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij heq => ?_)
      simp only [List.getElem_map, List.getElem_finRange] at heq
      have hfin := congrArg Fin.val (Sum.inr.inj heq)
      simp only [Fin.val_cast] at hfin
      omega
    · intro a ha b hb heq
      rcases List.mem_map.mp ha with ⟨x, _, rfl⟩
      rcases List.mem_map.mp hb with ⟨y, _, rfl⟩
      cases heq
  have h_comp_cap : ∀ z : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k, z ∈ darts_cap := by
    intro z
    apply List.mem_append.mpr
    cases z with
    | inl x => left; exact List.mem_map.mpr ⟨x, hsub_mem x, rfl⟩
    | inr m => right; exact List.mem_map.mpr ⟨m, List.mem_finRange m, rfl⟩
  have h_ne_cap : darts_cap ≠ [] := by
    intro hemp
    have h0 := h_comp_cap (Sum.inr ⟨0, by omega⟩)
    rw [hemp] at h0
    cases h0
  let dartsL := dartsL_sub.map Subtype.val
  have hL_nd : dartsL.Nodup := by
    refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij heq => ?_)
    simp only [dartsL, List.getElem_map] at heq
    have heq' : dartsL_sub[i]'(by simpa [dartsL] using hi) = dartsL_sub[j]'(by simpa [dartsL] using hj) :=
      Subtype.ext heq
    exact List.pairwise_iff_getElem.mp hsub_nd i j (by simpa [dartsL] using hi) (by simpa [dartsL] using hj) hij heq'
  have hL_iff : ∀ d : H.Dart, d ∈ dartsL ↔ cut.capSingleVertex_DL d := by
    intro d
    constructor
    · intro hd
      rcases List.mem_map.mp hd with ⟨x, _, rfl⟩
      exact x.property
    · intro hd
      exact List.mem_map.mpr ⟨⟨d, hd⟩, hsub_mem ⟨d, hd⟩, rfl⟩
  have hL_le : dartsL.length ≤ darts.length :=
    nodup_length_le_of_subset dartsL darts hL_nd (fun d _ => h_all d)
  have hlen : darts_cap.length = dartsL.length + k := by
    simp only [darts_cap, dartsL, dartsL_sub, FaceCycleCut.capSingleVertexDarts, List.length_append,
      List.length_map, List.length_finRange]
  exact ⟨h_nd_cap, h_comp_cap, h_ne_cap, dartsL, hL_nd, hL_iff, hlen, hL_le⟩

private theorem singleCycleTriple_iter_f_from_zero {m : Nat} (hm : 1 ≤ m)
    {s : Nat} (hs1 : 1 ≤ s) (hsm : s ≤ m) :
    Perm.iter (singleCycleTriple m hm).f s ⟨0, hm⟩ = ⟨(m - s) % m, Nat.mod_lt _ hm⟩ := by
  have hf0 : (singleCycleTriple m hm).f.f ⟨0, hm⟩ = ⟨m - 1, by omega⟩ := by
    have h := (singleCycleTriple m hm).f_eq_n_inv_e_inv ⟨0, hm⟩
    dsimp [singleCycleTriple, permId] at h ⊢
    rw [h]
    apply Fin.ext; dsimp
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  have hs_add : s = (s - 1) + 1 := by omega
  rw [hs_add, Perm.iter_add]
  change Perm.iter (singleCycleTriple m hm).f (s - 1) ((singleCycleTriple m hm).f.f ⟨0, hm⟩) = _
  rw [hf0]
  have hf := singleCycleTriple_iter_f m hm (s - 1) (by omega)
  rw [hf]
  apply Fin.ext; dsimp
  by_cases hsm_eq : s = m
  · rw [hsm_eq, show (m - 1) % m = m - 1 from Nat.mod_eq_of_lt (by omega),
      Nat.sub_self, show m - 1 + 1 = m by omega, Nat.sub_self, Nat.zero_mod]
  · have h_sub_mod : (s - 1) % m = s - 1 := Nat.mod_eq_of_lt (by omega)
    rw [h_sub_mod, show m - 1 - (s - 1) = m - s by omega, show s - 1 + 1 = s by omega,
      Nat.mod_eq_of_lt (by omega)]

private theorem stepEN_preserves_pred_jcs {D : Type} (e n : Perm D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (e.f d)) (h_n : ∀ d, P d ↔ P (n.f d))
    {a b : D} (s : StepEN e n a b) : P a ↔ P b := by
  cases s with
  | e_fwd => exact h_e a
  | e_bwd =>
    have h1 := (h_e (e.inv a)).symm
    rw [e.right_inv] at h1
    exact h1
  | n_fwd => exact h_n a
  | n_bwd =>
    have h1 := (h_n (n.inv a)).symm
    rw [n.right_inv] at h1
    exact h1

private def stepEN_lift_restrictTriple {D : Type} (T : PermTriple D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (T.e.f d)) (h_n : ∀ d, P d ↔ P (T.n.f d))
    {x y : D} (hx : P x) (s : StepEN T.e T.n x y) :
    StepEN (restrictTriplePred T P h_e h_n).e (restrictTriplePred T P h_e h_n).n
      ⟨x, hx⟩ ⟨y, (stepEN_preserves_pred_jcs T.e T.n P h_e h_n s).mp hx⟩ := by
  cases s with
  | e_fwd =>
    exact StepEN.e_fwd (e := (restrictTriplePred T P h_e h_n).e)
      (n := (restrictTriplePred T P h_e h_n).n) (⟨x, hx⟩ : { d : D // P d })
  | e_bwd =>
    exact StepEN.e_bwd (e := (restrictTriplePred T P h_e h_n).e)
      (n := (restrictTriplePred T P h_e h_n).n) (⟨x, hx⟩ : { d : D // P d })
  | n_fwd =>
    exact StepEN.n_fwd (e := (restrictTriplePred T P h_e h_n).e)
      (n := (restrictTriplePred T P h_e h_n).n) (⟨x, hx⟩ : { d : D // P d })
  | n_bwd =>
    exact StepEN.n_bwd (e := (restrictTriplePred T P h_e h_n).e)
      (n := (restrictTriplePred T P h_e h_n).n) (⟨x, hx⟩ : { d : D // P d })

private def walkEN_lift_restrictTriple {D : Type} (T : PermTriple D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (T.e.f d)) (h_n : ∀ d, P d ↔ P (T.n.f d)) :
    ∀ {a b : D} (ha : P a) (hb : P b), WalkEN T.e T.n a b →
      WalkEN (restrictTriplePred T P h_e h_n).e (restrictTriplePred T P h_e h_n).n ⟨a, ha⟩ ⟨b, hb⟩
  | a, _, ha, hb, WalkEN.refl _ => by
    have hsub : (⟨a, ha⟩ : { d : D // P d }) = ⟨a, hb⟩ := Subtype.ext rfl
    rw [hsub]; exact WalkEN.refl _
  | _, b, ha, hb, WalkEN.step s w =>
    WalkEN.step (stepEN_lift_restrictTriple T P h_e h_n ha s)
      (walkEN_lift_restrictTriple T P h_e h_n ((stepEN_preserves_pred_jcs T.e T.n P h_e h_n s).mp ha) hb w)

private theorem reachEN_lift_restrictTriple {D : Type} (T : PermTriple D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (T.e.f d)) (h_n : ∀ d, P d ↔ P (T.n.f d))
    {a b : D} (ha : P a) (hb : P b) (h : ReachEN T.e T.n a b) :
    ReachEN (restrictTriplePred T P h_e h_n).e (restrictTriplePred T P h_e h_n).n ⟨a, ha⟩ ⟨b, hb⟩ :=
  h.elim fun w => ⟨walkEN_lift_restrictTriple T P h_e h_n ha hb w⟩

theorem FaceCycleCut.capSingleVertex_DL_cut_all {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) :
    cut.capSingleVertex_DL (cut.cutDart i) :=
  (uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut).2.2.2.2.2.2.2.1 i |>.1

private theorem FaceCycleCut.capSingleVertex_not_DL_edge_cut {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) (i : Fin k) :
    ¬ cut.capSingleVertex_DL (H.edge.f (cut.cutDart i)) := by
  have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  intro hDL
  exact hsep.2.2.2.2.2.2.1 _ ⟨hDL, (hsep.2.2.2.2.2.2.2.1 i).2⟩

private theorem FaceCycleCut.capSingleVertex_posL_le_dartsL {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) :
    cut.posL darts h_all k ≤ (cut.capDartsL_sub darts).length := by
  have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hcomp := cut.capSingleVertexDarts_nodup_complete darts h_nd h_all
  dsimp only at hcomp
  rcases hcomp with ⟨_, _, _, dartsL, hL_nd, hL_iff, hlen, _⟩
  have hlenL : (cut.capDartsL_sub darts).length = dartsL.length := by
    simp [FaceCycleCut.capSingleVertexDarts] at hlen
    omega
  rw [hlenL, ← cut.uncoupleTriple_posL_orbit_length darts h_all (Nat.le_refl _)]
  apply nodup_length_le_of_subset _ _ (getOrbit_nodup _ _ _)
  intro x hx
  rcases (hsep.2.2.2.2.2.2.2.2.2.2.1 x).mp hx with ⟨i, hi⟩
  exact (hL_iff x).mpr (cut.inArcL_imp_DL darts h_nd h_all h_planar h_conn i x hi)

private theorem FaceCycleCut.capSingleVertex_specs_ok {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) :
    let darts_cap := cut.capSingleVertexDarts darts
    let La := cut.posL darts h_all k
    let v0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k :=
      Sum.inr ⟨0, by have := cut.hk; omega⟩
    let specs := cut.capSpecs darts h_all
    let T_base := cut.capBaseTriple
    (getOrbit T_base.f darts_cap.length v0_sum).length = La + k ∧
    List.Pairwise (fun x y : Nat × Nat => y.fst < x.fst ∧ x.snd < y.snd) specs ∧
    (∀ pq ∈ specs, 1 ≤ pq.fst ∧ pq.fst < pq.snd ∧ pq.snd < La + k) ∧
    (∀ pq ∈ specs,
      T_base.e.f (Perm.iter T_base.f pq.fst v0_sum) = Perm.iter T_base.f pq.fst v0_sum ∧
      T_base.e.f (Perm.iter T_base.f pq.snd v0_sum) = Perm.iter T_base.f pq.snd v0_sum) ∧
    (∀ i : Nat, ∀ hi : i < specs.length,
      Perm.iter T_base.f specs[i].fst v0_sum =
        Sum.inl ⟨cut.cutDart ⟨k - 1 - i, by have := cut.hk; simp [specs, FaceCycleCut.capSpecs] at hi; omega⟩,
          cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn _⟩ ∧
      Perm.iter T_base.f specs[i].snd v0_sum =
        Sum.inr ⟨k - 1 - i, by have := cut.hk; simp [specs, FaceCycleCut.capSpecs] at hi; omega⟩) := by
  intro darts_cap La v0_sum specs T_base
  have hk := cut.hk
  have hcomp := cut.capSingleVertexDarts_nodup_complete darts h_nd h_all
  dsimp only at hcomp
  rcases hcomp with ⟨_, h_all_cap, _, dartsL, _, _, hlen_cap, hL_le⟩
  have hsub_len : (cut.capDartsL_sub darts).length = dartsL.length := by
    simp [FaceCycleCut.capSingleVertexDarts] at hlen_cap
    omega
  have hsub_mem : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d }, x ∈ cut.capDartsL_sub darts := by
    intro x
    letI decDL : DecidablePred cut.capSingleVertex_DL := fun d => Classical.propDecidable _
    exact (@mem_predDarts_iff H.Dart cut.capSingleVertex_DL decDL darts x).mpr (h_all x.val)
  let a0' : { d : H.Dart // cut.capSingleVertex_DL d } :=
    ⟨cut.cutDart ⟨0, by omega⟩, reachEN_refl _ _ _⟩
  let a0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k := Sum.inl a0'
  let v0 : Fin k := ⟨0, by omega⟩
  let bCap : BEq ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) := @instBEqOfDecidableEq _ _
  have ha0_orb_len : (@getOrbit _ bCap cut.capSumTriple.f darts_cap.length a0_sum).length = La := by
    dsimp only [a0_sum, FaceCycleCut.capSumTriple, sumTriple]
    rw [getOrbit_sumPerm_inl_gen deceq_beq_iff_eq (b1 := inferInstance)
      (fun u v => beq_iff_eq)]
    simp only [List.length_map]
    dsimp only [FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
    let bSub : BEq { d : H.Dart // cut.capSingleVertex_DL d } := inferInstance
    let bSubDec : BEq { d : H.Dart // cut.capSingleVertex_DL d } := @instBEqOfDecidableEq _ _
    have hb_iff : ∀ u v : { d : H.Dart // cut.capSingleVertex_DL d },
        bSub.beq u v = true ↔ bSubDec.beq u v = true :=
      fun u v => beq_iff_eq.trans (deceq_beq_iff_eq u v).symm
    have h_inv_f : ∀ d, cut.capSingleVertex_DL d ↔ cut.capSingleVertex_DL (cut.uncoupleTriple.f.f d) := by
      intro d
      have he := cut.capSingleVertex_DL_e (cut.uncoupleTriple.n.f (cut.uncoupleTriple.f.f d))
      have hn := cut.capSingleVertex_DL_n (cut.uncoupleTriple.f.f d)
      rw [cut.uncoupleTriple.enf_id d] at he
      exact (Iff.trans hn he).symm
    change (@getOrbit _ bSub (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f)
      darts_cap.length a0').length = La
    have h2 : @getOrbit _ bSub (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) darts_cap.length a0' =
        @getOrbit _ bSub (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) darts.length a0' := by
      rw [@getOrbit_beq_congr _ bSub bSubDec hb_iff
            (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) darts_cap.length a0',
          @getOrbit_beq_congr _ bSub bSubDec hb_iff
            (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) darts.length a0']
      have h_eq1 := getOrbit_fuel_eq_of_complete
        (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f)
        (cut.capDartsL_sub darts) hsub_mem a0' (fuel := darts_cap.length) (by
          dsimp only [darts_cap, FaceCycleCut.capSingleVertexDarts]
          rw [List.length_append, List.length_map]
          exact Nat.le_add_right _ _)
      have h_eq2 := getOrbit_fuel_eq_of_complete
        (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f)
        (cut.capDartsL_sub darts) hsub_mem a0' (fuel := darts.length) (by
          rw [hsub_len]; exact hL_le)
      exact h_eq1.trans h_eq2.symm
    rw [h2, getOrbit_restrictPermPred_length]
    exact cut.uncoupleTriple_posL_orbit_length darts h_all (Nat.le_refl _)
  have hv0_orb_len : (@getOrbit _ bCap cut.capSumTriple.f darts_cap.length v0_sum).length = k := by
    dsimp only [v0_sum, FaceCycleCut.capSumTriple, sumTriple]
    rw [getOrbit_sumPerm_inr_gen deceq_beq_iff_eq (fun _ _ => beq_iff_eq)]
    simp only [List.length_map]
    have htv := singleCycleTriple_spec k (by omega)
    dsimp only at htv
    have hfuel : getOrbit (singleCycleTriple k (by omega)).f darts_cap.length ⟨0, by omega⟩ =
        getOrbit (singleCycleTriple k (by omega)).f k ⟨0, by omega⟩ := by
      simpa [List.length_finRange] using
        getOrbit_fuel_eq_of_complete (singleCycleTriple k (by omega)).f (List.finRange k)
          (fun i => List.mem_finRange i) ⟨0, by omega⟩ (fuel := darts_cap.length) (by
            rw [List.length_finRange, hlen_cap]; omega)
    rw [hfuel]
    exact htv.2.2.2.2
  have ha0_not_v0 : ¬ v0_sum ∈ @getOrbit _ bCap cut.capSumTriple.f darts_cap.length a0_sum := by
    dsimp only [a0_sum, v0_sum, FaceCycleCut.capSumTriple, sumTriple]
    rw [getOrbit_sumPerm_inl_deceq]
    intro hmem
    rcases List.mem_map.mp hmem with ⟨x, _, heq⟩
    cases heq
  have hmerge := swapCompRight_merge_orbit cut.capSumTriple.f darts_cap h_all_cap
    (Nat.le_refl _) ha0_not_v0
  dsimp only at hmerge
  have hbase_f_eq : T_base.f = swapCompRight cut.capSumTriple.f a0_sum v0_sum := rfl
  have hbase_len : (@getOrbit _ (@Sum.instBEq _ _ _ _) T_base.f darts_cap.length v0_sum).length = La + k := by
    rw [@getOrbit_beq_congr _ (@Sum.instBEq _ _ _ _) bCap
      (fun u v => (sum_instBEq_iff_eq u v).trans (deceq_beq_iff_eq u v).symm)]
    rw [hbase_f_eq, hmerge.2.2.2.2, ha0_orb_len, hv0_orb_len]
  have hiter_pos : ∀ {m : Nat} (hm1 : 1 ≤ m) (hmk : m < k),
      Perm.iter T_base.f (cut.posL darts h_all m) v0_sum =
        Sum.inl ⟨cut.cutDart ⟨m, by omega⟩, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn _⟩ := by
    intro m hm1 hmk
    have hpos1 : 1 ≤ cut.posL darts h_all m := by
      have hlt := cut.posL_strictMono darts h_all (m := 0) (n := m) (by omega)
      dsimp [FaceCycleCut.posL] at hlt; omega
    have hpos_lt : cut.posL darts h_all m < La :=
      cut.posL_strictMono darts h_all hmk
    rw [hbase_f_eq, hmerge.2.1 (cut.posL darts h_all m) hpos1 (by rw [ha0_orb_len]; exact Nat.le_of_lt hpos_lt)]
    dsimp only [a0_sum, FaceCycleCut.capSumTriple, sumTriple]
    rw [sumPerm_iter_inl]
    congr 1; apply Subtype.ext
    dsimp only [FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
    rw [restrictPermPred_iter]
    rw [cut.uncoupleTriple_iter_posL darts h_all m]
    congr 1; apply Fin.ext; exact Nat.mod_eq_of_lt hmk
  have hiter_snd : ∀ {s : Nat} (hs1 : 1 ≤ s) (hsk : s ≤ k - 1),
      Perm.iter T_base.f (La + s) v0_sum = Sum.inr ⟨k - s, by omega⟩ := by
    intro s hs1 hsk
    rw [hbase_f_eq, ← ha0_orb_len, hmerge.2.2.1 s hs1 (by rw [hv0_orb_len]; omega)]
    dsimp only [v0_sum, FaceCycleCut.capSumTriple, sumTriple]
    rw [sumPerm_iter_inr, singleCycleTriple_iter_f_from_zero (by omega) hs1 (by omega)]
    congr 1; apply Fin.ext; dsimp
    exact Nat.mod_eq_of_lt (by omega)
  have hpw : List.Pairwise (fun x y : Nat × Nat => y.fst < x.fst ∧ x.snd < y.snd) specs := by
    dsimp only [specs, FaceCycleCut.capSpecs]
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [List.length_map, List.length_finRange] at hi hj
    simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
    refine ⟨?_, by omega⟩
    exact cut.posL_strictMono darts h_all (by omega)
  have hbnd : ∀ pq ∈ specs, 1 ≤ pq.fst ∧ pq.fst < pq.snd ∧ pq.snd < La + k := by
    intro pq hpq
    rcases List.mem_map.mp hpq with ⟨i, _, rfl⟩
    dsimp only
    have hi := i.isLt
    have h1 : 1 ≤ cut.posL darts h_all (k - 1 - i.val) := by
      have hlt := cut.posL_strictMono darts h_all (m := 0) (n := k - 1 - i.val) (by omega)
      dsimp [FaceCycleCut.posL] at hlt; omega
    have hltLa : cut.posL darts h_all (k - 1 - i.val) < La :=
      cut.posL_strictMono darts h_all (by omega)
    omega
  have hfix : ∀ pq ∈ specs,
      T_base.e.f (Perm.iter T_base.f pq.fst v0_sum) = Perm.iter T_base.f pq.fst v0_sum ∧
      T_base.e.f (Perm.iter T_base.f pq.snd v0_sum) = Perm.iter T_base.f pq.snd v0_sum := by
    intro pq hpq
    rcases List.mem_map.mp hpq with ⟨i, _, rfl⟩
    dsimp only
    have hi := i.isLt
    have hf1 := hiter_pos (m := k - 1 - i.val) (by omega) (by omega)
    have hf2 := hiter_snd (s := 1 + i.val) (by omega) (by omega)
    have ha_fix : cut.capSumTriple.e.f a0_sum = a0_sum := by
      dsimp only [a0_sum, FaceCycleCut.capSumTriple, sumTriple, sumPerm, Sum.map,
        FaceCycleCut.capSingleVertex_TL, restrictTriplePred, restrictPermPred,
        Sum.elim, Function.comp_def]
      congr 1; apply Subtype.ext
      exact (uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut).2.2.2.2.2.2.2.2.1 ⟨0, by omega⟩ |>.1
    have hv_fix : cut.capSumTriple.e.f v0_sum = v0_sum := rfl
    have hne_a0 : Sum.inl (⟨cut.cutDart ⟨k - 1 - i.val, by omega⟩,
        cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn _⟩ :
        { d : H.Dart // cut.capSingleVertex_DL d }) ≠ a0_sum := by
      intro heq
      have hsub := congrArg Subtype.val (Sum.inl.inj heq)
      have hfin := cut.cut_inj darts h_all hsub
      have := congrArg Fin.val hfin
      dsimp [a0'] at this
      omega
    have hne_v0 : Sum.inr (⟨k - (1 + i.val), by omega⟩ : Fin k) ≠ v0_sum := by
      intro heq
      have := congrArg Fin.val (Sum.inr.inj heq)
      dsimp [v0_sum] at this
      omega
    refine ⟨?_, ?_⟩
    · rw [hf1]
      change (coupleEdge cut.capSumTriple a0_sum v0_sum).e.f _ = _
      rw [coupleEdge_e_of_ne cut.capSumTriple ha_fix hv_fix hne_a0 (fun h => by dsimp only [v0_sum] at h; cases h)]
      dsimp only [FaceCycleCut.capSumTriple, sumTriple, sumPerm, Sum.map,
        FaceCycleCut.capSingleVertex_TL, restrictTriplePred, restrictPermPred,
        Sum.elim, Function.comp_def]
      congr 1; apply Subtype.ext
      exact (uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut).2.2.2.2.2.2.2.2.1
        ⟨k - 1 - i.val, by omega⟩ |>.1
    · rw [show cut.posL darts h_all k + 1 + i.val = La + (1 + i.val) by dsimp only [La]; omega, hf2]
      change (coupleEdge cut.capSumTriple a0_sum v0_sum).e.f _ = _
      rw [coupleEdge_e_of_ne cut.capSumTriple ha_fix hv_fix (fun h => by dsimp only [a0_sum] at h; cases h) hne_v0]
      rfl
  have hspecs_i : ∀ i : Nat, ∀ hi : i < specs.length,
      Perm.iter T_base.f specs[i].fst v0_sum =
        Sum.inl ⟨cut.cutDart ⟨k - 1 - i, by have := cut.hk; simp [specs, FaceCycleCut.capSpecs] at hi; omega⟩,
          cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn _⟩ ∧
      Perm.iter T_base.f specs[i].snd v0_sum =
        Sum.inr ⟨k - 1 - i, by have := cut.hk; simp [specs, FaceCycleCut.capSpecs] at hi; omega⟩ := by
    intro i hi
    have hi' : i < k - 1 := by simpa [specs, FaceCycleCut.capSpecs] using hi
    simp only [specs, FaceCycleCut.capSpecs, List.getElem_map, List.getElem_finRange, Fin.val_cast]
    refine ⟨hiter_pos (by omega) (by omega), ?_⟩
    have hf2 := hiter_snd (s := 1 + i) (by omega) (by omega)
    rw [show La + 1 + i = La + (1 + i) by omega, hf2]
    congr 1; apply Fin.ext; dsimp; omega
  exact ⟨hbase_len, hpw, hbnd, hfix, hspecs_i⟩

/-- Exact edge permutation, involutivity, and fixed-point-freeness of `capSingleVertexTriple`. -/
theorem FaceCycleCut.capSingleVertexTriple_edge_spec {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) :
    let T_cap := cut.capSingleVertexTriple darts h_all
    T_cap.n = cut.capSumTriple.n ∧
    (∀ m : Fin k,
      T_cap.e.f (Sum.inl ⟨cut.cutDart m, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn m⟩) = Sum.inr m ∧
      T_cap.e.f (Sum.inr m) = Sum.inl ⟨cut.cutDart m, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn m⟩) ∧
    (∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      (∀ m : Fin k, d ≠ cut.cutDart m) →
      ∃ hdn : cut.capSingleVertex_DL (H.edge.f d),
        T_cap.e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩) ∧
    (∀ x : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k, T_cap.e.f (T_cap.e.f x) = x) := by
  intro T_cap
  have hk := cut.hk
  have hcomp := cut.capSingleVertexDarts_nodup_complete darts h_nd h_all
  dsimp only at hcomp
  rcases hcomp with ⟨_, h_all_cap, _, _, _, _, _, _⟩
  have hok := cut.capSingleVertex_specs_ok darts h_nd h_all h_planar h_conn
  dsimp only at hok
  rcases hok with ⟨hbase_len, hpw, hbnd, hfix, hspecs_i⟩
  let v0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k := Sum.inr ⟨0, by omega⟩
  let a0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k :=
    Sum.inl ⟨cut.cutDart ⟨0, by omega⟩, reachEN_refl _ _ _⟩
  let bCap : BEq ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) := @instBEqOfDecidableEq _ _
  let bSum : BEq ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) := Sum.instBEq
  have hbase_len_deceq : (@getOrbit _ bCap cut.capBaseTriple.f
      (cut.capSingleVertexDarts darts).length v0_sum).length =
      cut.posL darts h_all k + k := by
    rw [← @getOrbit_beq_congr _ bSum bCap
      (fun u v => (sum_instBEq_iff_eq u v).trans (deceq_beq_iff_eq u v).symm)]
    exact hbase_len
  have hnest := coupleNestedPairs_spec cut.capBaseTriple (cut.capSingleVertexDarts darts)
    h_all_cap (Nat.le_refl _) v0_sum (cut.capSpecs darts h_all)
    hpw (fun pq hpq => by
      rcases hbnd pq hpq with ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [hbase_len_deceq]; exact h3) hfix
  dsimp only at hnest
  have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have ha0_fix : cut.capSumTriple.e.f a0_sum = a0_sum := by
    dsimp only [a0_sum, FaceCycleCut.capSumTriple, sumTriple, sumPerm, Sum.map,
      FaceCycleCut.capSingleVertex_TL, restrictTriplePred, restrictPermPred,
      Sum.elim, Function.comp_def]
    congr 1; apply Subtype.ext
    exact (hsep.2.2.2.2.2.2.2.2.1 ⟨0, by omega⟩).1
  have hv0_fix : cut.capSumTriple.e.f v0_sum = v0_sum := rfl
  have h_not_in_specs : ∀ (x : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k),
      (x = a0_sum ∨ x = v0_sum ∨
        (∃ d hd, x = Sum.inl ⟨d, hd⟩ ∧ ∀ m : Fin k, d ≠ cut.cutDart m)) →
      ∀ pq ∈ cut.capSpecs darts h_all,
        x ≠ Perm.iter cut.capBaseTriple.f pq.fst v0_sum ∧
        x ≠ Perm.iter cut.capBaseTriple.f pq.snd v0_sum := by
    intro x hx pq hpq
    rcases List.mem_iff_getElem.mp hpq with ⟨i, hi, rfl⟩
    have hsi := hspecs_i i hi
    rw [hsi.1, hsi.2]
    rcases hx with rfl | rfl | ⟨d, hd, rfl, hnot⟩
    · refine ⟨fun h => ?_, (fun h => by dsimp only [a0_sum] at h; cases h)⟩
      have hi' : i < k - 1 := by simpa [FaceCycleCut.capSpecs] using hi
      have hfin := cut.cut_inj darts h_all (congrArg Subtype.val (Sum.inl.inj h))
      simp only [Fin.mk.injEq] at hfin
      omega
    · refine ⟨(fun h => by dsimp only [v0_sum] at h; cases h), fun h => ?_⟩
      have hi' : i < k - 1 := by simpa [FaceCycleCut.capSpecs] using hi
      have hv := congrArg Fin.val (Sum.inr.inj h)
      dsimp [v0_sum] at hv; omega
    · refine ⟨fun h => hnot _ (congrArg Subtype.val (Sum.inl.inj h)), (fun h => by cases h)⟩
  have hTn : T_cap.n = cut.capSumTriple.n := by
    rw [show T_cap = coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all)) from rfl]
    rw [hnest.1]; rfl
  have h_bdy : ∀ m : Fin k,
      T_cap.e.f (Sum.inl ⟨cut.cutDart m, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn m⟩) = Sum.inr m ∧
      T_cap.e.f (Sum.inr m) = Sum.inl ⟨cut.cutDart m, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn m⟩ := by
    intro m
    by_cases hm0 : m.val = 0
    · have hm_eq : m = ⟨0, by omega⟩ := Fin.ext hm0
      rw [hm_eq]
      dsimp only [T_cap, FaceCycleCut.capSingleVertexTriple]
      rw [hnest.2.1 a0_sum (h_not_in_specs a0_sum (Or.inl rfl)),
        hnest.2.1 v0_sum (h_not_in_specs v0_sum (Or.inr (Or.inl rfl)))]
      exact ⟨coupleEdge_e_left cut.capSumTriple ha0_fix hv0_fix,
        coupleEdge_e_right cut.capSumTriple ha0_fix hv0_fix⟩
    · let i := k - 1 - m.val
      have hi : i < (cut.capSpecs darts h_all).length := by
        simp [FaceCycleCut.capSpecs]; omega
      have hsi := hspecs_i i hi
      have hmem : (cut.capSpecs darts h_all)[i]'hi ∈ cut.capSpecs darts h_all := List.getElem_mem hi
      have hpair := hnest.2.2.1 _ hmem
      have hm_fin : (⟨k - 1 - i, by simp [FaceCycleCut.capSpecs] at hi; omega⟩ : Fin k) = m := by
        apply Fin.ext; dsimp [i]; omega
      rw [hsi.1, hsi.2, hm_fin] at hpair
      exact hpair
  have h_interior : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      (∀ m : Fin k, d ≠ cut.cutDart m) →
      ∃ hdn : cut.capSingleVertex_DL (H.edge.f d),
        T_cap.e.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩ := by
    intro d hd hnot
    have hnot_edge : ∀ m : Fin k, d ≠ H.edge.f (cut.cutDart m) := by
      intro m heq
      exact cut.capSingleVertex_not_DL_edge_cut darts h_nd h_all h_planar h_conn m (heq ▸ hd)
    have he_eq : cut.uncoupleTriple.e.f d = H.edge.f d :=
      (hsep.2.2.2.2.2.2.2.2.2.1 d (fun m => ⟨hnot m, hnot_edge m⟩)).1
    have hdn : cut.capSingleVertex_DL (H.edge.f d) := by
      rw [← he_eq]
      exact (cut.capSingleVertex_DL_e d).mp hd
    refine ⟨hdn, ?_⟩
    change (coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all))).e.f
      (Sum.inl ⟨d, hd⟩) = _
    rw [hnest.2.1 _ (h_not_in_specs _ (Or.inr (Or.inr ⟨d, hd, rfl, hnot⟩)))]
    have hne_a : (Sum.inl ⟨d, hd⟩ : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) ≠ a0_sum :=
      fun h => hnot ⟨0, by omega⟩ (congrArg Subtype.val (Sum.inl.inj h))
    change (coupleEdge cut.capSumTriple a0_sum v0_sum).e.f (Sum.inl ⟨d, hd⟩) = _
    rw [coupleEdge_e_of_ne cut.capSumTriple ha0_fix hv0_fix hne_a
      (fun h => by dsimp only [v0_sum] at h; cases h)]
    dsimp only [FaceCycleCut.capSumTriple, sumTriple, sumPerm, Sum.map,
      FaceCycleCut.capSingleVertex_TL, restrictTriplePred, restrictPermPred,
      Sum.elim, Function.comp_def]
    congr 1; apply Subtype.ext; exact he_eq
  have h_invol : ∀ x : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k, T_cap.e.f (T_cap.e.f x) = x := by
    intro x
    cases x with
    | inr m =>
      rw [(h_bdy m).2, (h_bdy m).1]
    | inl dsub =>
      rcases dsub with ⟨d, hd⟩
      by_cases hcut : ∃ m : Fin k, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        rw [(h_bdy m).1, (h_bdy m).2]
      · have hnot : ∀ m : Fin k, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
        rcases h_interior d hd hnot with ⟨hdn, h1⟩
        have hnot_ed : ∀ m : Fin k, H.edge.f d ≠ cut.cutDart m := by
          intro m heq
          have hd_eq : d = H.edge.f (cut.cutDart m) := by rw [← H.edge_involution d, heq]
          exact cut.capSingleVertex_not_DL_edge_cut darts h_nd h_all h_planar h_conn m (hd_eq ▸ hd)
        rcases h_interior (H.edge.f d) hdn hnot_ed with ⟨hdnn, h2⟩
        rw [h1, h2]
        congr 1; apply Subtype.ext; exact H.edge_involution d
  exact ⟨hTn, h_bdy, h_interior, h_invol⟩

/-- Helper lemma proving involutivity of `capSingleVertexTriple.e` for `tripleToHypermap`. -/
theorem FaceCycleCut.capSingleVertexTriple_invol {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) :
    ∀ x : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k,
      (cut.capSingleVertexTriple darts h_all).e.f
        ((cut.capSingleVertexTriple darts h_all).e.f x) = x :=
  (cut.capSingleVertexTriple_edge_spec darts h_nd h_all h_planar h_conn).2.2.2

/-- **Single-Vertex Capped Hypermap `H_cap`** on `{ d ∈ D_L } ⊕ Fin k`. -/
@[reducible] noncomputable def FaceCycleCut.capSingleVertexHypermap {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) : Hypermap where
  Dart := { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k
  edge := (cut.capSingleVertexTriple darts h_all).e
  node := (cut.capSingleVertexTriple darts h_all).n
  face := (cut.capSingleVertexTriple darts h_all).f
  edge_involution := cut.capSingleVertexTriple_invol darts h_nd h_all h_planar h_conn
  edge_node_face_id := (cut.capSingleVertexTriple darts h_all).enf_id

private theorem sub_lt_swap_jcs {k a j : Nat} (_hk : 2 ≤ k) (ha : a < k) (hj : j < k - 1 - a) :
    a + 1 ≤ k - 1 - j ∧ k - 1 - j < k :=
  ⟨by omega, by omega⟩

theorem FaceCycleCut.capSingleVertexHypermap_face_ring {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) (m : Fin k)
    (x : (cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn).Dart) :
    x ∈ getOrbit (cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn).face
        (cut.capSingleVertexDarts darts).length (Sum.inr m) ↔
      x = Sum.inr m ∨
        ∃ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
          x = Sum.inl ⟨d, hd⟩ ∧
            cut.inArcL darts h_all ⟨(m.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d := by
  have hk := cut.hk
  let darts_cap := cut.capSingleVertexDarts darts
  have hcomp := cut.capSingleVertexDarts_nodup_complete darts h_nd h_all
  dsimp only at hcomp
  rcases hcomp with ⟨_, h_all_cap, _, dartsL, _, _, hlen_cap, hL_le⟩
  have hok := cut.capSingleVertex_specs_ok darts h_nd h_all h_planar h_conn
  dsimp only at hok
  rcases hok with ⟨hbase_len, hpw, hbnd, hfix, hspecs_i⟩
  let La := cut.posL darts h_all k
  let a0' : { d : H.Dart // cut.capSingleVertex_DL d } :=
    ⟨cut.cutDart ⟨0, by omega⟩, reachEN_refl _ _ _⟩
  let a0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k := Sum.inl a0'
  let v0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k := Sum.inr ⟨0, by omega⟩
  let bCap : BEq ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) := @instBEqOfDecidableEq _ _
  let bSum : BEq ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) := Sum.instBEq
  have hbase_len_deceq : (@getOrbit _ bCap cut.capBaseTriple.f
      darts_cap.length v0_sum).length = La + k := by
    rw [← @getOrbit_beq_congr _ bSum bCap
      (fun u v => (sum_instBEq_iff_eq u v).trans (deceq_beq_iff_eq u v).symm)]
    exact hbase_len
  have hnest := coupleNestedPairs_spec cut.capBaseTriple darts_cap
    h_all_cap (Nat.le_refl _) v0_sum (cut.capSpecs darts h_all)
    hpw (fun pq hpq => by
      rcases hbnd pq hpq with ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [hbase_len_deceq]; exact h3) hfix
  dsimp only at hnest
  have h_sub_orb_len : (@getOrbit _ bCap cut.capSumTriple.f darts_cap.length a0_sum).length = La := by
    have hsub_len : (cut.capDartsL_sub darts).length ≤ darts.length := by
      simp only [FaceCycleCut.capSingleVertexDarts, List.length_append, List.length_map,
        List.length_finRange] at hlen_cap
      omega
    have hsub_mem : ∀ y : { d : H.Dart // cut.capSingleVertex_DL d }, y ∈ cut.capDartsL_sub darts := by
      intro y
      letI decDL : DecidablePred cut.capSingleVertex_DL := fun _ => Classical.propDecidable _
      exact (@mem_predDarts_iff H.Dart cut.capSingleVertex_DL decDL darts y).mpr (h_all y.val)
    dsimp only [a0_sum, FaceCycleCut.capSumTriple, sumTriple]
    rw [getOrbit_sumPerm_inl_gen deceq_beq_iff_eq (b1 := inferInstance)
      (fun u v => beq_iff_eq),
      List.length_map]
    dsimp only [FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
    let bSub : BEq { d : H.Dart // cut.capSingleVertex_DL d } := inferInstance
    let bSubDec : BEq { d : H.Dart // cut.capSingleVertex_DL d } := @instBEqOfDecidableEq _ _
    have hb_iff : ∀ u v : { d : H.Dart // cut.capSingleVertex_DL d },
        bSub.beq u v = true ↔ bSubDec.beq u v = true :=
      fun u v => beq_iff_eq.trans (deceq_beq_iff_eq u v).symm
    have h_inv_f : ∀ d, cut.capSingleVertex_DL d ↔ cut.capSingleVertex_DL (cut.uncoupleTriple.f.f d) := by
      intro d
      have he := cut.capSingleVertex_DL_e (cut.uncoupleTriple.n.f (cut.uncoupleTriple.f.f d))
      have hn := cut.capSingleVertex_DL_n (cut.uncoupleTriple.f.f d)
      rw [cut.uncoupleTriple.enf_id d] at he
      exact (Iff.trans hn he).symm
    change (@getOrbit _ bSub (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f)
      darts_cap.length a0').length = La
    have h_orb_eq : @getOrbit _ bSub (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) darts_cap.length a0' =
        @getOrbit _ bSub (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) darts.length a0' := by
      rw [@getOrbit_beq_congr _ bSub bSubDec hb_iff
            (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) darts_cap.length a0',
          @getOrbit_beq_congr _ bSub bSubDec hb_iff
            (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) darts.length a0']
      have h1 := getOrbit_fuel_eq_of_complete
        (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f)
        (cut.capDartsL_sub darts) hsub_mem a0' (fuel := darts_cap.length) (by
          change (cut.capDartsL_sub darts).length ≤
            ((cut.capDartsL_sub darts).map Sum.inl ++ (List.finRange k).map Sum.inr).length
          rw [List.length_append, List.length_map]
          exact Nat.le_add_right _ _)
      have h2 := getOrbit_fuel_eq_of_complete
        (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f)
        (cut.capDartsL_sub darts) hsub_mem a0' hsub_len
      exact h1.trans h2.symm
    rw [h_orb_eq, getOrbit_restrictPermPred_length]
    exact cut.uncoupleTriple_posL_orbit_length darts h_all (Nat.le_refl _)
  have ha0_not_v0 : ¬ v0_sum ∈ @getOrbit _ bCap cut.capSumTriple.f darts_cap.length a0_sum := by
    dsimp only [a0_sum, v0_sum, FaceCycleCut.capSumTriple, sumTriple]
    rw [getOrbit_sumPerm_inl_deceq]
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, _, heq⟩
    cases heq
  have hmerge := swapCompRight_merge_orbit cut.capSumTriple.f darts_cap h_all_cap
    (Nat.le_refl _) ha0_not_v0
  have h_pos_step_block : ∀ r : Nat, 1 ≤ r → r ≤ La →
      Perm.iter cut.capBaseTriple.f r v0_sum =
        Sum.inl ⟨Perm.iter cut.uncoupleTriple.f r (cut.cutDart ⟨0, by omega⟩),
          by
            have : ∀ s, cut.capSingleVertex_DL (Perm.iter cut.uncoupleTriple.f s (cut.cutDart ⟨0, by omega⟩)) := by
              intro s
              induction s with
              | zero => exact reachEN_refl _ _ _
              | succ s ih =>
                rw [Perm.iter_succ]
                exact reachEN_trans _ _ ih (reachEN_f_step cut.uncoupleTriple _)
            exact this r⟩ := by
    intro r hr1 hrLa
    change Perm.iter (swapCompRight cut.capSumTriple.f a0_sum v0_sum) r v0_sum = _
    rw [hmerge.2.1 r hr1 (by rw [h_sub_orb_len]; exact hrLa)]
    dsimp only [a0_sum, FaceCycleCut.capSumTriple, sumTriple]
    rw [sumPerm_iter_inl]
    congr 1; apply Subtype.ext
    dsimp only [FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
    exact restrictPermPred_iter cut.uncoupleTriple.f cut.capSingleVertex_DL _ r a0'
  change x ∈ @getOrbit _ bSum (cut.capSingleVertexTriple darts h_all).f darts_cap.length (Sum.inr m) ↔ _
  rw [@getOrbit_beq_congr _ bSum bCap (fun u v => (sum_instBEq_iff_eq u v).trans (deceq_beq_iff_eq u v).symm)]
  by_cases hm0 : m.val = 0
  · have hm_eq : m = ⟨0, by clear m hm0; omega⟩ := Fin.ext hm0
    subst hm_eq
    change x ∈ @getOrbit _ bCap (coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all))).f
        darts_cap.length v0_sum ↔ _
    rw [hnest.2.2.2.2.2.2.1]
    have hidx_last : k - 2 < (cut.capSpecs darts h_all).length := by
      simp [FaceCycleCut.capSpecs]; omega
    have hlast_mem : (cut.capSpecs darts h_all)[k - 2]'hidx_last ∈ cut.capSpecs darts h_all :=
      List.getElem_mem hidx_last
    have hlast_eq : (cut.capSpecs darts h_all)[k - 2]'hidx_last =
        (cut.posL darts h_all 1, La + k - 1) := by
      simp only [FaceCycleCut.capSpecs, List.getElem_map, List.getElem_finRange, Fin.val_cast]
      exact Prod.ext (congrArg (cut.posL darts h_all) (by omega)) (by omega)
    constructor
    · rintro ⟨r, hr_lt, h_avoid, rfl⟩
      rw [hbase_len_deceq] at hr_lt
      have hr_le1 : r ≤ cut.posL darts h_all 1 := by
        by_cases hgt : cut.posL darts h_all 1 < r
        · exfalso
          have h_not_mem := h_avoid _ hlast_mem
          rw [hlast_eq] at h_not_mem
          exact h_not_mem ⟨hgt, by omega⟩
        · omega
      by_cases hr0 : r = 0
      · subst hr0; left; rfl
      · right
        have hr1 : 1 ≤ r := by omega
        have hrLa : r ≤ La := Nat.le_trans hr_le1 (Nat.le_of_lt (cut.posL_strictMono darts h_all (m := 1) (n := k) (by omega)))
        rw [h_pos_step_block r hr1 hrLa]
        refine ⟨_, _, rfl, ?_⟩
        have hpos0 : cut.posL darts h_all 0 = 0 := rfl
        have hfin_eq : (⟨((⟨0, by omega⟩ : Fin k).val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) =
            ⟨(0 + 1) % k, Nat.mod_lt _ (by omega)⟩ := Fin.ext rfl
        rw [hfin_eq]
        exact (cut.inArcL_iff_posL_block darts h_all (m := 0) (by omega) _).mpr
          ⟨r, by rw [hpos0]; omega, hr_le1, rfl⟩
    · rintro (rfl | ⟨d, hd, rfl, hin⟩)
      · refine ⟨0, by rw [hbase_len_deceq]; omega, ?_, rfl⟩
        intro pq hpq
        rcases hbnd pq hpq with ⟨h1, _, _⟩
        omega
      · have hfin_eq : (⟨((⟨0, by omega⟩ : Fin k).val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) =
            ⟨(0 + 1) % k, Nat.mod_lt _ (by omega)⟩ := Fin.ext rfl
        rw [hfin_eq] at hin
        rcases (cut.inArcL_iff_posL_block darts h_all (m := 0) (by omega) d).mp hin with ⟨r, hr0, hr1, hr_eq⟩
        have hpos0 : cut.posL darts h_all 0 = 0 := rfl
        rw [hpos0] at hr0
        have hr1' : r ≤ cut.posL darts h_all 1 := by simpa [Nat.zero_add] using hr1
        have hrLa : r ≤ La := Nat.le_trans hr1' (Nat.le_of_lt (cut.posL_strictMono darts h_all (m := 1) (n := k) (by omega)))
        refine ⟨r, by rw [hbase_len_deceq]; omega, ?_, ?_⟩
        · intro pq hpq
          rcases List.mem_map.mp hpq with ⟨j, _, rfl⟩
          have hj_pos : cut.posL darts h_all 1 ≤ cut.posL darts h_all (k - 1 - j.val) := by
            have hj_le : 1 ≤ k - 1 - j.val := by have := j.isLt; omega
            by_cases heq : 1 = k - 1 - j.val
            · rw [← heq]; exact Nat.le_refl _
            · exact Nat.le_of_lt (cut.posL_strictMono darts h_all (by omega : 1 < k - 1 - j.val))
          dsimp only
          omega
        · rw [h_pos_step_block r hr0 hrLa]
          congr 1; exact Subtype.ext hr_eq
  · have hm_lt := m.isLt
    let i := k - 1 - m.val
    have hi : i < (cut.capSpecs darts h_all).length := by
      simp [FaceCycleCut.capSpecs]; omega
    have hi' : i < k - 1 := by simpa [FaceCycleCut.capSpecs] using hi
    have hsi := hspecs_i i hi
    have hm_k_sub : k - 1 - i = m.val := by
      dsimp [i]
      exact Nat.sub_sub_self (Nat.le_sub_of_add_le hm_lt)
    have hm_fin : (⟨k - 1 - i, by rw [hm_k_sub]; exact hm_lt⟩ : Fin k) = m :=
      Fin.ext hm_k_sub
    have h_inr_eq : Perm.iter cut.capBaseTriple.f (cut.capSpecs darts h_all)[i].snd v0_sum = Sum.inr m := by
      rw [hsi.2, hm_fin]
    have hpeel := hnest.2.2.2.2.2.2.2 i hi x
    rw [h_inr_eq] at hpeel
    change x ∈ @getOrbit _ bCap (coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all))).f
        darts_cap.length (Sum.inr m) ↔ _
    rw [hpeel]
    have hspec_i_eq : (cut.capSpecs darts h_all)[i]'hi =
        (cut.posL darts h_all m.val, La + 1 + i) := by
      simp only [FaceCycleCut.capSpecs, List.getElem_map, List.getElem_finRange, Fin.val_cast]
      exact Prod.ext (congrArg (cut.posL darts h_all) hm_k_sub) rfl
    constructor
    · rintro ⟨r, hlo, hhi, h_avoid, rfl⟩
      rw [hspec_i_eq] at hlo hhi
      by_cases hi0 : i = 0
      · have hm_k1 : m.val = k - 1 := by rw [← hm_k_sub, hi0, Nat.sub_zero]
        rw [hi0, Nat.add_zero] at hhi
        by_cases hrLa : r = La + 1
        · subst hrLa
          left
          rw [← show (cut.capSpecs darts h_all)[i].snd = La + 1 by rw [hspec_i_eq, hi0, Nat.add_zero]]
          exact h_inr_eq
        · right
          have hr_gt : cut.posL darts h_all m.val < r := hlo
          have hr_le : r ≤ La := by omega
          have hr1 : 1 ≤ r := by
            have := cut.posL_strictMono darts h_all (m := 0) (n := m.val) (by omega)
            dsimp [FaceCycleCut.posL] at this; omega
          rw [h_pos_step_block r hr1 hr_le]
          refine ⟨_, _, rfl, ?_⟩
          apply (cut.inArcL_iff_posL_block darts h_all m.isLt _).mpr
          refine ⟨r, hr_gt, by rw [show m.val + 1 = k by omega]; exact hr_le, rfl⟩
      · have hj_lt : i - 1 < i := by omega
        have hj_spec := List.getElem_mem (by omega : i - 1 < (cut.capSpecs darts h_all).length)
        have hj_eq : (cut.capSpecs darts h_all)[i - 1]'(by omega) =
            (cut.posL darts h_all (m.val + 1), La + i) := by
          simp only [FaceCycleCut.capSpecs, List.getElem_map, List.getElem_finRange, Fin.val_cast]
          exact Prod.ext (congrArg (cut.posL darts h_all) (by dsimp [i]; omega)) (by omega)
        by_cases hr_top : r = La + 1 + i
        · subst hr_top
          left
          rw [← show (cut.capSpecs darts h_all)[i].snd = La + 1 + i by rw [hspec_i_eq]]
          exact h_inr_eq
        · right
          have h_not_j := h_avoid (i - 1) hj_lt
          rw [hj_eq] at h_not_j
          have hr_le_next : r ≤ cut.posL darts h_all (m.val + 1) := by
            by_cases hgt : cut.posL darts h_all (m.val + 1) < r
            · exfalso; exact h_not_j ⟨hgt, by omega⟩
            · omega
          have hr1 : 1 ≤ r := by
            have := cut.posL_strictMono darts h_all (m := 0) (n := m.val) (by omega)
            dsimp [FaceCycleCut.posL] at this; omega
          have hr_le_La : r ≤ La := by
            by_cases hm_eq : m.val + 1 = k
            · rw [hm_eq] at hr_le_next; exact hr_le_next
            · exact Nat.le_trans hr_le_next (Nat.le_of_lt (cut.posL_strictMono darts h_all (by omega : m.val + 1 < k)))
          rw [h_pos_step_block r hr1 hr_le_La]
          refine ⟨_, _, rfl, ?_⟩
          exact (cut.inArcL_iff_posL_block darts h_all m.isLt _).mpr ⟨r, hlo, hr_le_next, rfl⟩
    · rintro (rfl | ⟨d, hd, rfl, hin⟩)
      · refine ⟨(cut.capSpecs darts h_all)[i].snd, ?_, Nat.le_refl _, ?_, h_inr_eq⟩
        · rw [hspec_i_eq]
          have hlt := cut.posL_strictMono darts h_all m.isLt
          dsimp only; omega
        · intro j hj hbad
          simp only [FaceCycleCut.capSpecs, List.getElem_map, List.getElem_finRange, Fin.val_cast] at hbad
          omega
      · rcases (cut.inArcL_iff_posL_block darts h_all m.isLt d).mp hin with ⟨r, hr_gt, hr_le, hr_eq⟩
        have hr1 : 1 ≤ r := by
          have := cut.posL_strictMono darts h_all (m := 0) (n := m.val) (by omega)
          dsimp [FaceCycleCut.posL] at this; omega
        have hr_le_La : r ≤ La := by
          by_cases hm_eq : m.val + 1 = k
          · rw [hm_eq] at hr_le; exact hr_le
          · exact Nat.le_trans hr_le (Nat.le_of_lt (cut.posL_strictMono darts h_all (by omega : m.val + 1 < k)))
        refine ⟨r, ?_, ?_, ?_, ?_⟩
        · rw [hspec_i_eq]; exact hr_gt
        · rw [hspec_i_eq]; dsimp only; omega
        · intro j hj
          simp only [FaceCycleCut.capSpecs, List.getElem_map, List.getElem_finRange, Fin.val_cast]
          have h_sw := sub_lt_swap_jcs hk hm_lt (show j < k - 1 - m.val from hj)
          have hj_gt : m.val + 1 ≤ k - 1 - j := h_sw.1
          have hj_lt_k : k - 1 - j < k := h_sw.2
          have hj_pos : cut.posL darts h_all (m.val + 1) ≤ cut.posL darts h_all (k - 1 - j) := by
            by_cases heq : m.val + 1 = k - 1 - j
            · rw [← heq]; exact Nat.le_refl _
            · exact Nat.le_of_lt (cut.posL_strictMono darts h_all (by omega : m.val + 1 < k - 1 - j))
          omega
        · rw [h_pos_step_block r hr1 hr_le_La]
          congr 1; exact Subtype.ext hr_eq

theorem FaceCycleCut.capSingleVertexHypermap_face_interior {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k)
    (d : H.Dart) (hd : cut.capSingleVertex_DL d)
    (h_nonring : ∀ i : Fin k, ¬ SameOrbit H.face (cut.ringFace i) d) :
    ∃ hfn : cut.capSingleVertex_DL (H.face.f d),
      (cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn).face.f (Sum.inl ⟨d, hd⟩) =
        Sum.inl ⟨H.face.f d, hfn⟩ := by
  have hk := cut.hk
  have hed := cut.capSingleVertexTriple_edge_spec darts h_nd h_all h_planar h_conn
  have hnot : ∀ m : Fin k, d ≠ cut.cutDart m := fun m h =>
    h_nonring m (by rw [h]; exact cut.h_a m)
  have hnot_ed : ∀ m : Fin k, H.edge.f d ≠ cut.cutDart m := fun m h =>
    cut.capSingleVertex_not_DL_edge_cut darts h_nd h_all h_planar h_conn m
      (by rw [← H.edge_involution d, h] at hd; exact hd)
  -- `H_cap.face.f = T_cap.n.inv ∘ T_cap.e.inv = T_cap.n.inv ∘ T_cap.e.f`
  have hf_eq := (cut.capSingleVertexTriple darts h_all).f_eq_n_inv_e_inv (Sum.inl ⟨d, hd⟩)
  have h_e_inv : (cut.capSingleVertexTriple darts h_all).e.inv (Sum.inl ⟨d, hd⟩) =
      (cut.capSingleVertexTriple darts h_all).e.f (Sum.inl ⟨d, hd⟩) := by
    have hinvol := hed.2.2.2 ((cut.capSingleVertexTriple darts h_all).e.inv (Sum.inl ⟨d, hd⟩))
    rw [(cut.capSingleVertexTriple darts h_all).e.right_inv] at hinvol
    exact hinvol.symm
  rcases hed.2.2.1 d hd hnot with ⟨hd_e, he_eval⟩
  have h_n_inv : ∀ y : { z : H.Dart // cut.capSingleVertex_DL z },
      ∃ hny : cut.capSingleVertex_DL (H.node.inv y.val),
        (cut.capSingleVertexTriple darts h_all).n.inv (Sum.inl y) =
          Sum.inl ⟨H.node.inv y.val, hny⟩ := by
    intro y
    have hTn := hed.1
    have hin := congrArg Perm.inv hTn
    have hev := congrFun hin (Sum.inl y)
    dsimp only [FaceCycleCut.capSumTriple, sumTriple, sumPerm, Sum.map,
      FaceCycleCut.capSingleVertex_TL, restrictTriplePred, restrictPermPred] at hev
    have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
    have hTn_H : ∀ z : H.Dart, cut.uncoupleTriple.n.inv z = H.node.inv z := fun z => by
      rw [hsep.1]
    refine ⟨?_, ?_⟩
    · have hhy := (cut.capSingleVertex_DL_n (cut.uncoupleTriple.n.inv y.val)).mpr
        (by rw [cut.uncoupleTriple.n.right_inv]; exact y.property)
      rwa [hTn_H] at hhy
    · rw [hev]
      dsimp only [Sum.elim, Function.comp_def]
      congr 1; apply Subtype.ext; exact hTn_H y.val
  rcases h_n_inv ⟨H.edge.f d, hd_e⟩ with ⟨hny, hn_eval⟩
  have hface_eq : H.node.inv (H.edge.f d) = H.face.f d := by
    have := H.hypermapToTriple.f_eq_n_inv_e_inv d
    dsimp [hypermapToTriple] at this
    have he_inv : H.edge.inv d = H.edge.f d := by
      have h := H.edge_involution (H.edge.inv d)
      rw [H.edge.right_inv] at h
      exact h.symm
    rw [he_inv] at this
    exact this.symm
  refine ⟨hface_eq ▸ hny, ?_⟩
  change (cut.capSingleVertexTriple darts h_all).f.f (Sum.inl ⟨d, hd⟩) = _
  rw [hf_eq, h_e_inv, he_eval, hn_eval]
  congr 1; apply Subtype.ext; exact hface_eq

private theorem nodup_finRange_jcs (m : Nat) : (List.finRange m).Nodup :=
  List.pairwise_iff_getElem.mpr fun i j hi hj hij heq => by
    simp only [List.getElem_finRange] at heq
    have hv := congrArg Fin.val heq
    dsimp at hv
    omega

theorem FaceCycleCut.capSingleVertexHypermap_node_dual_ring {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k) (m : Fin k) :
    let H_cap := cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn
    H_cap.node.f (Sum.inr m) = Sum.inr ⟨(m.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ ∧
    H_cap.dual.face.f (Sum.inr m) = Sum.inr ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ := by
  intro H_cap
  have hk := cut.hk
  have hed := cut.capSingleVertexTriple_edge_spec darts h_nd h_all h_planar h_conn
  have hnode_step : ∀ r : Fin k,
      H_cap.node.f (Sum.inr r) = Sum.inr ⟨(r.val + 1) % k, Nat.mod_lt _ (by omega)⟩ := by
    intro r
    have hTn : (cut.capSingleVertexTriple darts h_all).n.f = cut.capSumTriple.n.f :=
      congrArg Perm.f hed.1
    change (cut.capSingleVertexTriple darts h_all).n.f (Sum.inr r) = _
    rw [hTn]
    dsimp only [FaceCycleCut.capSumTriple, sumTriple, sumPerm, Sum.map, singleCycleTriple]
    rfl
  refine ⟨hnode_step m, ?_⟩
  let m_prev : Fin k := ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
  have hm_next : (⟨(m_prev.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = m := by
    apply Fin.ext; dsimp [m_prev]; exact mod_pred_succ hk m.val m.isLt
  have hf_prev : H_cap.node.f (Sum.inr m_prev) = Sum.inr m := by
    rw [hnode_step m_prev, hm_next]
  change H_cap.node.inv (Sum.inr m) = Sum.inr m_prev
  rw [← hf_prev, H_cap.node.left_inv]

/-- **Complete Specification of Single-Vertex Cycle Capping (`capSingleVertex_spec`)**:
    `H_cap := cut.capSingleVertexHypermap ...` is a connected planar bridgeless hypermap on
    `|D_L| + k` darts, preserving `H.node` on `D_L`, collapsing the boundary into a degree-`k`
    vertex on `Fin k` (whose `H_cap.dual.face` steps decrement mod `k`), preserving all interior
    faces on `D_L`, and mapping each ring dart `Sum.inr m` to face `{Sum.inr m} ∪ Sum.inl '' inArcL (m+1)`. -/
theorem FaceCycleCut.capSingleVertex_spec {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts darts.length)
    {k : Nat} (cut : FaceCycleCut H k) :
    let H_cap := cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn
    let darts_cap := cut.capSingleVertexDarts darts
    darts_cap.Nodup ∧ (∀ x : H_cap.Dart, x ∈ darts_cap) ∧ darts_cap ≠ [] ∧
    (∃ dartsL : List H.Dart, dartsL.Nodup ∧ (∀ d, d ∈ dartsL ↔ cut.capSingleVertex_DL d) ∧
      darts_cap.length = dartsL.length + k ∧ dartsL.length ≤ darts.length) ∧
    H_cap.isPlanar darts_cap.length darts_cap = true ∧
    H_cap.numComponents darts_cap.length darts_cap = 1 ∧
    Math.Hypermap.isBridgeless H_cap darts_cap darts_cap.length ∧
    (∀ m : Fin k,
      H_cap.edge.f (Sum.inl ⟨cut.cutDart m, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn m⟩) = Sum.inr m ∧
      H_cap.edge.f (Sum.inr m) = Sum.inl ⟨cut.cutDart m, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn m⟩) ∧
    (∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d), (∀ m : Fin k, d ≠ cut.cutDart m) →
      ∃ hdn : cut.capSingleVertex_DL (H.edge.f d),
        H_cap.edge.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.edge.f d, hdn⟩) ∧
    (∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      ∃ hdn : cut.capSingleVertex_DL (H.node.f d),
        H_cap.node.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.node.f d, hdn⟩) ∧
    (∀ m : Fin k,
      H_cap.node.f (Sum.inr m) = Sum.inr ⟨(m.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ ∧
      H_cap.dual.face.f (Sum.inr m) = Sum.inr ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩) ∧
    (∀ m : Fin k, ∀ x : H_cap.Dart,
      x ∈ getOrbit H_cap.face darts_cap.length (Sum.inr m) ↔
        x = Sum.inr m ∨ ∃ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
          x = Sum.inl ⟨d, hd⟩ ∧
            cut.inArcL darts h_all ⟨(m.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d) ∧
    (∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      (∀ i : Fin k, ¬ SameOrbit H.face (cut.ringFace i) d) →
      ∃ hfn : cut.capSingleVertex_DL (H.face.f d),
        H_cap.face.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.face.f d, hfn⟩) := by
  intro H_cap darts_cap
  have hk := cut.hk
  have hcomp := cut.capSingleVertexDarts_nodup_complete darts h_nd h_all
  dsimp only at hcomp
  rcases hcomp with ⟨h_nd_cap, h_all_cap, h_ne_cap, dartsL, hL_nd, hL_iff, hlen_cap, hL_le⟩
  have hok := cut.capSingleVertex_specs_ok darts h_nd h_all h_planar h_conn
  dsimp only at hok
  rcases hok with ⟨hbase_len, hpw, hbnd, hfix, _⟩
  have hed := cut.capSingleVertexTriple_edge_spec darts h_nd h_all h_planar h_conn
  have hno_fix_H := edge_no_fix_of_isBridgeless H darts h_all h_bridgeless
  have hno_fix_cap : ∀ x : H_cap.Dart, (cut.capSingleVertexTriple darts h_all).e.f x ≠ x := by
    intro x
    cases x with
    | inr m => rw [(hed.2.1 m).2]; intro h; cases h
    | inl dsub =>
      rcases dsub with ⟨d, hd⟩
      by_cases hcut : ∃ m : Fin k, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        rw [(hed.2.1 m).1]; intro h; cases h
      · have hnot : ∀ m : Fin k, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
        rcases hed.2.2.1 d hd hnot with ⟨hdn, heq⟩
        rw [heq]
        intro h
        exact hno_fix_H d (congrArg Subtype.val (Sum.inl.inj h))
  have hsep := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  letI decDL : DecidablePred cut.capSingleVertex_DL := fun _ => Classical.propDecidable _
  let dartsL_sub := cut.capDartsL_sub darts
  have hsub_nd : dartsL_sub.Nodup :=
    @nodup_predDarts H.Dart cut.capSingleVertex_DL decDL darts h_nd
  have hsub_mem : ∀ y : { d : H.Dart // cut.capSingleVertex_DL d }, y ∈ dartsL_sub := fun y =>
    (@mem_predDarts_iff H.Dart cut.capSingleVertex_DL decDL darts y).mpr (h_all y.val)
  have hsub_len : dartsL_sub.length = dartsL.length := by
    simp only [FaceCycleCut.capSingleVertexDarts, List.length_append, List.length_map,
      List.length_finRange] at hlen_cap
    change dartsL_sub.length + k = dartsL.length + k at hlen_cap
    omega
  have hgen_TL : genusDeficit cut.capSingleVertex_TL darts_cap.length dartsL_sub = 0 := by
    have hsplit := genusDeficit_pred_split cut.uncoupleTriple darts.length darts h_nd h_all (Nat.le_refl _)
      cut.capSingleVertex_DL cut.capSingleVertex_DL_e cut.capSingleVertex_DL_n
    rw [hsep.2.2.1] at hsplit
    have hnd1 := nodup_predDarts cut.capSingleVertex_DL h_nd
    have hmem1 : ∀ y, y ∈ predDarts cut.capSingleVertex_DL darts :=
      fun y => (mem_predDarts_iff cut.capSingleVertex_DL darts y).mpr (h_all y.val)
    have hle1 : (predDarts cut.capSingleVertex_DL darts).length ≤ darts.length := by
      have : List.map Subtype.val (predDarts cut.capSingleVertex_DL darts) =
          darts.filter (fun d => decide (cut.capSingleVertex_DL d)) :=
        map_predDarts cut.capSingleVertex_DL darts
      have hlen_f := congrArg List.length this
      simp only [List.length_map] at hlen_f
      rw [hlen_f]
      exact filter_length_le _ _
    have hgn1 := genusDeficit_nonneg
      (restrictTriplePred cut.uncoupleTriple cut.capSingleVertex_DL cut.capSingleVertex_DL_e cut.capSingleVertex_DL_n)
      (predDarts cut.capSingleVertex_DL darts) hnd1 hmem1 hle1
    have hnd2 := nodup_predDarts (fun d => ¬ cut.capSingleVertex_DL d) h_nd
    have hmem2 : ∀ y, y ∈ predDarts (fun d => ¬ cut.capSingleVertex_DL d) darts :=
      fun y => (mem_predDarts_iff (fun d => ¬ cut.capSingleVertex_DL d) darts y).mpr (h_all y.val)
    have hle2 : (predDarts (fun d => ¬ cut.capSingleVertex_DL d) darts).length ≤ darts.length := by
      have : List.map Subtype.val (predDarts (fun d => ¬ cut.capSingleVertex_DL d) darts) =
          darts.filter (fun d => decide (¬ cut.capSingleVertex_DL d)) :=
        map_predDarts (fun d => ¬ cut.capSingleVertex_DL d) darts
      have hlen_f := congrArg List.length this
      simp only [List.length_map] at hlen_f
      rw [hlen_f]
      exact filter_length_le _ _
    have hgn2 := genusDeficit_nonneg
      (restrictTriplePred cut.uncoupleTriple (fun d => ¬ cut.capSingleVertex_DL d)
        (fun d => ⟨fun h nef => h ((cut.capSingleVertex_DL_e d).mpr nef), fun h d_ok => h ((cut.capSingleVertex_DL_e d).mp d_ok)⟩)
        (fun d => ⟨fun h nnf => h ((cut.capSingleVertex_DL_n d).mpr nnf), fun h d_ok => h ((cut.capSingleVertex_DL_n d).mp d_ok)⟩))
      (predDarts (fun d => ¬ cut.capSingleVertex_DL d) darts) hnd2 hmem2 hle2
    have hg0 : genusDeficit cut.capSingleVertex_TL darts.length (predDarts cut.capSingleVertex_DL darts) = 0 := by
      change genusDeficit
          (restrictTriplePred cut.uncoupleTriple cut.capSingleVertex_DL cut.capSingleVertex_DL_e cut.capSingleVertex_DL_n)
          darts.length (predDarts cut.capSingleVertex_DL darts) = 0
      omega
    calc genusDeficit cut.capSingleVertex_TL darts_cap.length dartsL_sub
        = genusDeficit cut.capSingleVertex_TL darts.length (predDarts cut.capSingleVertex_DL darts) :=
          genusDeficit_eq_of_complete cut.capSingleVertex_TL dartsL_sub
            (predDarts cut.capSingleVertex_DL darts) hsub_nd hsub_mem hnd1 hmem1
            (by rw [hsub_len, hlen_cap]; omega) hle1
      _ = 0 := hg0
  let a0' : { d : H.Dart // cut.capSingleVertex_DL d } :=
    ⟨cut.cutDart ⟨0, by omega⟩, reachEN_refl _ _ _⟩
  have hc_TL : countRelClasses (ReachEN cut.capSingleVertex_TL.e cut.capSingleVertex_TL.n) dartsL_sub = 1 := by
    apply countRelClasses_eq_one_of_forall _ a0'
    · intro x _
      exact reachEN_lift_restrictTriple cut.uncoupleTriple cut.capSingleVertex_DL
        cut.capSingleVertex_DL_e cut.capSingleVertex_DL_n (reachEN_refl _ _ _) x.property x.property
    · intro hemp
      have hm := hsub_mem a0'
      rw [hemp] at hm
      cases hm
    · intro _ _ h; exact reachEN_symm _ _ h
    · intro _ _ _ h1 h2; exact reachEN_trans _ _ h1 h2
  have htv := singleCycleTriple_spec k (by omega)
  dsimp only at htv
  have htv_gen : genusDeficit (singleCycleTriple k (by omega)) darts_cap.length (List.finRange k) = 0 := by
    have h_le_fin : (List.finRange k).length ≤ darts_cap.length := by
      rw [List.length_finRange, hlen_cap]
      omega
    rw [genusDeficit_fuel_eq (singleCycleTriple k (by omega)) (List.finRange k)
      (fun i => List.mem_finRange i) (fuel2 := k) h_le_fin (by simp only [List.length_finRange]; omega)]
    exact htv.1
  have hsum := sumTriple_spec cut.capSingleVertex_TL (singleCycleTriple k (by omega))
    dartsL_sub hsub_nd hsub_mem (List.finRange k) (nodup_finRange_jcs k) (fun i => List.mem_finRange i)
    (fuel := darts_cap.length) (by
      simp only [List.length_finRange]
      rw [hsub_len]
      exact Nat.le_of_eq hlen_cap.symm)
  have hgen_sum : genusDeficit cut.capSumTriple darts_cap.length darts_cap = 0 := by
    change genusDeficit (sumTriple cut.capSingleVertex_TL (singleCycleTriple k (by omega))) darts_cap.length
      (dartsL_sub.map Sum.inl ++ (List.finRange k).map Sum.inr) = 0
    rw [hsum.2.2.1, hgen_TL, htv_gen]
    rfl
  have hc_sum : countRelClasses (ReachEN cut.capSumTriple.e cut.capSumTriple.n) darts_cap = 2 := by
    change countRelClasses (ReachEN (sumTriple cut.capSingleVertex_TL (singleCycleTriple k (by omega))).e
      (sumTriple cut.capSingleVertex_TL (singleCycleTriple k (by omega))).n)
      (dartsL_sub.map Sum.inl ++ (List.finRange k).map Sum.inr) = 2
    rw [hsum.2.2.2, hc_TL, htv.2.1]
  let a0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k := Sum.inl a0'
  let v0_sum : { d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k := Sum.inr ⟨0, by omega⟩
  have ha0_fix : cut.capSumTriple.e.f a0_sum = a0_sum := by
    dsimp only [a0_sum, FaceCycleCut.capSumTriple, sumTriple, sumPerm, Sum.map,
      FaceCycleCut.capSingleVertex_TL, restrictTriplePred, restrictPermPred,
      Sum.elim, Function.comp_def]
    congr 1; apply Subtype.ext
    exact (hsep.2.2.2.2.2.2.2.2.1 ⟨0, by omega⟩).1
  have hv0_fix : cut.capSumTriple.e.f v0_sum = v0_sum := rfl
  have h_disj_base : ¬ ReachEN cut.capSumTriple.e cut.capSumTriple.n a0_sum v0_sum :=
    reachEN_sumPerm_inl_inr_false cut.capSingleVertex_TL.e cut.capSingleVertex_TL.n
      (singleCycleTriple k (by omega)).e (singleCycleTriple k (by omega)).n a0' ⟨0, by omega⟩
  have hcoup := coupleEdge_diff cut.capSumTriple darts_cap h_all_cap (Nat.le_refl _)
    ha0_fix hv0_fix h_disj_base
  have hgen_base : genusDeficit cut.capBaseTriple darts_cap.length darts_cap = 0 := by
    change genusDeficit (coupleEdge cut.capSumTriple a0_sum v0_sum) darts_cap.length darts_cap = 0
    rw [hcoup.2.2.2.2.2.2.2, hgen_sum]
  have hc_base : countRelClasses (ReachEN cut.capBaseTriple.e cut.capBaseTriple.n) darts_cap = 1 := by
    have hcc := hcoup.2.2.2.2.1
    change countRelClasses (ReachEN cut.capBaseTriple.e cut.capBaseTriple.n) darts_cap + 1 =
      countRelClasses (ReachEN cut.capSumTriple.e cut.capSumTriple.n) darts_cap at hcc
    rw [hc_sum] at hcc
    omega
  let bCap : BEq ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) := @instBEqOfDecidableEq _ _
  let bSum : BEq ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) := Sum.instBEq
  have hbase_len_deceq : (@getOrbit _ bCap cut.capBaseTriple.f
      darts_cap.length v0_sum).length = cut.posL darts h_all k + k := by
    rw [← @getOrbit_beq_congr _ bSum bCap
      (fun u v => (sum_instBEq_iff_eq u v).trans (deceq_beq_iff_eq u v).symm)]
    exact hbase_len
  have hnest := coupleNestedPairs_spec cut.capBaseTriple darts_cap
    h_all_cap (Nat.le_refl _) v0_sum (cut.capSpecs darts h_all)
    hpw (fun pq hpq => by
      rcases hbnd pq hpq with ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [hbase_len_deceq]; exact h3) hfix
  dsimp only at hnest
  have hgen_cap : genusDeficit (cut.capSingleVertexTriple darts h_all) darts_cap.length darts_cap = 0 := by
    change genusDeficit (coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all)))
      darts_cap.length darts_cap = 0
    rw [hnest.2.2.2.2.1, hgen_base]
  have hc_cap : countRelClasses
      (ReachEN (cut.capSingleVertexTriple darts h_all).e (cut.capSingleVertexTriple darts h_all).n)
      darts_cap = 1 := by
    change countRelClasses (ReachEN
      (coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all))).e
      (coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all))).n)
      darts_cap = 1
    rw [countRelClasses_eq_of_rel_iff _ _ (fun x y => hnest.2.2.2.1) darts_cap.length darts_cap (Nat.le_refl _)]
    exact hc_base
  have hb_eq : (@Sum.instBEq { d : H.Dart // cut.capSingleVertex_DL d } (Fin k) _ _) =
      (@instBEqOfDecidableEq ({ d : H.Dart // cut.capSingleVertex_DL d } ⊕ Fin k) _) :=
    beq_eq_of_iff (fun u v => (sum_instBEq_iff_eq u v).trans (deceq_beq_iff_eq u v).symm)
  have h_isPlanar : H_cap.isPlanar darts_cap.length darts_cap = true := by
    have hp := tripleToHypermap_isPlanar (cut.capSingleVertexTriple darts h_all)
      (cut.capSingleVertexTriple_invol darts h_nd h_all h_planar h_conn)
      darts_cap h_nd_cap h_all_cap hgen_cap hno_fix_cap
    change @Hypermap.isPlanar (tripleToHypermap _ _) Sum.instBEq darts_cap.length darts_cap = true
    rw [hb_eq]
    exact hp
  have h_numComp : H_cap.numComponents darts_cap.length darts_cap = 1 := by
    have hc := tripleToHypermap_numComponents_eq_one (cut.capSingleVertexTriple darts h_all)
      (cut.capSingleVertexTriple_invol darts h_nd h_all h_planar h_conn)
      darts_cap h_all_cap hc_cap
    change @Hypermap.numComponents (tripleToHypermap _ _) Sum.instBEq darts_cap.length darts_cap = 1
    rw [hb_eq]
    exact hc
  have h_bridgeless_cap : Math.Hypermap.isBridgeless H_cap darts_cap darts_cap.length := by
    apply (isBridgeless_iff_no_sameOrbit_face_edge_jcs H_cap darts_cap h_all_cap).mpr
    intro x hsame
    have hed_mem_deceq : H_cap.edge.f x ∈ @getOrbit H_cap.Dart (@instBEqOfDecidableEq _ _)
        H_cap.face darts_cap.length x :=
      (sameOrbit_face_iff_mem_getOrbit H_cap.face darts_cap h_all_cap (Nat.le_refl _) x (H_cap.edge.f x)).mp hsame
    have hed_mem : H_cap.edge.f x ∈ getOrbit H_cap.face darts_cap.length x := by
      change H_cap.edge.f x ∈ @getOrbit H_cap.Dart Sum.instBEq H_cap.face darts_cap.length x
      rw [hb_eq]; exact hed_mem_deceq
    cases x with
    | inr m =>
      have hed_eq : H_cap.edge.f (Sum.inr m) =
          Sum.inl ⟨cut.cutDart m, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn m⟩ :=
        (hed.2.1 m).2
      rw [hed_eq] at hed_mem
      rcases (cut.capSingleVertexHypermap_face_ring darts h_nd h_all h_planar h_conn m
        (Sum.inl ⟨cut.cutDart m, _⟩)).mp hed_mem with heq | ⟨d', hd', heq, hin⟩
      · cases heq
      · have hd'_eq : d' = cut.cutDart m := (congrArg Subtype.val (Sum.inl.inj heq)).symm
        subst hd'_eq
        let m_next : Fin k := ⟨(m.val + 1) % k, Nat.mod_lt _ (by omega)⟩
        have hsame_next : SameOrbit H.face (cut.ringFace m_next) (cut.cutDart m) :=
          cut.inArcL_sub_face darts h_all hin
        have hsame_m : SameOrbit H.face (cut.ringFace m) (cut.cutDart m) := cut.h_a m
        have hne_idx : m_next ≠ m := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [m_next] at hv
          have hmlt := m.isLt
          by_cases hm1 : m.val + 1 < k
          · rw [Nat.mod_eq_of_lt hm1] at hv; omega
          · have hm_eq : m.val + 1 = k := by omega
            rw [hm_eq, Nat.mod_self] at hv; omega
        exact cut.h_diff m_next m hne_idx
          (sameOrbit_trans H.face hsame_next (sameOrbit_symm_of_complete H.face darts h_all hsame_m))
    | inl dsub =>
      rcases dsub with ⟨d, hd⟩
      by_cases hcut : ∃ m : Fin k, d = cut.cutDart m
      · rcases hcut with ⟨m, rfl⟩
        have hed_eq : H_cap.edge.f (Sum.inl ⟨cut.cutDart m, hd⟩) = Sum.inr m := by
          have : (⟨cut.cutDart m, hd⟩ : { d // cut.capSingleVertex_DL d }) =
              ⟨cut.cutDart m, cut.capSingleVertex_DL_cut_all darts h_nd h_all h_planar h_conn m⟩ := Subtype.ext rfl
          rw [this]
          exact (hed.2.1 m).1
        rw [hed_eq] at hed_mem_deceq
        let m_prev : Fin k := ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
        have hm_next_eq : (⟨(m_prev.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = m := by
          apply Fin.ext; dsimp [m_prev]; exact mod_pred_succ hk m.val m.isLt
        have hx_in_prev : Sum.inl ⟨cut.cutDart m, hd⟩ ∈ getOrbit H_cap.face darts_cap.length (Sum.inr m_prev) :=
          (cut.capSingleVertexHypermap_face_ring darts h_nd h_all h_planar h_conn m_prev
            (Sum.inl ⟨cut.cutDart m, hd⟩)).mpr
              (Or.inr ⟨cut.cutDart m, hd, rfl, by rw [hm_next_eq]; exact cut.cutDart_mem_inArcL darts h_all m⟩)
        have hx_in_prev_deceq : Sum.inl ⟨cut.cutDart m, hd⟩ ∈
            @getOrbit H_cap.Dart (@instBEqOfDecidableEq _ _) H_cap.face darts_cap.length (Sum.inr m_prev) := by
          change Sum.inl ⟨cut.cutDart m, hd⟩ ∈ @getOrbit H_cap.Dart Sum.instBEq H_cap.face darts_cap.length (Sum.inr m_prev) at hx_in_prev
          rwa [hb_eq] at hx_in_prev
        have hm_in_prev_deceq : Sum.inr m ∈
            @getOrbit H_cap.Dart (@instBEqOfDecidableEq _ _) H_cap.face darts_cap.length (Sum.inr m_prev) :=
          mem_getOrbit_trans_complete H_cap.face darts_cap h_all_cap (Nat.le_refl _) hx_in_prev_deceq hed_mem_deceq
        have hm_in_prev : Sum.inr m ∈ getOrbit H_cap.face darts_cap.length (Sum.inr m_prev) := by
          change Sum.inr m ∈ @getOrbit H_cap.Dart Sum.instBEq H_cap.face darts_cap.length (Sum.inr m_prev)
          rw [hb_eq]; exact hm_in_prev_deceq
        rcases (cut.capSingleVertexHypermap_face_ring darts h_nd h_all h_planar h_conn m_prev
          (Sum.inr m)).mp hm_in_prev with heq | ⟨_, _, heq, _⟩
        · have hv := congrArg Fin.val (Sum.inr.inj heq)
          dsimp [m_prev] at hv
          have hmlt := m.isLt
          by_cases hm0 : m.val = 0
          · rw [hm0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hv; omega
          · have hsum : m.val + k - 1 = k + (m.val - 1) := by omega
            rw [hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hv; omega
        · cases heq
      · have hnot : ∀ m : Fin k, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
        rcases hed.2.2.1 d hd hnot with ⟨hdn, hed_eq⟩
        by_cases hring : ∃ i : Fin k, SameOrbit H.face (cut.ringFace i) d
        · rcases hring with ⟨i, hi_same⟩
          have hpart := (cut.face_partition_arcs darts h_all i d).1.mp hi_same
          have hin : cut.inArcL darts h_all i d := by
            rcases hpart with hL | hR
            · exact hL
            · exfalso
              exact hsep.2.2.2.2.2.2.1 d ⟨hd, cut.inArcR_imp_DR darts h_nd h_all h_planar h_conn i d hR⟩
          let i_prev : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩
          have hi_next_eq : (⟨(i_prev.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = i := by
            apply Fin.ext; dsimp [i_prev]; exact mod_pred_succ hk i.val i.isLt
          have hx_in_prev : Sum.inl ⟨d, hd⟩ ∈ getOrbit H_cap.face darts_cap.length (Sum.inr i_prev) :=
            (cut.capSingleVertexHypermap_face_ring darts h_nd h_all h_planar h_conn i_prev
              (Sum.inl ⟨d, hd⟩)).mpr
                (Or.inr ⟨d, hd, rfl, by rw [hi_next_eq]; exact hin⟩)
          have hx_in_prev_deceq : Sum.inl ⟨d, hd⟩ ∈
              @getOrbit H_cap.Dart (@instBEqOfDecidableEq _ _) H_cap.face darts_cap.length (Sum.inr i_prev) := by
            change Sum.inl ⟨d, hd⟩ ∈ @getOrbit H_cap.Dart Sum.instBEq H_cap.face darts_cap.length (Sum.inr i_prev) at hx_in_prev
            rwa [hb_eq] at hx_in_prev
          rw [hed_eq] at hed_mem_deceq
          have hed_in_prev_deceq :=
            mem_getOrbit_trans_complete H_cap.face darts_cap h_all_cap (Nat.le_refl _) hx_in_prev_deceq hed_mem_deceq
          have hed_in_prev : Sum.inl ⟨H.edge.f d, hdn⟩ ∈ getOrbit H_cap.face darts_cap.length (Sum.inr i_prev) := by
            change _ ∈ @getOrbit H_cap.Dart Sum.instBEq H_cap.face darts_cap.length (Sum.inr i_prev)
            rw [hb_eq]; exact hed_in_prev_deceq
          rcases (cut.capSingleVertexHypermap_face_ring darts h_nd h_all h_planar h_conn i_prev
            (Sum.inl ⟨H.edge.f d, hdn⟩)).mp hed_in_prev with heq | ⟨d', hd', heq, hin_ed⟩
          · cases heq
          · have hd'_eq : d' = H.edge.f d := (congrArg Subtype.val (Sum.inl.inj heq)).symm
            subst hd'_eq
            rw [hi_next_eq] at hin_ed
            have hsame_ed := cut.inArcL_sub_face darts h_all hin_ed
            have hsame_d_ed := sameOrbit_trans H.face
              (sameOrbit_symm_of_complete H.face darts h_all hi_same) hsame_ed
            exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_all).mp h_bridgeless d hsame_d_ed
        · have h_nonring : ∀ i : Fin k, ¬ SameOrbit H.face (cut.ringFace i) d := fun i h => hring ⟨i, h⟩
          have ha0_not_v0 : ¬ v0_sum ∈ @getOrbit _ (@instBEqOfDecidableEq _ _)
              cut.capSumTriple.f darts_cap.length a0_sum := by
            dsimp only [a0_sum, v0_sum, FaceCycleCut.capSumTriple, sumTriple]
            rw [getOrbit_sumPerm_inl_deceq]
            intro hm
            rcases List.mem_map.mp hm with ⟨y, _, heq⟩
            cases heq
          have hmerge := swapCompRight_merge_orbit cut.capSumTriple.f darts_cap h_all_cap
            (Nat.le_refl _) ha0_not_v0
          dsimp only at hmerge
          have hx_not_in_a0 : ¬ Sum.inl ⟨d, hd⟩ ∈ @getOrbit _ (@instBEqOfDecidableEq _ _)
              cut.capSumTriple.f darts_cap.length a0_sum := by
            intro hm
            dsimp only [a0_sum, FaceCycleCut.capSumTriple, sumTriple] at hm
            rw [getOrbit_sumPerm_inl_deceq] at hm
            rcases List.mem_map.mp hm with ⟨y, hy, heq⟩
            have hy_eq : y = ⟨d, hd⟩ := Sum.inl.inj heq
            subst hy_eq
            dsimp only [FaceCycleCut.capSingleVertex_TL] at hy
            have hy' : d ∈ getOrbit cut.uncoupleTriple.f darts.length a0'.val := by
              rcases mem_getOrbit_imp_exists_iter cut.capSingleVertex_TL.f darts_cap.length a0' ⟨d, hd⟩ hy
                with ⟨r, _, hr_eq⟩
              have h_inv_f : ∀ z, cut.capSingleVertex_DL z ↔ cut.capSingleVertex_DL (cut.uncoupleTriple.f.f z) := by
                intro z
                have he := cut.capSingleVertex_DL_e (cut.uncoupleTriple.n.f (cut.uncoupleTriple.f.f z))
                have hn := cut.capSingleVertex_DL_n (cut.uncoupleTriple.f.f z)
                rw [cut.uncoupleTriple.enf_id z] at he
                exact (Iff.trans hn he).symm
              change ⟨d, hd⟩ = Perm.iter (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) r a0' at hr_eq
              have hr_val := restrictPermPred_iter cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f r a0'
              rw [← hr_eq] at hr_val
              dsimp only at hr_val
              rw [hr_val]
              exact mem_getOrbit_of_iter_complete cut.uncoupleTriple.f darts h_all (Nat.le_refl _) a0'.val r
            rcases (hsep.2.2.2.2.2.2.2.2.2.2.1 d).mp hy' with ⟨i, hi⟩
            exact h_nonring i (cut.inArcL_sub_face darts h_all hi)
          have hx_not_in_v0_base : ¬ Sum.inl ⟨d, hd⟩ ∈ @getOrbit _ (@instBEqOfDecidableEq _ _)
              cut.capBaseTriple.f darts_cap.length v0_sum := by
            intro hx_in
            rcases (hmerge.2.2.2.1 (Sum.inl ⟨d, hd⟩)).mp hx_in with h_in_a0 | h_in_v0
            · exact hx_not_in_a0 h_in_a0
            · dsimp only [v0_sum, FaceCycleCut.capSumTriple, sumTriple] at h_in_v0
              rw [getOrbit_sumPerm_inr_deceq] at h_in_v0
              rcases List.mem_map.mp h_in_v0 with ⟨_, _, heq⟩
              cases heq
          rw [hed_eq] at hed_mem_deceq
          have hed_in_base : Sum.inl ⟨H.edge.f d, hdn⟩ ∈ @getOrbit _ (@instBEqOfDecidableEq _ _)
              cut.capBaseTriple.f darts_cap.length (Sum.inl ⟨d, hd⟩) := by
            have hforb := hnest.2.2.2.2.2.1 (Sum.inl ⟨d, hd⟩) hx_not_in_v0_base
            change Sum.inl ⟨H.edge.f d, hdn⟩ ∈ @getOrbit _ (@instBEqOfDecidableEq _ _)
              (coupleList cut.capBaseTriple (nestedPairs cut.capBaseTriple v0_sum (cut.capSpecs darts h_all))).f
              darts_cap.length (Sum.inl ⟨d, hd⟩) at hed_mem_deceq
            rwa [hforb] at hed_mem_deceq
          have h_not_a0 : ¬ a0_sum ∈ @getOrbit _ (@instBEqOfDecidableEq _ _)
              cut.capSumTriple.f darts_cap.length (Sum.inl ⟨d, hd⟩) := by
            intro hm
            exact hx_not_in_a0 (mem_getOrbit_symm_complete cut.capSumTriple.f darts_cap h_all_cap
              (Nat.le_refl _) hm)
          have h_not_v0 : ¬ v0_sum ∈ @getOrbit _ (@instBEqOfDecidableEq _ _)
              cut.capSumTriple.f darts_cap.length (Sum.inl ⟨d, hd⟩) := by
            intro hm
            dsimp only [v0_sum, FaceCycleCut.capSumTriple, sumTriple] at hm
            rw [getOrbit_sumPerm_inl_deceq] at hm
            rcases List.mem_map.mp hm with ⟨_, _, heq⟩
            cases heq
          have h_swap_orb := (swapCompRight_iter_eq_of_not_mem_orbit cut.capSumTriple.f darts_cap
            h_all_cap (Nat.le_refl _) h_not_a0 h_not_v0).2
          change @getOrbit _ (@instBEqOfDecidableEq _ _) cut.capBaseTriple.f darts_cap.length (Sum.inl ⟨d, hd⟩) =
            @getOrbit _ (@instBEqOfDecidableEq _ _) cut.capSumTriple.f darts_cap.length (Sum.inl ⟨d, hd⟩) at h_swap_orb
          rw [h_swap_orb] at hed_in_base
          dsimp only [FaceCycleCut.capSumTriple, sumTriple] at hed_in_base
          rw [getOrbit_sumPerm_inl_deceq] at hed_in_base
          rcases List.mem_map.mp hed_in_base with ⟨y, hy, heq⟩
          have hy_eq : y = ⟨H.edge.f d, hdn⟩ := Sum.inl.inj heq
          subst hy_eq
          have hed_in_unc : H.edge.f d ∈ getOrbit cut.uncoupleTriple.f darts.length d := by
            rcases mem_getOrbit_imp_exists_iter cut.capSingleVertex_TL.f darts_cap.length ⟨d, hd⟩
              ⟨H.edge.f d, hdn⟩ hy with ⟨r, _, hr_eq⟩
            have h_inv_f : ∀ z, cut.capSingleVertex_DL z ↔ cut.capSingleVertex_DL (cut.uncoupleTriple.f.f z) := by
              intro z
              have he := cut.capSingleVertex_DL_e (cut.uncoupleTriple.n.f (cut.uncoupleTriple.f.f z))
              have hn := cut.capSingleVertex_DL_n (cut.uncoupleTriple.f.f z)
              rw [cut.uncoupleTriple.enf_id z] at he
              exact (Iff.trans hn he).symm
            change ⟨H.edge.f d, hdn⟩ = Perm.iter (restrictPermPred cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f) r ⟨d, hd⟩ at hr_eq
            have hr_val := restrictPermPred_iter cut.uncoupleTriple.f cut.capSingleVertex_DL h_inv_f r ⟨d, hd⟩
            rw [← hr_eq] at hr_val
            dsimp only at hr_val
            rw [hr_val]
            exact mem_getOrbit_of_iter_complete cut.uncoupleTriple.f darts h_all (Nat.le_refl _) d r
          rw [hsep.2.2.2.2.2.2.2.2.2.2.2.2 d h_nonring] at hed_in_unc
          exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_all).mp h_bridgeless d
            ((sameOrbit_face_iff_mem_getOrbit H.face darts h_all (Nat.le_refl _) d (H.edge.f d)).mpr hed_in_unc)
  have h_node_int : ∀ (d : H.Dart) (hd : cut.capSingleVertex_DL d),
      ∃ hdn : cut.capSingleVertex_DL (H.node.f d),
        H_cap.node.f (Sum.inl ⟨d, hd⟩) = Sum.inl ⟨H.node.f d, hdn⟩ := by
    intro d hd
    have hTn : (cut.capSingleVertexTriple darts h_all).n.f = cut.capSumTriple.n.f :=
      congrArg Perm.f hed.1
    have hnd_eq : cut.uncoupleTriple.n.f d = H.node.f d := by rw [hsep.1]
    have hdn : cut.capSingleVertex_DL (H.node.f d) := by
      rw [← hnd_eq]
      exact (cut.capSingleVertex_DL_n d).mp hd
    refine ⟨hdn, ?_⟩
    change (cut.capSingleVertexTriple darts h_all).n.f (Sum.inl ⟨d, hd⟩) = _
    rw [hTn]
    dsimp only [FaceCycleCut.capSumTriple, sumTriple, sumPerm, Sum.map,
      FaceCycleCut.capSingleVertex_TL, restrictTriplePred, restrictPermPred,
      Sum.elim, Function.comp_def]
    congr 1; exact Subtype.ext hnd_eq
  have h_node_ring : ∀ m : Fin k,
      H_cap.node.f (Sum.inr m) = Sum.inr ⟨(m.val + 1) % k, Nat.mod_lt _ (by omega)⟩ ∧
      H_cap.dual.face.f (Sum.inr m) = Sum.inr ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩ :=
    fun m => cut.capSingleVertexHypermap_node_dual_ring darts h_nd h_all h_planar h_conn m
  exact ⟨h_nd_cap, h_all_cap, h_ne_cap, ⟨dartsL, hL_nd, hL_iff, hlen_cap, hL_le⟩,
    h_isPlanar, h_numComp, h_bridgeless_cap, hed.2.1, hed.2.2.1, h_node_int, h_node_ring,
    cut.capSingleVertexHypermap_face_ring darts h_nd h_all h_planar h_conn,
    cut.capSingleVertexHypermap_face_interior darts h_nd h_all h_planar h_conn⟩

/-- Strictly increasing boundary indices `i0 < i1 < i2 < i3 < k` have reverse cyclic order
    `(Sum.inr i3, Sum.inr i2, Sum.inr i1, Sum.inr i0)` around the degree-`k` cap face `H_cap.dual.face`. -/
noncomputable def FaceCycleCut.capSingleVertex_cyclicOrder4 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : FaceCycleCut H k)
    {i0 i1 i2 i3 : Nat} (h01 : i0 < i1) (h12 : i1 < i2) (h23 : i2 < i3) (h3k : i3 < k) :
    let H_cap := cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn
    CyclicOrder4 H_cap.dual.face k
      (Sum.inr ⟨i3, by omega⟩) (Sum.inr ⟨i2, by omega⟩)
      (Sum.inr ⟨i1, by omega⟩) (Sum.inr ⟨i0, by omega⟩) := by
  intro H_cap
  have hk := cut.hk
  have hdual_step : ∀ m : Fin k,
      H_cap.dual.face.f (Sum.inr m) = Sum.inr ⟨(m.val + k - 1) % k, Nat.mod_lt _ (by omega)⟩ :=
    fun m => (cut.capSingleVertexHypermap_node_dual_ring darts h_nd h_all h_planar h_conn m).2
  let base : H_cap.Dart := Sum.inr ⟨k - 1, by omega⟩
  have hiter : ∀ r : Nat, ∀ hr : r < k,
      Perm.iter H_cap.dual.face r base = Sum.inr ⟨k - 1 - r, by omega⟩ := by
    intro r
    induction r with
    | zero =>
      intro hr
      rfl
    | succ r ih =>
      intro hr
      rw [Perm.iter_succ, ih (by omega), hdual_step]
      congr 1
      apply Fin.ext
      dsimp only
      have hsum : k - 1 - r + k - 1 = k + (k - 1 - (r + 1)) := by omega
      rw [hsum, Nat.add_mod_left]
      exact Nat.mod_eq_of_lt (by omega)
  have h_inj : ∀ i j : Nat, i < k → j < k →
      Perm.iter H_cap.dual.face i base = Perm.iter H_cap.dual.face j base → i = j := by
    intro i j hi hj heq
    rw [hiter i hi, hiter j hj] at heq
    have hv := congrArg Fin.val (Sum.inr.inj heq)
    dsimp only at hv
    omega
  have h_per : Perm.iter H_cap.dual.face k base = base := by
    rw [show k = (k - 1) + 1 by omega, Perm.iter_succ, hiter (k - 1) (by omega), hdual_step]
    congr 1; apply Fin.ext; dsimp only [base]
    rw [Nat.sub_self, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  have hco := cyclicOrder4_of_strictMono_pos H_cap.dual.face (L := k) base h_inj h_per
    (p0 := k - 1 - i3) (p1 := k - 1 - i2) (p2 := k - 1 - i1) (p3 := k - 1 - i0)
    (by omega) (by omega) (by omega) (by omega)
  rw [hiter (k - 1 - i3) (by omega), hiter (k - 1 - i2) (by omega),
      hiter (k - 1 - i1) (by omega), hiter (k - 1 - i0) (by omega)] at hco
  simpa [show k - 1 - (k - 1 - i3) = i3 by omega,
         show k - 1 - (k - 1 - i2) = i2 by omega,
         show k - 1 - (k - 1 - i1) = i1 by omega,
         show k - 1 - (k - 1 - i0) = i0 by omega] using hco

end CapSingleVertex

end Hypermap
