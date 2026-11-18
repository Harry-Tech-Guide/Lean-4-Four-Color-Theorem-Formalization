module

/-
FourColorTheorem/Math/Topology/ShortCircuits.lean

Dual short-circuit reductions (k = 2, 3, 4) for minimal counterexamples:
- k = 2 (`mc_no_parallel_edges_dual`, `mc_no_parallel_edges_of_two_darts`): no parallel edges in `H.dual`
- k = 3 (`mc_three_cycle_is_facial_dual`, `mc_three_cycle_facial_orbits_dual`, `mc_no_separating_three_cycle_dual`):
        every 3-cycle in `H.dual` bounds a single cubic vertex (3 darts) on at least one side
- k = 4 (`mc_no_separating_four_cycle_dual`, `mc_four_cycle_small_side_dual`, `mc_no_chordless_four_cycle_dual`):
        every 4-cycle in `H.dual` bounds ≤ 6 darts (a single edge = two adjacent cubic vertices) on at least one side,
        hence has a chord (`H.dual` has no chordless 4-cycle).
-/
public import FourColorTheorem.Math.Topology.JordanCycleSeparation
public import FourColorTheorem.Math.Topology.CubicGirth5

@[expose] public section

namespace Hypermap

open Classical

/-! ## Section 1: List, Orbit, Cut Symmetry, Rotation, and Cap-Gluing Helpers -/

section Helpers

theorem filter_partition_length {α : Type} (l : List α) (P Q : α → Prop)
    (h_cov : ∀ x ∈ l, P x ∨ Q x) (h_disj : ∀ x ∈ l, ¬(P x ∧ Q x)) :
    (l.filter (fun x => decide (P x))).length +
      (l.filter (fun x => decide (Q x))).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hcov_xs : ∀ y ∈ xs, P y ∨ Q y := fun y hy => h_cov y (by simp [hy])
      have hdisj_xs : ∀ y ∈ xs, ¬(P y ∧ Q y) := fun y hy => h_disj y (by simp [hy])
      have ih' := ih hcov_xs hdisj_xs
      rcases h_cov x (by simp) with hPx | hQx
      · have hnQx : ¬Q x := fun hq => h_disj x (by simp) ⟨hPx, hq⟩
        simp [hPx, hnQx]
        omega
      · have hnPx : ¬P x := fun hp => h_disj x (by simp) ⟨hp, hQx⟩
        simp [hnPx, hQx]
        omega

theorem sc_nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ (l1 l2 : List α), l1.Nodup → (∀ x, x ∈ l1 → x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, l2, hnd, hsub => by
      have ha_nt : a ∉ t := (List.nodup_cons.mp hnd).1
      have ht_nd : t.Nodup := (List.nodup_cons.mp hnd).2
      have ha2 : a ∈ l2 := hsub a (by simp)
      have ht_sub : ∀ x, x ∈ t → x ∈ l2.erase a := by
        intro x hx
        have hne : x ≠ a := fun h => ha_nt (h ▸ hx)
        exact (List.mem_erase_of_ne hne).mpr (hsub x (by simp [hx]))
      have hle := sc_nodup_length_le_of_subset t (l2.erase a) ht_nd ht_sub
      have herase : (l2.erase a).length + 1 = l2.length := by
        have := List.length_erase_of_mem ha2
        have hpos : 0 < l2.length := by
          cases l2 with
          | nil => simp at ha2
          | cons _ _ => simp
        omega
      simp only [List.length_cons]
      omega

theorem sc_nodup_length_eq_of_iff {α : Type} [DecidableEq α] (l1 l2 : List α)
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hiff : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    l1.length = l2.length :=
  Nat.le_antisymm
    (sc_nodup_length_le_of_subset l1 l2 h1 (fun x hx => (hiff x).mp hx))
    (sc_nodup_length_le_of_subset l2 l1 h2 (fun x hx => (hiff x).mpr hx))

theorem sc_nodup_mem_of_subset_of_length_le {α : Type} [DecidableEq α] (l1 l2 : List α)
    (h1 : l1.Nodup) (hsub : ∀ x, x ∈ l1 → x ∈ l2) (hlen : l2.length ≤ l1.length) :
    ∀ x, x ∈ l2 → x ∈ l1 := by
  intro x hx
  by_cases hx1 : x ∈ l1
  · exact hx1
  · exfalso
    have hnd' : (x :: l1).Nodup := List.nodup_cons.mpr ⟨hx1, h1⟩
    have hsub' : ∀ y, y ∈ x :: l1 → y ∈ l2 := by
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact hsub y hy
    have hle' := sc_nodup_length_le_of_subset (x :: l1) l2 hnd' hsub'
    simp only [List.length_cons] at hle'
    omega

theorem beq_sum_eq_dec {α β : Type} [DecidableEq α] [DecidableEq β]
    [bα : BEq α] (hα : ∀ a b : α, @BEq.beq α bα a b = decide (a = b))
    [bβ : BEq β] (hβ : ∀ a b : β, @BEq.beq β bβ a b = decide (a = b)) :
    (@Sum.instBEq α β bα bβ : BEq (α ⊕ β)) = @instBEqOfDecidableEq (α ⊕ β) _ := by
  have hfun : (@Sum.instBEq α β bα bβ).beq = (@instBEqOfDecidableEq (α ⊕ β) _).beq := by
    funext x y
    rcases x with x | x <;> rcases y with y | y
    · change @BEq.beq α bα x y = decide (Sum.inl x = (Sum.inl y : α ⊕ β))
      rw [hα]
      exact decide_eq_decide.mpr (by simp)
    · change false = decide (Sum.inl x = (Sum.inr y : α ⊕ β))
      simp
    · change false = decide (Sum.inr x = (Sum.inl y : α ⊕ β))
      simp
    · change @BEq.beq β bβ x y = decide (Sum.inr x = (Sum.inr y : α ⊕ β))
      rw [hβ]
      exact decide_eq_decide.mpr (by simp)
  have hext : ∀ x y : BEq (α ⊕ β), x.beq = y.beq → x = y := by
    intro ⟨f1⟩ ⟨f2⟩ h
    cases h
    rfl
  exact hext _ _ hfun

theorem capSingleVertex_beq_eq {H : Hypermap} [DecidableEq H.Dart] {k : Nat}
    (cut : H.FaceCycleCut k) :
    (@Sum.instBEq { d // cut.capSingleVertex_DL d } (Fin k) _ _ :
        BEq ({ d // cut.capSingleVertex_DL d } ⊕ Fin k)) =
      @instBEqOfDecidableEq ({ d // cut.capSingleVertex_DL d } ⊕ Fin k) _ := by
  apply beq_sum_eq_dec
  · intro a b
    exact Bool.eq_iff_iff.mpr (by simp [beq_iff_eq])
  · intro a b
    exact Bool.eq_iff_iff.mpr (by simp [beq_iff_eq])

theorem fin_rev_inj (k i j : Nat) (hi : i < k) (hj : j < k)
    (heq : (k - i) % k = (k - j) % k) : i = j := by
  have hk1 : 1 ≤ k := by omega
  calc i = (k - (k - i) % k) % k := by
        by_cases h0 : i = 0
        · subst h0; simp
        · rw [Nat.mod_eq_of_lt (by omega : k - i < k), show k - (k - i) = i by omega, Nat.mod_eq_of_lt hi]
    _ = (k - (k - j) % k) % k := by rw [heq]
    _ = j := by
        by_cases h0 : j = 0
        · subst h0; simp
        · rw [Nat.mod_eq_of_lt (by omega : k - j < k), show k - (k - j) = j by omega, Nat.mod_eq_of_lt hj]

theorem fin_pairwise_distinct_eq_iff {k : Nat} (f g : Fin k → Color)
    (hf : ∀ i j : Fin k, i ≠ j → f i ≠ f j)
    (hg : ∀ i j : Fin k, i ≠ j → g i ≠ g j)
    (i j : Fin k) :
    f i = f j ↔ g ⟨(k - i.val) % k, Nat.mod_lt _ (by have := i.isLt; omega)⟩ =
      g ⟨(k - j.val) % k, Nat.mod_lt _ (by have := j.isLt; omega)⟩ := by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij; rfl
    · exact absurd h (hf i j hij)
  · intro h
    by_cases hij : i = j
    · subst hij; rfl
    · have hij' : (⟨(k - i.val) % k, Nat.mod_lt _ (by have := i.isLt; omega)⟩ : Fin k) ≠
          ⟨(k - j.val) % k, Nat.mod_lt _ (by have := j.isLt; omega)⟩ := by
        intro heq
        apply hij
        exact Fin.ext (fin_rev_inj k i.val j.val i.isLt j.isLt (Fin.mk.inj heq))
      exact absurd h (hg _ _ hij')

/-- Helper modular arithmetic identities on `Fin k` for `2 ≤ k`. -/
theorem mod_add_one_add_sub_one (k i : Nat) (hk : 2 ≤ k) (hi : i < k) :
    ((i + 1) % k + k - 1) % k = i := by
  by_cases h : i + 1 < k
  · rw [Nat.mod_eq_of_lt h]
    have h1 : i + 1 + k - 1 = i + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have hik : i + 1 = k := by omega
    rw [hik, Nat.mod_self, Nat.zero_add]
    have h1 : k - 1 < k := by omega
    rw [Nat.mod_eq_of_lt h1]
    omega

theorem mod_sub_one_add_one (k i : Nat) (hk : 2 ≤ k) (hi : i < k) :
    ((i + k - 1) % k + 1) % k = i := by
  by_cases h0 : i = 0
  · subst h0
    have hk1 : k - 1 < k := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt hk1]
    have hk2 : k - 1 + 1 = k := by omega
    rw [hk2, Nat.mod_self]
  · have h1 : i + k - 1 = (i - 1) + k := by omega
    rw [h1, Nat.add_mod_right]
    have him : i - 1 < k := by omega
    rw [Nat.mod_eq_of_lt him]
    have h2 : i - 1 + 1 = i := by omega
    rw [h2, Nat.mod_eq_of_lt hi]

theorem mod_rev_add_one (k i : Nat) (hk : 2 ≤ k) (hi : i < k) :
    ((k - (i + 1) % k) % k + 1) % k = (k - i) % k := by
  by_cases h0 : i = 0
  · subst h0
    have h1 : 1 < k := by omega
    rw [Nat.zero_add, Nat.mod_eq_of_lt h1]
    have hk1 : k - 1 < k := by omega
    rw [Nat.mod_eq_of_lt hk1]
    have hk2 : k - 1 + 1 = k := by omega
    rw [hk2, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · by_cases hik : i + 1 < k
    · rw [Nat.mod_eq_of_lt hik]
      have ha : k - (i + 1) < k := by omega
      have hb : k - i < k := by omega
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
      have hc : k - (i + 1) + 1 = k - i := by omega
      rw [hc, Nat.mod_eq_of_lt hb]
    · have heq : i + 1 = k := by omega
      rw [heq, Nat.mod_self, Nat.sub_zero, Nat.mod_self, Nat.zero_add]
      have h1 : 1 < k := by omega
      have hb : k - i < k := by omega
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hb]
      omega

theorem mod_rev_rev (k i : Nat) (_hk : 1 ≤ k) (hi : i < k) :
    (k - (k - i) % k) % k = i := by
  by_cases h0 : i = 0
  · subst h0
    rw [Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · have hlt : k - i < k := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hlt2 : k - (k - i) = i := by omega
    rw [hlt2, Nat.mod_eq_of_lt hi]

theorem mod_succ_inj (k i j : Nat) (_hk : 2 ≤ k) (hi : i < k) (hj : j < k)
    (heq : (i + 1) % k = (j + 1) % k) : i = j := by
  by_cases hi1 : i + 1 < k <;> by_cases hj1 : j + 1 < k
  · rw [Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj1] at heq; omega
  · have hje : j + 1 = k := by omega
    rw [Nat.mod_eq_of_lt hi1, hje, Nat.mod_self] at heq; omega
  · have hie : i + 1 = k := by omega
    rw [hie, Nat.mod_self, Nat.mod_eq_of_lt hj1] at heq; omega
  · omega

/-- Every `d` in `inArcL` lies in `DL`. -/
theorem FaceCycleCut.inArcL_sub_DL {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) {i : Fin k} {d : H.Dart}
    (hd : FaceCycleCut.inArcL darts h_all cut i d) :
    cut.capSingleVertex_DL d := by
  have hspec := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hmem : d ∈ getOrbit cut.uncoupleTriple.f darts.length (cut.cutDart ⟨0, by have := cut.hk; omega⟩) :=
    (hspec.2.2.2.2.2.2.2.2.2.2.1 d).mpr ⟨i, hd⟩
  have hso : SameOrbit cut.uncoupleTriple.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩) d :=
    (sameOrbit_iff_mem_getOrbit cut.uncoupleTriple.f darts h_all (Nat.le_refl _) _ d).mpr hmem
  exact sameOrbit_f_imp_reachEN cut.uncoupleTriple hso

/-- Every `d` in `inArcR` lies in `DR`. -/
theorem FaceCycleCut.inArcR_sub_DR {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) {i : Fin k} {d : H.Dart}
    (hd : FaceCycleCut.inArcR darts h_all cut i d) :
    ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
      (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) d := by
  have hspec := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hDR_last : ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
      (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩))
      (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩)) :=
    (hspec.2.2.2.2.2.2.2.1 ⟨k - 1, by have := cut.hk; omega⟩).2
  have hmem : d ∈ getOrbit cut.uncoupleTriple.f darts.length
      (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩)) :=
    (hspec.2.2.2.2.2.2.2.2.2.2.2.1 d).mpr ⟨i, hd⟩
  have hso : SameOrbit cut.uncoupleTriple.f
      (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩)) d :=
    (sameOrbit_iff_mem_getOrbit cut.uncoupleTriple.f darts h_all (Nat.le_refl _) _ d).mpr hmem
  exact reachEN_trans cut.uncoupleTriple.e cut.uncoupleTriple.n hDR_last
    (sameOrbit_f_imp_reachEN cut.uncoupleTriple hso)

theorem FaceCycleCut.inArcL_iff_sameOrbit_and_DL {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (i : Fin k) (d : H.Dart) :
    FaceCycleCut.inArcL darts h_all cut i d ↔
      SameOrbit H.face (cut.ringFace i) d ∧ cut.capSingleVertex_DL d := by
  constructor
  · intro hL
    exact ⟨FaceCycleCut.inArcL_sub_face darts h_all cut hL,
      cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn hL⟩
  · rintro ⟨hso, hDL⟩
    have hpart := (FaceCycleCut.face_partition_arcs darts h_all cut i d).1.mp hso
    rcases hpart with hL | hR
    · exact hL
    · have hDR := cut.inArcR_sub_DR darts h_nd h_all h_planar h_conn hR
      have hspec := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
      exact False.elim (hspec.2.2.2.2.2.2.1 d ⟨hDL, hDR⟩)

theorem FaceCycleCut.inArcR_iff_sameOrbit_and_DR {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (i : Fin k) (d : H.Dart) :
    FaceCycleCut.inArcR darts h_all cut i d ↔
      SameOrbit H.face (cut.ringFace i) d ∧
        ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
          (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) d := by
  constructor
  · intro hR
    exact ⟨FaceCycleCut.inArcR_sub_face darts h_all cut hR,
      cut.inArcR_sub_DR darts h_nd h_all h_planar h_conn hR⟩
  · rintro ⟨hso, hDR⟩
    have hpart := (FaceCycleCut.face_partition_arcs darts h_all cut i d).1.mp hso
    rcases hpart with hL | hR
    · have hDL := cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn hL
      have hspec := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
      exact False.elim (hspec.2.2.2.2.2.2.1 d ⟨hDL, hDR⟩)
    · exact hR

/-- `cut.rev` swaps the `DL` and `DR` sides. -/
theorem FaceCycleCut.rev_DL_iff_DR {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (d : H.Dart) :
    cut.rev.capSingleVertex_DL d ↔
      ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) d := by
  have hT : cut.rev.uncoupleTriple = cut.uncoupleTriple :=
    FaceCycleCut.uncoupleTriple_rev_eq darts h_all cut
  have hspec := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hDR_last : ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
      (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩))
      (H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩)) :=
    (hspec.2.2.2.2.2.2.2.1 ⟨k - 1, by have := cut.hk; omega⟩).2
  have hcut0 : cut.rev.cutDart ⟨0, by have := cut.hk; omega⟩ =
      H.edge.f (cut.cutDart ⟨k - 1, by have := cut.hk; omega⟩) := by
    simp [FaceCycleCut.rev]
  constructor
  · intro h
    change ReachEN cut.rev.uncoupleTriple.e cut.rev.uncoupleTriple.n
      (cut.rev.cutDart ⟨0, by have := cut.hk; omega⟩) d at h
    rw [hT, hcut0] at h
    exact reachEN_trans cut.uncoupleTriple.e cut.uncoupleTriple.n hDR_last h
  · intro h
    change ReachEN cut.rev.uncoupleTriple.e cut.rev.uncoupleTriple.n
      (cut.rev.cutDart ⟨0, by have := cut.hk; omega⟩) d
    rw [hT, hcut0]
    exact reachEN_trans cut.uncoupleTriple.e cut.uncoupleTriple.n
      (reachEN_symm cut.uncoupleTriple.e cut.uncoupleTriple.n hDR_last) h

theorem FaceCycleCut.inArcL_rev_iff_inArcR {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (m : Fin k) (d : H.Dart) :
    FaceCycleCut.inArcL darts h_all cut.rev m d ↔
      FaceCycleCut.inArcR darts h_all cut ⟨(k - m.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d := by
  rw [cut.rev.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn,
      cut.inArcR_iff_sameOrbit_and_DR darts h_nd h_all h_planar h_conn,
      cut.rev_DL_iff_DR darts h_nd h_all h_planar h_conn]
  rfl

theorem FaceCycleCut.inArcR_iff_inArcL_rev {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (i : Fin k) (d : H.Dart) :
    FaceCycleCut.inArcR darts h_all cut i d ↔
      FaceCycleCut.inArcL darts h_all cut.rev
        ⟨(k - i.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d := by
  rw [cut.inArcL_rev_iff_inArcR darts h_nd h_all h_planar h_conn]
  have hidx : (⟨(k - ((k - i.val) % k)) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ : Fin k) = i := by
    apply Fin.ext
    exact mod_rev_rev k i.val (by have := cut.hk; omega) i.isLt
  simp only [hidx]

/-- Cyclic rotation of a `FaceCycleCut` by `+1` along the ring cycle. -/
def FaceCycleCut.rot1 {H : Hypermap} {k : Nat} (cut : H.FaceCycleCut k) : H.FaceCycleCut k where
  hk := cut.hk
  ringFace i := cut.ringFace ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  cutDart i := cut.cutDart ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  h_diff i j hij := by
    apply cut.h_diff
    intro h
    apply hij
    apply Fin.ext
    exact mod_succ_inj k i.val j.val cut.hk i.isLt j.isLt (Fin.mk.inj h)
  h_a i := cut.h_a ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  h_b i := cut.h_b ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  h_disj_edge i j := cut.h_disj_edge _ _

theorem FaceCycleCut.rot1_uncoupleTriple_en_eq {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) :
    cut.rot1.uncoupleTriple.n = cut.uncoupleTriple.n ∧
      (∀ x, cut.rot1.uncoupleTriple.e.f x = cut.uncoupleTriple.e.f x) := by
  have h1 := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have h2 := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut.rot1
  refine ⟨by rw [h2.1, h1.1], fun x => ?_⟩
  by_cases hex : ∃ i : Fin k, x = cut.cutDart i ∨ x = H.edge.f (cut.cutDart i)
  · rcases hex with ⟨i, rfl | rfl⟩
    · have hidx : (⟨(((i.val + k - 1) % k) + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ : Fin k) = i := by
        apply Fin.ext
        exact mod_sub_one_add_one k i.val cut.hk i.isLt
      have hi' : cut.cutDart i = cut.rot1.cutDart
          ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ := by
        change cut.cutDart i = cut.cutDart ⟨(((i.val + k - 1) % k) + 1) % k, _⟩
        rw [hidx]
      rw [(h1.2.2.2.2.2.2.2.2.1 i).1, hi']
      exact (h2.2.2.2.2.2.2.2.2.1 ⟨(i.val + k - 1) % k, _⟩).1
    · have hidx : (⟨(((i.val + k - 1) % k) + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ : Fin k) = i := by
        apply Fin.ext
        exact mod_sub_one_add_one k i.val cut.hk i.isLt
      have hi' : H.edge.f (cut.cutDart i) = H.edge.f (cut.rot1.cutDart
          ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩) := by
        change H.edge.f (cut.cutDart i) = H.edge.f (cut.cutDart ⟨(((i.val + k - 1) % k) + 1) % k, _⟩)
        rw [hidx]
      rw [(h1.2.2.2.2.2.2.2.2.1 i).2, hi']
      exact (h2.2.2.2.2.2.2.2.2.1 ⟨(i.val + k - 1) % k, _⟩).2
  · have hnot1 : ∀ i : Fin k, x ≠ cut.cutDart i ∧ x ≠ H.edge.f (cut.cutDart i) := by
      intro i
      exact ⟨fun h => hex ⟨i, Or.inl h⟩, fun h => hex ⟨i, Or.inr h⟩⟩
    have hnot2 : ∀ i : Fin k, x ≠ cut.rot1.cutDart i ∧ x ≠ H.edge.f (cut.rot1.cutDart i) := by
      intro i
      exact hnot1 ⟨(i.val + 1) % k, _⟩
    rw [(h2.2.2.2.2.2.2.2.2.2.1 x hnot2).1, (h1.2.2.2.2.2.2.2.2.2.1 x hnot1).1]

theorem FaceCycleCut.rot1_DL_iff {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (d : H.Dart) :
    cut.rot1.capSingleVertex_DL d ↔ cut.capSingleVertex_DL d := by
  have hen := cut.rot1_uncoupleTriple_en_eq darts h_nd h_all h_planar h_conn
  have he_eq : cut.rot1.uncoupleTriple.e = cut.uncoupleTriple.e := by
    have hinv1 := (uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut).2.1
    have hinv2 := (uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut.rot1).2.1
    cases h1 : cut.rot1.uncoupleTriple.e with
    | mk f1 inv1 l1 r1 =>
      cases h2 : cut.uncoupleTriple.e with
      | mk f2 inv2 l2 r2 =>
        have hf : f1 = f2 := funext fun x => by
          have := hen.2 x
          simp only [h1, h2] at this
          exact this
        subst hf
        congr 1
        funext x
        have h1x : f1 (f1 x) = x := by
          have := hinv2 x
          simp only [h1] at this
          exact this
        calc inv1 x = inv1 (f1 (f1 x)) := by rw [h1x]
          _ = f1 x := l1 (f1 x)
          _ = inv2 (f1 (f1 x)) := (l2 (f1 x)).symm
          _ = inv2 x := by rw [h1x]
  have h_reach_iff : ∀ x y,
      ReachEN cut.rot1.uncoupleTriple.e cut.rot1.uncoupleTriple.n x y ↔
        ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n x y := by
    intro x y
    rw [he_eq, hen.1]
  have h1 := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hDL1 : cut.capSingleVertex_DL (cut.rot1.cutDart ⟨0, by have := cut.hk; omega⟩) :=
    (h1.2.2.2.2.2.2.2.1 ⟨(0 + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩).1
  change ReachEN cut.rot1.uncoupleTriple.e cut.rot1.uncoupleTriple.n
      (cut.rot1.cutDart ⟨0, by have := cut.hk; omega⟩) d ↔
    cut.capSingleVertex_DL d
  rw [h_reach_iff]
  constructor
  · intro h
    exact reachEN_trans _ _ hDL1 h
  · intro h
    exact reachEN_trans _ _ (reachEN_symm _ _ hDL1) h

theorem FaceCycleCut.inArcL_rot1_iff {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) (i : Fin k) (d : H.Dart) :
    FaceCycleCut.inArcL darts h_all cut.rot1 i d ↔
      FaceCycleCut.inArcL darts h_all cut ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ d := by
  rw [cut.rot1.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn,
      cut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn,
      cut.rot1_DL_iff darts h_nd h_all h_planar h_conn]
  rfl

/-- Boundary face colors extracted from `H_cap.FaceColoring` (`f i` is the color of `ringFace i`). -/
noncomputable def capBoundaryColors {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k)
    (col : (cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn).FaceColoring) :
    Fin k → Color :=
  fun i => col.color (Sum.inr ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)

theorem capBoundaryColors_adj {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts)
    {k : Nat} (cut : H.FaceCycleCut k)
    (col : (cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn).FaceColoring)
    (i : Fin k) :
    capBoundaryColors darts h_nd h_all h_planar h_conn cut col
        ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ ≠
      capBoundaryColors darts h_nd h_all h_planar h_conn cut col i := by
  let H_cap := cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn
  let darts_cap := cut.capSingleVertexDarts darts
  rcases cut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_bridgeless with
    ⟨_, h_cap_all, _, _, _, _, _, h_ed_b, _, _, _, h_orb_b, _⟩
  have h1 : capBoundaryColors darts h_nd h_all h_planar h_conn cut col
      ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ = col.color (Sum.inr i) := by
    simp only [capBoundaryColors]
    congr 2
    apply Fin.ext
    exact mod_add_one_add_sub_one k i.val cut.hk i.isLt
  have hd_cut : cut.capSingleVertex_DL (cut.cutDart i) :=
    cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn (FaceCycleCut.cutDart_mem_inArcL darts h_all cut i)
  have hedge : H_cap.edge.f (Sum.inr i) = Sum.inl ⟨cut.cutDart i, hd_cut⟩ := (h_ed_b i).2
  have hidx : ⟨((i.val + k - 1) % k + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ = i := by
    apply Fin.ext
    exact mod_sub_one_add_one k i.val cut.hk i.isLt
  have horb : (Sum.inl ⟨cut.cutDart i, hd_cut⟩ : H_cap.Dart) ∈
      @getOrbit H_cap.Dart Sum.instBEq H_cap.face darts_cap.length
        (Sum.inr ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩) := by
    rw [h_orb_b ⟨(i.val + k - 1) % k, _⟩ (Sum.inl ⟨cut.cutDart i, hd_cut⟩)]
    right
    refine ⟨cut.cutDart i, hd_cut, rfl, ?_⟩
    rw [hidx]
    exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut i
  rw [capSingleVertex_beq_eq cut] at horb
  have hso : SameOrbit H_cap.face
      (Sum.inr ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
      (Sum.inl ⟨cut.cutDart i, hd_cut⟩) :=
    (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap h_cap_all (Nat.le_refl _) _ _).mpr horb
  have h2 : capBoundaryColors darts h_nd h_all h_planar h_conn cut col i =
      col.color (H_cap.edge.f (Sum.inr i)) := by
    rw [hedge]
    exact sameOrbit_face_color_eq H_cap col hso
  rw [h1, h2]
  exact fun heq => col.edge_proper (Sum.inr i) heq.symm

theorem glue_of_cap_colorings {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {k : Nat} (cut : H.FaceCycleCut k)
    (colL : (cut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc)).FaceColoring)
    (colR : (cut.rev.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc)).FaceColoring)
    (h_eq_iff : ∀ i j : Fin k,
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut colL i =
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut colL j ↔
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut.rev colR
          ⟨(k - i.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ =
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut.rev colR
          ⟨(k - j.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩) :
    False := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  let H_capL := cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn
  let darts_capL := cut.capSingleVertexDarts darts
  rcases cut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br with
    ⟨_, hL_all, _, _, _, _, _, _, hL_ed_i, _, _, hL_orb_b, hL_fc_i⟩
  let H_capR := cut.rev.capSingleVertexHypermap darts h_nd h_all h_planar h_conn
  let darts_capR := cut.rev.capSingleVertexDarts darts
  rcases cut.rev.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br with
    ⟨_, hR_all, _, _, _, _, _, _, hR_ed_i, _, _, hR_orb_b, hR_fc_i⟩
  have hunc := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  let cL : H.Dart → Color := fun d =>
    if hd : cut.capSingleVertex_DL d then colL.color (Sum.inl ⟨d, hd⟩) else Color.c0
  let cR : H.Dart → Color := fun d =>
    if hd : cut.rev.capSingleVertex_DL d then colR.color (Sum.inl ⟨d, hd⟩) else Color.c0
  let f : Fin k → Color := capBoundaryColors darts h_nd h_all h_planar h_conn cut colL
  let g : Fin k → Color := fun i =>
    capBoundaryColors darts h_nd h_all h_planar h_conn cut.rev colR
      ⟨(k - i.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  have hL_arc : ∀ (i : Fin k) (d : H.Dart), FaceCycleCut.inArcL darts h_all cut i d → cL d = f i := by
    intro i d hi
    have hd : cut.capSingleVertex_DL d := cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn hi
    simp only [cL, dif_pos hd, f, capBoundaryColors]
    have hidx : ⟨((i.val + k - 1) % k + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ = i := by
      apply Fin.ext; exact mod_sub_one_add_one k i.val cut.hk i.isLt
    have horb : (Sum.inl ⟨d, hd⟩ : H_capL.Dart) ∈
        @getOrbit H_capL.Dart Sum.instBEq H_capL.face darts_capL.length
          (Sum.inr ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩) := by
      rw [hL_orb_b ⟨(i.val + k - 1) % k, _⟩ (Sum.inl ⟨d, hd⟩)]
      right
      refine ⟨d, hd, rfl, ?_⟩
      rw [hidx]
      exact hi
    rw [capSingleVertex_beq_eq cut] at horb
    have hso : SameOrbit H_capL.face
        (Sum.inr ⟨(i.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
        (Sum.inl ⟨d, hd⟩) :=
      (sameOrbit_iff_mem_getOrbit H_capL.face darts_capL hL_all (Nat.le_refl _) _ _).mpr horb
    exact (sameOrbit_face_color_eq H_capL colL hso).symm
  have hL_face : ∀ d, cut.capSingleVertex_DL d →
      (∀ i : Fin k, ¬SameOrbit H.face (cut.ringFace i) d) → cL (H.face.f d) = cL d := by
    intro d hd hnot
    rcases hL_fc_i d hd hnot with ⟨hfn, hface_eq⟩
    simp only [cL, dif_pos hd, dif_pos hfn]
    rw [← hface_eq]
    exact colL.face_invariant (Sum.inl ⟨d, hd⟩)
  have hL_edge : ∀ d, cut.capSingleVertex_DL d → cut.capSingleVertex_DL (H.edge.f d) →
      cL (H.edge.f d) ≠ cL d := by
    intro d hd hde
    have hnotcut : ∀ m : Fin k, d ≠ cut.cutDart m := by
      intro m hdm
      subst hdm
      exact hunc.2.2.2.2.2.2.1 (H.edge.f (cut.cutDart m)) ⟨hde, (hunc.2.2.2.2.2.2.2.1 m).2⟩
    rcases hL_ed_i d hd hnotcut with ⟨hdn, hedge_eq⟩
    simp only [cL, dif_pos hd, dif_pos hde]
    have hed : (⟨H.edge.f d, hde⟩ : { x // cut.capSingleVertex_DL x }) = ⟨H.edge.f d, hdn⟩ := rfl
    rw [hed, ← hedge_eq]
    exact colL.edge_proper (Sum.inl ⟨d, hd⟩)
  have hR_arc : ∀ (i : Fin k) (d : H.Dart), FaceCycleCut.inArcR darts h_all cut i d → cR d = g i := by
    intro i d hi
    have hi_rev := (cut.inArcR_iff_inArcL_rev darts h_nd h_all h_planar h_conn i d).mp hi
    have hd : cut.rev.capSingleVertex_DL d := cut.rev.inArcL_sub_DL darts h_nd h_all h_planar h_conn hi_rev
    let j : Fin k := ⟨(k - i.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
    simp only [cR, dif_pos hd, g, capBoundaryColors]
    have hidx : ⟨((j.val + k - 1) % k + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ = j := by
      apply Fin.ext; exact mod_sub_one_add_one k j.val cut.hk j.isLt
    have horb : (Sum.inl ⟨d, hd⟩ : H_capR.Dart) ∈
        @getOrbit H_capR.Dart Sum.instBEq H_capR.face darts_capR.length
          (Sum.inr ⟨(j.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩) := by
      rw [hR_orb_b ⟨(j.val + k - 1) % k, _⟩ (Sum.inl ⟨d, hd⟩)]
      right
      refine ⟨d, hd, rfl, ?_⟩
      rw [hidx]
      exact hi_rev
    rw [capSingleVertex_beq_eq cut.rev] at horb
    have hso : SameOrbit H_capR.face
        (Sum.inr ⟨(j.val + k - 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩)
        (Sum.inl ⟨d, hd⟩) :=
      (sameOrbit_iff_mem_getOrbit H_capR.face darts_capR hR_all (Nat.le_refl _) _ _).mpr horb
    exact (sameOrbit_face_color_eq H_capR colR hso).symm
  have hR_face : ∀ d, ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) d →
      (∀ i : Fin k, ¬SameOrbit H.face (cut.ringFace i) d) → cR (H.face.f d) = cR d := by
    intro d hdDR hnot
    have hd : cut.rev.capSingleVertex_DL d :=
      (cut.rev_DL_iff_DR darts h_nd h_all h_planar h_conn d).mpr hdDR
    have hnot_rev : ∀ j : Fin k, ¬SameOrbit H.face (cut.rev.ringFace j) d := by
      intro j
      exact hnot ⟨(k - j.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
    rcases hR_fc_i d hd hnot_rev with ⟨hfn, hface_eq⟩
    simp only [cR, dif_pos hd, dif_pos hfn]
    rw [← hface_eq]
    exact colR.face_invariant (Sum.inl ⟨d, hd⟩)
  have hR_edge : ∀ d, ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) d →
      ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
        (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) (H.edge.f d) →
      cR (H.edge.f d) ≠ cR d := by
    intro d hdDR hdeDR
    have hd : cut.rev.capSingleVertex_DL d :=
      (cut.rev_DL_iff_DR darts h_nd h_all h_planar h_conn d).mpr hdDR
    have hde : cut.rev.capSingleVertex_DL (H.edge.f d) :=
      (cut.rev_DL_iff_DR darts h_nd h_all h_planar h_conn (H.edge.f d)).mpr hdeDR
    have hnotcut : ∀ m : Fin k, d ≠ cut.rev.cutDart m := by
      intro m hdm
      have hcut_m : H.edge.f d = cut.cutDart ⟨k - 1 - m.val, by have := cut.hk; omega⟩ := by
        rw [hdm]
        simp [FaceCycleCut.rev, H.edge_edge]
      have hDL_e : cut.capSingleVertex_DL (H.edge.f d) := by
        rw [hcut_m]
        exact (hunc.2.2.2.2.2.2.2.1 ⟨k - 1 - m.val, _⟩).1
      exact hunc.2.2.2.2.2.2.1 (H.edge.f d) ⟨hDL_e, hdeDR⟩
    rcases hR_ed_i d hd hnotcut with ⟨hdn, hedge_eq⟩
    simp only [cR, dif_pos hd, dif_pos hde]
    have hed : (⟨H.edge.f d, hde⟩ : { x // cut.rev.capSingleVertex_DL x }) = ⟨H.edge.f d, hdn⟩ := rfl
    rw [hed, ← hedge_eq]
    exact colR.edge_proper (Sum.inl ⟨d, hd⟩)
  have hf_adj : ∀ i : Fin k, f ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ ≠ f i :=
    fun i => capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut colL i
  rcases glueCycleFaceColoring H darts h_nd h_all h_planar h_conn cut cL cR f g
      hL_arc hL_face hL_edge hR_arc hR_face hR_edge hf_adj h_eq_iff with ⟨colH⟩
  exact h_mc.not_colorable colH

theorem capBoundaryColors_rev_adj {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts)
    {k : Nat} (cut : H.FaceCycleCut k)
    (colR : (cut.rev.capSingleVertexHypermap darts h_nd h_all h_planar h_conn).FaceColoring)
    (i : Fin k) :
    capBoundaryColors darts h_nd h_all h_planar h_conn cut.rev colR
        ⟨(k - (i.val + 1) % k) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ ≠
      capBoundaryColors darts h_nd h_all h_planar h_conn cut.rev colR
        ⟨(k - i.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ := by
  let j : Fin k := ⟨(k - (i.val + 1) % k) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩
  have hidx : ⟨(j.val + 1) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ =
      (⟨(k - i.val) % k, Nat.mod_lt _ (by have := cut.hk; omega)⟩ : Fin k) := by
    apply Fin.ext
    exact mod_rev_add_one k i.val cut.hk i.isLt
  have hadj := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_bridgeless cut.rev colR j
  rw [hidx] at hadj
  exact hadj.symm

theorem side_lengths_sum {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) :
    (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length +
      (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length = darts.length := by
  have hunc := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  apply filter_partition_length
  · intro x _
    rw [cut.rev_DL_iff_DR darts h_nd h_all h_planar h_conn]
    exact hunc.2.2.2.2.2.1 x
  · intro x _
    rw [cut.rev_DL_iff_DR darts h_nd h_all h_planar h_conn]
    exact hunc.2.2.2.2.2.2.1 x

theorem side_parity_divisibility_cap {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {k : Nat} (cut : H.FaceCycleCut k) :
    (3 ∣ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length ∧
      k ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length ∧
      ∃ mL, (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 2 * mL + k) ∧
    (3 ∣ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length ∧
      k ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length ∧
      ∃ mR, (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length = 2 * mR + k) := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  have h_deg3 : ∀ d, Math.Hypermap.nodeDegree H d darts.length = 3 :=
    fun d => mc_nodeDegree_eq_three H darts h_mc d
  have hsp := side_parity_divisibility H darts h_nd h_all h_planar h_conn h_br h_deg3 cut
  have hfR_eq :
      (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length =
        (darts.filter (fun x => decide (ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
          (H.edge.f (cut.cutDart ⟨0, by have := cut.hk; omega⟩)) x))).length := by
    congr 1
    apply List.filter_congr
    intro x _
    exact decide_eq_decide.mpr (cut.rev_DL_iff_DR darts h_nd h_all h_planar h_conn x)
  refine ⟨⟨hsp.1.1, hsp.1.2.1, hsp.1.2.2.1⟩, ?_⟩
  rw [hfR_eq]
  exact ⟨hsp.2.1, hsp.2.2.1, hsp.2.2.2.1⟩

theorem capDarts_length_eq {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_bridgeless : Math.Hypermap.isBridgeless H darts)
    {k : Nat} (cut : H.FaceCycleCut k) :
    (cut.capSingleVertexDarts darts).length =
      (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length + k := by
  have hcap := cut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_bridgeless
  rcases hcap.2.2.2.1 with ⟨dartsL, hL_nd, hL_iff, hlen_cap, _⟩
  let fL := darts.filter (fun x => decide (cut.capSingleVertex_DL x))
  have hfL_nd : fL.Nodup := h_nd.filter _
  have hiff : ∀ d, d ∈ dartsL ↔ d ∈ fL := by
    intro d
    rw [hL_iff, List.mem_filter]
    simp [h_all d]
  have heq : dartsL.length = fL.length := sc_nodup_length_eq_of_iff dartsL fL hL_nd hfL_nd hiff
  rw [hlen_cap, heq]

theorem cap_colorable_of_lt {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {k : Nat} (cut : H.FaceCycleCut k)
    (hlt : (cut.capSingleVertexDarts darts).length < darts.length) :
    Nonempty (cut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc)).FaceColoring := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  rcases cut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br with
    ⟨h_cnd, h_call, h_cne, _, h_cpl, _, h_cbr, _⟩
  rw [capSingleVertex_beq_eq cut] at h_cpl
  exact h_mc.is_minimal (cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn)
    (cut.capSingleVertexDarts darts) h_cnd h_call h_cne hlt h_cpl h_cbr

end Helpers

/-! ## Section 2: `k = 2` Dual Short Circuit (`mc_no_parallel_edges_dual`) -/

section K2

/-- A minimal counterexample has no 2-edge cut in `H` separating two non-empty sides
    (equivalently, `H.dual` has no parallel edges). -/
theorem mc_no_parallel_edges_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 2) : False := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  have hsp := side_parity_divisibility_cap darts h_mc cut
  have hsum := side_lengths_sum darts h_nd h_all h_planar h_conn cut
  have hge6L : 6 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length := by
    rcases hsp.1 with ⟨hd3, h2, mL, hm⟩
    omega
  have hge6R : 6 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length := by
    rcases hsp.2 with ⟨hd3, h2, mR, hm⟩
    omega
  have hlenL := capDarts_length_eq darts h_nd h_all h_planar h_conn h_br cut
  have hlenR := capDarts_length_eq darts h_nd h_all h_planar h_conn h_br cut.rev
  have hltL : (cut.capSingleVertexDarts darts).length < darts.length := by omega
  have hltR : (cut.rev.capSingleVertexDarts darts).length < darts.length := by omega
  rcases cap_colorable_of_lt darts h_mc cut hltL with ⟨colL⟩
  rcases cap_colorable_of_lt darts h_mc cut.rev hltR with ⟨colR⟩
  have hf_adj : capBoundaryColors darts h_nd h_all h_planar h_conn cut colL ⟨1, by decide⟩ ≠
      capBoundaryColors darts h_nd h_all h_planar h_conn cut colL ⟨0, by decide⟩ :=
    capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut colL ⟨0, by decide⟩
  have hg_adj : capBoundaryColors darts h_nd h_all h_planar h_conn cut.rev colR ⟨1, by decide⟩ ≠
      capBoundaryColors darts h_nd h_all h_planar h_conn cut.rev colR ⟨0, by decide⟩ :=
    capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut.rev colR ⟨0, by decide⟩
  apply glue_of_cap_colorings darts h_mc cut colL colR
  apply fin_pairwise_distinct_eq_iff
  · intro a b hab
    rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
    match a, b with
    | 0, 0 | 1, 1 => exact absurd rfl hab
    | 0, 1 => exact hf_adj.symm
    | 1, 0 => exact hf_adj
  · intro a b hab
    rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
    match a, b with
    | 0, 0 | 1, 1 => exact absurd rfl hab
    | 0, 1 => exact hg_adj.symm
    | 1, 0 => exact hg_adj

/-- Any two distinct darts `d1 ≠ d2` sharing both `H.face` orbits on their endpoints
    yield a `FaceCycleCut 2`, impossible in a minimal counterexample. -/
theorem mc_no_parallel_edges_of_two_darts (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {d1 d2 : H.Dart} (hne : d1 ≠ d2)
    (hf1 : SameOrbit H.face d1 d2)
    (hf2 : SameOrbit H.face (H.edge.f d1) (H.edge.f d2)) : False := by
  have hbr : ∀ d, ¬SameOrbit H.face d (H.edge.f d) :=
    (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp h_mc.is_bridgeless
  have hcut : H.FaceCycleCut 2 :=
    { hk := by decide
      ringFace := fun i => if i.val = 0 then d1 else H.edge.f d1
      cutDart := fun i => if i.val = 0 then d1 else H.edge.f d2
      h_diff := fun i j hij => by
        rcases i with ⟨i, hi⟩
        rcases j with ⟨j, hj⟩
        match i, j with
        | 0, 0 => exact absurd rfl hij
        | 0, 1 => exact hbr d1
        | 1, 0 => intro h; exact hbr d1 (sameOrbit_symm_of_complete H.face darts h_mc.complete h)
        | 1, 1 => exact absurd rfl hij
      h_a := fun i => by
        rcases i with ⟨i, hi⟩
        match i with
        | 0 => exact sameOrbit_refl H.face d1
        | 1 => exact hf2
      h_b := fun i => by
        rcases i with ⟨i, hi⟩
        match i with
        | 0 => exact sameOrbit_refl H.face (H.edge.f d1)
        | 1 => simpa [H.edge_edge] using hf1
      h_disj_edge := fun i j => by
        rcases i with ⟨i, hi⟩
        rcases j with ⟨j, hj⟩
        match i, j with
        | 0, 0 => exact mc_edge_ne_self H darts h_mc d1
        | 0, 1 =>
            intro heq
            change H.edge.f d1 = H.edge.f d2 at heq
            apply hne
            calc d1 = H.edge.f (H.edge.f d1) := (H.edge_edge d1).symm
              _ = H.edge.f (H.edge.f d2) := by rw [heq]
              _ = d2 := H.edge_edge d2
        | 1, 0 => simpa [H.edge_edge] using hne.symm
        | 1, 1 => simpa [H.edge_edge] using (mc_edge_ne_self H darts h_mc d2).symm }
  exact mc_no_parallel_edges_dual H darts h_mc hcut

end K2

/-! ## Section 3: `k = 3` Dual Short Circuit (`mc_three_cycle_is_facial_dual`) -/

section K3

/-- Every 3-cycle in `H.dual` encloses only 3 darts (a single cubic vertex of `H`)
    on at least one of its two sides. -/
theorem mc_three_cycle_is_facial_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 3) :
    (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 3 ∨
      (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length = 3 := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  have hsp := side_parity_divisibility_cap darts h_mc cut
  have hsum := side_lengths_sum darts h_nd h_all h_planar h_conn cut
  have hL_cases : (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 3 ∨
      9 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length := by
    rcases hsp.1 with ⟨hd3, h3, mL, hm⟩
    omega
  have hR_cases : (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length = 3 ∨
      9 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length := by
    rcases hsp.2 with ⟨hd3, h3, mR, hm⟩
    omega
  by_cases hL3 : (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 3
  · exact Or.inl hL3
  · by_cases hR3 : (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length = 3
    · exact Or.inr hR3
    · exfalso
      have hge9L : 9 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length :=
        hL_cases.resolve_left hL3
      have hge9R : 9 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length :=
        hR_cases.resolve_left hR3
      have hlenL := capDarts_length_eq darts h_nd h_all h_planar h_conn h_br cut
      have hlenR := capDarts_length_eq darts h_nd h_all h_planar h_conn h_br cut.rev
      have hltL : (cut.capSingleVertexDarts darts).length < darts.length := by omega
      have hltR : (cut.rev.capSingleVertexDarts darts).length < darts.length := by omega
      rcases cap_colorable_of_lt darts h_mc cut hltL with ⟨colL⟩
      rcases cap_colorable_of_lt darts h_mc cut.rev hltR with ⟨colR⟩
      have hf10 := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut colL ⟨0, by decide⟩
      have hf21 := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut colL ⟨1, by decide⟩
      have hf02 : capBoundaryColors darts h_nd h_all h_planar h_conn cut colL ⟨0, by decide⟩ ≠
          capBoundaryColors darts h_nd h_all h_planar h_conn cut colL ⟨2, by decide⟩ := by
        simpa using capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut colL ⟨2, by decide⟩
      have hg10 := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut.rev colR ⟨0, by decide⟩
      have hg21 := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut.rev colR ⟨1, by decide⟩
      have hg02 : capBoundaryColors darts h_nd h_all h_planar h_conn cut.rev colR ⟨0, by decide⟩ ≠
          capBoundaryColors darts h_nd h_all h_planar h_conn cut.rev colR ⟨2, by decide⟩ := by
        simpa using capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut.rev colR ⟨2, by decide⟩
      simp only at hf10 hf21 hg10 hg21
      apply glue_of_cap_colorings darts h_mc cut colL colR
      apply fin_pairwise_distinct_eq_iff
      · intro a b hab
        rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
        match a, b with
        | 0, 0 | 1, 1 | 2, 2 => exact absurd rfl hab
        | 0, 1 => exact hf10.symm
        | 1, 0 => exact hf10
        | 1, 2 => exact hf21.symm
        | 2, 1 => exact hf21
        | 0, 2 => exact hf02
        | 2, 0 => exact hf02.symm
      · intro a b hab
        rcases a with ⟨a, ha⟩; rcases b with ⟨b, hb⟩
        match a, b with
        | 0, 0 | 1, 1 | 2, 2 => exact absurd rfl hab
        | 0, 1 => exact hg10.symm
        | 1, 0 => exact hg10
        | 1, 2 => exact hg21.symm
        | 2, 1 => exact hg21
        | 0, 2 => exact hg02
        | 2, 0 => exact hg02.symm

/-- Any 3-dart side of a `FaceCycleCut 3` consists solely of the three cut darts and
    forms a single cubic `H.node` orbit. -/
theorem mc_three_cycle_facial_orbits_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 3)
    (h3 : (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 3) :
    (∀ d, cut.capSingleVertex_DL d ↔
      d = cut.cutDart ⟨0, by decide⟩ ∨
      d = cut.cutDart ⟨1, by decide⟩ ∨
      d = cut.cutDart ⟨2, by decide⟩) ∧
    (∀ d, cut.capSingleVertex_DL d ↔ SameOrbit H.node (cut.cutDart ⟨0, by decide⟩) d) ∧
    (∀ i j : Fin 3, SameOrbit H.node (cut.cutDart i) (cut.cutDart j)) := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have hunc := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  let a0 := cut.cutDart ⟨0, by decide⟩
  let a1 := cut.cutDart ⟨1, by decide⟩
  let a2 := cut.cutDart ⟨2, by decide⟩
  have hne01 : a0 ≠ a1 := by
    intro h
    have h0 : SameOrbit H.face (cut.ringFace ⟨0, by decide⟩) a0 := cut.h_a ⟨0, by decide⟩
    have h1 : SameOrbit H.face (cut.ringFace ⟨1, by decide⟩) a1 := cut.h_a ⟨1, by decide⟩
    rw [← h] at h1
    exact cut.h_diff ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
      (sameOrbit_trans H.face h0 (sameOrbit_symm_of_complete H.face darts h_all h1))
  have hne02 : a0 ≠ a2 := by
    intro h
    have h0 : SameOrbit H.face (cut.ringFace ⟨0, by decide⟩) a0 := cut.h_a ⟨0, by decide⟩
    have h2 : SameOrbit H.face (cut.ringFace ⟨2, by decide⟩) a2 := cut.h_a ⟨2, by decide⟩
    rw [← h] at h2
    exact cut.h_diff ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
      (sameOrbit_trans H.face h0 (sameOrbit_symm_of_complete H.face darts h_all h2))
  have hne12 : a1 ≠ a2 := by
    intro h
    have h1 : SameOrbit H.face (cut.ringFace ⟨1, by decide⟩) a1 := cut.h_a ⟨1, by decide⟩
    have h2 : SameOrbit H.face (cut.ringFace ⟨2, by decide⟩) a2 := cut.h_a ⟨2, by decide⟩
    rw [← h] at h2
    exact cut.h_diff ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
      (sameOrbit_trans H.face h1 (sameOrbit_symm_of_complete H.face darts h_all h2))
  let L3 : List H.Dart := [a0, a1, a2]
  have hL3_nd : L3.Nodup := by
    simp [L3, List.nodup_cons, hne01, hne02, hne12]
  let fL := darts.filter (fun x => decide (cut.capSingleVertex_DL x))
  have hsub1 : ∀ x, x ∈ L3 → x ∈ fL := by
    intro x hx
    rw [List.mem_filter]
    refine ⟨h_all x, decide_eq_true ?_⟩
    simp only [L3, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (hunc.2.2.2.2.2.2.2.1 ⟨0, by decide⟩).1
    · exact (hunc.2.2.2.2.2.2.2.1 ⟨1, by decide⟩).1
    · exact (hunc.2.2.2.2.2.2.2.1 ⟨2, by decide⟩).1
  have hfL_le3 : fL.length ≤ L3.length := by
    change (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length ≤ 3
    omega
  have h_mem_L3 : ∀ x, x ∈ fL → x ∈ L3 :=
    sc_nodup_mem_of_subset_of_length_le L3 fL hL3_nd hsub1 hfL_le3
  have hDL_iff : ∀ d, cut.capSingleVertex_DL d ↔ d = a0 ∨ d = a1 ∨ d = a2 := by
    intro d
    constructor
    · intro hd
      have hmem : d ∈ fL := List.mem_filter.mpr ⟨h_all d, decide_eq_true hd⟩
      simpa [L3] using h_mem_L3 d hmem
    · intro hdisj
      rcases hdisj with rfl | rfl | rfl
      · exact (hunc.2.2.2.2.2.2.2.1 ⟨0, by decide⟩).1
      · exact (hunc.2.2.2.2.2.2.2.1 ⟨1, by decide⟩).1
      · exact (hunc.2.2.2.2.2.2.2.1 ⟨2, by decide⟩).1
  have horb_sub_DL : ∀ d, SameOrbit H.node a0 d → cut.capSingleVertex_DL d := by
    intro d hso
    change ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n a0 d
    rw [hunc.1]
    exact sameOrbit_n_imp_reachEN hso
  let orb := getOrbit H.node darts.length a0
  have horb_nd : orb.Nodup := getOrbit_nodup H.node darts.length a0
  have horb_len : orb.length = 3 := mc_nodeDegree_eq_three H darts h_mc a0
  have hsub2 : ∀ x, x ∈ orb → x ∈ fL := by
    intro x hx
    have hso : SameOrbit H.node a0 x :=
      (sameOrbit_iff_mem_getOrbit H.node darts h_all (Nat.le_refl _) a0 x).mpr hx
    exact List.mem_filter.mpr ⟨h_all x, decide_eq_true (horb_sub_DL x hso)⟩
  have hfL_le_orb : fL.length ≤ orb.length := by
    change (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length ≤ orb.length
    omega
  have h_mem_orb : ∀ x, x ∈ fL → x ∈ orb :=
    sc_nodup_mem_of_subset_of_length_le orb fL horb_nd hsub2 hfL_le_orb
  have hDL_so : ∀ d, cut.capSingleVertex_DL d ↔ SameOrbit H.node a0 d := by
    intro d
    constructor
    · intro hd
      have hmem : d ∈ orb := h_mem_orb d (List.mem_filter.mpr ⟨h_all d, decide_eq_true hd⟩)
      exact (sameOrbit_iff_mem_getOrbit H.node darts h_all (Nat.le_refl _) a0 d).mpr hmem
    · exact horb_sub_DL d
  refine ⟨hDL_iff, hDL_so, fun i j => ?_⟩
  have hi : SameOrbit H.node a0 (cut.cutDart i) :=
    (hDL_so _).mp (hunc.2.2.2.2.2.2.2.1 i).1
  have hj : SameOrbit H.node a0 (cut.cutDart j) :=
    (hDL_so _).mp (hunc.2.2.2.2.2.2.2.1 j).1
  exact sameOrbit_trans H.node (sameOrbit_symm_of_complete H.node darts h_all hi) hj

theorem mc_no_separating_three_cycle_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 3)
    (hL : 4 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length)
    (hR : 4 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) :
    False := by
  rcases mc_three_cycle_is_facial_dual H darts h_mc cut with h3 | h3 <;> omega

end K3

section K4ParityAndChords

theorem mc_edge_inv {H : Hypermap} (x : H.Dart) : H.edge.f (H.edge.f x) = x :=
  H.edge_involution x

theorem sameOrbit_face_symm {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : SameOrbit H.face x y) : SameOrbit H.face y x :=
  sameOrbit_symm_of_complete H.face darts h_mc.complete h

theorem dl_edge_of_ne_cutDart {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) {k : Nat} (cut : H.FaceCycleCut k)
    {u : H.Dart} (huL : cut.capSingleVertex_DL u)
    (hne : ∀ i : Fin k, u ≠ cut.cutDart i) :
    cut.uncoupleTriple.e.f u = H.edge.f u ∧ cut.capSingleVertex_DL (H.edge.f u) := by
  have h_uc := uncoupleCycle_two_components H darts h_mc.nodup h_mc.complete
    h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut
  rcases h_uc with ⟨-, -, -, -, -, -, hdisj, hcut_sides, -, hint, -, -, -⟩
  have h_not_b : ∀ i : Fin k, u ≠ H.edge.f (cut.cutDart i) := by
    intro i hi
    have hDR := (hcut_sides i).2
    rw [← hi] at hDR
    exact hdisj u ⟨huL, hDR⟩
  have he_eq : cut.uncoupleTriple.e.f u = H.edge.f u :=
    (hint u (fun i => ⟨hne i, h_not_b i⟩)).1
  refine ⟨he_eq, ?_⟩
  rw [← he_eq]
  exact reachEN_trans cut.uncoupleTriple.e cut.uncoupleTriple.n huL
    (sameOrbit_e_imp_reachEN ⟨1, rfl⟩)

theorem four_cycle_side_length_cases {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (cut : H.FaceCycleCut 4) :
    ((darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 6 ∨
      12 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length) ∧
    ((darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length = 6 ∨
      12 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) := by
  have h_par := side_parity_divisibility_cap darts h_mc cut
  rcases h_par.1 with ⟨⟨qL, hqL⟩, h4L, mL, hmL⟩
  rcases h_par.2 with ⟨⟨qR, hqR⟩, h4R, mR, hmR⟩
  constructor
  · omega
  · omega

def HasDiagChord02 {H : Hypermap} [DecidableEq H.Dart] (cut : H.FaceCycleCut 4) : Prop :=
  ∃ u : H.Dart,
    cut.capSingleVertex_DL u ∧
    cut.capSingleVertex_DL (H.edge.f u) ∧
    SameOrbit H.face (cut.ringFace ⟨0, by decide⟩) u ∧
    SameOrbit H.face (cut.ringFace ⟨2, by decide⟩) (H.edge.f u)

def HasDiagChord13 {H : Hypermap} [DecidableEq H.Dart] (cut : H.FaceCycleCut 4) : Prop :=
  HasDiagChord02 cut.rot1

theorem nodup_filter_sc {α : Type} (p : α → Bool) : ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => by simp
  | x :: xs, hnd => by
      have hsub := List.nodup_cons.mp hnd
      have ih := nodup_filter_sc p hsub.2
      simp only [List.filter_cons]
      cases hp : p x with
      | false => exact ih
      | true =>
          refine List.nodup_cons.mpr ⟨?_, ih⟩
          intro hmem
          exact hsub.1 (List.mem_filter.mp hmem).1

theorem cutDart_ne_of_ne {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) {k : Nat} (cut : H.FaceCycleCut k)
    {i j : Fin k} (hij : i ≠ j) : cut.cutDart i ≠ cut.cutDart j := by
  intro heq
  have ha_i := cut.h_a i
  have ha_j := cut.h_a j
  rw [← heq] at ha_j
  exact cut.h_diff i j hij (sameOrbit_trans H.face ha_i (sameOrbit_face_symm darts h_mc ha_j))

theorem four_cycle_six_dart_side_has_chord {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (h6 : (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 6) :
    HasDiagChord02 cut ∨ HasDiagChord13 cut := by
  have h_uc := uncoupleCycle_two_components H darts h_mc.nodup h_mc.complete
    h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut
  rcases h_uc with ⟨-, -, -, -, -, -, hdisj, hcut_sides, -, -, -, -, horb_out⟩
  let dartsL := darts.filter (fun x => decide (cut.capSingleVertex_DL x))
  have hL_nd : dartsL.Nodup := nodup_filter_sc _ h_mc.nodup
  let i0 : Fin 4 := ⟨0, by decide⟩
  let i1 : Fin 4 := ⟨1, by decide⟩
  let i2 : Fin 4 := ⟨2, by decide⟩
  let i3 : Fin 4 := ⟨3, by decide⟩
  let a0 := cut.cutDart i0
  let a1 := cut.cutDart i1
  let a2 := cut.cutDart i2
  let a3 := cut.cutDart i3
  have ha01 : a0 ≠ a1 := cutDart_ne_of_ne darts h_mc cut (by decide)
  have ha02 : a0 ≠ a2 := cutDart_ne_of_ne darts h_mc cut (by decide)
  have ha03 : a0 ≠ a3 := cutDart_ne_of_ne darts h_mc cut (by decide)
  have ha12 : a1 ≠ a2 := cutDart_ne_of_ne darts h_mc cut (by decide)
  have ha13 : a1 ≠ a3 := cutDart_ne_of_ne darts h_mc cut (by decide)
  have ha23 : a2 ≠ a3 := cutDart_ne_of_ne darts h_mc cut (by decide)
  have ha_mem : ∀ i : Fin 4, cut.cutDart i ∈ dartsL := fun i =>
    List.mem_filter.mpr ⟨h_mc.complete _, decide_eq_true (hcut_sides i).1⟩
  let P := fun x : H.Dart => x = a0 ∨ x = a1 ∨ x = a2 ∨ x = a3
  let Q := fun x : H.Dart => ¬P x
  have h_cov : ∀ x ∈ dartsL, P x ∨ Q x := fun x _ => Classical.em _
  have h_disj : ∀ x ∈ dartsL, ¬(P x ∧ Q x) := fun x _ ⟨hp, hnp⟩ => hnp hp
  have h_part := filter_partition_length dartsL P Q h_cov h_disj
  have ha4_nd : [a0, a1, a2, a3].Nodup := by simp [ha01, ha02, ha03, ha12, ha13, ha23]
  have ha4_len : (dartsL.filter (fun x => decide (P x))).length = 4 := by
    have h_eq := sc_nodup_length_eq_of_iff (dartsL.filter (fun x => decide (P x))) [a0, a1, a2, a3]
      (nodup_filter_sc _ hL_nd) ha4_nd (fun x => by
        constructor
        · intro hx
          rcases List.mem_filter.mp hx with ⟨_, hpx⟩
          rcases of_decide_eq_true hpx with rfl | rfl | rfl | rfl <;> simp
        · intro hx
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl
          · exact List.mem_filter.mpr ⟨ha_mem i0, decide_eq_true (Or.inl rfl)⟩
          · exact List.mem_filter.mpr ⟨ha_mem i1, decide_eq_true (Or.inr (Or.inl rfl))⟩
          · exact List.mem_filter.mpr ⟨ha_mem i2, decide_eq_true (Or.inr (Or.inr (Or.inl rfl)))⟩
          · exact List.mem_filter.mpr ⟨ha_mem i3, decide_eq_true (Or.inr (Or.inr (Or.inr rfl)))⟩)
    simpa using h_eq
  have h_part_eq1 : (dartsL.filter (fun x => decide (P x))).length =
      (dartsL.filter (fun x => @decide (P x) (Classical.propDecidable _))).length := by
    congr 1; congr 1; funext x; by_cases hx : P x <;> simp [hx]
  have h_part_eq2 : (dartsL.filter (fun x => decide (Q x))).length =
      (dartsL.filter (fun x => @decide (Q x) (Classical.propDecidable _))).length := by
    congr 1; congr 1; funext x; by_cases hx : Q x <;> simp [hx]
  have h_rem_len : (dartsL.filter (fun x => decide (Q x))).length = 2 := by
    change dartsL.length = 6 at h6
    omega
  have hu_ex : ∃ u, u ∈ dartsL.filter (fun x => decide (Q x)) := by
    cases h_f : dartsL.filter (fun x => decide (Q x)) with
    | nil =>
        have h_nil : (dartsL.filter (fun x => decide (Q x))).length = 0 := by simp [h_f]
        omega
    | cons x _ => exact ⟨x, List.mem_cons_self⟩
  rcases hu_ex with ⟨u, hu_rem⟩
  rcases List.mem_filter.mp hu_rem with ⟨hu_inL, hu_notP⟩
  have hu_DL : cut.capSingleVertex_DL u := of_decide_eq_true (List.mem_filter.mp hu_inL).2
  have hu_np : ¬P u := of_decide_eq_true hu_notP
  have hu_ne_cut : ∀ i : Fin 4, u ≠ cut.cutDart i := by
    intro ⟨i, hi⟩ h_eq
    match i with
    | 0 => exact hu_np (Or.inl h_eq)
    | 1 => exact hu_np (Or.inr (Or.inl h_eq))
    | 2 => exact hu_np (Or.inr (Or.inr (Or.inl h_eq)))
    | 3 => exact hu_np (Or.inr (Or.inr (Or.inr h_eq)))
  let v := H.edge.f u
  have hv_pair := dl_edge_of_ne_cutDart darts h_mc cut hu_DL hu_ne_cut
  have hv_DL : cut.capSingleVertex_DL v := hv_pair.2
  have hv_inL : v ∈ dartsL := List.mem_filter.mpr ⟨h_mc.complete _, decide_eq_true hv_DL⟩
  have hv_ne_u : v ≠ u := mc_edge_ne_self H darts h_mc u
  have hv_ne_cut : ∀ i : Fin 4, v ≠ cut.cutDart i := by
    intro i hi
    have he_eq := congrArg H.edge.f hi
    change H.edge.f (H.edge.f u) = H.edge.f (cut.cutDart i) at he_eq
    rw [mc_edge_inv] at he_eq
    have hDR := (hcut_sides i).2
    rw [← he_eq] at hDR
    exact hdisj u ⟨hu_DL, hDR⟩
  have h6_nd : [a0, a1, a2, a3, u, v].Nodup := by
    have hne_u0 : u ≠ a0 := hu_ne_cut i0
    have hne_u1 : u ≠ a1 := hu_ne_cut i1
    have hne_u2 : u ≠ a2 := hu_ne_cut i2
    have hne_u3 : u ≠ a3 := hu_ne_cut i3
    have hne_v0 : v ≠ a0 := hv_ne_cut i0
    have hne_v1 : v ≠ a1 := hv_ne_cut i1
    have hne_v2 : v ≠ a2 := hv_ne_cut i2
    have hne_v3 : v ≠ a3 := hv_ne_cut i3
    simp [ha01, ha02, ha03, ha12, ha13, ha23,
      hne_u0.symm, hne_u1.symm, hne_u2.symm, hne_u3.symm,
      hne_v0.symm, hne_v1.symm, hne_v2.symm, hne_v3.symm, hv_ne_u.symm]
  have h6_sub : ∀ x, x ∈ [a0, a1, a2, a3, u, v] → x ∈ dartsL := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ha_mem i0
    · exact ha_mem i1
    · exact ha_mem i2
    · exact ha_mem i3
    · exact hu_inL
    · exact hv_inL
  have hL_in_6 : ∀ x, x ∈ dartsL → x ∈ [a0, a1, a2, a3, u, v] := by
    have hlen6 : dartsL.length ≤ [a0, a1, a2, a3, u, v].length := by
      change dartsL.length = 6 at h6
      simp [h6]
    exact sc_nodup_mem_of_subset_of_length_le [a0, a1, a2, a3, u, v] dartsL h6_nd h6_sub hlen6
  have h_hits_ring : ∀ z : H.Dart, cut.capSingleVertex_DL z →
      (∀ i : Fin 4, z ≠ cut.cutDart i) →
      ∃ i : Fin 4, SameOrbit H.face (cut.ringFace i) z := by
    intro z hzDL _
    refine Classical.byContradiction fun h_none => ?_
    have h_not_f : ∀ i : Fin 4, ¬SameOrbit H.face (cut.ringFace i) z := fun i hi => h_none ⟨i, hi⟩
    have h_orb_eq := horb_out z h_not_f
    have h_sub_uv : ∀ w ∈ getOrbit H.face darts.length z, w ∈ [u, v] := by
      intro w hw
      have hwT : w ∈ getOrbit cut.uncoupleTriple.f darts.length z := by rw [h_orb_eq]; exact hw
      have h_so_Tf : SameOrbit cut.uncoupleTriple.f z w :=
        (sameOrbit_iff_mem_getOrbit cut.uncoupleTriple.f darts h_mc.complete (Nat.le_refl _) z w).mpr hwT
      have hw_DL : cut.capSingleVertex_DL w :=
        reachEN_trans cut.uncoupleTriple.e cut.uncoupleTriple.n hzDL
          (sameOrbit_f_imp_reachEN cut.uncoupleTriple h_so_Tf)
      have hw_inL : w ∈ dartsL := List.mem_filter.mpr ⟨h_mc.complete _, decide_eq_true hw_DL⟩
      have hw_6 := hL_in_6 w hw_inL
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw_6
      rcases hw_6 with rfl | rfl | rfl | rfl | rfl | rfl
      · exfalso
        have h_so_f : SameOrbit H.face z (cut.cutDart i0) :=
          (sameOrbit_iff_mem_getOrbit H.face darts h_mc.complete (Nat.le_refl _) z (cut.cutDart i0)).mpr hw
        exact h_not_f i0 (sameOrbit_trans H.face (cut.h_a i0) (sameOrbit_face_symm darts h_mc h_so_f))
      · exfalso
        have h_so_f : SameOrbit H.face z (cut.cutDart i1) :=
          (sameOrbit_iff_mem_getOrbit H.face darts h_mc.complete (Nat.le_refl _) z (cut.cutDart i1)).mpr hw
        exact h_not_f i1 (sameOrbit_trans H.face (cut.h_a i1) (sameOrbit_face_symm darts h_mc h_so_f))
      · exfalso
        have h_so_f : SameOrbit H.face z (cut.cutDart i2) :=
          (sameOrbit_iff_mem_getOrbit H.face darts h_mc.complete (Nat.le_refl _) z (cut.cutDart i2)).mpr hw
        exact h_not_f i2 (sameOrbit_trans H.face (cut.h_a i2) (sameOrbit_face_symm darts h_mc h_so_f))
      · exfalso
        have h_so_f : SameOrbit H.face z (cut.cutDart i3) :=
          (sameOrbit_iff_mem_getOrbit H.face darts h_mc.complete (Nat.le_refl _) z (cut.cutDart i3)).mpr hw
        exact h_not_f i3 (sameOrbit_trans H.face (cut.h_a i3) (sameOrbit_face_symm darts h_mc h_so_f))
      · simp
      · simp
    have h_fdeg := mc_faceDegree_ge_five H darts h_mc z
    have h_nd_orb := getOrbit_nodup H.face darts.length z
    have h_le2 := sc_nodup_length_le_of_subset (getOrbit H.face darts.length z) [u, v] h_nd_orb h_sub_uv
    have h_len_uv : [u, v].length = 2 := rfl
    change 5 ≤ (getOrbit H.face darts.length z).length at h_fdeg
    omega
  rcases h_hits_ring u hu_DL hu_ne_cut with ⟨⟨i, hi⟩, hfi⟩
  rcases h_hits_ring v hv_DL hv_ne_cut with ⟨⟨j, hj⟩, hfj⟩
  have h_bridge : ∀ k : Fin 4, SameOrbit H.face (cut.ringFace k) u →
      SameOrbit H.face (cut.ringFace k) v → False := by
    intro k hku hkv
    have huv_f : SameOrbit H.face u (H.edge.f u) :=
      sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hku) hkv
    exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp h_mc.is_bridgeless u huv_f
  have h_par_next : ∀ k : Fin 4,
      SameOrbit H.face (cut.ringFace k) u →
      SameOrbit H.face (cut.ringFace ⟨(k.val + 1) % 4, Nat.mod_lt _ (by decide)⟩) v → False := by
    intro k hku hkv
    have h_f1 : SameOrbit H.face u (cut.cutDart k) :=
      sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hku) (cut.h_a k)
    have h_f2 : SameOrbit H.face (H.edge.f u) (H.edge.f (cut.cutDart k)) :=
      sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hkv) (cut.h_b k)
    exact mc_no_parallel_edges_of_two_darts H darts h_mc (hu_ne_cut k) h_f1 h_f2
  have h_par_prev : ∀ k : Fin 4,
      SameOrbit H.face (cut.ringFace ⟨(k.val + 1) % 4, Nat.mod_lt _ (by decide)⟩) u →
      SameOrbit H.face (cut.ringFace k) v → False := by
    intro k hku hkv
    have h_f1 : SameOrbit H.face v (cut.cutDart k) :=
      sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hkv) (cut.h_a k)
    have h_f2 : SameOrbit H.face (H.edge.f v) (H.edge.f (cut.cutDart k)) := by
      have h_ev : H.edge.f v = u := mc_edge_inv u
      rw [h_ev]
      exact sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hku) (cut.h_b k)
    exact mc_no_parallel_edges_of_two_darts H darts h_mc (hv_ne_cut k) h_f1 h_f2
  match i, j with
  | 0, 0 => exact False.elim (h_bridge i0 hfi hfj)
  | 1, 1 => exact False.elim (h_bridge i1 hfi hfj)
  | 2, 2 => exact False.elim (h_bridge i2 hfi hfj)
  | 3, 3 => exact False.elim (h_bridge i3 hfi hfj)
  | 0, 1 => exact False.elim (h_par_next i0 hfi hfj)
  | 1, 2 => exact False.elim (h_par_next i1 hfi hfj)
  | 2, 3 => exact False.elim (h_par_next i2 hfi hfj)
  | 3, 0 => exact False.elim (h_par_next i3 hfi (by simpa [i3] using hfj))
  | 1, 0 => exact False.elim (h_par_prev i0 hfi hfj)
  | 2, 1 => exact False.elim (h_par_prev i1 hfi hfj)
  | 3, 2 => exact False.elim (h_par_prev i2 hfi hfj)
  | 0, 3 => exact False.elim (h_par_prev i3 (by simpa [i3] using hfi) hfj)
  | 0, 2 => exact Or.inl ⟨u, hu_DL, hv_DL, hfi, hfj⟩
  | 2, 0 => exact Or.inl ⟨v, hv_DL, by simpa [v, mc_edge_inv] using hu_DL, hfj,
      by simpa [v, mc_edge_inv] using hfi⟩
  | 1, 3 =>
      refine Or.inr ⟨u, (cut.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) u).mpr hu_DL, ?_, ?_, ?_⟩
      · exact (cut.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) (H.edge.f u)).mpr hv_DL
      · exact hfi
      · exact hfj
  | 3, 1 =>
      refine Or.inr ⟨v, (cut.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) v).mpr hv_DL, ?_, ?_, ?_⟩
      · simp only [v, mc_edge_inv]
        exact (cut.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) u).mpr hu_DL
      · exact hfj
      · simp only [v, mc_edge_inv]
        exact hfi

theorem hasDiagChord02_half_closed_node {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4) {u : H.Dart}
    (huL : cut.capSingleVertex_DL u)
    (hvuL : cut.capSingleVertex_DL (H.edge.f u))
    (hf0 : SameOrbit H.face (cut.ringFace ⟨0, by decide⟩) u)
    (hf2 : SameOrbit H.face (cut.ringFace ⟨2, by decide⟩) (H.edge.f u)) :
    let a0 := cut.cutDart ⟨0, by decide⟩
    let a1 := cut.cutDart ⟨1, by decide⟩
    let v := H.edge.f u
    (∀ d, d = a0 ∨ d = a1 ∨ d = v → H.node.f d = a0 ∨ H.node.f d = a1 ∨ H.node.f d = v) ∧
    (∀ d, d = a0 ∨ d = a1 ∨ d = v → H.node.inv d = a0 ∨ H.node.inv d = a1 ∨ H.node.inv d = v) := by
  have h_uc := uncoupleCycle_two_components H darts h_mc.nodup h_mc.complete
    h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut
  rcases h_uc with ⟨hn4, he4_invol, -, -, -, -, hdisj4, hcut_sides4, hcut_fix4, hint4, -, -, -⟩
  let rf3 : Fin 3 → H.Dart := fun ⟨i, _⟩ =>
    match i with
    | 0 => cut.ringFace ⟨0, by decide⟩
    | 1 => cut.ringFace ⟨1, by decide⟩
    | _ => cut.ringFace ⟨2, by decide⟩
  let cd3 : Fin 3 → H.Dart := fun ⟨i, _⟩ =>
    match i with
    | 0 => cut.cutDart ⟨0, by decide⟩
    | 1 => cut.cutDart ⟨1, by decide⟩
    | _ => H.edge.f u
  have h_diff3 : ∀ i j : Fin 3, i ≠ j → ¬SameOrbit H.face (rf3 i) (rf3 j) := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 1, 1 => exact absurd rfl hij
    | 2, 2 => exact absurd rfl hij
    | 0, 1 => exact cut.h_diff ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    | 0, 2 => exact cut.h_diff ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
    | 1, 0 => exact cut.h_diff ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)
    | 1, 2 => exact cut.h_diff ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
    | 2, 0 => exact cut.h_diff ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide)
    | 2, 1 => exact cut.h_diff ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide)
  have h_a3 : ∀ i : Fin 3, SameOrbit H.face (rf3 i) (cd3 i) := by
    intro ⟨i, hi⟩
    match i with
    | 0 => exact cut.h_a ⟨0, by decide⟩
    | 1 => exact cut.h_a ⟨1, by decide⟩
    | 2 => exact hf2
  have h_b3 : ∀ i : Fin 3,
      SameOrbit H.face (rf3 ⟨(i.val + 1) % 3, Nat.mod_lt _ (by decide)⟩) (H.edge.f (cd3 i)) := by
    intro ⟨i, hi⟩
    match i with
    | 0 => exact cut.h_b ⟨0, by decide⟩
    | 1 => exact cut.h_b ⟨1, by decide⟩
    | 2 => simpa [rf3, cd3, mc_edge_inv] using hf0
  have h_disj3 : ∀ i j : Fin 3, H.edge.f (cd3 i) ≠ cd3 j := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    have hu_not_b : ∀ m : Fin 4, u ≠ H.edge.f (cut.cutDart m) := fun m hm =>
      hdisj4 u ⟨huL, by rw [hm]; exact (hcut_sides4 m).2⟩
    have hv_not_b : ∀ m : Fin 4, H.edge.f u ≠ H.edge.f (cut.cutDart m) := fun m hm =>
      hdisj4 (H.edge.f u) ⟨hvuL, by rw [hm]; exact (hcut_sides4 m).2⟩
    match i, j with
    | 0, 0 => exact cut.h_disj_edge ⟨0, by decide⟩ ⟨0, by decide⟩ heq
    | 0, 1 => exact cut.h_disj_edge ⟨0, by decide⟩ ⟨1, by decide⟩ heq
    | 1, 0 => exact cut.h_disj_edge ⟨1, by decide⟩ ⟨0, by decide⟩ heq
    | 1, 1 => exact cut.h_disj_edge ⟨1, by decide⟩ ⟨1, by decide⟩ heq
    | 0, 2 => exact hv_not_b ⟨0, by decide⟩ heq.symm
    | 1, 2 => exact hv_not_b ⟨1, by decide⟩ heq.symm
    | 2, 0 =>
        have h_eq : u = cut.cutDart ⟨0, by decide⟩ := by simpa [cd3, mc_edge_inv] using heq
        have h1 : SameOrbit H.face (cut.ringFace ⟨1, by decide⟩) (H.edge.f u) := by
          rw [h_eq]; exact cut.h_b ⟨0, by decide⟩
        exact cut.h_diff ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
          (sameOrbit_trans H.face h1 (sameOrbit_face_symm darts h_mc hf2))
    | 2, 1 =>
        have h_eq : u = cut.cutDart ⟨1, by decide⟩ := by simpa [cd3, mc_edge_inv] using heq
        have h1 : SameOrbit H.face (cut.ringFace ⟨0, by decide⟩) (cut.ringFace ⟨1, by decide⟩) :=
          sameOrbit_trans H.face hf0
            (by rw [h_eq]; exact sameOrbit_face_symm darts h_mc (cut.h_a ⟨1, by decide⟩))
        exact cut.h_diff ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide) h1
    | 2, 2 => exact mc_edge_ne_self H darts h_mc u (by simpa [cd3, mc_edge_inv] using heq.symm)
  let cut3 : H.FaceCycleCut 3 :=
    { hk := by decide
      ringFace := rf3
      cutDart := cd3
      h_diff := h_diff3
      h_a := h_a3
      h_b := h_b3
      h_disj_edge := h_disj3 }
  have h_uc3 := uncoupleCycle_two_components H darts h_mc.nodup h_mc.complete
    h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut3
  rcases h_uc3 with ⟨hn3, he3_invol, -, -, -, -, -, hcut_sides3, -, hint3, -, -, -⟩
  let T4 := cut.uncoupleTriple
  let T3 := cut3.uncoupleTriple
  let b0 := H.edge.f (cut.cutDart ⟨0, by decide⟩)
  have hDR_lift : ∀ x, ReachEN T4.e T4.n b0 x → cut3.rev.capSingleVertex_DL x := by
    intro x hrx
    have h_step : ∀ {y z : H.Dart}, ReachEN T4.e T4.n b0 y →
        StepEN T4.e T4.n y z → ReachEN T3.e T3.n y z := by
      intro y z hy hst
      have hy_notL : ¬cut.capSingleVertex_DL y := fun hL => hdisj4 y ⟨hL, hy⟩
      have h_noncut4 : T4.e.f y ≠ y →
          (∀ i : Fin 4, y ≠ cut.cutDart i ∧ y ≠ H.edge.f (cut.cutDart i)) := by
        intro hnf i
        exact ⟨fun h => hy_notL (by rw [h]; exact (hcut_sides4 i).1),
          fun h => hnf (by rw [h]; exact (hcut_fix4 i).2)⟩
      have h_noncut3_of_noncut4 :
          (∀ i : Fin 4, y ≠ cut.cutDart i ∧ y ≠ H.edge.f (cut.cutDart i)) →
          (∀ i : Fin 3, y ≠ cut3.cutDart i ∧ y ≠ H.edge.f (cut3.cutDart i)) := by
        intro hnc4 ⟨i, hi⟩
        match i with
        | 0 => exact hnc4 ⟨0, by decide⟩
        | 1 => exact hnc4 ⟨1, by decide⟩
        | 2 =>
            refine ⟨fun h => hy_notL (by rw [h]; exact hvuL),
              fun h => hy_notL (by change y = H.edge.f (H.edge.f u) at h; rw [mc_edge_inv] at h; rw [h]; exact huL)⟩
      cases hst with
      | n_fwd =>
          have hn_eq : T4.n.f y = T3.n.f y := by rw [hn4, hn3]
          rw [hn_eq]
          exact ⟨WalkEN.step (StepEN.n_fwd y) (WalkEN.refl _)⟩
      | n_bwd =>
          have hn_eq : T4.n.inv y = T3.n.inv y := by rw [hn4, hn3]
          rw [hn_eq]
          exact ⟨WalkEN.step (StepEN.n_bwd y) (WalkEN.refl _)⟩
      | e_fwd =>
          by_cases hy_fix : T4.e.f y = y
          · rw [hy_fix]; exact reachEN_refl T3.e T3.n y
          · have hnc4 := h_noncut4 hy_fix
            have hnc3 := h_noncut3_of_noncut4 hnc4
            have he_eq : T4.e.f y = T3.e.f y := by
              rw [(hint4 y hnc4).1, (hint3 y hnc3).1]
            rw [he_eq]
            exact ⟨WalkEN.step (StepEN.e_fwd y) (WalkEN.refl _)⟩
      | e_bwd =>
          have hinv4 : T4.e.inv y = T4.e.f y := by
            calc T4.e.inv y = T4.e.inv (T4.e.f (T4.e.f y)) := by rw [he4_invol y]
            _ = T4.e.f y := T4.e.left_inv _
          have hinv3 : T3.e.inv y = T3.e.f y := by
            calc T3.e.inv y = T3.e.inv (T3.e.f (T3.e.f y)) := by rw [he3_invol y]
            _ = T3.e.f y := T3.e.left_inv _
          rw [hinv4]
          by_cases hy_fix : T4.e.f y = y
          · rw [hy_fix]; exact reachEN_refl T3.e T3.n y
          · have hnc4 := h_noncut4 hy_fix
            have hnc3 := h_noncut3_of_noncut4 hnc4
            have he_eq : T4.e.f y = T3.e.f y := by
              rw [(hint4 y hnc4).1, (hint3 y hnc3).1]
            rw [he_eq, ← hinv3]
            exact ⟨WalkEN.step (StepEN.e_bwd y) (WalkEN.refl _)⟩
    have h_walk : ∀ {a z : H.Dart}, WalkEN T4.e T4.n a z →
        ReachEN T4.e T4.n b0 a → ReachEN T3.e T3.n a z := by
      intro a z hw ha
      induction hw with
      | refl => exact reachEN_refl T3.e T3.n _
      | @step x y z hxy hyz ih =>
          have hy : ReachEN T4.e T4.n b0 y :=
            reachEN_trans T4.e T4.n ha ⟨WalkEN.step hxy (WalkEN.refl _)⟩
          exact reachEN_trans T3.e T3.n (h_step ha hxy) (ih hy)
    rcases hrx with ⟨w⟩
    exact (cut3.rev_DL_iff_DR darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) x).mpr (h_walk w (reachEN_refl T4.e T4.n b0))
  have hDR3_ge5 : 5 ≤ (darts.filter (fun x => decide (cut3.rev.capSingleVertex_DL x))).length := by
    have h_par4 := side_parity_divisibility_cap darts h_mc cut
    have hR4_le := h_par4.2.2.1
    let fR4 := darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))
    let fR3 := darts.filter (fun x => decide (cut3.rev.capSingleVertex_DL x))
    have hu_in_R3 : u ∈ fR3 := by
      refine List.mem_filter.mpr ⟨h_mc.complete u, decide_eq_true ?_⟩
      have hu_dr3 : ReachEN T3.e T3.n (H.edge.f (cut3.cutDart ⟨0, by decide⟩)) u := by
        have h_b2 := (hcut_sides3 ⟨2, by decide⟩).2
        have h_b2_eq : H.edge.f (cut3.cutDart ⟨2, by decide⟩) = u := by
          change H.edge.f (H.edge.f u) = u; exact mc_edge_inv u
        rw [h_b2_eq] at h_b2
        exact h_b2
      exact (cut3.rev_DL_iff_DR darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) u).mpr hu_dr3
    have hu_not_R4 : u ∉ fR4 := by
      intro hmem
      have hu_dr4 := (cut.rev_DL_iff_DR darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) u).mp (of_decide_eq_true (List.mem_filter.mp hmem).2)
      exact hdisj4 u ⟨huL, hu_dr4⟩
    have h_sub : ∀ x ∈ (u :: fR4), x ∈ fR3 := by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx4
      · exact hu_in_R3
      · have hx_dr4 := (cut.rev_DL_iff_DR darts h_mc.nodup h_mc.complete h_mc.is_planar
          (mc_numComponents_eq_one H darts h_mc) x).mp (of_decide_eq_true (List.mem_filter.mp hx4).2)
        exact List.mem_filter.mpr ⟨h_mc.complete x, decide_eq_true (hDR_lift x hx_dr4)⟩
    have hnd : (u :: fR4).Nodup := List.nodup_cons.mpr ⟨hu_not_R4, nodup_filter_sc _ h_mc.nodup⟩
    have h_le := sc_nodup_length_le_of_subset (u :: fR4) fR3 hnd h_sub
    dsimp only [fR3, fR4] at h_le
    simp only [List.length_cons] at h_le
    omega
  have hDL3_eq3 : (darts.filter (fun x => decide (cut3.capSingleVertex_DL x))).length = 3 := by
    rcases mc_three_cycle_is_facial_dual H darts h_mc cut3 with h3 | h3
    · exact h3
    · omega
  have horb3 := (mc_three_cycle_facial_orbits_dual H darts h_mc cut3 hDL3_eq3).1
  intro a0 a1 v
  have h_cl_f : ∀ d, d = a0 ∨ d = a1 ∨ d = v → H.node.f d = a0 ∨ H.node.f d = a1 ∨ H.node.f d = v := by
    intro d hd
    have hd_dl3 : cut3.capSingleVertex_DL d := (horb3 d).mpr hd
    have hnd_dl3 : cut3.capSingleVertex_DL (H.node.f d) := by
      rw [← hn3]
      exact reachEN_trans T3.e T3.n hd_dl3 ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩
    exact (horb3 (H.node.f d)).mp hnd_dl3
  have h_cl_inv : ∀ d, d = a0 ∨ d = a1 ∨ d = v → H.node.inv d = a0 ∨ H.node.inv d = a1 ∨ H.node.inv d = v := by
    intro d hd
    have hd_dl3 : cut3.capSingleVertex_DL d := (horb3 d).mpr hd
    have hnd_dl3 : cut3.capSingleVertex_DL (H.node.inv d) := by
      rw [← hn3]
      exact reachEN_trans T3.e T3.n hd_dl3 ⟨WalkEN.step (StepEN.n_bwd d) (WalkEN.refl _)⟩
    exact (horb3 (H.node.inv d)).mp hnd_dl3
  exact ⟨h_cl_f, h_cl_inv⟩

theorem separating_four_cycle_no_chord02_L {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (hL12 : 12 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length)
    (h_ch : HasDiagChord02 cut) : False := by
  rcases h_ch with ⟨u, huL, hvuL, hf0, hf2⟩
  have h_uc := uncoupleCycle_two_components H darts h_mc.nodup h_mc.complete
    h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut
  rcases h_uc with ⟨hn4, he4_invol, -, -, -, -, hdisj4, hcut_sides4, -, -, -, -, -⟩
  have h_cl1 := hasDiagChord02_half_closed_node darts h_mc cut huL hvuL hf0 hf2
  let cut2 := cut.rot1.rot1
  have h_rot2_dl : ∀ x, cut2.capSingleVertex_DL x ↔ cut.capSingleVertex_DL x := fun x =>
    Iff.trans (cut.rot1.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) x)
      (cut.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) x)
  have h_cl2 := hasDiagChord02_half_closed_node darts h_mc cut2
    ((h_rot2_dl (H.edge.f u)).mpr hvuL)
    (by simpa [mc_edge_inv] using (h_rot2_dl u).mpr huL)
    (by simpa [cut2, FaceCycleCut.rot1] using hf2)
    (by simpa [cut2, FaceCycleCut.rot1, mc_edge_inv] using hf0)
  let a0 := cut.cutDart ⟨0, by decide⟩
  let a1 := cut.cutDart ⟨1, by decide⟩
  let a2 := cut.cutDart ⟨2, by decide⟩
  let a3 := cut.cutDart ⟨3, by decide⟩
  let v := H.edge.f u
  let S6 := [a0, a1, v, a2, a3, u]
  have ha2_eq : cut2.cutDart ⟨0, by decide⟩ = a2 := rfl
  have ha3_eq : cut2.cutDart ⟨1, by decide⟩ = a3 := rfl
  have hv2_eq : H.edge.f (H.edge.f u) = u := mc_edge_inv u
  have h_cl1_f := h_cl1.1
  have h_cl1_inv := h_cl1.2
  have h_cl2_f := h_cl2.1
  have h_cl2_inv := h_cl2.2
  rw [ha2_eq, ha3_eq, hv2_eq] at h_cl2_f h_cl2_inv
  have hu_dl : ∀ i : Fin 4, u ≠ cut.cutDart i := by
    intro ⟨i, hi⟩ heq
    have hf_u : SameOrbit H.face (cut.ringFace ⟨i, hi⟩) u := by rw [heq]; exact cut.h_a ⟨i, hi⟩
    match i with
    | 0 =>
        have hv_b : v = H.edge.f (cut.cutDart ⟨0, by decide⟩) := by dsimp only [v]; rw [heq]
        have hDR : ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
            (H.edge.f (cut.cutDart ⟨0, by decide⟩)) v := by
          rw [hv_b]; exact (hcut_sides4 ⟨0, by decide⟩).2
        exact hdisj4 v ⟨hvuL, hDR⟩
    | 1 =>
        exact cut.h_diff ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
          (sameOrbit_trans H.face hf0 (sameOrbit_face_symm darts h_mc hf_u))
    | 2 =>
        exact cut.h_diff ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
          (sameOrbit_trans H.face hf0 (sameOrbit_face_symm darts h_mc hf_u))
    | 3 =>
        exact cut.h_diff ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide)
          (sameOrbit_trans H.face hf0 (sameOrbit_face_symm darts h_mc hf_u))
    | n + 4 => exact absurd hi (by omega)
  have hv_dl : ∀ i : Fin 4, v ≠ cut.cutDart i := by
    intro ⟨i, hi⟩ heq
    have hf_v : SameOrbit H.face (cut.ringFace ⟨i, hi⟩) v := by rw [heq]; exact cut.h_a ⟨i, hi⟩
    match i with
    | 0 =>
        exact cut.h_diff ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide)
          (sameOrbit_trans H.face hf2 (sameOrbit_face_symm darts h_mc hf_v))
    | 1 =>
        exact cut.h_diff ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide)
          (sameOrbit_trans H.face hf2 (sameOrbit_face_symm darts h_mc hf_v))
    | 2 =>
        have hu_b : u = H.edge.f (cut.cutDart ⟨2, by decide⟩) := by
          calc u = H.edge.f v := (mc_edge_inv u).symm
          _ = H.edge.f (cut.cutDart ⟨2, by decide⟩) := congrArg H.edge.f heq
        have hDR : ReachEN cut.uncoupleTriple.e cut.uncoupleTriple.n
            (H.edge.f (cut.cutDart ⟨0, by decide⟩)) u := by
          rw [hu_b]; exact (hcut_sides4 ⟨2, by decide⟩).2
        exact hdisj4 u ⟨huL, hDR⟩
    | 3 =>
        exact cut.h_diff ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
          (sameOrbit_trans H.face hf2 (sameOrbit_face_symm darts h_mc hf_v))
    | n + 4 => exact absurd hi (by omega)
  have h_uc_fix := (uncoupleCycle_two_components H darts h_mc.nodup h_mc.complete
    h_mc.is_planar (mc_numComponents_eq_one H darts h_mc) cut).2.2.2.2.2.2.2.2.1
  have h1_mem : ∀ d, (d = cut.cutDart ⟨0, by decide⟩ ∨ d = cut.cutDart ⟨1, by decide⟩ ∨
      d = H.edge.f u) → d ∈ S6 := by
    intro d hd
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false]
    rcases hd with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  have h2_mem : ∀ d, (d = a2 ∨ d = a3 ∨ d = u) → d ∈ S6 := by
    intro d hd
    simp only [S6, List.mem_cons, List.mem_nil_iff, or_false]
    rcases hd with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have h_step_S6 : ∀ {x y : H.Dart}, StepEN cut.uncoupleTriple.e cut.uncoupleTriple.n x y →
      x ∈ S6 → y ∈ S6 := by
    intro x y hst hx
    cases hst with
    | n_fwd =>
        rw [hn4]
        simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with hx | hx | hx | hx | hx | hx <;> rw [hx]
        · exact h1_mem _ (h_cl1_f (cut.cutDart ⟨0, by decide⟩) (Or.inl rfl))
        · exact h1_mem _ (h_cl1_f (cut.cutDart ⟨1, by decide⟩) (Or.inr (Or.inl rfl)))
        · exact h1_mem _ (h_cl1_f (H.edge.f u) (Or.inr (Or.inr rfl)))
        · exact h2_mem _ (h_cl2_f a2 (Or.inl rfl))
        · exact h2_mem _ (h_cl2_f a3 (Or.inr (Or.inl rfl)))
        · exact h2_mem _ (h_cl2_f u (Or.inr (Or.inr rfl)))
    | n_bwd =>
        rw [hn4]
        simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with hx | hx | hx | hx | hx | hx <;> rw [hx]
        · exact h1_mem _ (h_cl1_inv (cut.cutDart ⟨0, by decide⟩) (Or.inl rfl))
        · exact h1_mem _ (h_cl1_inv (cut.cutDart ⟨1, by decide⟩) (Or.inr (Or.inl rfl)))
        · exact h1_mem _ (h_cl1_inv (H.edge.f u) (Or.inr (Or.inr rfl)))
        · exact h2_mem _ (h_cl2_inv a2 (Or.inl rfl))
        · exact h2_mem _ (h_cl2_inv a3 (Or.inr (Or.inl rfl)))
        · exact h2_mem _ (h_cl2_inv u (Or.inr (Or.inr rfl)))
    | e_fwd =>
        simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [(h_uc_fix ⟨0, by decide⟩).1]; simp [a0]
        · rw [(h_uc_fix ⟨1, by decide⟩).1]; simp [a1]
        · rw [(dl_edge_of_ne_cutDart darts h_mc cut hvuL hv_dl).1]; simp [v, mc_edge_inv]
        · rw [(h_uc_fix ⟨2, by decide⟩).1]; simp [a2]
        · rw [(h_uc_fix ⟨3, by decide⟩).1]; simp [a3]
        · rw [(dl_edge_of_ne_cutDart darts h_mc cut huL hu_dl).1]; simp [v]
    | e_bwd =>
        have hinv : ∀ z, cut.uncoupleTriple.e.inv z = cut.uncoupleTriple.e.f z := fun z => by
          calc cut.uncoupleTriple.e.inv z =
              cut.uncoupleTriple.e.inv (cut.uncoupleTriple.e.f (cut.uncoupleTriple.e.f z)) := by
                rw [he4_invol z]
          _ = cut.uncoupleTriple.e.f z := cut.uncoupleTriple.e.left_inv _
        rw [hinv]
        simp only [S6, List.mem_cons, List.mem_nil_iff, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [(h_uc_fix ⟨0, by decide⟩).1]; simp [a0]
        · rw [(h_uc_fix ⟨1, by decide⟩).1]; simp [a1]
        · rw [(dl_edge_of_ne_cutDart darts h_mc cut hvuL hv_dl).1]; simp [v, mc_edge_inv]
        · rw [(h_uc_fix ⟨2, by decide⟩).1]; simp [a2]
        · rw [(h_uc_fix ⟨3, by decide⟩).1]; simp [a3]
        · rw [(dl_edge_of_ne_cutDart darts h_mc cut huL hu_dl).1]; simp [v]
  have h_walk_S6 : ∀ {x y : H.Dart}, WalkEN cut.uncoupleTriple.e cut.uncoupleTriple.n x y →
      x ∈ S6 → y ∈ S6 := by
    intro x y hw hx
    induction hw with
    | refl => exact hx
    | step hst _ ih => exact ih (h_step_S6 hst hx)
  have h_sub : ∀ y ∈ darts.filter (fun x => decide (cut.capSingleVertex_DL x)), y ∈ S6 := by
    intro y hy
    rcases of_decide_eq_true (List.mem_filter.mp hy).2 with ⟨w⟩
    exact h_walk_S6 w (by simp [S6, a0])
  have h_le := sc_nodup_length_le_of_subset
    (darts.filter (fun x => decide (cut.capSingleVertex_DL x))) S6
    (nodup_filter_sc _ h_mc.nodup) h_sub
  have hS6_len : S6.length = 6 := rfl
  omega

theorem separating_four_cycle_no_chord_both {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (hL12 : 12 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length)
    (hR12 : 12 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) :
    ¬HasDiagChord02 cut ∧ ¬HasDiagChord13 cut ∧
    ¬HasDiagChord02 cut.rev ∧ ¬HasDiagChord13 cut.rev := by
  have hL_rot12 : 12 ≤ (darts.filter (fun x => decide (cut.rot1.capSingleVertex_DL x))).length := by
    have h_eq : darts.filter (fun x => decide (cut.rot1.capSingleVertex_DL x)) =
        darts.filter (fun x => decide (cut.capSingleVertex_DL x)) := by
      congr 1; funext x
      exact decide_eq_decide.mpr (cut.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) x)
    rw [h_eq]; exact hL12
  have hR_rot12 : 12 ≤ (darts.filter (fun x => decide (cut.rev.rot1.capSingleVertex_DL x))).length := by
    have h_eq : darts.filter (fun x => decide (cut.rev.rot1.capSingleVertex_DL x)) =
        darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x)) := by
      congr 1; funext x
      exact decide_eq_decide.mpr (cut.rev.rot1_DL_iff darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) x)
    rw [h_eq]; exact hR12
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact separating_four_cycle_no_chord02_L darts h_mc cut hL12
  · exact separating_four_cycle_no_chord02_L darts h_mc cut.rot1 hL_rot12
  · exact separating_four_cycle_no_chord02_L darts h_mc cut.rev hR12
  · exact separating_four_cycle_no_chord02_L darts h_mc cut.rev.rot1 hR_rot12

end K4ParityAndChords

section K4SurgeriesAndKempe

def IsState2 (f : Fin 4 → Color) : Prop :=
  f ⟨0, by decide⟩ = f ⟨2, by decide⟩ ∧ f ⟨1, by decide⟩ = f ⟨3, by decide⟩

def IsState02 (f : Fin 4 → Color) : Prop :=
  f ⟨0, by decide⟩ = f ⟨2, by decide⟩ ∧ f ⟨1, by decide⟩ ≠ f ⟨3, by decide⟩

def IsState13 (f : Fin 4 → Color) : Prop :=
  f ⟨0, by decide⟩ ≠ f ⟨2, by decide⟩ ∧ f ⟨1, by decide⟩ = f ⟨3, by decide⟩

def IsState4 (f : Fin 4 → Color) : Prop :=
  f ⟨0, by decide⟩ ≠ f ⟨2, by decide⟩ ∧ f ⟨1, by decide⟩ ≠ f ⟨3, by decide⟩

private def subtypeFilterList {α : Type} (l : List α) (P : α → Prop) [DecidablePred P] :
    List { x // P x } :=
  match l with
  | [] => []
  | a :: rest =>
      if h : P a then ⟨a, h⟩ :: subtypeFilterList rest P
      else subtypeFilterList rest P

private theorem mem_subtypeFilterList {α : Type} (l : List α) (P : α → Prop) [DecidablePred P]
    (x : { a // P a }) : x ∈ subtypeFilterList l P ↔ x.val ∈ l := by
  induction l with
  | nil => simp [subtypeFilterList]
  | cons a rest ih =>
      simp only [subtypeFilterList]
      by_cases h : P a
      · simp only [dif_pos h, List.mem_cons]
        constructor
        · rintro (rfl | hm)
          · exact Or.inl rfl
          · exact Or.inr (ih.mp hm)
        · rintro (heq | hm)
          · left; exact Subtype.ext heq
          · right; exact ih.mpr hm
      · simp only [dif_neg h, List.mem_cons]
        constructor
        · intro hm; exact Or.inr (ih.mp hm)
        · rintro (heq | hm)
          · exact absurd (heq ▸ x.property) h
          · exact ih.mpr hm

private theorem nodup_subtypeFilterList {α : Type} (l : List α) (P : α → Prop) [DecidablePred P]
    (hnd : l.Nodup) : (subtypeFilterList l P).Nodup := by
  induction l with
  | nil => simp [subtypeFilterList]
  | cons a rest ih =>
      rcases List.nodup_cons.mp hnd with ⟨ha, hrest⟩
      simp only [subtypeFilterList]
      by_cases h : P a
      · simp only [dif_pos h, List.nodup_cons]
        refine ⟨fun hm => ha ((mem_subtypeFilterList rest P ⟨a, h⟩).mp hm), ih hrest⟩
      · simp only [dif_neg h]
        exact ih hrest

private theorem length_subtypeFilterList {α : Type} (l : List α) (P : α → Prop) [DecidablePred P] :
    (subtypeFilterList l P).length = (l.filter (fun x => decide (P x))).length := by
  induction l with
  | nil => simp [subtypeFilterList]
  | cons a rest ih =>
      simp only [subtypeFilterList, List.filter]
      by_cases h : P a
      · simp [dif_pos h, decide_eq_true h, ih]
      · simp [dif_neg h, decide_eq_false h, ih]

private theorem countRelClasses_eq_one_of_all {D : Type} (R : D → D → Prop) [DecidableRel R]
    (l : List D) (hne : l ≠ []) (hall : ∀ x y, R x y) :
    countRelClasses R l = 1 := by
  cases l with
  | nil => exact absurd rfl hne
  | cons d ds =>
      clear hne
      rw [countRelClasses_cons]
      have hflt : List.filter (fun x => !decide (R d x)) ds = [] := by
        induction ds with
        | nil => rfl
        | cons x xs ih =>
            simp only [List.filter, decide_eq_true (hall d x), Bool.not_true]
            exact ih
      rw [hflt]
      have h0 := countRelClasses_le_length R 0 [] (Nat.le_refl 0)
      simp only [List.length_nil] at h0
      omega

private theorem perm_ext_sc {D : Type} {p q : Perm D} (h : ∀ x, p.f x = q.f x) : p = q := by
  cases p with
  | mk f1 i1 l1 r1 =>
    cases q with
    | mk f2 i2 l2 r2 =>
      have hf : f1 = f2 := funext h
      subst hf
      have hi : i1 = i2 := funext fun x => by
        calc i1 x = i1 (f1 (i2 x)) := by rw [r2 x]
        _ = i2 x := l1 (i2 x)
      subst hi
      rfl

private theorem subtype_beq_eq_dec {α : Type} [DecidableEq α] (P : α → Prop) :
    (@Subtype.instBEq α P (@instBEqOfDecidableEq α _) : BEq { x // P x }) =
      @instBEqOfDecidableEq { x // P x } _ := by
  have h : (fun x y : { x // P x } => (@Subtype.instBEq α P (@instBEqOfDecidableEq α _)).beq x y) =
      (fun x y : { x // P x } => (@instBEqOfDecidableEq { x // P x } _).beq x y) := by
    funext x y
    change decide (x.val = y.val) = decide (x = y)
    by_cases hxy : x.val = y.val
    · have heq : x = y := Subtype.ext hxy; subst heq; simp
    · have hne : x ≠ y := fun heq => hxy (congrArg Subtype.val heq); simp [hxy, hne]
  exact congrArg BEq.mk h

private theorem decEq_beq_eq {α : Type} (d1 d2 : DecidableEq α) :
    (@instBEqOfDecidableEq α d1 : BEq α) = @instBEqOfDecidableEq α d2 := by
  have h : (fun x y : α => (@instBEqOfDecidableEq α d1).beq x y) =
      (fun x y : α => (@instBEqOfDecidableEq α d2).beq x y) := by
    funext x y
    change @decide (x = y) (d1 x y) = @decide (x = y) (d2 x y)
    rw [Subsingleton.elim (d1 x y) (d2 x y)]
  exact congrArg BEq.mk h

private theorem cut_inArcL_disjoint {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    {k : Nat} (cut : H.FaceCycleCut k) {i j : Fin k} {d : H.Dart}
    (hi : FaceCycleCut.inArcL darts h_all cut i d)
    (hj : FaceCycleCut.inArcL darts h_all cut j d) : i = j := by
  apply Classical.byContradiction
  intro hne
  have h1 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut i d).mp hi
  have h2 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut j d).mp hj
  have hsym := sameOrbit_symm_of_complete H.face darts h_all h2.1
  exact cut.h_diff i j hne (sameOrbit_trans H.face h1.1 hsym)

private theorem reachEN_trans_sc {D : Type} {e n : Perm D} {x y z : D}
    (h1 : ReachEN e n x y) (h2 : ReachEN e n y z) : ReachEN e n x z :=
  reachEN_trans e n h1 h2

private theorem sum_inr_not_mem_getOrbit_left {α β : Type} [DecidableEq α] [DecidableEq β]
    [bSum : BEq (α ⊕ β)] (hb : bSum = @instBEqOfDecidableEq (α ⊕ β) _)
    (p : Perm α) (q : Perm (α ⊕ β)) (hq : ∀ a : α, q.f (Sum.inl a) = Sum.inl (p.f a))
    (darts : List (α ⊕ β)) (hall : ∀ z, z ∈ darts) (fuel : Nat) (hf : darts.length ≤ fuel)
    (a : α) (b : β) :
    Sum.inr b ∉ getOrbit q fuel (Sum.inl a) := by
  subst hb
  intro hm
  rcases (sameOrbit_iff_mem_getOrbit q darts hall hf (Sum.inl a) (Sum.inr b)).mpr hm with ⟨n, hn⟩
  have hiter : ∀ k, Perm.iter q k (Sum.inl a) = Sum.inl (Perm.iter p k a) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        simp only [Perm.iter]
        rw [ih, hq]
  rw [hiter n] at hn
  cases hn

private theorem pinch_arc_sameOrbit_T2 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (cut : H.FaceCycleCut 4)
    (a' : Fin 4 → { d // cut.capSingleVertex_DL d })
    (ha'_val : ∀ i : Fin 4, (a' i).val = cut.cutDart i)
    (T1 T2 : PermTriple { d // cut.capSingleVertex_DL d })
    (hT1_def : T1 = coupleEdge cut.capSingleVertex_TL (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩))
    (hT2_def : T2 = coupleEdge T1 (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩))
    (m : Nat) (hm : m < 4) :
    ∀ x : { d // cut.capSingleVertex_DL d },
      FaceCycleCut.inArcL darts h_all cut ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩ x.val →
      SameOrbit T2.f x (a' ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩) := by
  intro x hxin
  let TL := cut.capSingleVertex_TL
  let pos := FaceCycleCut.posL darts h_all cut
  let a_tgt := a' ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩
  rcases (FaceCycleCut.inArcL_iff_posL_block darts h_all cut hm x.val).mp hxin with
    ⟨r, hrm, hrM, hr_eq⟩
  have hr_eq' : Perm.iter TL.f r (a' ⟨0, by decide⟩) = x := by
    apply Subtype.ext
    dsimp [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
    rw [restrictPermPred_iter, ha'_val]
    exact hr_eq
  have ha_step : ∀ j : Nat,
      Perm.iter TL.f (pos j) (a' ⟨0, by decide⟩) =
        a' ⟨j % 4, Nat.mod_lt _ (by decide)⟩ := by
    intro j
    apply Subtype.ext
    dsimp [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
    rw [restrictPermPred_iter, ha'_val, ha'_val]
    exact FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut j
  have hT2_step : ∀ y : { d // cut.capSingleVertex_DL d },
      (∀ i : Fin 4, y ≠ a' i) → T2.f.f y = TL.f.f y := by
    intro y hy
    subst hT2_def hT1_def
    have hy0 := hy ⟨0, by decide⟩
    have hy1 := hy ⟨1, by decide⟩
    have hy2 := hy ⟨2, by decide⟩
    have hy3 := hy ⟨3, by decide⟩
    change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩)
      (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) y)) = TL.f.f y
    simp only [swapFun, hy3, hy2, hy1, hy0, ↓reduceIte]
  have ha'_disj : ∀ y : { d // cut.capSingleVertex_DL d },
      FaceCycleCut.inArcL darts h_all cut ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩ y.val →
      ∀ i : Fin 4, i ≠ ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩ → y ≠ a' i := by
    intro y hy i hi heq
    apply hi
    apply Eq.symm
    apply cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut hy
    rw [heq, ha'_val i]
    exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut i
  have h_inv : ∀ s : Nat, r + s ≤ pos (m + 1) →
      SameOrbit T2.f x (Perm.iter TL.f (r + s) (a' ⟨0, by decide⟩)) ∨
      SameOrbit T2.f x a_tgt := by
    intro s hs
    induction s with
    | zero =>
        left
        simp only [Nat.add_zero]
        rw [hr_eq']
        exact sameOrbit_refl T2.f x
    | succ k ih =>
        have hk : r + k < pos (m + 1) := by dsimp [pos] at hs ⊢; omega
        rcases ih (by omega) with hso | hdone
        · let y := Perm.iter TL.f (r + k) (a' ⟨0, by decide⟩)
          have hy_arc : FaceCycleCut.inArcL darts h_all cut
              ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩ y.val := by
            refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut hm y.val).mpr ⟨r + k, ?_, ?_, ?_⟩
            · omega
            · dsimp [pos] at hk; omega
            · dsimp only [y, TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
              rw [← ha'_val ⟨0, by decide⟩]
              exact (restrictPermPred_iter _ _ _ _ _).symm
          by_cases hy_eq : y = a_tgt
          · right
            rw [← hy_eq]
            exact hso
          · left
            have hy_all : ∀ i : Fin 4, y ≠ a' i := by
              intro i
              by_cases hi : i = ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩
              · rw [hi]; exact hy_eq
              · exact ha'_disj y hy_arc i hi
            have hnext : Perm.iter TL.f (r + (k + 1)) (a' ⟨0, by decide⟩) = T2.f.f y := by
              rw [show r + (k + 1) = (r + k) + 1 by omega]
              exact (hT2_step y hy_all).symm
            rw [hnext]
            exact sameOrbit_trans T2.f hso ⟨1, rfl⟩
        · exact Or.inr hdone
  rcases h_inv (pos (m + 1) - r) (by dsimp [pos]; omega) with h1 | h2
  · rw [show r + (pos (m + 1) - r) = pos (m + 1) by dsimp [pos]; omega] at h1
    rw [ha_step (m + 1)] at h1
    exact h1
  · exact h2

private theorem pinch_coloring_of_no_chord02 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4) (h_no02 : ¬HasDiagChord02 cut) :
    ∃ colL : (cut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc)).FaceColoring,
      IsState2 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut colL) ∨
      IsState02 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut colL) := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  have hunc := uncoupleCycle_two_components H darts h_nd h_all h_planar h_conn cut
  have hn4 : cut.uncoupleTriple.n = H.node := hunc.1
  have he4_invol := hunc.2.1
  have hg4 := hunc.2.2.1
  have h_uc_fix := hunc.2.2.2.2.2.2.2.2.1
  have h_uc_out := hunc.2.2.2.2.2.2.2.2.2.1
  have hbr_no := (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_all).mp h_br
  let DL := cut.capSingleVertex_DL
  let D_L := { d : H.Dart // DL d }
  let darts_DL : List D_L := subtypeFilterList darts DL
  have hDL_nd : darts_DL.Nodup := nodup_subtypeFilterList darts DL h_nd
  have hDL_all : ∀ x : D_L, x ∈ darts_DL := fun x =>
    (mem_subtypeFilterList darts DL x).mpr (h_all x.val)
  have hDL_len : darts_DL.length = (darts.filter (fun x => decide (DL x))).length :=
    length_subtypeFilterList darts DL
  have hsp := side_parity_divisibility_cap darts h_mc cut
  have hsum := side_lengths_sum darts h_nd h_all h_planar h_conn cut
  have hDL_lt : darts_DL.length < darts.length := by
    dsimp only [DL] at hDL_len
    rcases hsp.2 with ⟨_, h4R, _⟩
    omega
  let a' : Fin 4 → D_L := fun i => ⟨cut.cutDart i,
    cut.inArcL_sub_DL darts h_nd h_all h_planar h_conn
      (FaceCycleCut.cutDart_mem_inArcL darts h_all cut i)⟩
  have ha'_val : ∀ i : Fin 4, (a' i).val = cut.cutDart i := fun _ => rfl
  have ha'_inj : ∀ i j : Fin 4, i ≠ j → a' i ≠ a' j := by
    intro i j hij heq
    exact cutDart_ne_of_ne darts h_mc cut hij (congrArg Subtype.val heq)
  have hDL_ne : darts_DL ≠ [] := by
    intro hnil
    have hmem := hDL_all (a' ⟨0, by decide⟩)
    rw [hnil] at hmem
    simp at hmem
  let TL : PermTriple D_L := cut.capSingleVertex_TL
  have hTL_invol : ∀ x : D_L, TL.e.f (TL.e.f x) = x := fun x => by
    apply Subtype.ext
    exact he4_invol x.val
  have hTL_fix : ∀ i : Fin 4, TL.e.f (a' i) = a' i := fun i => by
    apply Subtype.ext
    exact (h_uc_fix i).1
  have hTL_all_conn : ∀ x y : D_L, ReachEN TL.e TL.n x y := by
    intro x y
    have hx : ReachEN TL.e TL.n (a' ⟨0, by decide⟩) x := by
      dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
      exact (reachEN_restrictTriple_iff cut.uncoupleTriple.e cut.uncoupleTriple.n DL _ _ _ _).mpr x.property
    have hy : ReachEN TL.e TL.n (a' ⟨0, by decide⟩) y := by
      dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
      exact (reachEN_restrictTriple_iff cut.uncoupleTriple.e cut.uncoupleTriple.n DL _ _ _ _).mpr y.property
    exact reachEN_trans_sc (reachEN_symm _ _ hx) hy
  have hTL_rc : countRelClasses (ReachEN TL.e TL.n) darts_DL = 1 :=
    countRelClasses_eq_one_of_all _ darts_DL hDL_ne hTL_all_conn
  have hTL_g0 : genusDeficit TL darts_DL.length darts_DL = 0 := by
    have h0 := genusDeficit_nonneg TL darts_DL hDL_nd hDL_all (Nat.le_refl _)
    have hle : genusDeficit TL darts_DL.length darts_DL ≤
        genusDeficit cut.uncoupleTriple darts.length darts := by
      dsimp only [TL, FaceCycleCut.capSingleVertex_TL]
      exact genusDeficit_restrictTriple_le cut.uncoupleTriple darts.length darts_DL.length
        darts h_nd h_all (Nat.le_refl _) DL _ _ darts_DL hDL_nd hDL_all (Nat.le_refl _)
    rw [hg4] at hle
    omega
  have ha_in_TL : ∀ j : Fin 4,
      a' j ∈ @getOrbit D_L (@instBEqOfDecidableEq D_L _) TL.f darts_DL.length (a' ⟨0, by decide⟩) := by
    intro j
    apply (sameOrbit_iff_mem_getOrbit TL.f darts_DL hDL_all (Nat.le_refl _) _ _).mp
    refine ⟨FaceCycleCut.posL darts h_all cut j.val, ?_⟩
    apply Subtype.ext
    dsimp [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
    rw [restrictPermPred_iter, ha'_val, ha'_val]
    have hm := FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut j.val
    have hjmod : (⟨j.val % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = j := by
      apply Fin.ext; exact Nat.mod_eq_of_lt j.isLt
    rw [hjmod] at hm
    exact hm
  let T1 : PermTriple D_L := coupleEdge TL (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩)
  have hc1 := coupleEdge_sameFace TL darts_DL hDL_all (Nat.le_refl _)
    (hTL_fix ⟨0, by decide⟩) (hTL_fix ⟨1, by decide⟩)
    (ha'_inj ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)) (ha_in_TL ⟨1, by decide⟩)
  dsimp only at hc1
  change (T1.e.f (a' ⟨0, by decide⟩) = a' ⟨1, by decide⟩ ∧
      T1.e.f (a' ⟨1, by decide⟩) = a' ⟨0, by decide⟩) ∧
    (∀ {x y}, ReachEN T1.e T1.n x y ↔ ReachEN TL.e TL.n x y) ∧
    countRelClasses (ReachEN T1.e T1.n) darts_DL = countRelClasses (ReachEN TL.e TL.n) darts_DL ∧
    countOrbits T1.e darts_DL.length darts_DL + 1 = countOrbits TL.e darts_DL.length darts_DL ∧
    countOrbits T1.f darts_DL.length darts_DL = countOrbits TL.f darts_DL.length darts_DL + 1 ∧
    genusDeficit T1 darts_DL.length darts_DL = genusDeficit TL darts_DL.length darts_DL at hc1
  have hT1_fix2 : T1.e.f (a' ⟨2, by decide⟩) = a' ⟨2, by decide⟩ := by
    rw [coupleEdge_e_of_ne TL (hTL_fix ⟨0, by decide⟩) (hTL_fix ⟨1, by decide⟩)
      (ha'_inj ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide))
      (ha'_inj ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide))]
    exact hTL_fix ⟨2, by decide⟩
  have hT1_fix3 : T1.e.f (a' ⟨3, by decide⟩) = a' ⟨3, by decide⟩ := by
    rw [coupleEdge_e_of_ne TL (hTL_fix ⟨0, by decide⟩) (hTL_fix ⟨1, by decide⟩)
      (ha'_inj ⟨3, by decide⟩ ⟨0, by decide⟩ (by decide))
      (ha'_inj ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide))]
    exact hTL_fix ⟨3, by decide⟩
  have ha3_in_T1 :
      a' ⟨3, by decide⟩ ∈ @getOrbit D_L (@instBEqOfDecidableEq D_L _) T1.f darts_DL.length (a' ⟨2, by decide⟩) := by
    apply (sameOrbit_iff_mem_getOrbit T1.f darts_DL hDL_all (Nat.le_refl _) _ _).mp
    let pos := FaceCycleCut.posL darts h_all cut
    have hp12 : pos 1 < pos 2 := FaceCycleCut.posL_strictMono darts h_all cut (by decide)
    have hp23 : pos 2 < pos 3 := FaceCycleCut.posL_strictMono darts h_all cut (by decide)
    have hwalk : ∀ s : Nat, 1 ≤ s → s ≤ pos 3 - pos 1 →
        Perm.iter T1.f s (a' ⟨0, by decide⟩) =
          Perm.iter TL.f (pos 1 + s) (a' ⟨0, by decide⟩) := by
      intro s hs1 hs2
      induction s with
      | zero => omega
      | succ k ih =>
          rcases Nat.eq_or_lt_of_le hs1 with hk1 | hk_gt
          · have hk0 : k = 0 := by omega
            subst hk0
            simp only [Perm.iter]
            change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩) (a' ⟨0, by decide⟩)) =
              TL.f.f (Perm.iter TL.f (pos 1) (a' ⟨0, by decide⟩))
            simp only [swapFun, ↓reduceIte]
            congr 1
            apply Subtype.ext
            dsimp [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
            rw [restrictPermPred_iter, ha'_val, ha'_val]
            exact (FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 1).symm
          · have ihk := ih (by omega) (by omega)
            let y := Perm.iter TL.f (pos 1 + k) (a' ⟨0, by decide⟩)
            have hy_mem : FaceCycleCut.inArcL darts h_all cut ⟨2, by decide⟩ y.val ∨
                FaceCycleCut.inArcL darts h_all cut ⟨3, by decide⟩ y.val := by
              by_cases hle2 : pos 1 + k ≤ pos 2
              · left
                refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 1) (by decide) y.val).mpr
                  ⟨pos 1 + k, ?_, ?_, ?_⟩
                · dsimp [pos] at hk_gt ⊢; omega
                · dsimp [pos] at hle2 ⊢; omega
                · dsimp only [y, TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
                  rw [← ha'_val ⟨0, by decide⟩]
                  exact (restrictPermPred_iter _ _ _ _ _).symm
              · right
                refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 2) (by decide) y.val).mpr
                  ⟨pos 1 + k, ?_, ?_, ?_⟩
                · dsimp [pos] at hle2 ⊢; omega
                · dsimp [pos] at hs2 ⊢; omega
                · dsimp only [y, TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
                  rw [← ha'_val ⟨0, by decide⟩]
                  exact (restrictPermPred_iter _ _ _ _ _).symm
            have hy0 : y ≠ a' ⟨0, by decide⟩ := by
              intro heq
              have h0 := FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨0, by decide⟩
              rw [← ha'_val ⟨0, by decide⟩, ← heq] at h0
              rcases hy_mem with h2 | h3
              · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h2 h0) (by decide)
              · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h3 h0) (by decide)
            have hy1 : y ≠ a' ⟨1, by decide⟩ := by
              intro heq
              have h1 := FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨1, by decide⟩
              rw [← ha'_val ⟨1, by decide⟩, ← heq] at h1
              rcases hy_mem with h2 | h3
              · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h2 h1) (by decide)
              · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h3 h1) (by decide)
            have hy_step : T1.f.f y = TL.f.f y := by
              change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩) y) = TL.f.f y
              simp only [swapFun, hy1, hy0, ↓reduceIte]
            change T1.f.f (Perm.iter T1.f k (a' ⟨0, by decide⟩)) =
              TL.f.f (Perm.iter TL.f (pos 1 + k) (a' ⟨0, by decide⟩))
            rw [ihk]
            exact hy_step
    have h2 : Perm.iter T1.f (pos 2 - pos 1) (a' ⟨0, by decide⟩) = a' ⟨2, by decide⟩ := by
      rw [hwalk (pos 2 - pos 1) (by omega) (by omega), show pos 1 + (pos 2 - pos 1) = pos 2 by omega]
      apply Subtype.ext
      dsimp [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
      rw [restrictPermPred_iter, ha'_val, ha'_val]
      exact FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 2
    have h3 : Perm.iter T1.f (pos 3 - pos 1) (a' ⟨0, by decide⟩) = a' ⟨3, by decide⟩ := by
      rw [hwalk (pos 3 - pos 1) (by omega) (by omega), show pos 1 + (pos 3 - pos 1) = pos 3 by omega]
      apply Subtype.ext
      dsimp [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
      rw [restrictPermPred_iter, ha'_val, ha'_val]
      exact FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 3
    refine ⟨pos 3 - pos 2, ?_⟩
    rw [← h2, ← Perm.iter_add, show (pos 3 - pos 2) + (pos 2 - pos 1) = pos 3 - pos 1 by omega]
    exact h3
  let T2 : PermTriple D_L := coupleEdge T1 (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩)
  have hc2 := coupleEdge_sameFace T1 darts_DL hDL_all (Nat.le_refl _)
    hT1_fix2 hT1_fix3 (ha'_inj ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)) ha3_in_T1
  dsimp only at hc2
  change (T2.e.f (a' ⟨2, by decide⟩) = a' ⟨3, by decide⟩ ∧
      T2.e.f (a' ⟨3, by decide⟩) = a' ⟨2, by decide⟩) ∧
    (∀ {x y}, ReachEN T2.e T2.n x y ↔ ReachEN T1.e T1.n x y) ∧
    countRelClasses (ReachEN T2.e T2.n) darts_DL = countRelClasses (ReachEN T1.e T1.n) darts_DL ∧
    countOrbits T2.e darts_DL.length darts_DL + 1 = countOrbits T1.e darts_DL.length darts_DL ∧
    countOrbits T2.f darts_DL.length darts_DL = countOrbits T1.f darts_DL.length darts_DL + 1 ∧
    genusDeficit T2 darts_DL.length darts_DL = genusDeficit T1 darts_DL.length darts_DL at hc2
  have hT1_invol : ∀ x : D_L, T1.e.f (T1.e.f x) = x :=
    coupleEdge_edge_invol TL hTL_invol (hTL_fix ⟨0, by decide⟩) (hTL_fix ⟨1, by decide⟩)
  have hT2_invol : ∀ x : D_L, T2.e.f (T2.e.f x) = x :=
    coupleEdge_edge_invol T1 hT1_invol hT1_fix2 hT1_fix3
  have hT2_e0 : T2.e.f (a' ⟨0, by decide⟩) = a' ⟨1, by decide⟩ := by
    rw [coupleEdge_e_of_ne T1 hT1_fix2 hT1_fix3
      (ha'_inj ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide))
      (ha'_inj ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide))]
    exact hc1.1.1
  have hT2_e1 : T2.e.f (a' ⟨1, by decide⟩) = a' ⟨0, by decide⟩ := by
    rw [coupleEdge_e_of_ne T1 hT1_fix2 hT1_fix3
      (ha'_inj ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide))
      (ha'_inj ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide))]
    exact hc1.1.2
  have hT2_e_other : ∀ x : D_L, (∀ i : Fin 4, x ≠ a' i) →
      ∃ hx : DL (H.edge.f x.val), T2.e.f x = ⟨H.edge.f x.val, hx⟩ := by
    intro x hx
    have hnot : ∀ i : Fin 4, x.val ≠ cut.cutDart i := fun i h => hx i (Subtype.ext h)
    rcases dl_edge_of_ne_cutDart darts h_mc cut x.property hnot with ⟨huc_eq, hx'⟩
    refine ⟨hx', ?_⟩
    rw [coupleEdge_e_of_ne T1 hT1_fix2 hT1_fix3 (hx ⟨2, by decide⟩) (hx ⟨3, by decide⟩)]
    rw [coupleEdge_e_of_ne TL (hTL_fix ⟨0, by decide⟩) (hTL_fix ⟨1, by decide⟩)
      (hx ⟨0, by decide⟩) (hx ⟨1, by decide⟩)]
    apply Subtype.ext
    exact huc_eq
  have hT2_no_fix : ∀ x : D_L, T2.e.f x ≠ x := by
    intro x
    by_cases h0 : x = a' ⟨0, by decide⟩
    · rw [h0, hT2_e0]; exact (ha'_inj ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)).symm
    · by_cases h1 : x = a' ⟨1, by decide⟩
      · rw [h1, hT2_e1]; exact ha'_inj ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
      · by_cases h2 : x = a' ⟨2, by decide⟩
        · rw [h2, hc2.1.1]; exact (ha'_inj ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)).symm
        · by_cases h3 : x = a' ⟨3, by decide⟩
          · rw [h3, hc2.1.2]; exact ha'_inj ⟨2, by decide⟩ ⟨3, by decide⟩ (by decide)
          · have hx : ∀ i : Fin 4, x ≠ a' i := fun ⟨i, hi⟩ => by
              match i with
              | 0 => exact h0
              | 1 => exact h1
              | 2 => exact h2
              | 3 => exact h3
              | n + 4 => exact absurd hi (by omega)
            rcases hT2_e_other x hx with ⟨hx', heq⟩
            rw [heq]
            intro hfix
            apply hbr_no x.val
            have hx_eq : H.edge.f x.val = x.val := congrArg Subtype.val hfix
            exact ⟨0, hx_eq.symm⟩
  let H_pinch := tripleToHypermap T2 hT2_invol
  have hP_pl : H_pinch.isPlanar darts_DL.length darts_DL = true :=
    tripleToHypermap_isPlanar T2 hT2_invol darts_DL hDL_nd hDL_all
      (by rw [hc2.2.2.2.2.2, hc1.2.2.2.2.2, hTL_g0]) hT2_no_fix
  have hP_rc : countRelClasses (ReachEN T2.e T2.n) darts_DL = 1 := by
    rw [hc2.2.2.1, hc1.2.2.1, hTL_rc]
  have hP_conn : H_pinch.numComponents darts_DL.length darts_DL = 1 :=
    tripleToHypermap_numComponents_eq_one T2 hT2_invol darts_DL hDL_all hP_rc
  have h_arc_sameOrbit : ∀ (m : Nat) (hm : m < 4) (x : D_L),
      FaceCycleCut.inArcL darts h_all cut ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩ x.val →
      SameOrbit T2.f x (a' ⟨(m + 1) % 4, Nat.mod_lt _ (by decide)⟩) :=
    pinch_arc_sameOrbit_T2 darts h_nd h_all h_planar h_conn cut a' ha'_val T1 T2 rfl rfl
  have h_inv_1 : ∀ y : D_L, FaceCycleCut.inArcL darts h_all cut ⟨1, by decide⟩ y.val →
      FaceCycleCut.inArcL darts h_all cut ⟨1, by decide⟩ (T2.f.f y).val := by
    intro y hy
    rcases (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 0) (by decide) y.val).mp hy with
      ⟨r, hr0, hr1, hr_eq⟩
    change r ≤ FaceCycleCut.posL darts h_all cut 1 at hr1
    by_cases hy1 : y = a' ⟨1, by decide⟩
    · have hstep : T2.f.f y = TL.f.f (a' ⟨0, by decide⟩) := by
        rw [hy1]
        change T1.f.f (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) (a' ⟨1, by decide⟩)) = _
        have h12 := ha'_inj ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
        have h13 := ha'_inj ⟨1, by decide⟩ ⟨3, by decide⟩ (by decide)
        simp only [swapFun, h12, h13, ↓reduceIte]
        change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩) (a' ⟨1, by decide⟩)) = _
        have h10 := ha'_inj ⟨1, by decide⟩ ⟨0, by decide⟩ (by decide)
        simp only [swapFun, h10, ↓reduceIte]
      have hp01 : FaceCycleCut.posL darts h_all cut 0 < FaceCycleCut.posL darts h_all cut 1 :=
        FaceCycleCut.posL_strictMono darts h_all cut (by decide)
      have hp0_eq : FaceCycleCut.posL darts h_all cut 0 = 0 := rfl
      refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 0) (by decide) _).mpr
        ⟨1, by omega, by change 1 ≤ FaceCycleCut.posL darts h_all cut 1; omega, ?_⟩
      rw [hstep]
      rfl
    · have hy_all : ∀ i : Fin 4, y ≠ a' i := fun i heq => by
        by_cases hi1 : i = ⟨1, by decide⟩
        · exact hy1 (by rw [← hi1]; exact heq)
        · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut hy
            (by rw [heq, ha'_val i]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut i)).symm hi1
      have hstep : T2.f.f y = TL.f.f y := by
        have hy_0 := hy_all ⟨0, by decide⟩; have hy_1 := hy_all ⟨1, by decide⟩
        have hy_2 := hy_all ⟨2, by decide⟩; have hy_3 := hy_all ⟨3, by decide⟩
        change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩)
          (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) y)) = TL.f.f y
        simp only [swapFun, hy_3, hy_2, hy_1, hy_0, ↓reduceIte]
      have hr_lt : r < FaceCycleCut.posL darts h_all cut 1 := by
        apply Classical.byContradiction
        intro hge
        have heq_r : r = FaceCycleCut.posL darts h_all cut 1 := by omega
        apply hy1
        apply Subtype.ext
        rw [← hr_eq, heq_r, ha'_val ⟨1, by decide⟩]
        exact FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 1
      refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 0) (by decide) _).mpr
        ⟨r + 1, by omega, by change r + 1 ≤ FaceCycleCut.posL darts h_all cut 1; omega, ?_⟩
      rw [hstep]
      dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
      simp only [Perm.iter]
      rw [hr_eq]
      rfl
  have h_inv_3 : ∀ y : D_L, FaceCycleCut.inArcL darts h_all cut ⟨3, by decide⟩ y.val →
      FaceCycleCut.inArcL darts h_all cut ⟨3, by decide⟩ (T2.f.f y).val := by
    intro y hy
    rcases (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 2) (by decide) y.val).mp hy with
      ⟨r, hr2, hr3, hr_eq⟩
    change r ≤ FaceCycleCut.posL darts h_all cut 3 at hr3
    by_cases hy3 : y = a' ⟨3, by decide⟩
    · have hstep : T2.f.f y = TL.f.f (a' ⟨2, by decide⟩) := by
        rw [hy3]
        change T1.f.f (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) (a' ⟨3, by decide⟩)) = _
        have h32 := ha'_inj ⟨3, by decide⟩ ⟨2, by decide⟩ (by decide)
        simp only [swapFun, h32, ↓reduceIte]
        have h20 := ha'_inj ⟨2, by decide⟩ ⟨0, by decide⟩ (by decide)
        have h21 := ha'_inj ⟨2, by decide⟩ ⟨1, by decide⟩ (by decide)
        change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩) (a' ⟨2, by decide⟩)) = _
        simp only [swapFun, h20, h21, ↓reduceIte]
      have hp23 : FaceCycleCut.posL darts h_all cut 2 < FaceCycleCut.posL darts h_all cut 3 :=
        FaceCycleCut.posL_strictMono darts h_all cut (by decide)
      refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 2) (by decide) _).mpr
        ⟨FaceCycleCut.posL darts h_all cut 2 + 1, by omega, by change FaceCycleCut.posL darts h_all cut 2 + 1 ≤ FaceCycleCut.posL darts h_all cut 3; omega, ?_⟩
      rw [hstep]
      have h2 := FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 2
      have hm2 : (⟨2 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨2, by decide⟩ := rfl
      rw [hm2] at h2
      dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
      simp only [Perm.iter]
      rw [h2]
      rfl
    · have hy_all : ∀ i : Fin 4, y ≠ a' i := fun i heq => by
        by_cases hi3 : i = ⟨3, by decide⟩
        · exact hy3 (by rw [← hi3]; exact heq)
        · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut hy
            (by rw [heq, ha'_val i]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut i)).symm hi3
      have hstep : T2.f.f y = TL.f.f y := by
        have hy_0 := hy_all ⟨0, by decide⟩; have hy_1 := hy_all ⟨1, by decide⟩
        have hy_2 := hy_all ⟨2, by decide⟩; have hy_3 := hy_all ⟨3, by decide⟩
        change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩)
          (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) y)) = TL.f.f y
        simp only [swapFun, hy_3, hy_2, hy_1, hy_0, ↓reduceIte]
      have hr_lt : r < FaceCycleCut.posL darts h_all cut 3 := by
        apply Classical.byContradiction
        intro hge
        have heq_r : r = FaceCycleCut.posL darts h_all cut 3 := by omega
        apply hy3
        apply Subtype.ext
        rw [← hr_eq, heq_r, ha'_val ⟨3, by decide⟩]
        exact FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 3
      refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 2) (by decide) _).mpr
        ⟨r + 1, by omega, by change r + 1 ≤ FaceCycleCut.posL darts h_all cut 3; omega, ?_⟩
      rw [hstep]
      dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
      simp only [Perm.iter]
      rw [hr_eq]
      rfl
  have h_inv_02 : ∀ y : D_L,
      (FaceCycleCut.inArcL darts h_all cut ⟨0, by decide⟩ y.val ∨
        FaceCycleCut.inArcL darts h_all cut ⟨2, by decide⟩ y.val) →
      (FaceCycleCut.inArcL darts h_all cut ⟨0, by decide⟩ (T2.f.f y).val ∨
        FaceCycleCut.inArcL darts h_all cut ⟨2, by decide⟩ (T2.f.f y).val) := by
    intro y hy
    rcases hy with hy0 | hy2
    · rcases (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 3) (by decide) y.val).mp hy0 with
        ⟨r, hr3, hr4, hr_eq⟩
      change r ≤ FaceCycleCut.posL darts h_all cut 4 at hr4
      by_cases hy_a0 : y = a' ⟨0, by decide⟩
      · right
        have hstep : T2.f.f y = TL.f.f (a' ⟨1, by decide⟩) := by
          rw [hy_a0]
          change T1.f.f (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) (a' ⟨0, by decide⟩)) = _
          have h02 := ha'_inj ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
          have h03 := ha'_inj ⟨0, by decide⟩ ⟨3, by decide⟩ (by decide)
          simp only [swapFun, h02, h03, ↓reduceIte]
          change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩) (a' ⟨0, by decide⟩)) = _
          simp only [swapFun, ↓reduceIte]
        have hp12 : FaceCycleCut.posL darts h_all cut 1 < FaceCycleCut.posL darts h_all cut 2 :=
          FaceCycleCut.posL_strictMono darts h_all cut (by decide)
        refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 1) (by decide) _).mpr
          ⟨FaceCycleCut.posL darts h_all cut 1 + 1, by omega, by change FaceCycleCut.posL darts h_all cut 1 + 1 ≤ FaceCycleCut.posL darts h_all cut 2; omega, ?_⟩
        rw [hstep]
        have h1 := FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 1
        have hm1 : (⟨1 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨1, by decide⟩ := rfl
        rw [hm1] at h1
        dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
        simp only [Perm.iter]
        rw [h1]
        rfl
      · left
        have hy_all : ∀ i : Fin 4, y ≠ a' i := fun i heq => by
          by_cases hi0 : i = ⟨0, by decide⟩
          · exact hy_a0 (by rw [← hi0]; exact heq)
          · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut hy0
              (by rw [heq, ha'_val i]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut i)).symm hi0
        have hstep : T2.f.f y = TL.f.f y := by
          have hy_0 := hy_all ⟨0, by decide⟩; have hy_1 := hy_all ⟨1, by decide⟩
          have hy_2 := hy_all ⟨2, by decide⟩; have hy_3 := hy_all ⟨3, by decide⟩
          change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩)
            (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) y)) = TL.f.f y
          simp only [swapFun, hy_3, hy_2, hy_1, hy_0, ↓reduceIte]
        have hr_lt : r < FaceCycleCut.posL darts h_all cut 4 := by
          apply Classical.byContradiction
          intro hge
          have heq_r : r = FaceCycleCut.posL darts h_all cut 4 := by omega
          apply hy_a0
          apply Subtype.ext
          rw [← hr_eq, heq_r, ha'_val ⟨0, by decide⟩]
          exact FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 4
        refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 3) (by decide) _).mpr
          ⟨r + 1, by omega, by change r + 1 ≤ FaceCycleCut.posL darts h_all cut 4; omega, ?_⟩
        rw [hstep]
        dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
        simp only [Perm.iter]
        rw [hr_eq]
        rfl
    · rcases (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 1) (by decide) y.val).mp hy2 with
        ⟨r, hr1, hr2, hr_eq⟩
      change r ≤ FaceCycleCut.posL darts h_all cut 2 at hr2
      by_cases hy_a2 : y = a' ⟨2, by decide⟩
      · left
        have hstep : T2.f.f y = TL.f.f (a' ⟨3, by decide⟩) := by
          rw [hy_a2]
          change T1.f.f (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) (a' ⟨2, by decide⟩)) = _
          simp only [swapFun, ↓reduceIte]
          have h30 := ha'_inj ⟨3, by decide⟩ ⟨0, by decide⟩ (by decide)
          have h31 := ha'_inj ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide)
          change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩) (a' ⟨3, by decide⟩)) = _
          simp only [swapFun, h30, h31, ↓reduceIte]
        have hp34 : FaceCycleCut.posL darts h_all cut 3 < FaceCycleCut.posL darts h_all cut 4 :=
          FaceCycleCut.posL_strictMono darts h_all cut (by decide)
        refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 3) (by decide) _).mpr
          ⟨FaceCycleCut.posL darts h_all cut 3 + 1, by omega, by change FaceCycleCut.posL darts h_all cut 3 + 1 ≤ FaceCycleCut.posL darts h_all cut 4; omega, ?_⟩
        rw [hstep]
        have h3 := FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 3
        have hm3 : (⟨3 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨3, by decide⟩ := rfl
        rw [hm3] at h3
        dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
        simp only [Perm.iter]
        rw [h3]
        rfl
      · right
        have hy_all : ∀ i : Fin 4, y ≠ a' i := fun i heq => by
          by_cases hi2 : i = ⟨2, by decide⟩
          · exact hy_a2 (by rw [← hi2]; exact heq)
          · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut hy2
              (by rw [heq, ha'_val i]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut i)).symm hi2
        have hstep : T2.f.f y = TL.f.f y := by
          have hy_0 := hy_all ⟨0, by decide⟩; have hy_1 := hy_all ⟨1, by decide⟩
          have hy_2 := hy_all ⟨2, by decide⟩; have hy_3 := hy_all ⟨3, by decide⟩
          change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩)
            (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) y)) = TL.f.f y
          simp only [swapFun, hy_3, hy_2, hy_1, hy_0, ↓reduceIte]
        have hr_lt : r < FaceCycleCut.posL darts h_all cut 2 := by
          apply Classical.byContradiction
          intro hge
          have heq_r : r = FaceCycleCut.posL darts h_all cut 2 := by omega
          apply hy_a2
          apply Subtype.ext
          rw [← hr_eq, heq_r, ha'_val ⟨2, by decide⟩]
          exact FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 2
        refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 1) (by decide) _).mpr
          ⟨r + 1, by omega, by change r + 1 ≤ FaceCycleCut.posL darts h_all cut 2; omega, ?_⟩
        rw [hstep]
        dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
        simp only [Perm.iter]
        rw [hr_eq]
        rfl
  have h_inv_out : ∀ y : D_L, (∀ i : Fin 4, ¬FaceCycleCut.inArcL darts h_all cut i y.val) →
      (∀ i : Fin 4, ¬FaceCycleCut.inArcL darts h_all cut i (T2.f.f y).val) ∧
      (T2.f.f y).val = H.face.f y.val := by
    intro y hy
    have hy_all : ∀ i : Fin 4, y ≠ a' i := fun i heq =>
      hy i (by rw [heq, ha'_val i]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut i)
    have hstep : T2.f.f y = TL.f.f y := by
      have hy_0 := hy_all ⟨0, by decide⟩; have hy_1 := hy_all ⟨1, by decide⟩
      have hy_2 := hy_all ⟨2, by decide⟩; have hy_3 := hy_all ⟨3, by decide⟩
      change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩)
        (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) y)) = TL.f.f y
      simp only [swapFun, hy_3, hy_2, hy_1, hy_0, ↓reduceIte]
    have hnot_cut : ∀ i : Fin 4, y.val ≠ cut.cutDart i ∧ y.val ≠ H.edge.f (cut.cutDart i) := by
      intro i
      refine ⟨fun h => hy_all i (Subtype.ext h), fun h => ?_⟩
      have hDR := (hunc.2.2.2.2.2.2.2.1 i).2
      rw [← h] at hDR
      exact hunc.2.2.2.2.2.2.1 y.val ⟨y.property, hDR⟩
    have hf_eq : (T2.f.f y).val = H.face.f y.val := by
      rw [hstep]
      exact (h_uc_out y.val hnot_cut).2
    refine ⟨fun i hi => ?_, hf_eq⟩
    have hso : SameOrbit H.face (cut.ringFace i) (H.face.f y.val) :=
      ((FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut i _).mp
        (hf_eq ▸ hi)).1
    have hso_y : SameOrbit H.face (cut.ringFace i) y.val :=
      sameOrbit_trans H.face hso (sameOrbit_symm_of_complete H.face darts h_all ⟨1, rfl⟩)
    exact hy i ((FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut i y.val).mpr
      ⟨hso_y, y.property⟩)
  have hP_br : Math.Hypermap.isBridgeless H_pinch darts_DL := by
    rw [isBridgeless_iff_no_sameOrbit_face_edge_jcs H_pinch darts_DL hDL_all]
    intro x hso
    have hso1 : ∀ k, FaceCycleCut.inArcL darts h_all cut ⟨1, by decide⟩ x.val →
        FaceCycleCut.inArcL darts h_all cut ⟨1, by decide⟩ (Perm.iter T2.f k x).val := by
      intro k hk
      induction k with
      | zero => exact hk
      | succ k ih => exact h_inv_1 _ ih
    have hso3 : ∀ k, FaceCycleCut.inArcL darts h_all cut ⟨3, by decide⟩ x.val →
        FaceCycleCut.inArcL darts h_all cut ⟨3, by decide⟩ (Perm.iter T2.f k x).val := by
      intro k hk
      induction k with
      | zero => exact hk
      | succ k ih => exact h_inv_3 _ ih
    have hso02 : ∀ k,
        (FaceCycleCut.inArcL darts h_all cut ⟨0, by decide⟩ x.val ∨
          FaceCycleCut.inArcL darts h_all cut ⟨2, by decide⟩ x.val) →
        (FaceCycleCut.inArcL darts h_all cut ⟨0, by decide⟩ (Perm.iter T2.f k x).val ∨
          FaceCycleCut.inArcL darts h_all cut ⟨2, by decide⟩ (Perm.iter T2.f k x).val) := by
      intro k hk
      induction k with
      | zero => exact hk
      | succ k ih => exact h_inv_02 _ ih
    have hso_out : ∀ k, (∀ i : Fin 4, ¬FaceCycleCut.inArcL darts h_all cut i x.val) →
        (∀ i : Fin 4, ¬FaceCycleCut.inArcL darts h_all cut i (Perm.iter T2.f k x).val) ∧
        (Perm.iter T2.f k x).val = Perm.iter H.face k x.val := by
      intro k hk
      induction k with
      | zero => exact ⟨hk, rfl⟩
      | succ k ih =>
          rcases ih with ⟨ih1, ih2⟩
          rcases h_inv_out _ ih1 with ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          change (T2.f.f (Perm.iter T2.f k x)).val = H.face.f (Perm.iter H.face k x.val)
          rw [h2, ih2]
    rcases hso with ⟨n, hn⟩
    change Perm.iter T2.f n x = T2.e.f x at hn
    by_cases hx0 : x = a' ⟨0, by decide⟩
    · have h02 := hso02 n (Or.inl (by rw [hx0, ha'_val]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨0, by decide⟩))
      rw [hn, hx0, hT2_e0, ha'_val] at h02
      have h1 := FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨1, by decide⟩
      rcases h02 with h0 | h2
      · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h0 h1) (by decide)
      · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h2 h1) (by decide)
    · by_cases hx1 : x = a' ⟨1, by decide⟩
      · have h1 := hso1 n (by rw [hx1, ha'_val]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨1, by decide⟩)
        rw [hn, hx1, hT2_e1, ha'_val] at h1
        exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h1
          (FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨0, by decide⟩)) (by decide)
      · by_cases hx2 : x = a' ⟨2, by decide⟩
        · have h02 := hso02 n (Or.inr (by rw [hx2, ha'_val]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨2, by decide⟩))
          rw [hn, hx2, hc2.1.1, ha'_val] at h02
          have h3 := FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨3, by decide⟩
          rcases h02 with h0 | h2
          · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h0 h3) (by decide)
          · exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h2 h3) (by decide)
        · by_cases hx3 : x = a' ⟨3, by decide⟩
          · have h3 := hso3 n (by rw [hx3, ha'_val]; exact FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨3, by decide⟩)
            rw [hn, hx3, hc2.1.2, ha'_val] at h3
            exact absurd (cut_inArcL_disjoint darts h_nd h_all h_planar h_conn cut h3
              (FaceCycleCut.cutDart_mem_inArcL darts h_all cut ⟨2, by decide⟩)) (by decide)
          · have hx_all : ∀ i : Fin 4, x ≠ a' i := fun ⟨i, hi⟩ => by
              match i with
              | 0 => exact hx0
              | 1 => exact hx1
              | 2 => exact hx2
              | 3 => exact hx3
              | n + 4 => exact absurd hi (by omega)
            rcases hT2_e_other x hx_all with ⟨hx', he_eq⟩
            rw [he_eq] at hn
            by_cases hex : ∃ i : Fin 4, FaceCycleCut.inArcL darts h_all cut i x.val
            · rcases hex with ⟨fi, hxi⟩
              rcases fi with ⟨i, hi⟩
              have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
              rcases hi_cases with rfl | rfl | rfl | rfl
              · have h02 := hso02 n (Or.inl hxi)
                rw [hn] at h02
                have hfx0 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨0, by decide⟩ x.val).mp hxi
                rcases h02 with h_e0 | h_e2
                · have hfe0 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨0, by decide⟩ (H.edge.f x.val)).mp h_e0
                  exact hbr_no x.val (sameOrbit_trans H.face
                    (sameOrbit_symm_of_complete H.face darts h_all hfx0.1) hfe0.1)
                · have hfe2 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨2, by decide⟩ (H.edge.f x.val)).mp h_e2
                  exact h_no02 ⟨x.val, x.property, hx', hfx0.1, hfe2.1⟩
              · have h1' := hso1 n hxi
                rw [hn] at h1'
                have hfx1 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨1, by decide⟩ x.val).mp hxi
                have hfe1 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨1, by decide⟩ (H.edge.f x.val)).mp h1'
                exact hbr_no x.val (sameOrbit_trans H.face
                  (sameOrbit_symm_of_complete H.face darts h_all hfx1.1) hfe1.1)
              · have h02 := hso02 n (Or.inr hxi)
                rw [hn] at h02
                have hfx2 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨2, by decide⟩ x.val).mp hxi
                rcases h02 with h_e0 | h_e2
                · have hfe0 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨0, by decide⟩ (H.edge.f x.val)).mp h_e0
                  exact h_no02 ⟨H.edge.f x.val, hx', by rw [mc_edge_inv]; exact x.property, hfe0.1, by rw [mc_edge_inv]; exact hfx2.1⟩
                · have hfe2 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨2, by decide⟩ (H.edge.f x.val)).mp h_e2
                  exact hbr_no x.val (sameOrbit_trans H.face
                    (sameOrbit_symm_of_complete H.face darts h_all hfx2.1) hfe2.1)
              · have h3' := hso3 n hxi
                rw [hn] at h3'
                have hfx3 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨3, by decide⟩ x.val).mp hxi
                have hfe3 := (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut ⟨3, by decide⟩ (H.edge.f x.val)).mp h3'
                exact hbr_no x.val (sameOrbit_trans H.face
                  (sameOrbit_symm_of_complete H.face darts h_all hfx3.1) hfe3.1)
            · have hx_not : ∀ i : Fin 4, ¬FaceCycleCut.inArcL darts h_all cut i x.val := fun i h => hex ⟨i, h⟩
              have hout := (hso_out n hx_not).2
              rw [hn] at hout
              exact hbr_no x.val ⟨n, hout.symm⟩
  rcases h_mc.is_minimal H_pinch darts_DL hDL_nd hDL_all hDL_ne hDL_lt hP_pl hP_br with ⟨col2⟩
  let H_cap := cut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn
  let darts_cap := cut.capSingleVertexDarts darts
  rcases cut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br with
    ⟨_, h_cap_all, _, _, _, _, _, h_ed_b, h_ed_i, _, _, h_orb_b, h_fc_i⟩
  have h02_same : SameOrbit T2.f (a' ⟨2, by decide⟩) (a' ⟨0, by decide⟩) := by
    have hstep2 : T2.f.f (a' ⟨2, by decide⟩) = TL.f.f (a' ⟨3, by decide⟩) := by
      change T1.f.f (swapFun (a' ⟨2, by decide⟩) (a' ⟨3, by decide⟩) (a' ⟨2, by decide⟩)) = _
      simp only [swapFun, ↓reduceIte]
      have h30 := ha'_inj ⟨3, by decide⟩ ⟨0, by decide⟩ (by decide)
      have h31 := ha'_inj ⟨3, by decide⟩ ⟨1, by decide⟩ (by decide)
      change TL.f.f (swapFun (a' ⟨0, by decide⟩) (a' ⟨1, by decide⟩) (a' ⟨3, by decide⟩)) = _
      simp only [swapFun, h30, h31, ↓reduceIte]
    have hp34 : FaceCycleCut.posL darts h_all cut 3 < FaceCycleCut.posL darts h_all cut 4 :=
      FaceCycleCut.posL_strictMono darts h_all cut (by decide)
    have h_in0 : FaceCycleCut.inArcL darts h_all cut ⟨0, by decide⟩ (T2.f.f (a' ⟨2, by decide⟩)).val := by
      refine (FaceCycleCut.inArcL_iff_posL_block darts h_all cut (m := 3) (by decide) _).mpr
        ⟨FaceCycleCut.posL darts h_all cut 3 + 1, by omega, by change FaceCycleCut.posL darts h_all cut 3 + 1 ≤ FaceCycleCut.posL darts h_all cut 4; omega, ?_⟩
      rw [hstep2]
      have h3 := FaceCycleCut.uncoupleTriple_iter_posL darts h_all cut 3
      have hm3 : (⟨3 % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨3, by decide⟩ := rfl
      rw [hm3] at h3
      dsimp only [TL, FaceCycleCut.capSingleVertex_TL, restrictTriplePred]
      simp only [Perm.iter]
      rw [h3]
      rfl
    have hso_nxt := h_arc_sameOrbit 3 (by decide) (T2.f.f (a' ⟨2, by decide⟩)) h_in0
    exact sameOrbit_trans T2.f ⟨1, rfl⟩ hso_nxt
  have hcol_arc : ∀ (i : Fin 4) (x : D_L),
      FaceCycleCut.inArcL darts h_all cut i x.val → col2.color x = col2.color (a' i) := by
    intro ⟨i, hi⟩ x hxi
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi_cases with rfl | rfl | rfl | rfl
    · have hc := sameOrbit_face_color_eq H_pinch col2 (h_arc_sameOrbit 3 (by decide) x hxi)
      rwa [show (⟨(3 + 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨0, hi⟩ from Fin.ext rfl] at hc
    · have hc := sameOrbit_face_color_eq H_pinch col2 (h_arc_sameOrbit 0 (by decide) x hxi)
      rwa [show (⟨(0 + 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨1, hi⟩ from Fin.ext rfl] at hc
    · have hc := sameOrbit_face_color_eq H_pinch col2 (h_arc_sameOrbit 1 (by decide) x hxi)
      rwa [show (⟨(1 + 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨2, hi⟩ from Fin.ext rfl] at hc
    · have hc := sameOrbit_face_color_eq H_pinch col2 (h_arc_sameOrbit 2 (by decide) x hxi)
      rwa [show (⟨(2 + 1) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = ⟨3, hi⟩ from Fin.ext rfl] at hc
  let colL_fn : H_cap.Dart → Color := fun z =>
    match z with
    | Sum.inl x => col2.color x
    | Sum.inr m => col2.color (a' ⟨(m.val + 1) % 4, Nat.mod_lt _ (by decide)⟩)
  have h_inv_b : ∀ (m : Fin 4) (z : H_cap.Dart),
      SameOrbit H_cap.face (Sum.inr m) z → colL_fn z = colL_fn (Sum.inr m) := by
    intro m z hz
    have hm_orb : z ∈ @getOrbit H_cap.Dart Sum.instBEq H_cap.face darts_cap.length (Sum.inr m) := by
      rw [capSingleVertex_beq_eq cut]
      exact (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap h_cap_all (Nat.le_refl _) _ _).mp hz
    rw [h_orb_b m z] at hm_orb
    rcases hm_orb with rfl | ⟨d, hd, rfl, hd_arc⟩
    · rfl
    · exact hcol_arc ⟨(m.val + 1) % 4, _⟩ ⟨d, hd⟩ hd_arc
  let colL : H_cap.FaceColoring := {
    color := colL_fn
    face_invariant := fun z => by
      match z with
      | Sum.inr m =>
          have hso : SameOrbit H_cap.face (Sum.inr m) (H_cap.face.f (Sum.inr m)) := ⟨1, rfl⟩
          exact h_inv_b m (H_cap.face.f (Sum.inr m)) hso
      | Sum.inl ⟨d, hd⟩ =>
          by_cases hex : ∃ i : Fin 4, SameOrbit H.face (cut.ringFace i) d
          · rcases hex with ⟨i, hfi⟩
            have hi_arc : FaceCycleCut.inArcL darts h_all cut i d :=
              (FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut i d).mpr ⟨hfi, hd⟩
            let m : Fin 4 := ⟨(i.val + 3) % 4, Nat.mod_lt _ (by decide)⟩
            have hm_idx : ⟨(m.val + 1) % 4, Nat.mod_lt _ (by decide)⟩ = i := by
              apply Fin.ext
              exact mod_sub_one_add_one 4 i.val (by decide) i.isLt
            have hz_orb : Sum.inl ⟨d, hd⟩ ∈ @getOrbit H_cap.Dart Sum.instBEq H_cap.face darts_cap.length (Sum.inr m) := by
              rw [h_orb_b m (Sum.inl ⟨d, hd⟩)]
              right
              refine ⟨d, hd, rfl, ?_⟩
              rw [hm_idx]
              exact hi_arc
            rw [capSingleVertex_beq_eq cut] at hz_orb
            have hso1 : SameOrbit H_cap.face (Sum.inr m) (Sum.inl ⟨d, hd⟩) :=
              (sameOrbit_iff_mem_getOrbit H_cap.face darts_cap h_cap_all (Nat.le_refl _) _ _).mpr hz_orb
            have hso2 : SameOrbit H_cap.face (Sum.inr m) (H_cap.face.f (Sum.inl ⟨d, hd⟩)) :=
              sameOrbit_trans H_cap.face hso1 ⟨1, rfl⟩
            rw [h_inv_b m _ hso2, h_inv_b m _ hso1]
          · have hnot : ∀ i : Fin 4, ¬SameOrbit H.face (cut.ringFace i) d := fun i h => hex ⟨i, h⟩
            rcases h_fc_i d hd hnot with ⟨hfn, hfc_eq⟩
            rw [hfc_eq]
            have hnot_arc : ∀ i : Fin 4, ¬FaceCycleCut.inArcL darts h_all cut i d := fun i h =>
              hnot i ((FaceCycleCut.inArcL_iff_sameOrbit_and_DL darts h_nd h_all h_planar h_conn cut i d).mp h).1
            have hstep_T2 := h_inv_out ⟨d, hd⟩ hnot_arc
            have heq_sub : (⟨H.face.f d, hfn⟩ : D_L) = T2.f.f ⟨d, hd⟩ :=
              Subtype.ext hstep_T2.2.symm
            change col2.color ⟨H.face.f d, hfn⟩ = col2.color ⟨d, hd⟩
            rw [heq_sub]
            exact col2.face_invariant ⟨d, hd⟩
    edge_proper := fun z => by
      match z with
      | Sum.inr ⟨m, hm⟩ =>
          have hed := (h_ed_b ⟨m, hm⟩).2
          rw [hed]
          change col2.color (a' ⟨m, hm⟩) ≠ col2.color (a' ⟨(m + 1) % 4, _⟩)
          have h01 : col2.color (a' ⟨0, by decide⟩) ≠ col2.color (a' ⟨1, by decide⟩) := by
            have he0 := col2.edge_proper (a' ⟨0, by decide⟩)
            change col2.color (T2.e.f (a' ⟨0, by decide⟩)) ≠ col2.color (a' ⟨0, by decide⟩) at he0
            rw [hT2_e0] at he0
            exact he0.symm
          have h23 : col2.color (a' ⟨2, by decide⟩) ≠ col2.color (a' ⟨3, by decide⟩) := by
            have he2 := col2.edge_proper (a' ⟨2, by decide⟩)
            change col2.color (T2.e.f (a' ⟨2, by decide⟩)) ≠ col2.color (a' ⟨2, by decide⟩) at he2
            rw [hc2.1.1] at he2
            exact he2.symm
          have h02_c : col2.color (a' ⟨2, by decide⟩) = col2.color (a' ⟨0, by decide⟩) :=
            sameOrbit_face_color_eq H_pinch col2 h02_same
          match m with
          | 0 => exact h01
          | 1 => rw [show ⟨(1 + 1) % 4, Nat.mod_lt _ (by decide)⟩ = (⟨2, by decide⟩ : Fin 4) from rfl, h02_c]; exact h01.symm
          | 2 => exact h23
          | 3 => rw [show ⟨(3 + 1) % 4, Nat.mod_lt _ (by decide)⟩ = (⟨0, by decide⟩ : Fin 4) from rfl, ← h02_c]; exact h23.symm
          | n + 4 => exact absurd hm (by omega)
      | Sum.inl ⟨d, hd⟩ =>
          by_cases hcut : ∃ m : Fin 4, d = cut.cutDart m
          · rcases hcut with ⟨⟨m, hm⟩, rfl⟩
            have hed := (h_ed_b ⟨m, hm⟩).1
            have heq_sub : (⟨cut.cutDart ⟨m, hm⟩, hd⟩ : D_L) = a' ⟨m, hm⟩ := rfl
            rw [heq_sub]
            have hed' : H_cap.edge.f (Sum.inl (a' ⟨m, hm⟩)) = Sum.inr ⟨m, hm⟩ :=
              hed
            rw [hed']
            change col2.color (a' ⟨(m + 1) % 4, _⟩) ≠ col2.color (a' ⟨m, hm⟩)
            have h01 : col2.color (a' ⟨0, by decide⟩) ≠ col2.color (a' ⟨1, by decide⟩) := by
              have he0 := col2.edge_proper (a' ⟨0, by decide⟩)
              change col2.color (T2.e.f (a' ⟨0, by decide⟩)) ≠ col2.color (a' ⟨0, by decide⟩) at he0
              rw [hT2_e0] at he0
              exact he0.symm
            have h23 : col2.color (a' ⟨2, by decide⟩) ≠ col2.color (a' ⟨3, by decide⟩) := by
              have he2 := col2.edge_proper (a' ⟨2, by decide⟩)
              change col2.color (T2.e.f (a' ⟨2, by decide⟩)) ≠ col2.color (a' ⟨2, by decide⟩) at he2
              rw [hc2.1.1] at he2
              exact he2.symm
            have h02_c : col2.color (a' ⟨2, by decide⟩) = col2.color (a' ⟨0, by decide⟩) :=
              sameOrbit_face_color_eq H_pinch col2 h02_same
            match m with
            | 0 => exact h01.symm
            | 1 => rw [show ⟨(1 + 1) % 4, Nat.mod_lt _ (by decide)⟩ = (⟨2, by decide⟩ : Fin 4) from rfl, h02_c]; exact h01
            | 2 => exact h23.symm
            | 3 => rw [show ⟨(3 + 1) % 4, Nat.mod_lt _ (by decide)⟩ = (⟨0, by decide⟩ : Fin 4) from rfl, ← h02_c]; exact h23
            | n + 4 => exact absurd hm (by omega)
          · have hnot : ∀ m : Fin 4, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
            rcases h_ed_i d hd hnot with ⟨hdn, hed_eq⟩
            rw [hed_eq]
            have hx_all : ∀ i : Fin 4, (⟨d, hd⟩ : D_L) ≠ a' i := fun i heq =>
              hnot i (congrArg Subtype.val heq)
            rcases hT2_e_other ⟨d, hd⟩ hx_all with ⟨hx', he_t2⟩
            have hsub_eq : (⟨H.edge.f d, hdn⟩ : D_L) = T2.e.f ⟨d, hd⟩ := by
              apply Subtype.ext
              exact (congrArg Subtype.val he_t2).symm
            change col2.color ⟨H.edge.f d, hdn⟩ ≠ col2.color ⟨d, hd⟩
            rw [hsub_eq]
            exact col2.edge_proper ⟨d, hd⟩
  }
  refine ⟨colL, ?_⟩
  let f := capBoundaryColors darts h_nd h_all h_planar h_conn cut colL
  have hf02 : f ⟨0, by decide⟩ = f ⟨2, by decide⟩ := by
    simp only [f, capBoundaryColors, colL, colL_fn]
    exact (sameOrbit_face_color_eq H_pinch col2 h02_same).symm
  by_cases h13 : f ⟨1, by decide⟩ = f ⟨3, by decide⟩
  · exact Or.inl ⟨hf02, h13⟩
  · exact Or.inr ⟨hf02, h13⟩

private theorem swapCompRight_comm {D : Type} [DecidableEq D] (p : Perm D) (a b : D) :
    swapCompRight p a b = swapCompRight p b a := by
  apply perm_ext_sc
  intro x
  dsimp [swapCompRight, swapFun]
  by_cases hxa : x = a <;> by_cases hxb : x = b
  · subst hxa; rw [hxb]
  · subst hxa; simp [hxb]
  · subst hxb; simp [hxa]
  · simp [hxa, hxb]

private theorem iter_eq_self_of_fix {D : Type} (p : Perm D) {a : D} (h : p.f a = a) :
    ∀ k : Nat, Perm.iter p k a = a
  | 0 => rfl
  | k + 1 => by
      change p.f (Perm.iter p k a) = a
      rw [iter_eq_self_of_fix p h k, h]

private theorem not_mem_getOrbit_of_fix {D : Type} [DecidableEq D]
    [BEq D] (hb : (inferInstance : BEq D) = @instBEqOfDecidableEq D _)
    (p : Perm D) (fuel : Nat) {a b : D} (hfix : p.f a = a) (hne : b ≠ a) :
    b ∉ getOrbit p fuel a := by
  intro hm
  obtain ⟨k, _, hbk⟩ := mem_getOrbit_imp_exists_iter p fuel a b (hb ▸ hm)
  rw [iter_eq_self_of_fix p hfix k] at hbk
  exact hne hbk

private theorem reachEN_of_countRelClasses_eq_one {D : Type} (e n : Perm D)
    [DecidableRel (ReachEN e n)] (darts : List D) (h_c1 : countRelClasses (ReachEN e n) darts = 1)
    {a b : D} (ha : a ∈ darts) (hb : b ∈ darts) : ReachEN e n a b := by
  have hpart := countRelClasses_eq_one_add_filter_of_mem (ReachEN e n)
    (reachEN_refl e n) (fun h => reachEN_symm e n h)
    (fun h1 h2 => reachEN_trans e n h1 h2) darts a ha
  rw [h_c1] at hpart
  have hzero : countRelClasses (ReachEN e n) (darts.filter (fun x => !decide (ReachEN e n a x))) = 0 := by
    omega
  apply Classical.byContradiction
  intro hnot
  have hb_filt : b ∈ darts.filter (fun x => !decide (ReachEN e n a x)) := by
    rw [List.mem_filter]
    exact ⟨hb, by simp [hnot]⟩
  cases hfl : darts.filter (fun x => !decide (ReachEN e n a x)) with
  | nil => rw [hfl] at hb_filt; simp at hb_filt
  | cons y ys =>
      rw [hfl, countRelClasses_cons] at hzero
      omega

private def s2Triple : PermTriple (Fin 2) where
  e :=
    { f := fun i => ⟨(i.val + 1) % 2, Nat.mod_lt _ (by decide)⟩
      inv := fun i => ⟨(i.val + 1) % 2, Nat.mod_lt _ (by decide)⟩
      left_inv := by intro ⟨m, hm⟩; exact Fin.ext (by simp; omega)
      right_inv := by intro ⟨m, hm⟩; exact Fin.ext (by simp; omega) }
  n := { f := id, inv := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  f :=
    { f := fun i => ⟨(i.val + 1) % 2, Nat.mod_lt _ (by decide)⟩
      inv := fun i => ⟨(i.val + 1) % 2, Nat.mod_lt _ (by decide)⟩
      left_inv := by intro ⟨m, hm⟩; exact Fin.ext (by simp; omega)
      right_inv := by intro ⟨m, hm⟩; exact Fin.ext (by simp; omega) }
  enf_id := by intro ⟨m, hm⟩; exact Fin.ext (by simp; omega)

private def s2Darts : List (Fin 2) := [⟨0, by decide⟩, ⟨1, by decide⟩]

private theorem s2Darts_nodup : s2Darts.Nodup := by decide

private theorem s2Darts_complete (y : Fin 2) : y ∈ s2Darts := by
  rcases y with ⟨m, hm⟩
  have hm_cases : m = 0 ∨ m = 1 := by omega
  rcases hm_cases with rfl | rfl <;> simp [s2Darts]

private theorem s2_reachEN_all (x y : Fin 2) : ReachEN s2Triple.e s2Triple.n x y := by
  by_cases hxy : x = y
  · subst hxy; exact reachEN_refl _ _ _
  · refine ⟨WalkEN.step (StepEN.e_fwd x) ?_⟩
    have hex : s2Triple.e.f x = y := by
      rcases x with ⟨mx, hmx⟩
      rcases y with ⟨my, hmy⟩
      apply Fin.ext
      change (mx + 1) % 2 = my
      have hne : mx ≠ my := fun h => hxy (Fin.ext h)
      omega
    rw [hex]
    exact WalkEN.refl y

private theorem s2_genusDeficit_zero :
    genusDeficit s2Triple 2 s2Darts = 0 := by
  dsimp only [genusDeficit]
  rw [countRelClasses_eq_one_of_all (ReachEN s2Triple.e s2Triple.n) s2Darts
    (by simp [s2Darts]) s2_reachEN_all]
  have hn : countOrbits s2Triple.n 2 s2Darts = 2 := by decide
  have he : countOrbits s2Triple.e 2 s2Darts = 1 := by decide
  have hf : countOrbits s2Triple.f 2 s2Darts = 1 := by decide
  rw [hn, he, hf]
  rfl

private theorem capSplit02_coloring {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (hR12 : 12 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) :
    ∃ colL : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState02 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut colL) ∨
      IsState4 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut colL) := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut
  let darts_cap := FaceCycleCut.capSingleVertexDarts darts cut
  have hsp := FaceCycleCut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br cut
  have h_cap_nd : darts_cap.Nodup := hsp.1
  have h_cap_all : ∀ x : H_cap.Dart, x ∈ darts_cap := hsp.2.1
  have h_cap_ne : darts_cap ≠ [] := hsp.2.2.1
  have h_cap_planar : H_cap.isPlanar darts_cap.length darts_cap = true := hsp.2.2.2.2.1
  have h_cap_conn : H_cap.numComponents darts_cap.length darts_cap = 1 := hsp.2.2.2.2.2.1
  have h_cap_br : Math.Hypermap.isBridgeless H_cap darts_cap darts_cap.length := hsp.2.2.2.2.2.2.1
  have hb_cap := (capSingleVertex_beq_eq cut).trans (@decEq_beq_eq H_cap.Dart _ inferInstance)
  have hb_cap_fun : ∀ x y : H_cap.Dart, (x == y) = decide (x = y) := by
    intro x y
    change @BEq.beq H_cap.Dart Sum.instBEq x y = decide (x = y)
    rw [hb_cap]
    rfl
  have hb3 := (beq_sum_eq_dec hb_cap_fun (fun ⟨ma, hma⟩ ⟨mb, hmb⟩ => by
      have ha : ma = 0 ∨ ma = 1 := by omega
      have hb : mb = 0 ∨ mb = 1 := by omega
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rfl)).trans
    (@decEq_beq_eq (H_cap.Dart ⊕ Fin 2) _ (@instDecidableEqSum _ _ _ (instDecidableEqFin 2)))
  have h_cap_edge_inj : ∀ {x y : H_cap.Dart}, H_cap.edge.f x = H_cap.edge.f y → x = y := by
    intro x y hxy
    calc x = H_cap.edge.f (H_cap.edge.f x) := (H_cap.edge_involution x).symm
      _ = H_cap.edge.f (H_cap.edge.f y) := congrArg H_cap.edge.f hxy
      _ = y := H_cap.edge_involution y
  have h_cap_node_inj : ∀ {x y : H_cap.Dart}, H_cap.node.f x = H_cap.node.f y → x = y := by
    intro x y hxy
    calc x = H_cap.node.inv (H_cap.node.f x) := (H_cap.node.left_inv x).symm
      _ = H_cap.node.inv (H_cap.node.f y) := congrArg H_cap.node.inv hxy
      _ = y := H_cap.node.left_inv y
  let v : Fin 4 → H_cap.Dart ⊕ Fin 2 := fun i => Sum.inl (Sum.inr i)
  let da : H_cap.Dart ⊕ Fin 2 := Sum.inr ⟨0, by decide⟩
  let db : H_cap.Dart ⊕ Fin 2 := Sum.inr ⟨1, by decide⟩
  let a1_cap : H_cap.Dart := H_cap.edge.f (Sum.inr ⟨1, by decide⟩)
  let a3_cap : H_cap.Dart := H_cap.edge.f (Sum.inr ⟨3, by decide⟩)
  let a1 : H_cap.Dart ⊕ Fin 2 := Sum.inl a1_cap
  let a3 : H_cap.Dart ⊕ Fin 2 := Sum.inl a3_cap
  let T0 : PermTriple (H_cap.Dart ⊕ Fin 2) := sumTriple H_cap.hypermapToTriple s2Triple
  let darts3 : List (H_cap.Dart ⊕ Fin 2) :=
    List.map Sum.inl darts_cap ++ List.map Sum.inr s2Darts
  have h3_spec := sumTriple_spec H_cap.hypermapToTriple s2Triple darts_cap h_cap_nd h_cap_all
    s2Darts s2Darts_nodup s2Darts_complete
    (show darts_cap.length + s2Darts.length ≤ darts_cap.length + 2 by simp [s2Darts])
  have h3_nd : darts3.Nodup := h3_spec.1
  have h3_all : ∀ z : H_cap.Dart ⊕ Fin 2, z ∈ darts3 := h3_spec.2.1
  have h3_ne : darts3 ≠ [] := by
    intro hnil
    have ha : da ∈ darts3 := h3_all da
    rw [hnil] at ha
    simp at ha
  have h3_len : darts3.length = darts_cap.length + 2 := by
    simp [darts3, s2Darts]
  have ha13_cap : a1_cap ≠ a3_cap := by
    intro heq
    have hinj := h_cap_edge_inj heq
    have hval := congrArg Fin.val (Sum.inr.inj hinj)
    dsimp at hval
    omega
  have ha1_ne_a3 : a1 ≠ a3 := fun h => ha13_cap (Sum.inl.inj h)
  have hv0_ne_v2 : v ⟨0, by decide⟩ ≠ v ⟨2, by decide⟩ := by
    intro heq
    have hval := congrArg Fin.val (Sum.inr.inj (Sum.inl.inj heq))
    dsimp at hval
    omega
  have hv0_da : v ⟨0, by decide⟩ ≠ da := by simp [v, da]
  have hv0_db : v ⟨0, by decide⟩ ≠ db := by simp [v, db]
  have hv2_da : v ⟨2, by decide⟩ ≠ da := by simp [v, da]
  have hv2_db : v ⟨2, by decide⟩ ≠ db := by simp [v, db]
  have hda_db : da ≠ db := by
    intro h
    have hval := congrArg Fin.val (Sum.inr.inj h)
    dsimp at hval
    omega
  have ha1_da : a1 ≠ da := by simp [a1, da]
  have ha1_db : a1 ≠ db := by simp [a1, db]
  have ha3_da : a3 ≠ da := by simp [a3, da]
  have ha3_db : a3 ≠ db := by simp [a3, db]
  have h_cap_face_bnd : ∀ (m : Fin 4),
      H_cap.face.f (H_cap.edge.f (Sum.inr m)) = Sum.inr ⟨(m.val + 3) % 4, Nat.mod_lt _ (by decide)⟩ := by
    intro m
    let am := H_cap.edge.f (Sum.inr m)
    have hnf : H_cap.node.f (Sum.inr ⟨(m.val + 3) % 4, Nat.mod_lt _ (by decide)⟩) = Sum.inr m := by
      have h11 := (hsp.2.2.2.2.2.2.2.2.2.2.1 ⟨(m.val + 3) % 4, Nat.mod_lt _ (by decide)⟩).1
      rw [h11]
      exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))
    have h1 : H_cap.node.f (H_cap.face.f am) = Sum.inr m := by
      have henf := H_cap.edge_node_face_id am
      calc H_cap.node.f (H_cap.face.f am)
          = H_cap.edge.f (H_cap.edge.f (H_cap.node.f (H_cap.face.f am))) := (H_cap.edge_involution _).symm
        _ = H_cap.edge.f am := congrArg H_cap.edge.f henf
        _ = Sum.inr m := H_cap.edge_involution _
    exact h_cap_node_inj (h1.trans hnf.symm)
  have hT0_f_a1 : T0.f.f a1 = v ⟨0, by decide⟩ := by
    change Sum.inl (H_cap.face.f a1_cap) = Sum.inl (Sum.inr ⟨0, by decide⟩)
    rw [h_cap_face_bnd ⟨1, by decide⟩]
    rfl
  have hT0_f_a3 : T0.f.f a3 = v ⟨2, by decide⟩ := by
    change Sum.inl (H_cap.face.f a3_cap) = Sum.inl (Sum.inr ⟨2, by decide⟩)
    rw [h_cap_face_bnd ⟨3, by decide⟩]
    rfl
  have hT0_f_da : T0.f.f da = db := rfl
  have hT0_f_db : T0.f.f db = da := rfl
  have hT0_n_v0 : T0.n.f (v ⟨0, by decide⟩) = v ⟨1, by decide⟩ := by
    change Sum.inl (H_cap.node.f (Sum.inr ⟨0, by decide⟩)) = Sum.inl (Sum.inr ⟨1, by decide⟩)
    rw [(hsp.2.2.2.2.2.2.2.2.2.2.1 ⟨0, by decide⟩).1]
    rfl
  have hT0_n_v2 : T0.n.f (v ⟨2, by decide⟩) = v ⟨3, by decide⟩ := by
    change Sum.inl (H_cap.node.f (Sum.inr ⟨2, by decide⟩)) = Sum.inl (Sum.inr ⟨3, by decide⟩)
    rw [(hsp.2.2.2.2.2.2.2.2.2.2.1 ⟨2, by decide⟩).1]
    rfl
  have hT0_n_da : T0.n.f da = da := rfl
  have hT0_n_db : T0.n.f db = db := rfl
  have hT0_e_v1 : T0.e.f (v ⟨1, by decide⟩) = a1 := by
    change Sum.inl (H_cap.edge.f (Sum.inr ⟨1, by decide⟩)) = Sum.inl a1_cap
    rfl
  have hT0_e_v3 : T0.e.f (v ⟨3, by decide⟩) = a3 := by
    change Sum.inl (H_cap.edge.f (Sum.inr ⟨3, by decide⟩)) = Sum.inl a3_cap
    rfl
  let p1 : Perm (H_cap.Dart ⊕ Fin 2) := swapCompRight T0.n (v ⟨0, by decide⟩) (v ⟨2, by decide⟩)
  let p2 : Perm (H_cap.Dart ⊕ Fin 2) := swapCompRight p1 (v ⟨2, by decide⟩) da
  let n3 : Perm (H_cap.Dart ⊕ Fin 2) := swapCompRight p2 (v ⟨0, by decide⟩) db
  let q1 : Perm (H_cap.Dart ⊕ Fin 2) := swapCompRight T0.f da db
  let q2 : Perm (H_cap.Dart ⊕ Fin 2) := swapCompRight q1 a1 da
  let f3 : Perm (H_cap.Dart ⊕ Fin 2) := swapCompRight q2 a3 db
  have hn3_v0 : n3.f (v ⟨0, by decide⟩) = db := by
    dsimp only [n3, p2, p1, swapCompRight]
    rw [swapFun_left, swapFun_of_ne hv2_db.symm hda_db.symm, swapFun_of_ne hv0_db.symm hv2_db.symm]
    exact hT0_n_db
  have hn3_db : n3.f db = v ⟨3, by decide⟩ := by
    dsimp only [n3, p2, p1, swapCompRight]
    rw [swapFun_right, swapFun_of_ne hv0_ne_v2 hv0_da, swapFun_left]
    exact hT0_n_v2
  have hn3_v2 : n3.f (v ⟨2, by decide⟩) = da := by
    dsimp only [n3, p2, p1, swapCompRight]
    rw [swapFun_of_ne hv0_ne_v2.symm hv2_db, swapFun_left, swapFun_of_ne hv0_da.symm hv2_da.symm]
    exact hT0_n_da
  have hn3_da : n3.f da = v ⟨1, by decide⟩ := by
    dsimp only [n3, p2, p1, swapCompRight]
    rw [swapFun_of_ne hv0_da.symm hda_db, swapFun_right, swapFun_right]
    exact hT0_n_v0
  have hn3_other : ∀ w : H_cap.Dart ⊕ Fin 2,
      w ≠ v ⟨0, by decide⟩ → w ≠ v ⟨2, by decide⟩ → w ≠ da → w ≠ db →
      n3.f w = T0.n.f w := by
    intro w hw0 hw2 hwda hwdb
    dsimp only [n3, p2, p1, swapCompRight]
    rw [swapFun_of_ne hw0 hwdb, swapFun_of_ne hw2 hwda, swapFun_of_ne hw0 hw2]
  have hf3_a1 : f3.f a1 = da := by
    dsimp only [f3, q2, q1, swapCompRight]
    rw [swapFun_of_ne ha1_ne_a3 ha1_db, swapFun_left, swapFun_left]
    exact hT0_f_db
  have hf3_da : f3.f da = v ⟨0, by decide⟩ := by
    dsimp only [f3, q2, q1, swapCompRight]
    rw [swapFun_of_ne ha3_da.symm hda_db, swapFun_right, swapFun_of_ne ha1_da ha1_db]
    exact hT0_f_a1
  have hf3_a3 : f3.f a3 = db := by
    dsimp only [f3, q2, q1, swapCompRight]
    rw [swapFun_left, swapFun_of_ne ha1_db.symm hda_db.symm, swapFun_right]
    exact hT0_f_da
  have hf3_db : f3.f db = v ⟨2, by decide⟩ := by
    dsimp only [f3, q2, q1, swapCompRight]
    rw [swapFun_right, swapFun_of_ne ha1_ne_a3.symm ha3_da, swapFun_of_ne ha3_da ha3_db]
    exact hT0_f_a3
  have hf3_other : ∀ z : H_cap.Dart ⊕ Fin 2,
      z ≠ a1 → z ≠ da → z ≠ a3 → z ≠ db → f3.f z = T0.f.f z := by
    intro z hz1 hzda hz3 hzdb
    dsimp only [f3, q2, q1, swapCompRight]
    rw [swapFun_of_ne hz3 hzdb, swapFun_of_ne hz1 hzda, swapFun_of_ne hzda hzdb]
  let T3 : PermTriple (H_cap.Dart ⊕ Fin 2) :=
    { e := T0.e
      n := n3
      f := f3
      enf_id := by
        intro x
        by_cases hx1 : x = a1
        · subst hx1
          rw [hf3_a1, hn3_da]
          exact hT0_e_v1
        · by_cases hxda : x = da
          · subst hxda; rw [hf3_da, hn3_v0]; rfl
          · by_cases hx3 : x = a3
            · subst hx3
              rw [hf3_a3, hn3_db]
              exact hT0_e_v3
            · by_cases hxdb : x = db
              · subst hxdb; rw [hf3_db, hn3_v2]; rfl
              · rw [hf3_other x hx1 hxda hx3 hxdb]
                have hne_v0 : T0.f.f x ≠ v ⟨0, by decide⟩ := by
                  intro h; rw [← hT0_f_a1] at h
                  have heq : x = a1 := T0.f.left_inv x ▸ T0.f.left_inv a1 ▸ congrArg T0.f.inv h
                  exact hx1 heq
                have hne_v2 : T0.f.f x ≠ v ⟨2, by decide⟩ := by
                  intro h; rw [← hT0_f_a3] at h
                  have heq : x = a3 := T0.f.left_inv x ▸ T0.f.left_inv a3 ▸ congrArg T0.f.inv h
                  exact hx3 heq
                have hne_da : T0.f.f x ≠ da := by
                  intro h; rw [← hT0_f_db] at h
                  have heq : x = db := T0.f.left_inv x ▸ T0.f.left_inv db ▸ congrArg T0.f.inv h
                  exact hxdb heq
                have hne_db : T0.f.f x ≠ db := by
                  intro h; rw [← hT0_f_da] at h
                  have heq : x = da := T0.f.left_inv x ▸ T0.f.left_inv da ▸ congrArg T0.f.inv h
                  exact hxda heq
                rw [hn3_other (T0.f.f x) hne_v0 hne_v2 hne_da hne_db]
                exact T0.enf_id x }
  have hT3_invol : ∀ d : H_cap.Dart ⊕ Fin 2, T3.e.f (T3.e.f d) = d := by
    intro d
    cases d with
    | inl y => exact congrArg Sum.inl (H_cap.edge_involution y)
    | inr i =>
        rcases i with ⟨m, hm⟩
        have hm_cases : m = 0 ∨ m = 1 := by omega
        rcases hm_cases with rfl | rfl <;>
          exact congrArg Sum.inr (Fin.ext (by dsimp [T3, T0, sumTriple, sumPerm, s2Triple]))
  have hT3_no_fix : ∀ d : H_cap.Dart ⊕ Fin 2, T3.e.f d ≠ d := by
    intro d heq
    cases d with
    | inl y =>
        exact edge_no_fix_of_isBridgeless H_cap darts_cap h_cap_all h_cap_br y (Sum.inl.inj heq)
    | inr i =>
        rcases i with ⟨m, hm⟩
        have hm' := congrArg Fin.val (Sum.inr.inj heq)
        dsimp [T3, T0, sumTriple, s2Triple] at hm'
        omega
  -- Step 1: Connectedness of T3 (`countRelClasses (ReachEN T3.e T3.n) darts3 = 1`)
  have h_cap_c1 : countRelClasses (ReachEN H_cap.edge H_cap.node) darts_cap = 1 := by
    have heq := countRelClasses_reachEN_eq_countComponents H_cap darts_cap h_cap_all
      (Nat.le_refl _) darts_cap
    rw [heq]
    have h_conn' := h_cap_conn
    rw [hb_cap] at h_conn'
    exact h_conn'
  have h_lift_nfwd : ∀ x : H_cap.Dart,
      ReachEN T3.e T3.n (Sum.inl x) (Sum.inl (H_cap.node.f x)) := by
    intro x
    by_cases hx0 : Sum.inl x = v ⟨0, by decide⟩
    · have hx0' : x = Sum.inr ⟨0, by decide⟩ := Sum.inl.inj hx0
      subst hx0'
      rw [(hsp.2.2.2.2.2.2.2.2.2.2.1 ⟨0, by decide⟩).1]
      have h1 : ReachEN T3.e T3.n (v ⟨0, by decide⟩) db :=
        ⟨WalkEN.step (StepEN.n_fwd (v ⟨0, by decide⟩)) (hn3_v0 ▸ WalkEN.refl db)⟩
      have h2 : ReachEN T3.e T3.n db da :=
        ⟨WalkEN.step (StepEN.e_fwd db) (WalkEN.refl da)⟩
      have h3 : ReachEN T3.e T3.n da (v ⟨1, by decide⟩) :=
        ⟨WalkEN.step (StepEN.n_fwd da) (hn3_da ▸ WalkEN.refl (v ⟨1, by decide⟩))⟩
      exact reachEN_trans T3.e T3.n h1 (reachEN_trans T3.e T3.n h2 h3)
    · by_cases hx2 : Sum.inl x = v ⟨2, by decide⟩
      · have hx2' : x = Sum.inr ⟨2, by decide⟩ := Sum.inl.inj hx2
        subst hx2'
        rw [(hsp.2.2.2.2.2.2.2.2.2.2.1 ⟨2, by decide⟩).1]
        have h1 : ReachEN T3.e T3.n (v ⟨2, by decide⟩) da :=
          ⟨WalkEN.step (StepEN.n_fwd (v ⟨2, by decide⟩)) (hn3_v2 ▸ WalkEN.refl da)⟩
        have h2 : ReachEN T3.e T3.n da db :=
          ⟨WalkEN.step (StepEN.e_fwd da) (WalkEN.refl db)⟩
        have h3 : ReachEN T3.e T3.n db (v ⟨3, by decide⟩) :=
          ⟨WalkEN.step (StepEN.n_fwd db) (hn3_db ▸ WalkEN.refl (v ⟨3, by decide⟩))⟩
        exact reachEN_trans T3.e T3.n h1 (reachEN_trans T3.e T3.n h2 h3)
      · have hnf : T3.n.f (Sum.inl x) = Sum.inl (H_cap.node.f x) :=
          hn3_other (Sum.inl x) hx0 hx2 (by simp [da]) (by simp [db])
        exact ⟨WalkEN.step (StepEN.n_fwd (Sum.inl x)) (hnf ▸ WalkEN.refl _)⟩
  have h_lift_step : ∀ a b, StepEN H_cap.edge H_cap.node a b →
      ReachEN T3.e T3.n (Sum.inl a) (Sum.inl b) := by
    intro a b st
    cases st with
    | e_fwd => exact ⟨WalkEN.step (StepEN.e_fwd _) (WalkEN.refl _)⟩
    | e_bwd => exact ⟨WalkEN.step (StepEN.e_bwd _) (WalkEN.refl _)⟩
    | n_fwd => exact h_lift_nfwd a
    | n_bwd =>
        have hr := h_lift_nfwd (H_cap.node.inv a)
        rw [H_cap.node.right_inv a] at hr
        exact reachEN_symm T3.e T3.n hr
  have h_lift_cap : ∀ u w : H_cap.Dart, ReachEN H_cap.edge H_cap.node u w →
      ReachEN T3.e T3.n (Sum.inl u) (Sum.inl w) := by
    intro u w huw
    obtain ⟨wk⟩ := huw
    induction wk with
    | refl => exact reachEN_refl _ _ _
    | step st _ ih => exact reachEN_trans T3.e T3.n (h_lift_step _ _ st) ih
  have hT3_reach_v1 : ∀ z : H_cap.Dart ⊕ Fin 2, ReachEN T3.e T3.n (v ⟨1, by decide⟩) z := by
    intro z
    cases z with
    | inl y =>
        exact h_lift_cap (Sum.inr ⟨1, by decide⟩) y
          (reachEN_of_countRelClasses_eq_one H_cap.edge H_cap.node darts_cap h_cap_c1
            (h_cap_all _) (h_cap_all y))
    | inr i =>
        have h_v1_da : ReachEN T3.e T3.n (v ⟨1, by decide⟩) da :=
          reachEN_symm T3.e T3.n ⟨WalkEN.step (StepEN.n_fwd da) (hn3_da ▸ WalkEN.refl _)⟩
        rcases i with ⟨m, hm⟩
        have hm_cases : m = 0 ∨ m = 1 := by omega
        rcases hm_cases with rfl | rfl
        · exact h_v1_da
        · exact reachEN_trans T3.e T3.n h_v1_da ⟨WalkEN.step (StepEN.e_fwd da) (WalkEN.refl db)⟩
  have hT3_c1 : countRelClasses (ReachEN T3.e T3.n) darts3 = 1 :=
    countRelClasses_eq_one_of_all (ReachEN T3.e T3.n) darts3 h3_ne
      (fun x y => reachEN_trans T3.e T3.n (reachEN_symm T3.e T3.n (hT3_reach_v1 x)) (hT3_reach_v1 y))
  -- Step 2: Planarity (`genusDeficit T3 darts3.length darts3 = 0`)
  have hT0_gen0 : @genusDeficit (H_cap.Dart ⊕ Fin 2)
      (@instDecidableEqSum _ _ _ (instDecidableEqFin 2)) T0 darts3.length darts3 = 0 := by
    rw [h3_len, h3_spec.2.2.1]
    have h_cap_gen0 : @genusDeficit H_cap.Dart _
        H_cap.hypermapToTriple (darts_cap.length + 2) darts_cap = 0 := by
      have h_cap_planar' := h_cap_planar
      rw [hb_cap] at h_cap_planar'
      have h1 := ((eulerChar_le_two_mul_numComponents H_cap darts_cap h_cap_nd h_cap_all (Nat.le_refl _)).2.mp h_cap_planar').1
      rw [← genusDeficit_fuel_eq H_cap.hypermapToTriple darts_cap h_cap_all (Nat.le_refl _) (by omega)]
      exact h1
    have h_s2_gen0 : @genusDeficit (Fin 2)
        (instDecidableEqFin 2) s2Triple (darts_cap.length + 2) s2Darts = 0 := by
      have hs2_len : s2Darts.length = 2 := by decide
      rw [@genusDeficit_fuel_eq (Fin 2) (instDecidableEqFin 2) s2Triple s2Darts s2Darts_complete
        (darts_cap.length + 2) 2 (by omega) (by decide)]
      exact s2_genusDeficit_zero
    rw [h_cap_gen0, h_s2_gen0]
    rfl
  have hT0_c2 : countRelClasses (ReachEN T0.e T0.n) darts3 = 2 := by
    rw [h3_spec.2.2.2]
    have hs2_c1 : countRelClasses (ReachEN s2Triple.e s2Triple.n) s2Darts = 1 :=
      countRelClasses_eq_one_of_all (ReachEN s2Triple.e s2Triple.n) s2Darts
        (by simp [s2Darts]) s2_reachEN_all
    change countRelClasses (ReachEN H_cap.edge H_cap.node) darts_cap +
      countRelClasses (ReachEN s2Triple.e s2Triple.n) s2Darts = 2
    rw [h_cap_c1, hs2_c1]
  -- Count n3 orbits
  have hp1_orb : countOrbits p1 darts3.length darts3 = countOrbits T0.n darts3.length darts3 + 1 := by
    rw [hb3]
    apply countOrbits_swapCompRight_same T0.n darts3 h3_all (Nat.le_refl _) hv0_ne_v2
    have hcloses := orbitClosesWithin_of_complete T0.n darts3 h3_all (v ⟨0, by decide⟩)
    have hiter2 : Perm.iter T0.n 2 (v ⟨0, by decide⟩) = v ⟨2, by decide⟩ := by
      change T0.n.f (T0.n.f (v ⟨0, by decide⟩)) = v ⟨2, by decide⟩
      rw [hT0_n_v0]
      change Sum.inl (H_cap.node.f (Sum.inr ⟨1, by decide⟩)) = Sum.inl (Sum.inr ⟨2, by decide⟩)
      rw [(hsp.2.2.2.2.2.2.2.2.2.2.1 ⟨1, by decide⟩).1]
      rfl
    rw [← hiter2]
    exact iter_mem_getOrbit_of_closes T0.n darts3.length (v ⟨0, by decide⟩) hcloses 2
  have hp2_orb : countOrbits p2 darts3.length darts3 + 1 = countOrbits p1 darts3.length darts3 := by
    rw [hb3]
    apply countOrbits_swapCompRight_diff p1 darts3 h3_all (Nat.le_refl _)
    let p_cap1 : Perm H_cap.Dart := swapCompRight H_cap.node (Sum.inr ⟨0, by decide⟩) (Sum.inr ⟨2, by decide⟩)
    apply @sum_inr_not_mem_getOrbit_left H_cap.Dart (Fin 2) _ (instDecidableEqFin 2)
      (@instBEqOfDecidableEq (H_cap.Dart ⊕ Fin 2) (@instDecidableEqSum _ _ _ (instDecidableEqFin 2)))
      rfl p_cap1 p1
      (fun u => by
        dsimp only [p1, p_cap1, swapCompRight, v, T0, sumTriple, sumPerm, hypermapToTriple]
        by_cases hu0 : u = Sum.inr ⟨0, by decide⟩
        · subst hu0
          rw [swapFun_left]; rw [swapFun_left]; rfl
        · by_cases hu2 : u = Sum.inr ⟨2, by decide⟩
          · subst hu2
            rw [swapFun_right]; rw [swapFun_right]; rfl
          · have hi0 : (Sum.inl u : H_cap.Dart ⊕ Fin 2) ≠ Sum.inl (Sum.inr ⟨0, by decide⟩) :=
              fun h => hu0 (Sum.inl.inj h)
            have hi2 : (Sum.inl u : H_cap.Dart ⊕ Fin 2) ≠ Sum.inl (Sum.inr ⟨2, by decide⟩) :=
              fun h => hu2 (Sum.inl.inj h)
            rw [swapFun_of_ne hi0 hi2, swapFun_of_ne hu0 hu2]
            rfl)
      darts3 h3_all darts3.length (Nat.le_refl _) (Sum.inr ⟨2, by decide⟩) ⟨0, by decide⟩
  have hn3_orb : countOrbits n3 darts3.length darts3 + 1 = countOrbits p2 darts3.length darts3 := by
    change countOrbits (swapCompRight p2 (v ⟨0, by decide⟩) db) darts3.length darts3 + 1 =
      countOrbits p2 darts3.length darts3
    rw [hb3, swapCompRight_comm]
    apply countOrbits_swapCompRight_diff p2 darts3 h3_all (Nat.le_refl _)
    apply @not_mem_getOrbit_of_fix (H_cap.Dart ⊕ Fin 2)
      (@instDecidableEqSum _ _ _ (instDecidableEqFin 2))
      (@instBEqOfDecidableEq (H_cap.Dart ⊕ Fin 2) (@instDecidableEqSum _ _ _ (instDecidableEqFin 2)))
      rfl p2 darts3.length
    · dsimp only [p2, p1, swapCompRight, v, da, db]
      rw [swapFun_of_ne hv2_db.symm hda_db.symm, swapFun_of_ne hv0_db.symm hv2_db.symm]
      exact hT0_n_db
    · exact hv0_db
  -- Count f3 orbits
  have hq1_orb : countOrbits q1 darts3.length darts3 = countOrbits T0.f darts3.length darts3 + 1 := by
    rw [hb3]
    apply countOrbits_swapCompRight_same T0.f darts3 h3_all (Nat.le_refl _) hda_db
    have hcloses := orbitClosesWithin_of_complete T0.f darts3 h3_all da
    have hiter1 : Perm.iter T0.f 1 da = db := hT0_f_da
    rw [← hiter1]
    exact iter_mem_getOrbit_of_closes T0.f darts3.length da hcloses 1
  have hq2_orb : countOrbits q2 darts3.length darts3 + 1 = countOrbits q1 darts3.length darts3 := by
    change countOrbits (swapCompRight q1 a1 da) darts3.length darts3 + 1 =
      countOrbits q1 darts3.length darts3
    rw [hb3, swapCompRight_comm]
    apply countOrbits_swapCompRight_diff q1 darts3 h3_all (Nat.le_refl _)
    apply @not_mem_getOrbit_of_fix (H_cap.Dart ⊕ Fin 2)
      (@instDecidableEqSum _ _ _ (instDecidableEqFin 2))
      (@instBEqOfDecidableEq (H_cap.Dart ⊕ Fin 2) (@instDecidableEqSum _ _ _ (instDecidableEqFin 2)))
      rfl q1 darts3.length
    · dsimp only [q1, swapCompRight, da, db]
      rw [swapFun_left]
      exact hT0_f_db
    · exact ha1_da
  have hf3_orb : countOrbits f3 darts3.length darts3 + 1 = countOrbits q2 darts3.length darts3 := by
    change countOrbits (swapCompRight q2 a3 db) darts3.length darts3 + 1 =
      countOrbits q2 darts3.length darts3
    rw [hb3, swapCompRight_comm]
    apply countOrbits_swapCompRight_diff q2 darts3 h3_all (Nat.le_refl _)
    apply @not_mem_getOrbit_of_fix (H_cap.Dart ⊕ Fin 2)
      (@instDecidableEqSum _ _ _ (instDecidableEqFin 2))
      (@instBEqOfDecidableEq (H_cap.Dart ⊕ Fin 2) (@instDecidableEqSum _ _ _ (instDecidableEqFin 2)))
      rfl q2 darts3.length
    · dsimp only [q2, q1, swapCompRight, a1, da, db]
      rw [swapFun_of_ne ha1_db.symm hda_db.symm, swapFun_right]
      exact hT0_f_da
    · exact ha3_db
  have hT3_gen0 : @genusDeficit (H_cap.Dart ⊕ Fin 2)
      (@instDecidableEqSum _ _ _ (instDecidableEqFin 2)) T3 darts3.length darts3 = 0 := by
    dsimp [genusDeficit] at hT0_gen0 ⊢
    rw [hT3_c1]
    rw [hT0_c2] at hT0_gen0
    rw [hb3] at hp1_orb hp2_orb hn3_orb hq1_orb hq2_orb hf3_orb
    dsimp only [T3]
    omega
  have hH3_planar : @Hypermap.isPlanar (tripleToHypermap T3 hT3_invol)
      (@instBEqOfDecidableEq (H_cap.Dart ⊕ Fin 2) (@instDecidableEqSum _ _ _ (instDecidableEqFin 2)))
      darts3.length darts3 = true :=
    tripleToHypermap_isPlanar T3 hT3_invol darts3 h3_nd h3_all hT3_gen0 hT3_no_fix
  -- Step 3: Bridgelessness of H3 via faceId projection to H_cap
  let faceId : H_cap.Dart ⊕ Fin 2 → H_cap.Dart := fun
    | Sum.inl x => x
    | Sum.inr i => if i.val = 0 then Sum.inr ⟨0, by decide⟩ else Sum.inr ⟨2, by decide⟩
  have h_faceId_step : ∀ w : H_cap.Dart ⊕ Fin 2,
      faceId (f3.f w) = faceId w ∨ faceId (f3.f w) = H_cap.face.f (faceId w) := by
    intro w
    by_cases hw1 : w = a1
    · subst hw1
      rw [hf3_a1]
      right
      change Sum.inr ⟨0, by decide⟩ = H_cap.face.f a1_cap
      exact (h_cap_face_bnd ⟨1, by decide⟩).symm
    · by_cases hwda : w = da
      · subst hwda
        rw [hf3_da]
        left
        rfl
      · by_cases hw3 : w = a3
        · subst hw3
          rw [hf3_a3]
          right
          change Sum.inr ⟨2, by decide⟩ = H_cap.face.f a3_cap
          exact (h_cap_face_bnd ⟨3, by decide⟩).symm
        · by_cases hwdb : w = db
          · subst hwdb
            rw [hf3_db]
            left
            rfl
          · rw [hf3_other w hw1 hwda hw3 hwdb]
            cases w with
            | inl x =>
                right
                rfl
            | inr i =>
                rcases i with ⟨m, hm⟩
                exfalso
                have hm_cases : m = 0 ∨ m = 1 := by omega
                rcases hm_cases with rfl | rfl
                · exact hwda (congrArg Sum.inr (Fin.ext rfl))
                · exact hwdb (congrArg Sum.inr (Fin.ext rfl))
  have h_faceId_iter : ∀ (k : Nat) (z : H_cap.Dart ⊕ Fin 2),
      SameOrbit H_cap.face (faceId z) (faceId (Perm.iter f3 k z)) := by
    intro k z
    induction k with
    | zero => exact ⟨0, rfl⟩
    | succ k ih =>
        rcases ih with ⟨m, hm⟩
        change SameOrbit H_cap.face (faceId z) (faceId (f3.f (Perm.iter f3 k z)))
        rcases h_faceId_step (Perm.iter f3 k z) with hsame | hnext
        · rw [hsame]; exact ⟨m, hm⟩
        · rw [hnext, ← hm]
          exact ⟨m + 1, rfl⟩
  have hH3_br : @Math.Hypermap.isBridgeless (tripleToHypermap T3 hT3_invol)
      (@instDecidableEqSum _ _ _ (instDecidableEqFin 2))
      darts3 darts3.length := by
    intro z _hz
    apply Bool.eq_false_iff.mpr
    intro hbridge
    obtain ⟨k, _, hk⟩ := mem_getOrbit_imp_exists_iter f3 darts3.length z (T3.e.f z)
      (by simpa [Math.Hypermap.isBridge, Math.Hypermap.sameFace, List.contains_iff_mem] using hbridge)
    obtain ⟨m, hm⟩ := h_faceId_iter k z
    rw [← hk] at hm
    have hcloses := orbitClosesWithin_of_complete H_cap.face darts_cap h_cap_all (faceId z)
    have hmem_cap : faceId (T3.e.f z) ∈ getOrbit H_cap.face darts_cap.length (faceId z) := by
      rw [← hm, hb_cap]
      exact iter_mem_getOrbit_of_closes H_cap.face darts_cap.length (faceId z) hcloses m
    cases z with
    | inl x =>
        have h_same_cap := h_faceId_iter k (Sum.inl x)
        rw [← hk] at h_same_cap
        have h_same_x : SameOrbit H_cap.face x (H_cap.edge.f x) := by
          simpa [faceId, T3, T0, sumTriple, sumPerm, hypermapToTriple] using h_same_cap
        exact ((isBridgeless_iff_no_sameOrbit_face_edge_jcs H_cap darts_cap h_cap_all).mp h_cap_br) x h_same_x
    | inr i =>
        rcases i with ⟨mi, hmi⟩
        have hmi_cases : mi = 0 ∨ mi = 1 := by omega
        rcases hmi_cases with rfl | rfl
        · have h02 : (Sum.inr ⟨2, by decide⟩ : H_cap.Dart) ∈
              getOrbit H_cap.face darts_cap.length (Sum.inr ⟨0, by decide⟩) := by
            simpa [faceId, T3, T0, sumTriple, sumPerm, s2Triple] using hmem_cap
          rcases (hsp.2.2.2.2.2.2.2.2.2.2.2.1 ⟨0, by decide⟩ (Sum.inr ⟨2, by decide⟩)).mp h02 with h | ⟨_, _, h, _⟩
          · injection h with hfin; have hval := congrArg Fin.val hfin; dsimp at hval; omega
          · cases h
        · have h20 : (Sum.inr ⟨0, by decide⟩ : H_cap.Dart) ∈
              getOrbit H_cap.face darts_cap.length (Sum.inr ⟨2, by decide⟩) := by
            simpa [faceId, T3, T0, sumTriple, sumPerm, s2Triple] using hmem_cap
          rcases (hsp.2.2.2.2.2.2.2.2.2.2.2.1 ⟨2, by decide⟩ (Sum.inr ⟨0, by decide⟩)).mp h20 with h | ⟨_, _, h, _⟩
          · injection h with hfin; have hval := congrArg Fin.val hfin; dsimp at hval; omega
          · cases h
  -- Step 4: Minimality gives col3 : (tripleToHypermap T3 hT3_invol).FaceColoring
  have hsum := side_lengths_sum darts h_nd h_all h_planar h_conn cut
  have hcap_len := capDarts_length_eq darts h_nd h_all h_planar h_conn h_br cut
  have h3_lt : darts3.length < darts.length := by
    rw [h3_len, hcap_len]
    omega
  obtain ⟨col3⟩ := @h_mc.is_minimal (tripleToHypermap T3 hT3_invol)
    (@instDecidableEqSum _ _ _ (instDecidableEqFin 2))
    darts3 h3_nd h3_all h3_ne h3_lt hH3_planar hH3_br
  -- Step 5: Pull col3 back to H_cap
  let colL : H_cap.FaceColoring :=
    { color := fun x => col3.color (Sum.inl x)
      face_invariant := by
        intro x
        by_cases hx1 : x = a1_cap
        · subst hx1
          rw [h_cap_face_bnd ⟨1, by decide⟩]
          have h1 : col3.color da = col3.color a1 := by
            rw [← hf3_a1]
            exact col3.face_invariant a1
          have h2 : col3.color (v ⟨0, by decide⟩) = col3.color da := by
            rw [← hf3_da]
            exact col3.face_invariant da
          exact h2.trans h1
        · by_cases hx3 : x = a3_cap
          · subst hx3
            rw [h_cap_face_bnd ⟨3, by decide⟩]
            have h1 : col3.color db = col3.color a3 := by
              rw [← hf3_a3]
              exact col3.face_invariant a3
            have h2 : col3.color (v ⟨2, by decide⟩) = col3.color db := by
              rw [← hf3_db]
              exact col3.face_invariant db
            exact h2.trans h1
          · have hfx : f3.f (Sum.inl x) = Sum.inl (H_cap.face.f x) :=
              hf3_other (Sum.inl x) (fun h => hx1 (Sum.inl.inj h)) (by simp [da])
                (fun h => hx3 (Sum.inl.inj h)) (by simp [db])
            rw [← hfx]
            exact col3.face_invariant (Sum.inl x)
      edge_proper := by
        intro x
        exact col3.edge_proper (Sum.inl x) }
  refine ⟨colL, ?_⟩
  let f := capBoundaryColors darts h_nd h_all h_planar h_conn cut colL
  have hf13 : f ⟨1, by decide⟩ ≠ f ⟨3, by decide⟩ := by
    intro heq
    have h1 : col3.color (v ⟨0, by decide⟩) = col3.color da := by
      rw [← hf3_da]; exact col3.face_invariant da
    have h3 : col3.color (v ⟨2, by decide⟩) = col3.color db := by
      rw [← hf3_db]; exact col3.face_invariant db
    have hdb : col3.color db = col3.color da := by
      rw [← h3, ← h1]
      exact heq.symm
    exact col3.edge_proper da hdb
  by_cases hf02 : f ⟨0, by decide⟩ = f ⟨2, by decide⟩
  · exact Or.inl ⟨hf02, hf13⟩
  · exact Or.inr ⟨hf02, hf13⟩

private theorem capColoring_of_rot1 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nd : darts.Nodup) (h_all : ∀ d, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_br : Math.Hypermap.isBridgeless H darts)
    (cut : H.FaceCycleCut 4)
    (col_rot : (FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut.rot1).FaceColoring) :
    ∃ col : (FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut).FaceColoring,
      ∀ i : Fin 4,
        capBoundaryColors darts h_nd h_all h_planar h_conn cut col i =
          capBoundaryColors darts h_nd h_all h_planar h_conn cut.rot1 col_rot
            ⟨(i.val + 3) % 4, Nat.mod_lt _ (by decide)⟩ := by
  let H1 := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut
  let H2 := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut.rot1
  have hsp1 := FaceCycleCut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br cut
  have hsp2 := FaceCycleCut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br cut.rot1
  let psi : H1.Dart → H2.Dart := fun
    | Sum.inl ⟨d, hd⟩ => Sum.inl ⟨d, (FaceCycleCut.rot1_DL_iff darts h_nd h_all h_planar h_conn cut d).mpr hd⟩
    | Sum.inr m => Sum.inr ⟨(m.val + 3) % 4, Nat.mod_lt _ (by decide)⟩
  have h_rot_cut : ∀ m : Fin 4,
      cut.rot1.cutDart m = cut.cutDart ⟨(m.val + 1) % 4, Nat.mod_lt _ (by decide)⟩ :=
    fun _ => rfl
  have h_cut_rot : ∀ m : Fin 4,
      cut.cutDart m = cut.rot1.cutDart ⟨(m.val + 3) % 4, Nat.mod_lt _ (by decide)⟩ := by
    intro m
    rw [h_rot_cut]
    congr 1
    apply Fin.ext
    dsimp only
    omega
  have h_edge : ∀ x : H1.Dart, H2.edge.f (psi x) = psi (H1.edge.f x) := by
    intro x
    cases x with
    | inr m =>
        have h1 := (hsp1.2.2.2.2.2.2.2.1 m).2
        have h2 := (hsp2.2.2.2.2.2.2.2.1 ⟨(m.val + 3) % 4, Nat.mod_lt _ (by decide)⟩).2
        dsimp only [psi] at h2 ⊢
        rw [h1, h2]
        dsimp only [psi]
        exact congrArg Sum.inl (Subtype.ext (h_cut_rot m).symm)
    | inl dh =>
        rcases dh with ⟨d, hd⟩
        by_cases hcut : ∃ m : Fin 4, d = cut.cutDart m
        · rcases hcut with ⟨m, rfl⟩
          have h1 := (hsp1.2.2.2.2.2.2.2.1 m).1
          let m' : Fin 4 := ⟨(m.val + 3) % 4, Nat.mod_lt _ (by decide)⟩
          have hm'_eq : cut.cutDart m = cut.rot1.cutDart m' := h_cut_rot m
          have h2 := (hsp2.2.2.2.2.2.2.2.1 m').1
          have hm'_dl : cut.rot1.capSingleVertex_DL (cut.rot1.cutDart m') :=
            (FaceCycleCut.rot1_DL_iff darts h_nd h_all h_planar h_conn cut (cut.rot1.cutDart m')).mpr
              (by rw [← hm'_eq]; exact hd)
          have h2' : H2.edge.f (Sum.inl ⟨cut.cutDart m, (FaceCycleCut.rot1_DL_iff darts h_nd h_all h_planar h_conn cut _).mpr hd⟩) =
              Sum.inr m' := by
            have heq_sub : (⟨cut.cutDart m, (FaceCycleCut.rot1_DL_iff darts h_nd h_all h_planar h_conn cut _).mpr hd⟩ :
                { x // cut.rot1.capSingleVertex_DL x }) =
                ⟨cut.rot1.cutDart m', hm'_dl⟩ := Subtype.ext hm'_eq
            rw [heq_sub]
            exact h2
          dsimp only [psi]
          rw [h2']
          have h1' : H1.edge.f (Sum.inl ⟨cut.cutDart m, hd⟩) = Sum.inr m := h1
          rw [h1']
        · have hnot1 : ∀ m : Fin 4, d ≠ cut.cutDart m := fun m h => hcut ⟨m, h⟩
          have hnot2 : ∀ m : Fin 4, d ≠ cut.rot1.cutDart m := by
            intro m h
            rw [h_rot_cut] at h
            exact hcut ⟨_, h⟩
          obtain ⟨hdn1, h1⟩ := hsp1.2.2.2.2.2.2.2.2.1 d hd hnot1
          obtain ⟨hdn2, h2⟩ := hsp2.2.2.2.2.2.2.2.2.1 d
            ((FaceCycleCut.rot1_DL_iff darts h_nd h_all h_planar h_conn cut d).mpr hd) hnot2
          dsimp only [psi]
          rw [h2, h1]
  have h_node : ∀ x : H1.Dart, H2.node.f (psi x) = psi (H1.node.f x) := by
    intro x
    cases x with
    | inl dh =>
        rcases dh with ⟨d, hd⟩
        obtain ⟨hdn1, h1⟩ := hsp1.2.2.2.2.2.2.2.2.2.1 d hd
        obtain ⟨hdn2, h2⟩ := hsp2.2.2.2.2.2.2.2.2.2.1 d
          ((FaceCycleCut.rot1_DL_iff darts h_nd h_all h_planar h_conn cut d).mpr hd)
        dsimp only [psi]
        rw [h2, h1]
    | inr m =>
        have h1 := (hsp1.2.2.2.2.2.2.2.2.2.2.1 m).1
        have h2 := (hsp2.2.2.2.2.2.2.2.2.2.2.1 ⟨(m.val + 3) % 4, Nat.mod_lt _ (by decide)⟩).1
        dsimp only [psi]
        rw [h1, h2]
        dsimp only [psi]
        exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))
  have h2_edge_inj : ∀ {u w : H2.Dart}, H2.edge.f u = H2.edge.f w → u = w := by
    intro u w huw
    calc u = H2.edge.f (H2.edge.f u) := (H2.edge_involution u).symm
      _ = H2.edge.f (H2.edge.f w) := congrArg H2.edge.f huw
      _ = w := H2.edge_involution w
  have h2_node_inj : ∀ {u w : H2.Dart}, H2.node.f u = H2.node.f w → u = w := by
    intro u w huw
    calc u = H2.node.inv (H2.node.f u) := (H2.node.left_inv u).symm
      _ = H2.node.inv (H2.node.f w) := congrArg H2.node.inv huw
      _ = w := H2.node.left_inv w
  have h_face : ∀ x : H1.Dart, H2.face.f (psi x) = psi (H1.face.f x) := by
    intro x
    have h1 := H1.edge_node_face_id x
    have h2 := H2.edge_node_face_id (psi x)
    have h_en : H2.edge.f (H2.node.f (psi (H1.face.f x))) = psi x := by
      rw [h_node, h_edge, h1]
    have h_n : H2.node.f (H2.face.f (psi x)) = H2.node.f (psi (H1.face.f x)) :=
      h2_edge_inj (h2.trans h_en.symm)
    exact h2_node_inj h_n
  refine ⟨
    { color := fun x => col_rot.color (psi x)
      face_invariant := fun x => by rw [← h_face]; exact col_rot.face_invariant (psi x)
      edge_proper := fun x => by rw [← h_edge]; exact col_rot.edge_proper (psi x) },
    ?_⟩
  intro i
  dsimp only [capBoundaryColors, psi]
  rfl

private theorem reachENIn_target_prop {D : Type} {e n : Perm D} {P : D → Prop} {s t : D}
    (h : ReachENIn e n P s t) : P t := by
  induction h with
  | refl hp => exact hp
  | step_n_fwd _ hp => exact hp
  | step_n_bwd _ hp => exact hp
  | step_e _ hp => exact hp

private theorem reachENIn_lift_self {D : Type} {e n : Perm D} {P : D → Prop} {s t : D}
    (h : ReachENIn e n P s t) :
    ReachENIn e n (fun z => ReachENIn e n P s z) s t := by
  induction h with
  | refl hp => exact ReachENIn.refl (ReachENIn.refl hp)
  | step_n_fwd hr hp ih => exact ReachENIn.step_n_fwd ih (ReachENIn.step_n_fwd hr hp)
  | step_n_bwd hr hp ih => exact ReachENIn.step_n_bwd ih (ReachENIn.step_n_bwd hr hp)
  | step_e hr hp ih => exact ReachENIn.step_e ih (ReachENIn.step_e hr hp)

private theorem kempeComp_closed {H_cap : Hypermap} (col : H_cap.FaceColoring)
    (a b : Color) (start : H_cap.Dart) :
    H_cap.KempeClosed col a b
      (fun z => decide (ReachENIn H_cap.dual.edge H_cap.dual.node
        (fun x => col.color x = a ∨ col.color x = b) start z)) := by
  let P := fun x : H_cap.Dart => col.color x = a ∨ col.color x = b
  refine ⟨?_, ?_, ?_⟩
  · intro d
    have hface : H_cap.dual.node.inv d = H_cap.face.f d := rfl
    have hP : P (H_cap.face.f d) ↔ P d := by
      simp only [P, col.face_invariant d]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have h_bwd : H_cap.dual.node.f (H_cap.face.f d) = d := H_cap.dual.node.right_inv d
      have hPf : P (H_cap.face.f d) := reachENIn_target_prop h
      have hPd' : P (H_cap.dual.node.f (H_cap.face.f d)) := h_bwd.symm ▸ hP.mp hPf
      have hstep := ReachENIn.step_n_fwd h hPd'
      rwa [h_bwd] at hstep
    · intro h
      have hPd : P d := reachENIn_target_prop h
      have hPinv : P (H_cap.dual.node.inv d) := hface.symm ▸ hP.mpr hPd
      rw [← hface]
      exact ReachENIn.step_n_bwd h hPinv
  · intro d hd
    dsimp only at hd
    have hr := reachENIn_target_prop (of_decide_eq_true hd)
    exact hr
  · intro d hd hed
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      have he_eq : H_cap.dual.edge.f (H_cap.edge.f d) = d := H_cap.edge_involution d
      have hstep := ReachENIn.step_e h (he_eq.symm ▸ hd)
      rwa [he_eq] at hstep
    · intro h
      exact ReachENIn.step_e h hed

private theorem kempe_either_swap_4cycle {H_cap : Hypermap} [DecidableEq H_cap.Dart]
    (darts_cap : List H_cap.Dart) (h_nd : darts_cap.Nodup) (h_all : ∀ x, x ∈ darts_cap)
    (h_planar : H_cap.isPlanar darts_cap.length darts_cap = true)
    (col : H_cap.FaceColoring)
    {d0 d1 d2 d3 : H_cap.Dart} (hc : CyclicOrder4 H_cap.dual.face 4 d0 d1 d2 d3)
    (a b c d : Color)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (h0 : col.color d0 = a) (h2 : col.color d2 = b ∨ col.color d2 = a)
    (h1 : col.color d1 = c) (h3 : col.color d3 = d ∨ col.color d3 = c) :
    (∃ col' : H_cap.FaceColoring,
        col'.color d0 = b ∧ col'.color d2 = col.color d2 ∧
        col'.color d1 = col.color d1 ∧ col'.color d3 = col.color d3) ∨
    (∃ col' : H_cap.FaceColoring,
        col'.color d1 = d ∧ col'.color d3 = col.color d3 ∧
        col'.color d0 = col.color d0 ∧ col'.color d2 = col.color d2) := by
  let P1 := fun x : H_cap.Dart => col.color x = a ∨ col.color x = b
  let P2 := fun x : H_cap.Dart => col.color x = c ∨ col.color x = d
  let S1 := fun z : H_cap.Dart => decide (ReachENIn H_cap.dual.edge H_cap.dual.node P1 d0 z)
  let S2 := fun z : H_cap.Dart => decide (ReachENIn H_cap.dual.edge H_cap.dual.node P2 d1 z)
  have hS1_node : ∀ z, ReachENIn H_cap.dual.edge H_cap.dual.node P1 d0 (H_cap.dual.node.f z) ↔
      ReachENIn H_cap.dual.edge H_cap.dual.node P1 d0 z := by
    intro z
    have hPz : P1 (H_cap.dual.node.f z) ↔ P1 z := by
      have h_inv : H_cap.face.f (H_cap.dual.node.f z) = z := H_cap.face.right_inv z
      simp only [P1, ← col.face_invariant (H_cap.dual.node.f z), h_inv]
    constructor
    · intro hz
      have hinv : H_cap.dual.node.inv (H_cap.dual.node.f z) = z := H_cap.dual.node.left_inv z
      have hPfn : P1 (H_cap.dual.node.f z) := reachENIn_target_prop hz
      have hPinv : P1 (H_cap.dual.node.inv (H_cap.dual.node.f z)) := hinv.symm ▸ hPz.mp hPfn
      have hstep := ReachENIn.step_n_bwd hz hPinv
      rwa [hinv] at hstep
    · intro hz
      have hPz' : P1 z := reachENIn_target_prop hz
      exact ReachENIn.step_n_fwd hz (hPz.mpr hPz')
  have hS2_node : ∀ z, ReachENIn H_cap.dual.edge H_cap.dual.node P2 d1 (H_cap.dual.node.f z) ↔
      ReachENIn H_cap.dual.edge H_cap.dual.node P2 d1 z := by
    intro z
    have hPz : P2 (H_cap.dual.node.f z) ↔ P2 z := by
      have h_inv : H_cap.face.f (H_cap.dual.node.f z) = z := H_cap.face.right_inv z
      simp only [P2, ← col.face_invariant (H_cap.dual.node.f z), h_inv]
    constructor
    · intro hz
      have hinv : H_cap.dual.node.inv (H_cap.dual.node.f z) = z := H_cap.dual.node.left_inv z
      have hPfn : P2 (H_cap.dual.node.f z) := reachENIn_target_prop hz
      have hPinv : P2 (H_cap.dual.node.inv (H_cap.dual.node.f z)) := hinv.symm ▸ hPz.mp hPfn
      have hstep := ReachENIn.step_n_bwd hz hPinv
      rwa [hinv] at hstep
    · intro hz
      have hPz' : P2 z := reachENIn_target_prop hz
      exact ReachENIn.step_n_fwd hz (hPz.mpr hPz')
  by_cases h12 : ReachENIn H_cap.dual.edge H_cap.dual.node P1 d0 d2
  · have h_not_23 : ¬ReachENIn H_cap.dual.edge H_cap.dual.node P2 d1 d3 := by
      intro h23
      have hdual_pl : H_cap.dual.isPlanar darts_cap.length darts_cap = true := by
        rw [isPlanar_dual H_cap darts_cap h_nd h_all (Nat.le_refl _)]
        exact h_planar
      obtain ⟨z, hz1, hz2⟩ := alternating_walks_intersect_of_cyclic_face H_cap.dual darts_cap h_nd h_all
        hdual_pl hc (fun x => ReachENIn H_cap.dual.edge H_cap.dual.node P1 d0 x)
        (fun x => ReachENIn H_cap.dual.edge H_cap.dual.node P2 d1 x) hS1_node hS2_node
        (reachENIn_lift_self h12) (reachENIn_lift_self h23)
      have hP1 : P1 z := reachENIn_target_prop hz1
      have hP2 : P2 z := reachENIn_target_prop hz2
      rcases hP1 with he1 | he1 <;> rcases hP2 with he2 | he2
      · exact hac (he1.symm.trans he2)
      · exact had (he1.symm.trans he2)
      · exact hbc (he1.symm.trans he2)
      · exact hbd (he1.symm.trans he2)
    right
    refine ⟨H_cap.kempeSwap_valid col c d S2 (kempeComp_closed col c d d1), ?_, ?_, ?_, ?_⟩
    · have hd1 : S2 d1 = true := decide_eq_true (ReachENIn.refl (Or.inl h1))
      simp [kempeSwap_valid, kempeSwap, hd1, swapColor, h1]
    · have hd3 : S2 d3 = false := decide_eq_false h_not_23
      simp [kempeSwap_valid, kempeSwap, hd3]
    · have hd0 : S2 d0 = false := decide_eq_false (fun hr => by
        have hP2 : P2 d0 := reachENIn_target_prop hr
        dsimp only [P2] at hP2
        rw [h0] at hP2
        rcases hP2 with he | he
        · exact hac he
        · exact had he)
      simp [kempeSwap_valid, kempeSwap, hd0]
    · have hd2 : S2 d2 = false := decide_eq_false (fun hr => by
        have hP2 : P2 d2 := reachENIn_target_prop hr
        dsimp only [P2] at hP2
        rcases h2 with h2b | h2a
        · rw [h2b] at hP2
          rcases hP2 with he | he
          · exact hbc he
          · exact hbd he
        · rw [h2a] at hP2
          rcases hP2 with he | he
          · exact hac he
          · exact had he)
      simp [kempeSwap_valid, kempeSwap, hd2]
  · left
    refine ⟨H_cap.kempeSwap_valid col a b S1 (kempeComp_closed col a b d0), ?_, ?_, ?_, ?_⟩
    · have hd0 : S1 d0 = true := decide_eq_true (ReachENIn.refl (Or.inl h0))
      simp [kempeSwap_valid, kempeSwap, hd0, swapColor, h0]
    · have hd2 : S1 d2 = false := decide_eq_false h12
      simp [kempeSwap_valid, kempeSwap, hd2]
    · have hd1 : S1 d1 = false := decide_eq_false (fun hr => by
        have hP1 : P1 d1 := reachENIn_target_prop hr
        dsimp only [P1] at hP1
        rw [h1] at hP1
        rcases hP1 with he | he
        · exact hac he.symm
        · exact hbc he.symm)
      simp [kempeSwap_valid, kempeSwap, hd1]
    · have hd3 : S1 d3 = false := decide_eq_false (fun hr => by
        have hP1 : P1 d3 := reachENIn_target_prop hr
        dsimp only [P1] at hP1
        rcases h3 with h3d | h3c
        · rw [h3d] at hP1
          rcases hP1 with he | he
          · exact had he.symm
          · exact hbd he.symm
        · rw [h3c] at hP1
          rcases hP1 with he | he
          · exact hac he.symm
          · exact hbc he.symm)
      simp [kempeSwap_valid, kempeSwap, hd3]

private theorem exists_fourth_color (a c d : Color) :
    ∃ b : Color, b ≠ a ∧ b ≠ c ∧ b ≠ d := by
  cases a <;> cases c <;> cases d <;> first
    | exact ⟨Color.c0, by decide, by decide, by decide⟩
    | exact ⟨Color.c1, by decide, by decide, by decide⟩
    | exact ⟨Color.c2, by decide, by decide, by decide⟩
    | exact ⟨Color.c3, by decide, by decide, by decide⟩

private theorem kempe_P02_to_twoCol_or_P4 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring)
    (h02 : IsState02 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut col)) :
    ∃ col' : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState2 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut col') ∨
      IsState4 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut col') := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut
  let darts_cap := FaceCycleCut.capSingleVertexDarts darts cut
  have hsp := FaceCycleCut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br cut
  have h_cap_planar : @Hypermap.isPlanar H_cap (@instBEqOfDecidableEq H_cap.Dart _) darts_cap.length darts_cap = true := by
    have h1 := hsp.2.2.2.2.1
    rw [(capSingleVertex_beq_eq cut).trans (decEq_beq_eq _ _)] at h1
    exact h1
  have hc0 := FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
    (i0 := 0) (i1 := 1) (i2 := 2) (i3 := 3) (by decide) (by decide) (by decide) (by decide)
  have hc : CyclicOrder4 H_cap.dual.face 4 (Sum.inr ⟨2, by decide⟩) (Sum.inr ⟨1, by decide⟩)
      (Sum.inr ⟨0, by decide⟩) (Sum.inr ⟨3, by decide⟩) :=
    cyclicOrder4_rot H_cap.dual.face hc0
  let f := capBoundaryColors darts h_nd h_all h_planar h_conn cut col
  let a := f ⟨3, by decide⟩
  let b := f ⟨1, by decide⟩
  let c := f ⟨2, by decide⟩
  obtain ⟨d, hda, hdb, hdc⟩ := exists_fourth_color a b c
  have hac : a ≠ c := by
    have h := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut col (⟨2, by decide⟩ : Fin 4)
    change f ⟨3, by decide⟩ ≠ f ⟨2, by decide⟩ at h
    exact h
  have had : a ≠ d := hda.symm
  have hbc : b ≠ c := by
    have h := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut col (⟨1, by decide⟩ : Fin 4)
    change f ⟨2, by decide⟩ ≠ f ⟨1, by decide⟩ at h
    exact h.symm
  have hbd : b ≠ d := hdb.symm
  have h0' : col.color (Sum.inr ⟨2, by decide⟩) = a := rfl
  have h2' : col.color (Sum.inr ⟨0, by decide⟩) = b ∨ col.color (Sum.inr ⟨0, by decide⟩) = a :=
    Or.inl rfl
  have h1' : col.color (Sum.inr ⟨1, by decide⟩) = c := rfl
  have h3' : col.color (Sum.inr ⟨3, by decide⟩) = d ∨ col.color (Sum.inr ⟨3, by decide⟩) = c :=
    Or.inr (by dsimp only [c, f, capBoundaryColors]; exact h02.1)
  have hres := kempe_either_swap_4cycle darts_cap hsp.1 hsp.2.1 h_cap_planar col hc
    a b c d hac had hbc hbd h0' h2' h1' h3'
  rcases hres with ⟨col', hs2, hs0, hs1, hs3⟩ | ⟨col', hs1, hs3, hs2, hs0⟩
  · refine ⟨col', Or.inl ⟨?_, ?_⟩⟩
    · change col'.color (Sum.inr ⟨3, by decide⟩) = col'.color (Sum.inr ⟨1, by decide⟩)
      rw [hs3, hs1]
      exact h02.1
    · change col'.color (Sum.inr ⟨0, by decide⟩) = col'.color (Sum.inr ⟨2, by decide⟩)
      rw [hs0, hs2]
      rfl
  · refine ⟨col', Or.inr ⟨?_, ?_⟩⟩
    · change col'.color (Sum.inr ⟨3, by decide⟩) ≠ col'.color (Sum.inr ⟨1, by decide⟩)
      rw [hs3, hs1]
      change capBoundaryColors darts h_nd h_all h_planar h_conn cut col ⟨0, by decide⟩ ≠ d
      rw [h02.1]
      exact hdc.symm
    · change col'.color (Sum.inr ⟨0, by decide⟩) ≠ col'.color (Sum.inr ⟨2, by decide⟩)
      rw [hs0, hs2]
      exact h02.2

private theorem kempe_P4_to_02_or_13 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring)
    (h4 : IsState4 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut col)) :
    ∃ col' : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState02 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut col') ∨
      IsState13 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut col') := by
  have h_nd := h_mc.nodup
  have h_all := h_mc.complete
  have h_planar := h_mc.is_planar
  have h_conn := mc_numComponents_eq_one H darts h_mc
  have h_br := h_mc.is_bridgeless
  let H_cap := FaceCycleCut.capSingleVertexHypermap darts h_nd h_all h_planar h_conn cut
  let darts_cap := FaceCycleCut.capSingleVertexDarts darts cut
  have hsp := FaceCycleCut.capSingleVertex_spec darts h_nd h_all h_planar h_conn h_br cut
  have h_cap_planar : @Hypermap.isPlanar H_cap (@instBEqOfDecidableEq H_cap.Dart _) darts_cap.length darts_cap = true := by
    have h1 := hsp.2.2.2.2.1
    rw [(capSingleVertex_beq_eq cut).trans (decEq_beq_eq _ _)] at h1
    exact h1
  have hc0 := FaceCycleCut.capSingleVertex_cyclicOrder4 darts h_nd h_all h_planar h_conn cut
    (i0 := 0) (i1 := 1) (i2 := 2) (i3 := 3) (by decide) (by decide) (by decide) (by decide)
  have hc : CyclicOrder4 H_cap.dual.face 4 (Sum.inr ⟨2, by decide⟩) (Sum.inr ⟨1, by decide⟩)
      (Sum.inr ⟨0, by decide⟩) (Sum.inr ⟨3, by decide⟩) :=
    cyclicOrder4_rot H_cap.dual.face hc0
  let f := capBoundaryColors darts h_nd h_all h_planar h_conn cut col
  let a := f ⟨3, by decide⟩
  let b := f ⟨1, by decide⟩
  let c := f ⟨2, by decide⟩
  let d := f ⟨0, by decide⟩
  have hac : a ≠ c := by
    have h := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut col (⟨2, by decide⟩ : Fin 4)
    change f ⟨3, by decide⟩ ≠ f ⟨2, by decide⟩ at h
    exact h
  have had : a ≠ d := by
    have h := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut col (⟨3, by decide⟩ : Fin 4)
    change f ⟨0, by decide⟩ ≠ f ⟨3, by decide⟩ at h
    exact h.symm
  have hbc : b ≠ c := by
    have h := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut col (⟨1, by decide⟩ : Fin 4)
    change f ⟨2, by decide⟩ ≠ f ⟨1, by decide⟩ at h
    exact h.symm
  have hbd : b ≠ d := by
    have h := capBoundaryColors_adj darts h_nd h_all h_planar h_conn h_br cut col (⟨0, by decide⟩ : Fin 4)
    change f ⟨1, by decide⟩ ≠ f ⟨0, by decide⟩ at h
    exact h
  have h0' : col.color (Sum.inr ⟨2, by decide⟩) = a := rfl
  have h2' : col.color (Sum.inr ⟨0, by decide⟩) = b ∨ col.color (Sum.inr ⟨0, by decide⟩) = a :=
    Or.inl rfl
  have h1' : col.color (Sum.inr ⟨1, by decide⟩) = c := rfl
  have h3' : col.color (Sum.inr ⟨3, by decide⟩) = d ∨ col.color (Sum.inr ⟨3, by decide⟩) = c :=
    Or.inl rfl
  have hres := kempe_either_swap_4cycle darts_cap hsp.1 hsp.2.1 h_cap_planar col hc
    a b c d hac had hbc hbd h0' h2' h1' h3'
  rcases hres with ⟨col', hs2, hs0, hs1, hs3⟩ | ⟨col', hs1, hs3, hs2, hs0⟩
  · refine ⟨col', Or.inr ⟨?_, ?_⟩⟩
    · change col'.color (Sum.inr ⟨3, by decide⟩) ≠ col'.color (Sum.inr ⟨1, by decide⟩)
      rw [hs3, hs1]
      exact h4.1
    · change col'.color (Sum.inr ⟨0, by decide⟩) = col'.color (Sum.inr ⟨2, by decide⟩)
      rw [hs0, hs2]
      rfl
  · refine ⟨col', Or.inl ⟨?_, ?_⟩⟩
    · change col'.color (Sum.inr ⟨3, by decide⟩) = col'.color (Sum.inr ⟨1, by decide⟩)
      rw [hs3, hs1]
      rfl
    · change col'.color (Sum.inr ⟨0, by decide⟩) ≠ col'.color (Sum.inr ⟨2, by decide⟩)
      rw [hs0, hs2]
      exact h4.2

end K4SurgeriesAndKempe

section K4Main

private theorem fin4_col_eq_iff_of_adj {f g : Fin 4 → Color}
    (hf : ∀ i : Fin 4, f ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩ ≠ f i)
    (hg : ∀ i : Fin 4, g ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩ ≠ g i)
    (h02 : f ⟨0, by decide⟩ = f ⟨2, by decide⟩ ↔ g ⟨0, by decide⟩ = g ⟨2, by decide⟩)
    (h13 : f ⟨1, by decide⟩ = f ⟨3, by decide⟩ ↔ g ⟨1, by decide⟩ = g ⟨3, by decide⟩) :
    ∀ i j : Fin 4, f i = f j ↔
      g ⟨(4 - i.val) % 4, Nat.mod_lt _ (by decide)⟩ =
      g ⟨(4 - j.val) % 4, Nat.mod_lt _ (by decide)⟩ := by
  intro ⟨i, hi⟩ ⟨j, hj⟩
  have hf01 : f ⟨0, by decide⟩ ≠ f ⟨1, by decide⟩ := (hf ⟨0, by decide⟩).symm
  have hf12 : f ⟨1, by decide⟩ ≠ f ⟨2, by decide⟩ := (hf ⟨1, by decide⟩).symm
  have hf23 : f ⟨2, by decide⟩ ≠ f ⟨3, by decide⟩ := (hf ⟨2, by decide⟩).symm
  have hf30 : f ⟨3, by decide⟩ ≠ f ⟨0, by decide⟩ := by simpa using (hf ⟨3, by decide⟩).symm
  have hg01 : g ⟨0, by decide⟩ ≠ g ⟨1, by decide⟩ := (hg ⟨0, by decide⟩).symm
  have hg12 : g ⟨1, by decide⟩ ≠ g ⟨2, by decide⟩ := (hg ⟨1, by decide⟩).symm
  have hg23 : g ⟨2, by decide⟩ ≠ g ⟨3, by decide⟩ := (hg ⟨2, by decide⟩).symm
  have hg30 : g ⟨3, by decide⟩ ≠ g ⟨0, by decide⟩ := by simpa using (hg ⟨3, by decide⟩).symm
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  dsimp only <;>
  first
  | exact ⟨fun _ => rfl, fun _ => rfl⟩
  | simp only [hf01, hf01.symm, hf12, hf12.symm, hf23, hf23.symm, hf30, hf30.symm,
      hg01, hg01.symm, hg12, hg12.symm, hg23, hg23.symm, hg30, hg30.symm, iff_self]
  | exact h02
  | exact ⟨fun h => (h02.mp h.symm).symm, fun h => (h02.mpr h.symm).symm⟩
  | exact ⟨fun h => (h13.mp h).symm, fun h => h13.mpr h.symm⟩
  | exact ⟨fun h => h13.mp h.symm, fun h => (h13.mpr h).symm⟩

private theorem glue_of_state_match {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (colL : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring)
    (colR : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut.rev).FaceColoring)
    (h02 : capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut colL ⟨0, by decide⟩ =
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut colL ⟨2, by decide⟩ ↔
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut.rev colR ⟨0, by decide⟩ =
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut.rev colR ⟨2, by decide⟩)
    (h13 : capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut colL ⟨1, by decide⟩ =
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut colL ⟨3, by decide⟩ ↔
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut.rev colR ⟨1, by decide⟩ =
      capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut.rev colR ⟨3, by decide⟩) :
    False :=
  glue_of_cap_colorings darts h_mc cut colL colR
    (fin4_col_eq_iff_of_adj
      (capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) h_mc.is_bridgeless cut colL)
      (capBoundaryColors_adj darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) h_mc.is_bridgeless cut.rev colR)
      h02 h13)

private theorem pinch13_of_no_chord13 {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4) (h_no13 : ¬HasDiagChord13 cut) :
    ∃ col : (FaceCycleCut.capSingleVertexHypermap darts h_mc.nodup h_mc.complete h_mc.is_planar
      (mc_numComponents_eq_one H darts h_mc) cut).FaceColoring,
      IsState2 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut col) ∨
      IsState13 (capBoundaryColors darts h_mc.nodup h_mc.complete h_mc.is_planar
        (mc_numComponents_eq_one H darts h_mc) cut col) := by
  obtain ⟨col_rot, hrot⟩ := pinch_coloring_of_no_chord02 darts h_mc cut.rot1 h_no13
  obtain ⟨col, hcol⟩ := capColoring_of_rot1 darts h_mc.nodup h_mc.complete h_mc.is_planar
    (mc_numComponents_eq_one H darts h_mc) h_mc.is_bridgeless cut col_rot
  refine ⟨col, ?_⟩
  rcases hrot with h2 | h02
  · left
    exact ⟨by rw [hcol ⟨0, by decide⟩, hcol ⟨2, by decide⟩]; exact h2.2.symm,
           by rw [hcol ⟨1, by decide⟩, hcol ⟨3, by decide⟩]; exact h2.1⟩
  · right
    exact ⟨by rw [hcol ⟨0, by decide⟩, hcol ⟨2, by decide⟩]; exact fun h => h02.2 h.symm,
           by rw [hcol ⟨1, by decide⟩, hcol ⟨3, by decide⟩]; exact h02.1⟩

/-- If both sides of a 4-edge cut in a minimal counterexample have at least 12 darts
    (equivalently, the 4-cycle is separating with `|D_L|, |D_R| ≥ 12`), Kempe-chain
    non-crossing + pinching yields matching boundary colorings on `cut` and `cut.rev`,
    contradicting minimality. -/
theorem mc_four_cycle_both_sides_ge12_impossible {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (hL12 : 12 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length)
    (hR12 : 12 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) :
    False := by
  have hnc := separating_four_cycle_no_chord_both darts h_mc cut hL12 hR12
  rcases hnc with ⟨h_no02L, h_no13L, h_no02R, h_no13R⟩
  have hL12_rev : 12 ≤ (darts.filter (fun x => decide (cut.rev.rev.capSingleVertex_DL x))).length := by
    rw [cut.rev_rev]; exact hL12
  obtain ⟨colL_A, hLA⟩ := pinch_coloring_of_no_chord02 darts h_mc cut h_no02L
  obtain ⟨colL_B, hLB⟩ := pinch13_of_no_chord13 darts h_mc cut h_no13L
  obtain ⟨colL_C, hLC⟩ := capSplit02_coloring darts h_mc cut hR12
  obtain ⟨colR_A, hRA⟩ := pinch_coloring_of_no_chord02 darts h_mc cut.rev h_no02R
  obtain ⟨colR_B, hRB⟩ := pinch13_of_no_chord13 darts h_mc cut.rev h_no13R
  obtain ⟨colR_C, hRC⟩ := capSplit02_coloring darts h_mc cut.rev hL12_rev
  rcases hLA with hLA2 | hLA02 <;> rcases hRA with hRA2 | hRA02
  · exact glue_of_state_match darts h_mc cut colL_A colR_A
      (iff_of_true hLA2.1 hRA2.1) (iff_of_true hLA2.2 hRA2.2)
  · rcases hRB with hRB2 | hRB13
    · exact glue_of_state_match darts h_mc cut colL_A colR_B
        (iff_of_true hLA2.1 hRB2.1) (iff_of_true hLA2.2 hRB2.2)
    · rcases hLC with hLC02 | hLC4
      · exact glue_of_state_match darts h_mc cut colL_C colR_A
          (iff_of_true hLC02.1 hRA02.1) (iff_of_false hLC02.2 hRA02.2)
      · obtain ⟨colL_K, hLK⟩ := kempe_P4_to_02_or_13 darts h_mc cut colL_C hLC4
        rcases hLK with hLK02 | hLK13
        · exact glue_of_state_match darts h_mc cut colL_K colR_A
            (iff_of_true hLK02.1 hRA02.1) (iff_of_false hLK02.2 hRA02.2)
        · exact glue_of_state_match darts h_mc cut colL_K colR_B
            (iff_of_false hLK13.1 hRB13.1) (iff_of_true hLK13.2 hRB13.2)
  · rcases hLB with hLB2 | hLB13
    · exact glue_of_state_match darts h_mc cut colL_B colR_A
        (iff_of_true hLB2.1 hRA2.1) (iff_of_true hLB2.2 hRA2.2)
    · rcases hRC with hRC02 | hRC4
      · exact glue_of_state_match darts h_mc cut colL_A colR_C
          (iff_of_true hLA02.1 hRC02.1) (iff_of_false hLA02.2 hRC02.2)
      · obtain ⟨colR_K, hRK⟩ := kempe_P4_to_02_or_13 darts h_mc cut.rev colR_C hRC4
        rcases hRK with hRK02 | hRK13
        · exact glue_of_state_match darts h_mc cut colL_A colR_K
            (iff_of_true hLA02.1 hRK02.1) (iff_of_false hLA02.2 hRK02.2)
        · exact glue_of_state_match darts h_mc cut colL_B colR_K
            (iff_of_false hLB13.1 hRK13.1) (iff_of_true hLB13.2 hRK13.2)
  · exact glue_of_state_match darts h_mc cut colL_A colR_A
      (iff_of_true hLA02.1 hRA02.1) (iff_of_false hLA02.2 hRA02.2)

/-- **K4 No Separating 4-Cycle:** Every 4-cycle in `H.dual` for a minimal counterexample
    has at least one side containing only 6 darts (two adjacent facial triangles, no strictly
    interior cubic vertices of `H`). -/
theorem mc_no_separating_four_cycle_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4) :
    (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length = 6 ∨
      (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length = 6 := by
  rcases four_cycle_side_length_cases darts h_mc cut with ⟨hL6 | hL12, hR6 | hR12⟩
  · exact Or.inl hL6
  · exact Or.inl hL6
  · exact Or.inr hR6
  · exact absurd (mc_four_cycle_both_sides_ge12_impossible darts h_mc cut hL12 hR12) False.elim

/-- Equivalently, no 4-cycle in `H.dual` separates two sides each having at least 7 darts. -/
theorem mc_four_cycle_small_side_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4)
    (hL7 : 7 ≤ (darts.filter (fun x => decide (cut.capSingleVertex_DL x))).length)
    (hR7 : 7 ≤ (darts.filter (fun x => decide (cut.rev.capSingleVertex_DL x))).length) :
    False := by
  rcases mc_no_separating_four_cycle_dual H darts h_mc cut with hL6 | hR6 <;> omega

/-- **K4 No Chordless 4-Cycle (cut-chord form):** Every 4-cycle in `H.dual` for a
    minimal counterexample has a diagonal chord (`0-2` or `1-3`) on its small 6-dart side. -/
theorem mc_no_chordless_four_cycle_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4) :
    HasDiagChord02 cut ∨ HasDiagChord13 cut ∨ HasDiagChord02 cut.rev ∨ HasDiagChord13 cut.rev := by
  rcases mc_no_separating_four_cycle_dual H darts h_mc cut with hL6 | hR6
  · rcases four_cycle_six_dart_side_has_chord darts h_mc cut hL6 with h02 | h13
    · exact Or.inl h02
    · exact Or.inr (Or.inl h13)
  · rcases four_cycle_six_dart_side_has_chord darts h_mc cut.rev hR6 with h02 | h13
    · exact Or.inr (Or.inr (Or.inl h02))
    · exact Or.inr (Or.inr (Or.inr h13))

/-- **K4 No Chordless 4-Cycle (vertex-chord form):** Every 4-cycle `(v0, v1, v2, v3)`
    in `H.dual` has a diagonal edge joining `v0` to `v2` or `v1` to `v3`. -/
theorem mc_four_cycle_has_diag_edge_dual (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    (cut : H.FaceCycleCut 4) :
    (∃ u : H.Dart, SameOrbit H.face (cut.ringFace ⟨0, by decide⟩) u ∧
        SameOrbit H.face (cut.ringFace ⟨2, by decide⟩) (H.edge.f u)) ∨
      (∃ u : H.Dart, SameOrbit H.face (cut.ringFace ⟨1, by decide⟩) u ∧
        SameOrbit H.face (cut.ringFace ⟨3, by decide⟩) (H.edge.f u)) := by
  rcases mc_no_chordless_four_cycle_dual H darts h_mc cut with h02L | h13L | h02R | h13R
  · rcases h02L with ⟨u, -, -, hf0, hf2⟩
    exact Or.inl ⟨u, hf0, hf2⟩
  · rcases h13L with ⟨u, -, -, hf1, hf3⟩
    exact Or.inr ⟨u, hf1, hf3⟩
  · rcases h02R with ⟨u, -, -, hf0, hf2⟩
    exact Or.inl ⟨u, hf0, hf2⟩
  · rcases h13R with ⟨u, -, -, hf3, hf1⟩
    exact Or.inr ⟨H.edge.f u, hf1, by rw [mc_edge_inv]; exact hf3⟩

end K4Main

end Hypermap

