module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Hypermap
public import FourColorTheorem.Math.Planarity
public import FourColorTheorem.Math.Kempe
public import FourColorTheorem.Math.Reducibility
public import FourColorTheorem.Math.Topology.OrbitLemmas
public import FourColorTheorem.Math.Topology.Surgery
public import FourColorTheorem.Math.Topology.Euler
public import FourColorTheorem.Math.Topology.ComponentLemmas
public import FourColorTheorem.Math.Topology.SubtypeSurgery
public import FourColorTheorem.Math.Topology.Genus
public import FourColorTheorem.Math.Topology.K5Obstruction

@[expose] public section

/-!
# Stage S.3 (Part 2): Planar Kempe-Chain Non-Crossing & Boundary Partition Pullback

This module establishes the planar Kempe topological engine on hypermaps:
1. Equivalence-class and orbit-counting congruence/monotonicity bridges, constructive
   `WalkENIn` walks with `e`-step length, and `isPlanar_dual` (`H.dual.isPlanar = H.isPlanar`).
2. `splitVertexAtPair`: 1-step vertex split along two corners `(d_a, d_b)` sharing a face,
   giving the exact Euler deficit drop `ΔgenusDeficit = -2` when a cross-arc `V(d_a)`-avoiding
   walk connects both arcs (`no_cross_arc_walk_on_face`), or a planar 2-component split.
3. `addFaceApex4`: 4-spoke star apex subdivision of a face `F` preserving planarity
   (`isPlanar_addFaceApex4`) via `genusDeficit = 0`.
4. `alternating_walks_intersect_of_cyclic_face`: any two disjoint `node`-invariant alternating
   walks crossing cyclically at `(d0, d1, d2, d3)` on a planar face contradict `no_K5_minor_of_isPlanar`.
5. `swapKempeClassUnion`, `cappedRing_isJointPlanarRingPartition`, and `kempe_pullback_of_cappedRing`:
   connects planar `FaceColoring` Kempe chains around a capped boundary ring to RSST's
   `IsJointPlanarRingPartition` and pulls `Eliminated c bnd` back to `H_ext`.
-/

namespace Hypermap

section OrbitAndRelationHelpers

theorem countOrbits_pos_cons {D : Type} [BEq D] (p : Perm D) (fuel : Nat) (d : D) (ds : List D) :
    1 ≤ countOrbits p fuel (d :: ds) := by
  change 1 ≤ countOrbitsAux p fuel (ds.length + 1) (d :: ds)
  rw [countOrbitsAux]
  exact Nat.le_add_right 1 _

theorem countRelClasses_pos_cons {D : Type} (R : D → D → Prop) [DecidableRel R] (d : D) (ds : List D) :
    1 ≤ countRelClasses R (d :: ds) := by
  rw [countRelClasses_cons]
  exact Nat.le_add_right 1 _

theorem countRelClasses_le_of_cover {D : Type} (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z) :
    ∀ (reps l : List D), (∀ x ∈ l, ∃ r ∈ reps, R r x) → countRelClasses R l ≤ reps.length
  | [], l, hcov => by
    cases l with
    | nil => rw [countRelClasses_nil]; exact Nat.zero_le _
    | cons x _ =>
      obtain ⟨r, hr, _⟩ := hcov x List.mem_cons_self
      cases hr
  | r :: rs, l, hcov => by
    let S : D → Bool := fun x => decide (R r x)
    have hS : ∀ {x y : D}, R x y → S x = S y := by
      intro x y hxy
      simp only [S]
      exact Bool.eq_iff_iff.mpr (by
        simp only [decide_eq_true_eq]
        exact ⟨fun hrx => h_trans hrx hxy, fun hry => h_trans hry (h_symm hxy)⟩)
    have hpart := countRelClasses_partition_of_closed R h_refl h_symm h_trans S hS l
    have h1 : countRelClasses R (l.filter S) ≤ 1 := by
      cases hfl : l.filter S with
      | nil => rw [countRelClasses_nil]; omega
      | cons a as =>
        rw [countRelClasses_cons]
        have ha_mem : a ∈ l.filter S := hfl ▸ List.mem_cons_self
        have haS : S a = true := (List.mem_filter.mp ha_mem).2
        have hra : R r a := of_decide_eq_true haS
        have h_nil : as.filter (fun x => !decide (R a x)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          have hx_mem : x ∈ l.filter S := hfl ▸ List.mem_cons_of_mem a hx
          have hxS : S x = true := (List.mem_filter.mp hx_mem).2
          have hrx : R r x := of_decide_eq_true hxS
          have hax : R a x := h_trans (h_symm hra) hrx
          simp [hax]
        rw [h_nil, countRelClasses_nil]
        exact Nat.le_refl 1
    have h2 : countRelClasses R (l.filter (fun x => !S x)) ≤ rs.length := by
      apply countRelClasses_le_of_cover R h_refl h_symm h_trans rs
      intro x hx
      have hx' := List.mem_filter.mp hx
      obtain ⟨r', hr'_mem, hr'x⟩ := hcov x hx'.1
      rcases List.mem_cons.mp hr'_mem with rfl | hr'_rs
      · have : S x = true := decide_eq_true hr'x
        simp [this] at hx'
      · exact ⟨r', hr'_rs, hr'x⟩
    rw [hpart]
    simp only [List.length_cons]
    omega

theorem countRelClasses_eq_singleton_of_closed {D : Type} (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    (a : D) {l : List D} (hne : l ≠ []) (hall : ∀ x ∈ l, R a x) :
    countRelClasses R l = 1 := by
  have hle := countRelClasses_le_of_cover R h_refl h_symm h_trans [a] l
    (fun x hx => ⟨a, List.mem_cons_self, hall x hx⟩)
  cases l with
  | nil => exact absurd rfl hne
  | cons d ds =>
    have hge := countRelClasses_pos_cons R d ds
    simp only [List.length_singleton] at hle
    omega

theorem countRelClasses_eq_of_iff {D : Type}
    (R1 R2 : D → D → Prop) [DecidableRel R1] [DecidableRel R2]
    (h1_refl : ∀ x, R1 x x) (h1_symm : ∀ {x y}, R1 x y → R1 y x) (h1_trans : ∀ {x y z}, R1 x y → R1 y z → R1 x z)
    (h2_refl : ∀ x, R2 x x) (h2_symm : ∀ {x y}, R2 x y → R2 y x) (h2_trans : ∀ {x y z}, R2 x y → R2 y z → R2 x z)
    (hiff : ∀ x y, R1 x y ↔ R2 x y) :
    ∀ l : List D, countRelClasses R1 l = countRelClasses R2 l := by
  intro l
  induction hl : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => rw [countRelClasses_nil, countRelClasses_nil]
    | cons a as =>
      let S : D → Bool := fun x => decide (R1 a x)
      have hS1 : ∀ {x y : D}, R1 x y → S x = S y := fun hxy => by
        simp only [S]
        exact Bool.eq_iff_iff.mpr (by
          simp only [decide_eq_true_eq]
          exact ⟨fun h => h1_trans h hxy, fun h => h1_trans h (h1_symm hxy)⟩)
      have hS2 : ∀ {x y : D}, R2 x y → S x = S y := fun {x y} hxy => hS1 ((hiff x y).mpr hxy)
      have hp1 := countRelClasses_partition_of_closed R1 h1_refl h1_symm h1_trans S hS1 (a :: as)
      have hp2 := countRelClasses_partition_of_closed R2 h2_refl h2_symm h2_trans S hS2 (a :: as)
      have haS : S a = true := decide_eq_true (h1_refl a)
      have hne_s : (a :: as).filter S ≠ [] := by
        intro hnil
        have hm : a ∈ (a :: as).filter S := List.mem_filter.mpr ⟨List.mem_cons_self, haS⟩
        rw [hnil] at hm; exact List.not_mem_nil hm
      have heq1 : countRelClasses R1 ((a :: as).filter S) = 1 :=
        countRelClasses_eq_singleton_of_closed R1 h1_refl h1_symm h1_trans a hne_s
          (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)
      have heq2 : countRelClasses R2 ((a :: as).filter S) = 1 :=
        countRelClasses_eq_singleton_of_closed R2 h2_refl h2_symm h2_trans a hne_s
          (fun x hx => (hiff a x).mp (of_decide_eq_true (List.mem_filter.mp hx).2))
      have hrest_sub : ((a :: as).filter (fun x => !S x)) = as.filter (fun x => !S x) := by
        rw [List.filter_cons]; simp [haS]
      have hlt : ((a :: as).filter (fun x => !S x)).length < n := by
        rw [hrest_sub, ← hl, List.length_cons]
        exact Nat.lt_succ_of_le (List.length_filter_le _ as)
      have ih_rest := ih _ hlt _ rfl
      rw [hp1, hp2, heq1, heq2, ih_rest]

theorem countRelClasses_le_of_finer {D : Type}
    (R1 R2 : D → D → Prop) [DecidableRel R1] [DecidableRel R2]
    (h1_refl : ∀ x, R1 x x) (h1_symm : ∀ {x y}, R1 x y → R1 y x) (h1_trans : ∀ {x y z}, R1 x y → R1 y z → R1 x z)
    (h2_refl : ∀ x, R2 x x) (h2_symm : ∀ {x y}, R2 x y → R2 y x) (h2_trans : ∀ {x y z}, R2 x y → R2 y z → R2 x z)
    (himp : ∀ {x y}, R1 x y → R2 x y) :
    ∀ l : List D, countRelClasses R2 l ≤ countRelClasses R1 l := by
  intro l
  induction hl : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => rw [countRelClasses_nil, countRelClasses_nil]; exact Nat.le_refl _
    | cons a as =>
      let S : D → Bool := fun x => decide (R2 a x)
      have hS2 : ∀ {x y : D}, R2 x y → S x = S y := fun hxy => by
        simp only [S]
        exact Bool.eq_iff_iff.mpr (by
          simp only [decide_eq_true_eq]
          exact ⟨fun h => h2_trans h hxy, fun h => h2_trans h (h2_symm hxy)⟩)
      have hS1 : ∀ {x y : D}, R1 x y → S x = S y := fun hxy => hS2 (himp hxy)
      have hp1 := countRelClasses_partition_of_closed R1 h1_refl h1_symm h1_trans S hS1 (a :: as)
      have hp2 := countRelClasses_partition_of_closed R2 h2_refl h2_symm h2_trans S hS2 (a :: as)
      have haS : S a = true := decide_eq_true (h2_refl a)
      have hne_s : (a :: as).filter S ≠ [] := by
        intro hnil
        have hm : a ∈ (a :: as).filter S := List.mem_filter.mpr ⟨List.mem_cons_self, haS⟩
        rw [hnil] at hm; exact List.not_mem_nil hm
      have heq2 : countRelClasses R2 ((a :: as).filter S) = 1 :=
        countRelClasses_eq_singleton_of_closed R2 h2_refl h2_symm h2_trans a hne_s
          (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)
      have hge1 : 1 ≤ countRelClasses R1 ((a :: as).filter S) := by
        cases hfl : (a :: as).filter S with
        | nil => exact absurd hfl hne_s
        | cons b bs => exact countRelClasses_pos_cons R1 b bs
      have hrest_sub : ((a :: as).filter (fun x => !S x)) = as.filter (fun x => !S x) := by
        rw [List.filter_cons]; simp [haS]
      have hlt : ((a :: as).filter (fun x => !S x)).length < n := by
        rw [hrest_sub, ← hl, List.length_cons]
        exact Nat.lt_succ_of_le (List.length_filter_le _ as)
      have ih_rest := ih _ hlt _ rfl
      omega

theorem countOrbits_eq_countRelClasses {D : Type} [DecidableEq D]
    (p : Perm D) (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    [DecidableRel (SameOrbit p)] :
    ∀ l : List D, countOrbits p fuel l = countRelClasses (SameOrbit p) l := by
  intro l
  have hrefl : ∀ x, SameOrbit p x x := sameOrbit_refl p
  have hsymm : ∀ {x y}, SameOrbit p x y → SameOrbit p y x := sameOrbit_symm_of_complete p darts h_all
  have htrans : ∀ {x y z}, SameOrbit p x y → SameOrbit p y z → SameOrbit p x z := sameOrbit_trans p
  induction hl : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => rw [countOrbits_nil, countRelClasses_nil]
    | cons a as =>
      let S : D → Bool := fun x => decide (SameOrbit p a x)
      have hS_step : ∀ x, S (p.f x) = S x := fun x => by
        simp only [S]
        exact Bool.eq_iff_iff.mpr (by
          simp only [decide_eq_true_eq]
          exact ⟨fun h => htrans h (hsymm (sameOrbit_step p rfl)),
                 fun h => htrans h (sameOrbit_step p rfl)⟩)
      have hS_rel : ∀ {x y : D}, SameOrbit p x y → S x = S y := fun hxy => by
        simp only [S]
        exact Bool.eq_iff_iff.mpr (by
          simp only [decide_eq_true_eq]
          exact ⟨fun h => htrans h hxy, fun h => htrans h (hsymm hxy)⟩)
      have hpo := countOrbits_partition_of_closed p fuel (a :: as) S hS_step
      have hpr := countRelClasses_partition_of_closed (SameOrbit p) hrefl hsymm htrans S hS_rel (a :: as)
      have haS : S a = true := decide_eq_true (hrefl a)
      have hne_s : (a :: as).filter S ≠ [] := by
        intro hnil
        have hm : a ∈ (a :: as).filter S := List.mem_filter.mpr ⟨List.mem_cons_self, haS⟩
        rw [hnil] at hm; exact List.not_mem_nil hm
      have heq_o : countOrbits p fuel ((a :: as).filter S) = 1 := by
        have hle := countOrbits_le_of_cover p darts h_all h_len [a] ((a :: as).filter S)
          (fun x hx => ⟨a, List.mem_cons_self, of_decide_eq_true (List.mem_filter.mp hx).2⟩)
        cases hfl : (a :: as).filter S with
        | nil => exact absurd hfl hne_s
        | cons b bs =>
          have hge := countOrbits_pos_cons p fuel b bs
          rw [hfl] at hle
          simp only [List.length_singleton] at hle
          omega
      have heq_r : countRelClasses (SameOrbit p) ((a :: as).filter S) = 1 :=
        countRelClasses_eq_singleton_of_closed (SameOrbit p) hrefl hsymm htrans a hne_s
          (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)
      have hrest_sub : ((a :: as).filter (fun x => !S x)) = as.filter (fun x => !S x) := by
        rw [List.filter_cons]; simp [haS]
      have hlt : ((a :: as).filter (fun x => !S x)).length < n := by
        rw [hrest_sub, ← hl, List.length_cons]
        exact Nat.lt_succ_of_le (List.length_filter_le _ as)
      have ih_rest := ih _ hlt _ rfl
      rw [hpo, hpr, heq_o, heq_r, ih_rest]

theorem countOrbits_eq_of_sameOrbit_iff {D : Type} [DecidableEq D]
    (p1 p2 : Perm D) (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel1 fuel2 : Nat} (h_len1 : darts.length ≤ fuel1) (h_len2 : darts.length ≤ fuel2)
    (hiff : ∀ x y, SameOrbit p1 x y ↔ SameOrbit p2 x y)
    (l : List D) :
    countOrbits p1 fuel1 l = countOrbits p2 fuel2 l := by
  classical
  rw [countOrbits_eq_countRelClasses p1 darts h_all h_len1 l,
      countOrbits_eq_countRelClasses p2 darts h_all h_len2 l]
  exact countRelClasses_eq_of_iff (SameOrbit p1) (SameOrbit p2)
    (sameOrbit_refl p1) (sameOrbit_symm_of_complete p1 darts h_all) (sameOrbit_trans p1)
    (sameOrbit_refl p2) (sameOrbit_symm_of_complete p2 darts h_all) (sameOrbit_trans p2)
    hiff l

theorem countOrbits_le_of_finer {D : Type} [DecidableEq D]
    (p1 p2 : Perm D) (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel1 fuel2 : Nat} (h_len1 : darts.length ≤ fuel1) (h_len2 : darts.length ≤ fuel2)
    (himp : ∀ {x y}, SameOrbit p1 x y → SameOrbit p2 x y)
    (l : List D) :
    countOrbits p2 fuel2 l ≤ countOrbits p1 fuel1 l := by
  classical
  rw [countOrbits_eq_countRelClasses p1 darts h_all h_len1 l,
      countOrbits_eq_countRelClasses p2 darts h_all h_len2 l]
  exact countRelClasses_le_of_finer (SameOrbit p1) (SameOrbit p2)
    (sameOrbit_refl p1) (sameOrbit_symm_of_complete p1 darts h_all) (sameOrbit_trans p1)
    (sameOrbit_refl p2) (sameOrbit_symm_of_complete p2 darts h_all) (sameOrbit_trans p2)
    himp l

end OrbitAndRelationHelpers

section SwapFunAndPermIter

theorem swapFun_self {D : Type} [DecidableEq D] (a x : D) : swapFun a a x = x := by
  dsimp only [swapFun]
  by_cases h : x = a
  · rw [if_pos h, h]
  · rw [if_neg h, if_neg h]

theorem swapFun_involutive {D : Type} [DecidableEq D] (a b x : D) :
    swapFun a b (swapFun a b x) = x := by
  by_cases ha : x = a
  · subst ha; rw [swapFun_left, swapFun_right]
  · by_cases hb : x = b
    · subst hb; rw [swapFun_right, swapFun_left]
    · rw [swapFun_of_ne ha hb, swapFun_of_ne ha hb]

theorem swapCompRight_involutive {D : Type} [DecidableEq D] (p : Perm D) (a b : D) :
    swapCompRight (swapCompRight p a b) a b = p := by
  cases p with
  | mk f inv li ri =>
    simp only [swapCompRight]
    congr 1
    · funext x; exact congrArg f (swapFun_involutive a b x)
    · funext x; exact swapFun_involutive a b (inv x)

theorem perm_iter_succ_left {D : Type} (p : Perm D) :
    ∀ (n : Nat) (x : D), Perm.iter p (n + 1) x = p.f (Perm.iter p n x)
  | 0, _ => rfl
  | n + 1, x => by
    rw [Perm.iter_succ_right, perm_iter_succ_left p n (p.f x), ← Perm.iter_succ_right]

theorem perm_iter_add {D : Type} (p : Perm D) :
    ∀ (m n : Nat) (x : D), Perm.iter p (m + n) x = Perm.iter p m (Perm.iter p n x)
  | 0, n, x => by rw [Nat.zero_add]; rfl
  | m + 1, n, x => by
    rw [Nat.add_right_comm, perm_iter_succ_left, perm_iter_succ_left, perm_iter_add p m n x]

theorem perm_iter_sameOrbit {D : Type} (p : Perm D) :
    ∀ (k : Nat) (x : D), SameOrbit p x (Perm.iter p k x)
  | 0, x => sameOrbit_refl p x
  | k + 1, x => by
    rw [Perm.iter_succ_right]
    exact sameOrbit_trans p (sameOrbit_step p rfl) (perm_iter_sameOrbit p k (p.f x))

end SwapFunAndPermIter

section WalksAndDual

/-- Constructive walk in `(e, n)` staying within vertex-or-dart predicate `P`,
    supporting explicit `e`-step length accounting (`eLen`). -/
inductive WalkENIn {D : Type} (e n : Perm D) (P : D → Prop) (x : D) : D → Type
  | refl : P x → WalkENIn e n P x x
  | n_fwd {y : D} : WalkENIn e n P x y → P (n.f y) → WalkENIn e n P x (n.f y)
  | n_bwd {y : D} : WalkENIn e n P x y → P (n.inv y) → WalkENIn e n P x (n.inv y)
  | e_step {y : D} : WalkENIn e n P x y → P (e.f y) → WalkENIn e n P x (e.f y)

def WalkENIn.eLen {D : Type} {e n : Perm D} {P : D → Prop} {x y : D} :
    WalkENIn e n P x y → Nat
  | .refl _ => 0
  | .n_fwd w _ => w.eLen
  | .n_bwd w _ => w.eLen
  | .e_step w _ => w.eLen + 1

theorem walkENIn_left {D : Type} {e n : Perm D} {P : D → Prop} {x y : D} :
    WalkENIn e n P x y → P x
  | .refl hx => hx
  | .n_fwd w _ => walkENIn_left w
  | .n_bwd w _ => walkENIn_left w
  | .e_step w _ => walkENIn_left w

theorem walkENIn_right {D : Type} {e n : Perm D} {P : D → Prop} {x y : D} :
    WalkENIn e n P x y → P y
  | .refl hx => hx
  | .n_fwd _ hy => hy
  | .n_bwd _ hy => hy
  | .e_step _ hy => hy

def WalkENIn.trans {D : Type} {e n : Perm D} {P : D → Prop} {x y z : D}
    (w1 : WalkENIn e n P x y) (w2 : WalkENIn e n P y z) : WalkENIn e n P x z :=
  match w2 with
  | .refl _ => w1
  | .n_fwd w hy => .n_fwd (w1.trans w) hy
  | .n_bwd w hy => .n_bwd (w1.trans w) hy
  | .e_step w hy => .e_step (w1.trans w) hy

theorem WalkENIn.eLen_trans {D : Type} {e n : Perm D} {P : D → Prop} {x y z : D}
    (w1 : WalkENIn e n P x y) (w2 : WalkENIn e n P y z) :
    (w1.trans w2).eLen = w1.eLen + w2.eLen := by
  induction w2 with
  | refl _ => simp [WalkENIn.trans, WalkENIn.eLen]
  | n_fwd w _ ih => simp [WalkENIn.trans, WalkENIn.eLen, ih]
  | n_bwd w _ ih => simp [WalkENIn.trans, WalkENIn.eLen, ih]
  | e_step w _ ih => simp [WalkENIn.trans, WalkENIn.eLen, ih, Nat.add_assoc]

def WalkENIn.mapPred {D : Type} {e n : Perm D} {P Q : D → Prop} (hPQ : ∀ z, P z → Q z)
    {x y : D} : WalkENIn e n P x y → WalkENIn e n Q x y
  | .refl hx => .refl (hPQ _ hx)
  | .n_fwd w hy => .n_fwd (w.mapPred hPQ) (hPQ _ hy)
  | .n_bwd w hy => .n_bwd (w.mapPred hPQ) (hPQ _ hy)
  | .e_step w hy => .e_step (w.mapPred hPQ) (hPQ _ hy)

theorem WalkENIn.eLen_mapPred {D : Type} {e n : Perm D} {P Q : D → Prop} (hPQ : ∀ z, P z → Q z)
    {x y : D} (w : WalkENIn e n P x y) : (w.mapPred hPQ).eLen = w.eLen := by
  induction w <;> simp [WalkENIn.mapPred, WalkENIn.eLen, *]

def WalkENIn.ofSameOrbit {D : Type} (e n : Perm D) (P : D → Prop)
    (hP : ∀ z, P (n.f z) ↔ P z) (x : D) (hx : P x) :
    ∀ k : Nat, WalkENIn e n P x (Perm.iter n k x)
  | 0 => .refl hx
  | k + 1 =>
    Eq.mp (congrArg (WalkENIn e n P x) (perm_iter_succ_left n k x).symm)
      (.n_fwd (WalkENIn.ofSameOrbit e n P hP x hx k)
        ((hP _).mpr (walkENIn_right (WalkENIn.ofSameOrbit e n P hP x hx k))))

theorem WalkENIn.eLen_ofSameOrbit {D : Type} (e n : Perm D) (P : D → Prop)
    (hP : ∀ z, P (n.f z) ↔ P z) (x : D) (hx : P x) (k : Nat) :
    (WalkENIn.ofSameOrbit e n P hP x hx k).eLen = 0 := by
  have hcast : ∀ {a b : D} (heq : a = b) (w : WalkENIn e n P x a),
      (Eq.mp (congrArg (WalkENIn e n P x) heq) w).eLen = w.eLen := by
    rintro _ _ rfl _; rfl
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [WalkENIn.ofSameOrbit]
    exact (hcast (perm_iter_succ_left n k x).symm _).trans ih

theorem nonempty_walkENIn_iff_reachENIn {D : Type} {e n : Perm D} {P : D → Prop} {x y : D} :
    Nonempty (WalkENIn e n P x y) ↔ ReachENIn e n P x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | refl hx => exact .refl hx
    | n_fwd _ hy ih => exact .step_n_fwd ih hy
    | n_bwd _ hy ih => exact .step_n_bwd ih hy
    | e_step _ hy ih => exact .step_e ih hy
  · intro h
    induction h with
    | refl hx => exact ⟨.refl hx⟩
    | step_n_fwd _ hy ih => obtain ⟨w⟩ := ih; exact ⟨.n_fwd w hy⟩
    | step_n_bwd _ hy ih => obtain ⟨w⟩ := ih; exact ⟨.n_bwd w hy⟩
    | step_e _ hy ih => obtain ⟨w⟩ := ih; exact ⟨.e_step w hy⟩

def WalkENIn.revOfInv {D : Type} {e n : Perm D} (he : ∀ z, e.f (e.f z) = z)
    {P : D → Prop} {x y : D} : WalkENIn e n P x y → WalkENIn e n P y x
  | .refl hx => .refl hx
  | .n_fwd (y := z) w hy =>
    let w_step : WalkENIn e n P (n.f z) z := by
      have h1 : WalkENIn e n P (n.f z) (n.inv (n.f z)) :=
        WalkENIn.n_bwd (.refl hy) (by rw [n.left_inv]; exact walkENIn_right w)
      rwa [n.left_inv] at h1
    w_step.trans (w.revOfInv he)
  | .n_bwd (y := z) w hy =>
    let w_step : WalkENIn e n P (n.inv z) z := by
      have h1 : WalkENIn e n P (n.inv z) (n.f (n.inv z)) :=
        WalkENIn.n_fwd (.refl hy) (by rw [n.right_inv]; exact walkENIn_right w)
      rwa [n.right_inv] at h1
    w_step.trans (w.revOfInv he)
  | .e_step (y := z) w hy =>
    let w_step : WalkENIn e n P (e.f z) z := by
      have h1 : WalkENIn e n P (e.f z) (e.f (e.f z)) :=
        WalkENIn.e_step (.refl hy) (by rw [he]; exact walkENIn_right w)
      rwa [he] at h1
    w_step.trans (w.revOfInv he)

theorem reachENIn_symm_of_involution {D : Type} {e n : Perm D} (he : ∀ z, e.f (e.f z) = z)
    {P : D → Prop} {x y : D} (h : ReachENIn e n P x y) : ReachENIn e n P y x := by
  obtain ⟨w⟩ := nonempty_walkENIn_iff_reachENIn.mpr h
  exact nonempty_walkENIn_iff_reachENIn.mp ⟨w.revOfInv he⟩

theorem reachENIn_mono {D : Type} {e n : Perm D} {P Q : D → Prop} (hPQ : ∀ z, P z → Q z)
    {x y : D} (h : ReachENIn e n P x y) : ReachENIn e n Q x y := by
  obtain ⟨w⟩ := nonempty_walkENIn_iff_reachENIn.mpr h
  exact nonempty_walkENIn_iff_reachENIn.mp ⟨w.mapPred hPQ⟩

theorem reachENIn_to_reachEN {D : Type} {e n : Perm D} {P : D → Prop} {x y : D}
    (h : ReachENIn e n P x y) : ReachEN e n x y := by
  induction h with
  | refl _ => exact reachEN_refl e n x
  | step_n_fwd _ _ ih => exact reachEN_trans e n ih ⟨.step (.n_fwd _) (.refl _)⟩
  | step_n_bwd _ _ ih => exact reachEN_trans e n ih ⟨.step (.n_bwd _) (.refl _)⟩
  | step_e _ _ ih => exact reachEN_trans e n ih ⟨.step (.e_fwd _) (.refl _)⟩

theorem sameOrbit_of_walkENIn_eLen_zero {D : Type} [DecidableEq D]
    (e n : Perm D) (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {P : D → Prop} {x y : D} (w : WalkENIn e n P x y) (hw0 : w.eLen = 0) :
    SameOrbit n x y := by
  induction w with
  | refl _ => exact sameOrbit_refl n x
  | n_fwd w _ ih => exact sameOrbit_trans n (ih hw0) (sameOrbit_step n rfl)
  | n_bwd w _ ih => exact sameOrbit_trans n (ih hw0) (sameOrbit_inv_step_of_complete n darts h_all _)
  | e_step _ _ => simp [WalkENIn.eLen] at hw0

/-- Split a `WalkENIn` walk starting at `x` with `¬ Q x` at its first hit of `Q`, if any,
assuming `Q` is `n`-invariant. -/
def WalkENIn.splitFirstHit {D : Type} {e n : Perm D} {P : D → Prop}
    (Q : D → Prop) [DecidablePred Q] (hQn : ∀ z, Q (n.f z) ↔ Q z)
    {x y : D} (hx_not : ¬ Q x) :
    ∀ (w : WalkENIn e n P x y),
      PSum
        ((w1 : WalkENIn e n (fun d => P d ∧ ¬ Q d) x y) ×' (w1.eLen = w.eLen))
        ((m : D) ×' (m' : D) ×'
          (_ : P m ∧ ¬ Q m ∧ P m' ∧ Q m' ∧ e.f m = m') ×'
          (w1 : WalkENIn e n (fun d => P d ∧ ¬ Q d) x m) ×'
          (w2 : WalkENIn e n P m' y) ×'
          (w1.eLen + 1 + w2.eLen = w.eLen))
  | .refl hx => .inl ⟨.refl ⟨hx, hx_not⟩, rfl⟩
  | .n_fwd (y := z) w hy =>
    match w.splitFirstHit Q hQn hx_not with
    | .inl ⟨w_avoid, hlen⟩ =>
      .inl ⟨.n_fwd w_avoid ⟨hy, fun h => (walkENIn_right w_avoid).2 ((hQn z).mp h)⟩,
        by simp [WalkENIn.eLen, hlen]⟩
    | .inr ⟨m, m', hinfo, w1, w2, hlen⟩ =>
      .inr ⟨m, m', hinfo, w1, .n_fwd w2 hy, by simp [WalkENIn.eLen, hlen]⟩
  | .n_bwd (y := z) w hy =>
    match w.splitFirstHit Q hQn hx_not with
    | .inl ⟨w_avoid, hlen⟩ =>
      .inl ⟨.n_bwd w_avoid ⟨hy, fun h => by
          have h1 := (hQn (n.inv z)).mpr h
          rw [n.right_inv z] at h1
          exact (walkENIn_right w_avoid).2 h1⟩,
        by simp [WalkENIn.eLen, hlen]⟩
    | .inr ⟨m, m', hinfo, w1, w2, hlen⟩ =>
      .inr ⟨m, m', hinfo, w1, .n_bwd w2 hy, by simp [WalkENIn.eLen, hlen]⟩
  | .e_step (y := z) w hy =>
    match w.splitFirstHit Q hQn hx_not with
    | .inl ⟨w_avoid, hlen⟩ =>
      if hQ : Q (e.f z) then
        .inr ⟨z, e.f z, ⟨(walkENIn_right w_avoid).1, (walkENIn_right w_avoid).2, hy, hQ, rfl⟩,
          w_avoid, .refl hy, by simp [WalkENIn.eLen, hlen]⟩
      else
        .inl ⟨.e_step w_avoid ⟨hy, hQ⟩, by simp [WalkENIn.eLen, hlen]⟩
    | .inr ⟨m, m', hinfo, w1, w2, hlen⟩ =>
      .inr ⟨m, m', hinfo, w1, .e_step w2 hy, by simp [WalkENIn.eLen]; omega⟩

theorem stepEN_to_dual {H : Hypermap} {x y : H.Dart}
    (h : StepEN H.edge H.node x y) : ReachEN H.dual.edge H.dual.node x y := by
  cases h with
  | e_fwd => exact ⟨.step (.e_fwd _) (.refl _)⟩
  | e_bwd => exact ⟨.step (.e_bwd _) (.refl _)⟩
  | n_fwd =>
    have h_eq : H.edge.f (H.face.inv x) = H.node.f x := by
      have h1 := H.edge_node_face_id (H.face.inv x)
      rw [H.face.right_inv] at h1
      rw [← h1, H.edge_involution]
    have hx1 : StepEN H.dual.edge H.dual.node x (H.dual.node.f x) := .n_fwd x
    have hx2 : StepEN H.dual.edge H.dual.node (H.dual.node.f x) (H.dual.edge.f (H.dual.node.f x)) := .e_fwd _
    have hfin : H.dual.edge.f (H.dual.node.f x) = H.node.f x := h_eq
    rw [hfin] at hx2
    exact ⟨.step hx1 (.step hx2 (.refl _))⟩
  | n_bwd =>
    have h1 := H.edge_node_face_id (H.face.inv (H.node.inv x))
    rw [H.face.right_inv, H.node.right_inv] at h1
    have h_eq : H.face.f (H.edge.f x) = H.node.inv x := by
      calc H.face.f (H.edge.f x)
          = H.face.f (H.face.inv (H.node.inv x)) := by rw [← h1]
        _ = H.node.inv x := H.face.right_inv _
    have hx1 : StepEN H.dual.edge H.dual.node x (H.dual.edge.f x) := .e_fwd x
    have hx2 : StepEN H.dual.edge H.dual.node (H.dual.edge.f x) (H.dual.node.inv (H.dual.edge.f x)) := .n_bwd _
    have hfin : H.dual.node.inv (H.dual.edge.f x) = H.node.inv x := h_eq
    rw [hfin] at hx2
    exact ⟨.step hx1 (.step hx2 (.refl _))⟩

theorem stepEN_dual_to_primal {H : Hypermap} {x y : H.Dart}
    (h : StepEN H.dual.edge H.dual.node x y) : ReachEN H.edge H.node x y := by
  cases h with
  | e_fwd => exact ⟨.step (.e_fwd _) (.refl _)⟩
  | e_bwd => exact ⟨.step (.e_bwd _) (.refl _)⟩
  | n_fwd =>
    have h1 := H.edge_node_face_id (H.face.inv x)
    rw [H.face.right_inv] at h1
    have h_eq : H.edge.f (H.node.f x) = H.dual.node.f x := h1
    have hx1 : StepEN H.edge H.node x (H.node.f x) := .n_fwd x
    have hx2 : StepEN H.edge H.node (H.node.f x) (H.edge.f (H.node.f x)) := .e_fwd _
    rw [h_eq] at hx2
    exact ⟨.step hx1 (.step hx2 (.refl _))⟩
  | n_bwd =>
    have h1 := H.edge_node_face_id x
    have h2 : H.node.f (H.face.f x) = H.edge.f x := by
      calc H.node.f (H.face.f x)
          = H.edge.f (H.edge.f (H.node.f (H.face.f x))) := (H.edge_involution _).symm
        _ = H.edge.f x := by rw [h1]
    have h_eq : H.node.inv (H.edge.f x) = H.dual.node.inv x := by
      calc H.node.inv (H.edge.f x)
          = H.node.inv (H.node.f (H.face.f x)) := by rw [h2]
        _ = H.face.f x := H.node.left_inv _
    have hx1 : StepEN H.edge H.node x (H.edge.f x) := .e_fwd x
    have hx2 : StepEN H.edge H.node (H.edge.f x) (H.node.inv (H.edge.f x)) := .n_bwd _
    rw [h_eq] at hx2
    exact ⟨.step hx1 (.step hx2 (.refl _))⟩

theorem reachEN_iff_dual (H : Hypermap) (x y : H.Dart) :
    ReachEN H.edge H.node x y ↔ ReachEN H.dual.edge H.dual.node x y := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | refl => exact reachEN_refl _ _ _
    | step hs _ ih => exact reachEN_trans _ _ (stepEN_to_dual hs) ih
  · rintro ⟨w⟩
    induction w with
    | refl => exact reachEN_refl _ _ _
    | step hs _ ih => exact reachEN_trans _ _ (stepEN_dual_to_primal hs) ih

theorem genusDeficit_dual_eq (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_all : ∀ d : H.Dart, d ∈ darts) {fuel : Nat} (h_len : darts.length ≤ fuel) :
    genusDeficit H.dual.hypermapToTriple fuel darts = genusDeficit H.hypermapToTriple fuel darts := by
  classical
  dsimp only [genusDeficit, hypermapToTriple, Hypermap.dual]
  have hcomp : countRelClasses (ReachEN H.edge H.face.symm) darts =
      countRelClasses (ReachEN H.edge H.node) darts :=
    countRelClasses_eq_of_iff (ReachEN H.edge H.face.symm) (ReachEN H.edge H.node)
      (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
      (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
      (fun x y => (reachEN_iff_dual H x y).symm) darts
  have hnode : countOrbits H.face.symm fuel darts = countOrbits H.face fuel darts :=
    countOrbits_eq_of_sameOrbit_iff H.face.symm H.face darts h_all h_len h_len
      (fun x y => (sameOrbit_symm_perm H.face).trans
        ⟨fun h => sameOrbit_symm_of_complete H.face darts h_all h,
         fun h => sameOrbit_symm_of_complete H.face darts h_all h⟩)
      darts
  have hface : countOrbits H.node.symm fuel darts = countOrbits H.node fuel darts :=
    countOrbits_eq_of_sameOrbit_iff H.node.symm H.node darts h_all h_len h_len
      (fun x y => (sameOrbit_symm_perm H.node).trans
        ⟨fun h => sameOrbit_symm_of_complete H.node darts h_all h,
         fun h => sameOrbit_symm_of_complete H.node darts h_all h⟩)
      darts
  rw [hcomp, hnode, hface]
  omega

theorem isPlanar_dual (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) :
    H.dual.isPlanar fuel darts = H.isPlanar fuel darts := by
  rw [Bool.eq_iff_iff]
  have hd := (eulerChar_le_two_mul_numComponents H.dual darts h_nodup h_all h_len).2
  have hp := (eulerChar_le_two_mul_numComponents H darts h_nodup h_all h_len).2
  rw [hd, hp, genusDeficit_dual_eq H darts h_all h_len]

end WalksAndDual

section SplitVertexAndCrossArc

theorem sameOrbit_iff_mem_getOrbit_of_complete {D : Type} [DecidableEq D]
    (p : Perm D) (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (a b : D) :
    SameOrbit p a b ↔ b ∈ getOrbit p fuel a := by
  have hcl : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_len
  rw [mem_getOrbit_iff_exists_iter p fuel a b hcl]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, hk.symm⟩

/-- 1-step vertex/face split on a `PermTriple`: splits `n` at `(d_a, d_b)` and `f` at `(d_a, d_b)` via
`swapCompRight`, preserving `e` and the hypermap triple law `e ∘ n ∘ f = id`. -/
def splitVertexTriple {D : Type} [DecidableEq D] (T : PermTriple D) (d_a d_b : D) :
    PermTriple D where
  e := T.e
  n := swapCompRight T.n d_a d_b
  f := (swapCompRight T.f.symm d_a d_b).symm
  enf_id x := by
    change T.e.f (T.n.f (swapFun d_a d_b (swapFun d_a d_b (T.f.f x)))) = x
    rw [swapFun_involutive d_a d_b (T.f.f x)]
    exact T.enf_id x

/-- 1-step vertex/face split on a `Hypermap`. -/
abbrev splitVertexAtPair (H : Hypermap) [DecidableEq H.Dart] (d_a d_b : H.Dart) : Hypermap where
  Dart := H.Dart
  edge := H.edge
  node := swapCompRight H.node d_a d_b
  face := (swapCompRight H.face.symm d_a d_b).symm
  edge_involution := H.edge_involution
  edge_node_face_id x := by
    change H.edge.f (H.node.f (swapFun d_a d_b (swapFun d_a d_b (H.face.f x)))) = x
    rw [swapFun_involutive d_a d_b (H.face.f x)]
    exact H.edge_node_face_id x

theorem splitVertexAtPair_hypermapToTriple (H : Hypermap) [DecidableEq H.Dart] (d_a d_b : H.Dart) :
    (H.splitVertexAtPair d_a d_b).hypermapToTriple =
      splitVertexTriple H.hypermapToTriple d_a d_b := rfl

theorem sameOrbit_imp_reachEN {D : Type} (T : PermTriple D) {x y : D}
    (h : SameOrbit T.n x y) : ReachEN T.e T.n x y := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => exact reachEN_refl _ _ _
  | succ k ih =>
    rw [perm_iter_succ_left]
    exact reachEN_trans _ _ ih ⟨.step (.n_fwd _) (.refl _)⟩

theorem sameOrbit_f_imp_reachEN {D : Type} (T : PermTriple D) {x y : D}
    (h : SameOrbit T.f x y) : ReachEN T.e T.n x y := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => exact reachEN_refl _ _ _
  | succ k ih =>
    rw [perm_iter_succ_left]
    refine reachEN_trans _ _ ih ?_
    have hstep1 : StepEN T.e T.n (Perm.iter T.f k x) (T.e.inv (Perm.iter T.f k x)) := .e_bwd _
    have hstep2 : StepEN T.e T.n (T.e.inv (Perm.iter T.f k x)) (T.n.inv (T.e.inv (Perm.iter T.f k x))) := .n_bwd _
    rw [← PermTriple.f_eq_n_inv_e_inv] at hstep2
    exact ⟨.step hstep1 (.step hstep2 (.refl _))⟩

theorem reachEN_splitVertexTriple_imp {D : Type} [DecidableEq D]
    (T : PermTriple D) (d_a d_b : D) (hn : SameOrbit T.n d_a d_b)
    {x y : D} (h : ReachEN (splitVertexTriple T d_a d_b).e (splitVertexTriple T d_a d_b).n x y) :
    ReachEN T.e T.n x y := by
  have hswap : ∀ z : D, ReachEN T.e T.n z (swapFun d_a d_b z) := by
    intro z
    by_cases ha : z = d_a
    · subst ha; rw [swapFun_left]; exact sameOrbit_imp_reachEN T hn
    · by_cases hb : z = d_b
      · subst hb; rw [swapFun_right]
        exact reachEN_symm _ _ (sameOrbit_imp_reachEN T hn)
      · rw [swapFun_of_ne ha hb]; exact reachEN_refl _ _ _
  rcases h with ⟨w⟩
  induction w with
  | refl => exact reachEN_refl _ _ _
  | @step u v _ hs _ ih =>
    have huv : ReachEN T.e T.n u v := by
      cases hs with
      | e_fwd => exact ⟨.step (.e_fwd u) (.refl _)⟩
      | e_bwd => exact ⟨.step (.e_bwd u) (.refl _)⟩
      | n_fwd =>
        change ReachEN T.e T.n u (T.n.f (swapFun d_a d_b u))
        exact reachEN_trans _ _ (hswap u) ⟨.step (.n_fwd _) (.refl _)⟩
      | n_bwd =>
        change ReachEN T.e T.n u (swapFun d_a d_b (T.n.inv u))
        exact reachEN_trans _ _ ⟨.step (.n_bwd u) (.refl _)⟩ (hswap (T.n.inv u))
    exact reachEN_trans _ _ huv ih

def MergeEN {D : Type} (e n : Perm D) (d_a d_b x y : D) : Prop :=
  ReachEN e n x y ∨ ((ReachEN e n x d_a ∨ ReachEN e n x d_b) ∧ (ReachEN e n y d_a ∨ ReachEN e n y d_b))

private theorem mergeEN_refl {D : Type} (e n : Perm D) (d_a d_b x : D) :
    MergeEN e n d_a d_b x x := .inl (reachEN_refl e n x)

private theorem mergeEN_symm {D : Type} (e n : Perm D) (d_a d_b : D) {x y : D}
    (h : MergeEN e n d_a d_b x y) : MergeEN e n d_a d_b y x := by
  rcases h with h | ⟨hx, hy⟩
  · exact .inl (reachEN_symm e n h)
  · exact .inr ⟨hy, hx⟩

private theorem mergeEN_trans {D : Type} (e n : Perm D) (d_a d_b : D) {x y z : D}
    (h1 : MergeEN e n d_a d_b x y) (h2 : MergeEN e n d_a d_b y z) :
    MergeEN e n d_a d_b x z := by
  rcases h1 with hxy | ⟨hx, hy⟩
  · rcases h2 with hyz | ⟨hy', hz⟩
    · exact .inl (reachEN_trans e n hxy hyz)
    · refine .inr ⟨?_, hz⟩
      rcases hy' with hya | hyb
      · exact .inl (reachEN_trans e n hxy hya)
      · exact .inr (reachEN_trans e n hxy hyb)
  · rcases h2 with hyz | ⟨_, hz⟩
    · refine .inr ⟨hx, ?_⟩
      rcases hy with hya | hyb
      · exact .inl (reachEN_trans e n (reachEN_symm e n hyz) hya)
      · exact .inr (reachEN_trans e n (reachEN_symm e n hyz) hyb)
    · exact .inr ⟨hx, hz⟩

theorem reachEN_iff_mergeEN_splitVertexTriple {D : Type} [DecidableEq D]
    (T : PermTriple D) (d_a d_b : D) (hn : SameOrbit T.n d_a d_b)
    (x y : D) :
    ReachEN T.e T.n x y ↔
      MergeEN (splitVertexTriple T d_a d_b).e (splitVertexTriple T d_a d_b).n d_a d_b x y := by
  let T' := splitVertexTriple T d_a d_b
  have hstep_n_fwd : ∀ u : D, MergeEN T'.e T'.n d_a d_b u (T.n.f u) := by
    intro u
    by_cases ha : u = d_a
    · subst u
      have hb : T'.n.f d_b = T.n.f d_a := by
        change T.n.f (swapFun d_a d_b d_b) = T.n.f d_a; rw [swapFun_right]
      refine .inr ⟨.inl (reachEN_refl _ _ _), .inr ?_⟩
      rw [← hb]
      exact reachEN_symm _ _ ⟨.step (.n_fwd d_b) (.refl _)⟩
    · by_cases hb : u = d_b
      · subst u
        have ha' : T'.n.f d_a = T.n.f d_b := by
          change T.n.f (swapFun d_a d_b d_a) = T.n.f d_b; rw [swapFun_left]
        refine .inr ⟨.inr (reachEN_refl _ _ _), .inl ?_⟩
        rw [← ha']
        exact reachEN_symm _ _ ⟨.step (.n_fwd d_a) (.refl _)⟩
      · have heq : T'.n.f u = T.n.f u := by
          change T.n.f (swapFun d_a d_b u) = T.n.f u; rw [swapFun_of_ne ha hb]
        refine .inl ?_
        rw [← heq]
        exact ⟨.step (.n_fwd u) (.refl _)⟩
  constructor
  · rintro ⟨w⟩
    induction w with
    | refl => exact mergeEN_refl _ _ d_a d_b _
    | @step u v _ hs _ ih =>
      have huv : MergeEN T'.e T'.n d_a d_b u v := by
        cases hs with
        | e_fwd => exact .inl ⟨.step (.e_fwd u) (.refl _)⟩
        | e_bwd => exact .inl ⟨.step (.e_bwd u) (.refl _)⟩
        | n_fwd => exact hstep_n_fwd u
        | n_bwd =>
          have hvu := hstep_n_fwd (T.n.inv u)
          rw [T.n.right_inv u] at hvu
          exact mergeEN_symm _ _ d_a d_b hvu
      exact mergeEN_trans _ _ d_a d_b huv ih
  · intro hm
    rcases hm with h' | ⟨hx, hy⟩
    · exact reachEN_splitVertexTriple_imp T d_a d_b hn h'
    · have hadb : ReachEN T.e T.n d_a d_b := sameOrbit_imp_reachEN T hn
      have hx' : ReachEN T.e T.n x d_a := by
        rcases hx with hxa | hxb
        · exact reachEN_splitVertexTriple_imp T d_a d_b hn hxa
        · exact reachEN_trans _ _ (reachEN_splitVertexTriple_imp T d_a d_b hn hxb)
            (reachEN_symm _ _ hadb)
      have hy' : ReachEN T.e T.n y d_a := by
        rcases hy with hya | hyb
        · exact reachEN_splitVertexTriple_imp T d_a d_b hn hya
        · exact reachEN_trans _ _ (reachEN_splitVertexTriple_imp T d_a d_b hn hyb)
            (reachEN_symm _ _ hadb)
      exact reachEN_trans _ _ hx' (reachEN_symm _ _ hy')

theorem countRelClasses_splitVertexTriple_le {D : Type} [DecidableEq D]
    (T : PermTriple D) (d_a d_b : D) (hn : SameOrbit T.n d_a d_b)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts) :
    countRelClasses (ReachEN (splitVertexTriple T d_a d_b).e (splitVertexTriple T d_a d_b).n) darts ≤
      countRelClasses (ReachEN T.e T.n) darts + 1 := by
  classical
  let T' := splitVertexTriple T d_a d_b
  let S : D → Bool := fun x => decide (ReachEN T.e T.n d_a x)
  have hS : ∀ {x y : D}, ReachEN T.e T.n x y → S x = S y := by
    intro x y hxy
    simp only [S]
    exact Bool.eq_iff_iff.mpr (by
      simp only [decide_eq_true_eq]
      exact ⟨fun h => reachEN_trans _ _ h hxy, fun h => reachEN_trans _ _ h (reachEN_symm _ _ hxy)⟩)
  have hS' : ∀ {x y : D}, ReachEN T'.e T'.n x y → S x = S y := fun hxy =>
    hS (reachEN_splitVertexTriple_imp T d_a d_b hn hxy)
  have hp := countRelClasses_partition_of_closed (ReachEN T.e T.n)
    (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS darts
  have hp' := countRelClasses_partition_of_closed (ReachEN T'.e T'.n)
    (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS' darts
  have hcov : countRelClasses (ReachEN T'.e T'.n) (darts.filter S) ≤ 2 := by
    apply countRelClasses_le_of_cover (ReachEN T'.e T'.n)
      (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
      [d_a, d_b]
    intro x hx
    have hax : ReachEN T.e T.n d_a x := of_decide_eq_true (List.mem_filter.mp hx).2
    have hm := (reachEN_iff_mergeEN_splitVertexTriple T d_a d_b hn d_a x).mp hax
    rcases hm with h' | ⟨_, hx'⟩
    · exact ⟨d_a, List.mem_cons_self, h'⟩
    · rcases hx' with hxa | hxb
      · exact ⟨d_a, List.mem_cons_self, reachEN_symm _ _ hxa⟩
      · exact ⟨d_b, List.mem_cons_of_mem _ List.mem_cons_self, reachEN_symm _ _ hxb⟩
  have hge1 : 1 ≤ countRelClasses (ReachEN T.e T.n) (darts.filter S) := by
    have ha_mem : d_a ∈ darts.filter S := List.mem_filter.mpr ⟨h_all d_a, decide_eq_true (reachEN_refl _ _ _)⟩
    cases hfl : darts.filter S with
    | nil => rw [hfl] at ha_mem; exact absurd ha_mem List.not_mem_nil
    | cons u us => exact countRelClasses_pos_cons _ u us
  have hrest : countRelClasses (ReachEN T'.e T'.n) (darts.filter (fun x => !S x)) =
      countRelClasses (ReachEN T.e T.n) (darts.filter (fun x => !S x)) := by
    apply countRelClasses_eq_of_rel_iff_on_mem _ _ (darts.filter (fun x => !S x)).length _ (Nat.le_refl _)
    intro x hx y hy
    constructor
    · exact reachEN_splitVertexTriple_imp T d_a d_b hn
    · intro hxy
      have hm := (reachEN_iff_mergeEN_splitVertexTriple T d_a d_b hn x y).mp hxy
      rcases hm with h' | ⟨hx', _⟩
      · exact h'
      · have hxa_false : ¬ ReachEN T.e T.n d_a x := by
          intro hcon
          have hSx : S x = true := decide_eq_true hcon
          have hxS := (List.mem_filter.mp hx).2
          simp [hSx] at hxS
        have hadb : ReachEN T.e T.n d_a d_b := sameOrbit_imp_reachEN T hn
        exfalso; apply hxa_false
        rcases hx' with hxa | hxb
        · exact reachEN_symm _ _ (reachEN_splitVertexTriple_imp T d_a d_b hn hxa)
        · exact reachEN_trans _ _ hadb
            (reachEN_symm _ _ (reachEN_splitVertexTriple_imp T d_a d_b hn hxb))
  dsimp only [T'] at hp' hcov hrest
  omega

theorem countRelClasses_splitVertexTriple_eq_of_reachEN {D : Type} [DecidableEq D]
    (T : PermTriple D) (d_a d_b : D) (hn : SameOrbit T.n d_a d_b)
    (darts : List D)
    (h_conn : ReachEN (splitVertexTriple T d_a d_b).e (splitVertexTriple T d_a d_b).n d_a d_b) :
    countRelClasses (ReachEN (splitVertexTriple T d_a d_b).e (splitVertexTriple T d_a d_b).n) darts =
      countRelClasses (ReachEN T.e T.n) darts := by
  classical
  let T' := splitVertexTriple T d_a d_b
  apply countRelClasses_eq_of_iff (ReachEN T'.e T'.n) (ReachEN T.e T.n)
    (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
    (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
  intro x y
  constructor
  · exact reachEN_splitVertexTriple_imp T d_a d_b hn
  · intro hxy
    have hm := (reachEN_iff_mergeEN_splitVertexTriple T d_a d_b hn x y).mp hxy
    rcases hm with h' | ⟨hx, hy⟩
    · exact h'
    · have hx' : ReachEN T'.e T'.n x d_a := by
        rcases hx with hxa | hxb
        · exact hxa
        · exact reachEN_trans _ _ hxb (reachEN_symm _ _ h_conn)
      have hy' : ReachEN T'.e T'.n y d_a := by
        rcases hy with hya | hyb
        · exact hya
        · exact reachEN_trans _ _ hyb (reachEN_symm _ _ h_conn)
      exact reachEN_trans _ _ hx' (reachEN_symm _ _ hy')

theorem countOrbits_splitVertexTriple_n {D : Type} [DecidableEq D]
    (T : PermTriple D) (d_a d_b : D) (hne : d_a ≠ d_b) (hn : SameOrbit T.n d_a d_b)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts) {fuel : Nat} (h_len : darts.length ≤ fuel) :
    countOrbits (splitVertexTriple T d_a d_b).n fuel darts = countOrbits T.n fuel darts + 1 := by
  have hmem : d_b ∈ getOrbit T.n fuel d_a :=
    (sameOrbit_iff_mem_getOrbit_of_complete T.n darts h_all h_len d_a d_b).mp hn
  exact countOrbits_swapCompRight_same T.n darts h_all h_len hne hmem

theorem countOrbits_splitVertexTriple_f {D : Type} [DecidableEq D]
    (T : PermTriple D) (d_a d_b : D) (hne : d_a ≠ d_b) (hf : SameOrbit T.f d_a d_b)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts) {fuel : Nat} (h_len : darts.length ≤ fuel) :
    countOrbits (splitVertexTriple T d_a d_b).f fuel darts = countOrbits T.f fuel darts + 1 := by
  have hfs : SameOrbit T.f.symm d_a d_b :=
    (sameOrbit_symm_perm T.f).mpr (sameOrbit_symm_of_complete T.f darts h_all hf)
  have hmem : d_b ∈ getOrbit T.f.symm fuel d_a :=
    (sameOrbit_iff_mem_getOrbit_of_complete T.f.symm darts h_all h_len d_a d_b).mp hfs
  have h1 := countOrbits_swapCompRight_same T.f.symm darts h_all h_len hne hmem
  have h2 : countOrbits (splitVertexTriple T d_a d_b).f fuel darts =
      countOrbits (swapCompRight T.f.symm d_a d_b) fuel darts :=
    countOrbits_eq_of_sameOrbit_iff _ _ darts h_all h_len h_len
      (fun x y => (sameOrbit_symm_perm _).trans
        ⟨fun h => sameOrbit_symm_of_complete _ darts h_all h,
         fun h => sameOrbit_symm_of_complete _ darts h_all h⟩)
      darts
  have h3 : countOrbits T.f.symm fuel darts = countOrbits T.f fuel darts :=
    countOrbits_eq_of_sameOrbit_iff T.f.symm T.f darts h_all h_len h_len
      (fun x y => (sameOrbit_symm_perm T.f).trans
        ⟨fun h => sameOrbit_symm_of_complete T.f darts h_all h,
         fun h => sameOrbit_symm_of_complete T.f darts h_all h⟩)
      darts
  omega

theorem genusDeficit_splitVertexTriple_eq {D : Type} [DecidableEq D]
    (T : PermTriple D) (d_a d_b : D) (hne : d_a ≠ d_b)
    (hn : SameOrbit T.n d_a d_b) (hf : SameOrbit T.f d_a d_b)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts) {fuel : Nat} (h_len : darts.length ≤ fuel) :
    genusDeficit (splitVertexTriple T d_a d_b) fuel darts =
      genusDeficit T fuel darts +
        2 * (↑(countRelClasses (ReachEN (splitVertexTriple T d_a d_b).e (splitVertexTriple T d_a d_b).n) darts) -
             ↑(countRelClasses (ReachEN T.e T.n) darts) - 1) := by
  have hV := countOrbits_splitVertexTriple_n T d_a d_b hne hn darts h_all h_len
  have hF := countOrbits_splitVertexTriple_f T d_a d_b hne hf darts h_all h_len
  have hE : countOrbits (splitVertexTriple T d_a d_b).e fuel darts = countOrbits T.e fuel darts := rfl
  dsimp only [genusDeficit]
  rw [hV, hE, hF]
  omega

theorem splitVertexTriple_not_reachEN_of_genusDeficit_zero {D : Type} [DecidableEq D]
    (T : PermTriple D) (d_a d_b : D) (hne : d_a ≠ d_b)
    (hn : SameOrbit T.n d_a d_b) (hf : SameOrbit T.f d_a d_b)
    (darts : List D) (h_nodup : darts.Nodup) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (hg0 : genusDeficit T fuel darts = 0)
    (h_conn : ReachEN (splitVertexTriple T d_a d_b).e (splitVertexTriple T d_a d_b).n d_a d_b) :
    False := by
  have hnonneg := genusDeficit_nonneg (splitVertexTriple T d_a d_b) darts h_nodup h_all h_len
  have heq := genusDeficit_splitVertexTriple_eq T d_a d_b hne hn hf darts h_all h_len
  have hc := countRelClasses_splitVertexTriple_eq_of_reachEN T d_a d_b hn darts h_conn
  omega

theorem splitVertexAtPair_disconnected_isPlanar (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (h_planar : H.isPlanar fuel darts = true)
    (d_a d_b : H.Dart) (hne : d_a ≠ d_b) (hn : SameOrbit H.node d_a d_b) (hf : SameOrbit H.face d_a d_b) :
    (H.splitVertexAtPair d_a d_b).isPlanar fuel darts = true ∧
      (H.splitVertexAtPair d_a d_b).numComponents fuel darts = H.numComponents fuel darts + 1 ∧
      ¬ ReachEN (H.splitVertexAtPair d_a d_b).edge (H.splitVertexAtPair d_a d_b).node d_a d_b := by
  have hp := (eulerChar_le_two_mul_numComponents H darts h_nodup h_all h_len).2.mp h_planar
  have h_efree : ∀ d, (H.splitVertexAtPair d_a d_b).edge.f d ≠ d := hp.2
  have hnonneg := genusDeficit_nonneg (H.splitVertexAtPair d_a d_b).hypermapToTriple darts h_nodup h_all h_len
  have heq := genusDeficit_splitVertexTriple_eq H.hypermapToTriple d_a d_b hne hn hf darts h_all h_len
  have hp1 : genusDeficit H.hypermapToTriple fuel darts = 0 := hp.1
  rw [splitVertexAtPair_hypermapToTriple, heq, hp1] at hnonneg
  have hle := countRelClasses_splitVertexTriple_le H.hypermapToTriple d_a d_b hn darts h_all
  have h_c_eq : countRelClasses (ReachEN (splitVertexTriple H.hypermapToTriple d_a d_b).e
      (splitVertexTriple H.hypermapToTriple d_a d_b).n) darts =
      countRelClasses (ReachEN H.hypermapToTriple.e H.hypermapToTriple.n) darts + 1 := by
    omega
  have hg'_zero : genusDeficit (H.splitVertexAtPair d_a d_b).hypermapToTriple fuel darts = 0 := by
    rw [splitVertexAtPair_hypermapToTriple, heq, h_c_eq, hp1]
    omega
  have hpl' : (H.splitVertexAtPair d_a d_b).isPlanar fuel darts = true :=
    (eulerChar_le_two_mul_numComponents (H.splitVertexAtPair d_a d_b) darts h_nodup h_all h_len).2.mpr
      ⟨hg'_zero, h_efree⟩
  have hdisc : ¬ ReachEN (H.splitVertexAtPair d_a d_b).edge (H.splitVertexAtPair d_a d_b).node d_a d_b := by
    intro hconn
    exact splitVertexTriple_not_reachEN_of_genusDeficit_zero H.hypermapToTriple d_a d_b hne hn hf
      darts h_nodup h_all h_len hp.1 hconn
  have hc_h : H.numComponents fuel darts = countRelClasses (ReachEN H.hypermapToTriple.e H.hypermapToTriple.n) darts :=
    (countRelClasses_reachEN_eq_countComponents H darts h_all h_len darts).symm
  have hc_h' : (H.splitVertexAtPair d_a d_b).numComponents fuel darts =
      countRelClasses (ReachEN (splitVertexTriple H.hypermapToTriple d_a d_b).e
        (splitVertexTriple H.hypermapToTriple d_a d_b).n) darts :=
    (countRelClasses_reachEN_eq_countComponents (H.splitVertexAtPair d_a d_b) darts h_all h_len darts).symm
  refine ⟨hpl', ?_, hdisc⟩
  omega

/-- Strict cyclic order of 4 darts `(d0, d1, d2, d3)` along a permutation orbit of minimal period `L`. -/
structure CyclicOrder4 {D : Type} (p : Perm D) (L : Nat) (d0 d1 d2 d3 : D) : Type where
  inj_lt : ∀ i j, i < L → j < L → Perm.iter p i d0 = Perm.iter p j d0 → i = j
  period : Perm.iter p L d0 = d0
  k1 : Nat
  k2 : Nat
  k3 : Nat
  k4 : Nat
  hk1 : 1 ≤ k1
  hk2 : 1 ≤ k2
  hk3 : 1 ≤ k3
  hk4 : 1 ≤ k4
  hsum : k1 + k2 + k3 + k4 = L
  hd1 : Perm.iter p k1 d0 = d1
  hd2 : Perm.iter p (k1 + k2) d0 = d2
  hd3 : Perm.iter p (k1 + k2 + k3) d0 = d3

def cyclicOrder4_of_complete {D : Type} [DecidableEq D]
    (p : Perm D) (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    (d0 d1 d2 d3 : D)
    {i1 i2 i3 : Nat} (hi01 : 1 ≤ i1) (hi12 : i1 < i2) (hi23 : i2 < i3)
    (hi3L : i3 < (getOrbit p darts.length d0).length)
    (hd1 : Perm.iter p i1 d0 = d1)
    (hd2 : Perm.iter p i2 d0 = d2)
    (hd3 : Perm.iter p i3 d0 = d3) :
    CyclicOrder4 p (getOrbit p darts.length d0).length d0 d1 d2 d3 where
  inj_lt := fun _ _ hi hj h => perm_iter_inj_of_lt_getOrbit_length p hi hj h
  period := perm_iter_length_getOrbit_eq_self_of_complete p darts h_all (Nat.le_refl _) d0
  k1 := i1
  k2 := i2 - i1
  k3 := i3 - i2
  k4 := (getOrbit p darts.length d0).length - i3
  hk1 := hi01
  hk2 := by omega
  hk3 := by omega
  hk4 := by omega
  hsum := by omega
  hd1 := hd1
  hd2 := by rw [show i1 + (i2 - i1) = i2 by omega]; exact hd2
  hd3 := by rw [show i1 + (i2 - i1) + (i3 - i2) = i3 by omega]; exact hd3

def cyclicOrder4_rot {D : Type} (p : Perm D) {L : Nat} {d0 d1 d2 d3 : D}
    (h : CyclicOrder4 p L d0 d1 d2 d3) :
    CyclicOrder4 p L d1 d2 d3 d0 where
  inj_lt := by
    intro i j hi hj heq
    rw [← h.hd1, ← perm_iter_add, ← perm_iter_add] at heq
    have hkL : h.k1 < L := by have := h.hk2; have := h.hk3; have := h.hk4; have := h.hsum; omega
    have hshift : ∀ m, m < L → ∃ m', m' < L ∧ Perm.iter p (m + h.k1) d0 = Perm.iter p m' d0 ∧
        (m + h.k1 < L → m' = m + h.k1) ∧ (L ≤ m + h.k1 → m' = m + h.k1 - L) := by
      intro m hm
      by_cases hm_lt : m + h.k1 < L
      · exact ⟨m + h.k1, hm_lt, rfl, fun _ => rfl, fun hle => by omega⟩
      · refine ⟨m + h.k1 - L, by omega, ?_, fun hlt => by omega, fun _ => rfl⟩
        have h1 : Perm.iter p (m + h.k1) d0 = Perm.iter p (m + h.k1 - L + L) d0 :=
          congrArg (fun k => Perm.iter p k d0) (by omega)
        calc Perm.iter p (m + h.k1) d0
            = Perm.iter p ((m + h.k1 - L) + L) d0 := h1
          _ = Perm.iter p (m + h.k1 - L) (Perm.iter p L d0) := perm_iter_add p _ _ d0
          _ = Perm.iter p (m + h.k1 - L) d0 := by rw [h.period]
    obtain ⟨i', hi'L, hi'eq, hi'1, hi'2⟩ := hshift i hi
    obtain ⟨j', hj'L, hj'eq, hj'1, hj'2⟩ := hshift j hj
    have hij' : i' = j' := h.inj_lt i' j' hi'L hj'L (by rw [← hi'eq, ← hj'eq, heq])
    by_cases hi_lt : i + h.k1 < L <;> by_cases hj_lt : j + h.k1 < L
    · have := hi'1 hi_lt; have := hj'1 hj_lt; omega
    · have := hi'1 hi_lt; have := hj'2 (by omega); omega
    · have := hi'2 (by omega); have := hj'1 hj_lt; omega
    · have := hi'2 (by omega); have := hj'2 (by omega); omega
  period := by
    calc Perm.iter p L d1
        = Perm.iter p L (Perm.iter p h.k1 d0) := by rw [h.hd1]
      _ = Perm.iter p (L + h.k1) d0 := (perm_iter_add p L h.k1 d0).symm
      _ = Perm.iter p (h.k1 + L) d0 := by rw [Nat.add_comm]
      _ = Perm.iter p h.k1 (Perm.iter p L d0) := perm_iter_add p h.k1 L d0
      _ = d1 := by rw [h.period, h.hd1]
  k1 := h.k2
  k2 := h.k3
  k3 := h.k4
  k4 := h.k1
  hk1 := h.hk2
  hk2 := h.hk3
  hk3 := h.hk4
  hk4 := h.hk1
  hsum := by have := h.hsum; omega
  hd1 := by
    calc Perm.iter p h.k2 d1
        = Perm.iter p h.k2 (Perm.iter p h.k1 d0) := by rw [h.hd1]
      _ = Perm.iter p (h.k1 + h.k2) d0 := by rw [← perm_iter_add, Nat.add_comm]
      _ = d2 := h.hd2
  hd2 := by
    calc Perm.iter p (h.k2 + h.k3) d1
        = Perm.iter p (h.k2 + h.k3) (Perm.iter p h.k1 d0) := by rw [h.hd1]
      _ = Perm.iter p (h.k1 + h.k2 + h.k3) d0 := by rw [← perm_iter_add, Nat.add_comm (h.k2 + h.k3), Nat.add_assoc]
      _ = d3 := h.hd3
  hd3 := by
    have hs : h.k2 + h.k3 + h.k4 + h.k1 = L := by have := h.hsum; omega
    calc Perm.iter p (h.k2 + h.k3 + h.k4) d1
        = Perm.iter p (h.k2 + h.k3 + h.k4) (Perm.iter p h.k1 d0) := by rw [h.hd1]
      _ = Perm.iter p (h.k2 + h.k3 + h.k4 + h.k1) d0 := (perm_iter_add p _ _ d0).symm
      _ = d0 := by rw [hs, h.period]

theorem cyclicOrder4_distinct {D : Type} {p : Perm D} {L : Nat} {d0 d1 d2 d3 : D}
    (h : CyclicOrder4 p L d0 d1 d2 d3) :
    d0 ≠ d1 ∧ d0 ≠ d2 ∧ d0 ≠ d3 ∧ d1 ≠ d2 ∧ d1 ≠ d3 ∧ d2 ≠ d3 := by
  have hk := h.hsum; have h1 := h.hk1; have h2 := h.hk2; have h3 := h.hk3; have h4 := h.hk4
  have hl0 : 0 < L := by omega
  have hl1 : h.k1 < L := by omega
  have hl2 : h.k1 + h.k2 < L := by omega
  have hl3 : h.k1 + h.k2 + h.k3 < L := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro heq
    have := h.inj_lt 0 h.k1 hl0 hl1 (by rw [h.hd1, heq]; rfl)
    omega
  · intro heq
    have := h.inj_lt 0 (h.k1 + h.k2) hl0 hl2 (by rw [h.hd2, heq]; rfl)
    omega
  · intro heq
    have := h.inj_lt 0 (h.k1 + h.k2 + h.k3) hl0 hl3 (by rw [h.hd3, heq]; rfl)
    omega
  · intro heq
    have := h.inj_lt h.k1 (h.k1 + h.k2) hl1 hl2 (by rw [h.hd1, h.hd2, heq])
    omega
  · intro heq
    have := h.inj_lt h.k1 (h.k1 + h.k2 + h.k3) hl1 hl3 (by rw [h.hd1, h.hd3, heq])
    omega
  · intro heq
    have := h.inj_lt (h.k1 + h.k2) (h.k1 + h.k2 + h.k3) hl2 hl3 (by rw [h.hd2, h.hd3, heq])
    omega

theorem cyclicOrder4_sameOrbit {D : Type} {p : Perm D} {L : Nat} {d0 d1 d2 d3 : D}
    (h : CyclicOrder4 p L d0 d1 d2 d3) :
    SameOrbit p d0 d1 ∧ SameOrbit p d0 d2 ∧ SameOrbit p d0 d3 :=
  ⟨⟨h.k1, h.hd1⟩, ⟨h.k1 + h.k2, h.hd2⟩, ⟨h.k1 + h.k2 + h.k3, h.hd3⟩⟩

theorem sameOrbit_splitVertexTriple_f_of_cyclicOrder4 {D : Type} [DecidableEq D]
    (T : PermTriple D) {L : Nat} {d0 d1 d2 d3 : D}
    (hc : CyclicOrder4 T.f L d0 d1 d2 d3) :
    SameOrbit (splitVertexTriple T d0 d2).f d0 d1 ∧
      SameOrbit (splitVertexTriple T d0 d2).f d2 d3 := by
  let T' := splitVertexTriple T d0 d2
  have hk12 : ∀ i, i < hc.k1 + hc.k2 → Perm.iter T'.f i d0 = Perm.iter T.f i d0 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [perm_iter_succ_left, ih (by omega), perm_iter_succ_left]
      change swapFun d0 d2 (T.f.f (Perm.iter T.f i d0)) = T.f.f (Perm.iter T.f i d0)
      rw [← perm_iter_succ_left]
      have hne0 : Perm.iter T.f (i + 1) d0 ≠ d0 := by
        intro heq
        have := hc.inj_lt (i + 1) 0 (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
          (by have := hc.hk1; have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega) heq
        omega
      have hne2 : Perm.iter T.f (i + 1) d0 ≠ d2 := by
        intro heq
        rw [← hc.hd2] at heq
        have := hc.inj_lt (i + 1) (hc.k1 + hc.k2)
          (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
          (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega) heq
        omega
      exact swapFun_of_ne hne0 hne2
  have hk34 : ∀ j, j < hc.k3 + hc.k4 → Perm.iter T'.f j d2 = Perm.iter T.f (hc.k1 + hc.k2 + j) d0 := by
    intro j
    induction j with
    | zero => intro _; exact hc.hd2.symm
    | succ j ih =>
      intro hj
      rw [perm_iter_succ_left, ih (by omega)]
      change swapFun d0 d2 (T.f.f (Perm.iter T.f (hc.k1 + hc.k2 + j) d0)) =
        Perm.iter T.f (hc.k1 + hc.k2 + (j + 1)) d0
      rw [← perm_iter_succ_left]
      have heq_idx : hc.k1 + hc.k2 + j + 1 = hc.k1 + hc.k2 + (j + 1) := by omega
      rw [heq_idx]
      have hltL : hc.k1 + hc.k2 + (j + 1) < L := by have := hc.hsum; omega
      have hne0 : Perm.iter T.f (hc.k1 + hc.k2 + (j + 1)) d0 ≠ d0 := by
        intro heq
        have := hc.inj_lt _ 0 hltL (by omega) heq
        have := hc.hk1; have := hc.hk2; omega
      have hne2 : Perm.iter T.f (hc.k1 + hc.k2 + (j + 1)) d0 ≠ d2 := by
        intro heq
        have := hc.inj_lt _ (hc.k1 + hc.k2) hltL
          (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega) (heq.trans hc.hd2.symm)
        omega
      exact swapFun_of_ne hne0 hne2
  refine ⟨⟨hc.k1, ?_⟩, ⟨hc.k3, ?_⟩⟩
  · rw [hk12 hc.k1 (by have := hc.hk2; omega), hc.hd1]
  · rw [hk34 hc.k3 (by have := hc.hk4; omega), hc.hd3]

theorem reachEN_splitVertexTriple_of_avoid {D : Type} [DecidableEq D]
    (T : PermTriple D) (d0 d2 : D) (P : D → Prop)
    (havoid : ∀ z, P z → z ≠ d0 ∧ z ≠ d2)
    {x y : D} (h : ReachENIn T.e T.n P x y) :
    ReachEN (splitVertexTriple T d0 d2).e (splitVertexTriple T d0 d2).n x y := by
  let T' := splitVertexTriple T d0 d2
  obtain ⟨w⟩ := nonempty_walkENIn_iff_reachENIn.mpr h
  clear h
  induction w with
  | refl _ => exact reachEN_refl _ _ _
  | @n_fwd z w hz ih =>
    have hzw := havoid z (walkENIn_right w)
    have hstep : T'.n.f z = T.n.f z := by
      change T.n.f (swapFun d0 d2 z) = T.n.f z
      rw [swapFun_of_ne hzw.1 hzw.2]
    exact reachEN_trans _ _ ih (by rw [← hstep]; exact ⟨.step (.n_fwd z) (.refl _)⟩)
  | @n_bwd z w hz ih =>
    have hzw := havoid (T.n.inv z) hz
    have hstep : T'.n.inv z = T.n.inv z := by
      change swapFun d0 d2 (T.n.inv z) = T.n.inv z
      rw [swapFun_of_ne hzw.1 hzw.2]
    exact reachEN_trans _ _ ih (by rw [← hstep]; exact ⟨.step (.n_bwd z) (.refl _)⟩)
  | @e_step z w hz ih =>
    exact reachEN_trans _ _ ih ⟨.step (.e_fwd z) (.refl _)⟩

theorem no_cross_arc_walk_pair (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    {L : Nat} {d0 d1 d2 d3 : H.Dart} (hc : CyclicOrder4 H.face L d0 d1 d2 d3)
    (hn : SameOrbit H.node d0 d2)
    (P : H.Dart → Prop) (havoid : ∀ z, P z → z ≠ d0 ∧ z ≠ d2)
    (hw : ReachENIn H.edge H.node P d1 d3) : False := by
  have hp := (eulerChar_le_two_mul_numComponents H darts h_nodup h_all (Nat.le_refl _)).2.mp h_planar
  have hne : d0 ≠ d2 := (cyclicOrder4_distinct hc).2.1
  have hf : SameOrbit H.face d0 d2 := (cyclicOrder4_sameOrbit hc).2.1
  let T' := splitVertexTriple H.hypermapToTriple d0 d2
  have hf' := sameOrbit_splitVertexTriple_f_of_cyclicOrder4 H.hypermapToTriple hc
  have h01 : ReachEN T'.e T'.n d0 d1 := sameOrbit_f_imp_reachEN T' hf'.1
  have h23 : ReachEN T'.e T'.n d2 d3 := sameOrbit_f_imp_reachEN T' hf'.2
  have h13 : ReachEN T'.e T'.n d1 d3 := reachEN_splitVertexTriple_of_avoid H.hypermapToTriple d0 d2 P havoid hw
  have h02 : ReachEN T'.e T'.n d0 d2 :=
    reachEN_trans _ _ h01 (reachEN_trans _ _ h13 (reachEN_symm _ _ h23))
  exact splitVertexTriple_not_reachEN_of_genusDeficit_zero H.hypermapToTriple d0 d2 hne hn hf
    darts h_nodup h_all (Nat.le_refl _) hp.1 h02

end SplitVertexAndCrossArc

section AddFaceApex4

theorem exists_cover_countRelClasses {D : Type} (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) :
    ∀ l : List D, ∃ reps : List D,
      reps.length = countRelClasses R l ∧
      (∀ x ∈ l, ∃ r ∈ reps, R r x) ∧
      (∀ r ∈ reps, r ∈ l) := by
  intro l
  induction hl : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil =>
      refine ⟨[], ?_, ?_, ?_⟩
      · rw [countRelClasses_nil]; rfl
      · intro _ hx; cases hx
      · intro _ hr; cases hr
    | cons a as =>
      let S : D → Bool := fun x => decide (R a x)
      let rest := as.filter (fun x => !S x)
      have hrest_lt : rest.length < n := by
        have h1 : rest.length ≤ as.length := List.length_filter_le _ as
        rw [← hl, List.length_cons]
        omega
      obtain ⟨reps', hlen', hcov', hmem'⟩ := ih rest.length hrest_lt rest rfl
      refine ⟨a :: reps', ?_, ?_, ?_⟩
      · rw [countRelClasses_cons, List.length_cons, ← hlen']
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx_as
        · exact ⟨_, List.mem_cons_self, h_refl _⟩
        · by_cases hax : R a x
          · exact ⟨a, List.mem_cons_self, hax⟩
          · have hx_rest : x ∈ rest := by
              apply List.mem_filter.mpr
              refine ⟨hx_as, ?_⟩
              simp [S, hax]
            obtain ⟨r, hr_mem, hrx⟩ := hcov' x hx_rest
            exact ⟨r, List.mem_cons_of_mem a hr_mem, hrx⟩
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem a (List.mem_filter.mp (hmem' r hr')).1

def permInvComp {D : Type} (e n : Perm D) : Perm D where
  f x := n.inv (e.inv x)
  inv x := e.f (n.f x)
  left_inv x := by rw [n.right_inv, e.right_inv]
  right_inv x := by rw [e.left_inv, n.left_inv]

def cornerIdx {D : Type} [DecidableEq D] (c : Fin 4 → D) (d : D) : Option (Fin 4) :=
  if d = c 0 then some 0
  else if d = c 1 then some 1
  else if d = c 2 then some 2
  else if d = c 3 then some 3
  else none

theorem cornerIdx_c {D : Type} [DecidableEq D] (c : Fin 4 → D)
    (hc_inj : ∀ i j : Fin 4, c i = c j → i = j) (k : Fin 4) :
    cornerIdx c (c k) = some k := by
  rcases k with ⟨kv, hk⟩
  have h01 : c 1 ≠ c 0 := fun h => by have := hc_inj 1 0 h; exact absurd (congrArg Fin.val this) (by decide)
  have h02 : c 2 ≠ c 0 := fun h => by have := hc_inj 2 0 h; exact absurd (congrArg Fin.val this) (by decide)
  have h12 : c 2 ≠ c 1 := fun h => by have := hc_inj 2 1 h; exact absurd (congrArg Fin.val this) (by decide)
  have h03 : c 3 ≠ c 0 := fun h => by have := hc_inj 3 0 h; exact absurd (congrArg Fin.val this) (by decide)
  have h13 : c 3 ≠ c 1 := fun h => by have := hc_inj 3 1 h; exact absurd (congrArg Fin.val this) (by decide)
  have h23 : c 3 ≠ c 2 := fun h => by have := hc_inj 3 2 h; exact absurd (congrArg Fin.val this) (by decide)
  match kv, hk with
  | 0, _ => simp [cornerIdx]
  | 1, _ => simp [cornerIdx, h01]
  | 2, _ => simp [cornerIdx, h02, h12]
  | 3, _ => simp [cornerIdx, h03, h13, h23]

theorem eq_of_cornerIdx_some {D : Type} [DecidableEq D] {c : Fin 4 → D} {d : D} {k : Fin 4}
    (h : cornerIdx c d = some k) : d = c k := by
  dsimp only [cornerIdx] at h
  by_cases h0 : d = c 0
  · rw [if_pos h0] at h; cases h; exact h0
  · rw [if_neg h0] at h
    by_cases h1 : d = c 1
    · rw [if_pos h1] at h; cases h; exact h1
    · rw [if_neg h1] at h
      by_cases h2 : d = c 2
      · rw [if_pos h2] at h; cases h; exact h2
      · rw [if_neg h2] at h
        by_cases h3 : d = c 3
        · rw [if_pos h3] at h; cases h; exact h3
        · rw [if_neg h3] at h; cases h

theorem cornerIdx_eq_none_iff {D : Type} [DecidableEq D] {c : Fin 4 → D} {d : D} :
    cornerIdx c d = none ↔ ∀ k : Fin 4, d ≠ c k := by
  constructor
  · intro h ⟨kv, hk⟩
    dsimp only [cornerIdx] at h
    by_cases h0 : d = c 0
    · rw [if_pos h0] at h; cases h
    · rw [if_neg h0] at h
      by_cases h1 : d = c 1
      · rw [if_pos h1] at h; cases h
      · rw [if_neg h1] at h
        by_cases h2 : d = c 2
        · rw [if_pos h2] at h; cases h
        · rw [if_neg h2] at h
          by_cases h3 : d = c 3
          · rw [if_pos h3] at h; cases h
          · match kv, hk with
            | 0, _ => exact h0
            | 1, _ => exact h1
            | 2, _ => exact h2
            | 3, _ => exact h3
  · intro hall
    dsimp only [cornerIdx]
    rw [if_neg (hall 0), if_neg (hall 1), if_neg (hall 2), if_neg (hall 3)]

def addApex4E (H : Hypermap) : Perm (H.Dart ⊕ Fin 8) where
  f x := match x with
    | .inl d => .inl (H.edge.f d)
    | .inr k => .inr ⟨(k.val + 4) % 8, Nat.mod_lt _ (by omega)⟩
  inv x := match x with
    | .inl d => .inl (H.edge.inv d)
    | .inr k => .inr ⟨(k.val + 4) % 8, Nat.mod_lt _ (by omega)⟩
  left_inv x := by
    cases x with
    | inl d => simp [H.edge.left_inv]
    | inr k => have hk_lt := k.isLt; exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))
  right_inv x := by
    cases x with
    | inl d => simp [H.edge.right_inv]
    | inr k => have hk_lt := k.isLt; exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))

def addApex4NF (H : Hypermap) [DecidableEq H.Dart] (c : Fin 4 → H.Dart) :
    H.Dart ⊕ Fin 8 → H.Dart ⊕ Fin 8
  | .inl d =>
    match cornerIdx c d with
    | some k => .inr ⟨k.val, by omega⟩
    | none => .inl (H.node.f d)
  | .inr k =>
    if hk : k.val < 4 then
      .inl (H.node.f (c ⟨k.val, hk⟩))
    else
      .inr ⟨4 + (k.val + 1) % 4, by omega⟩

def addApex4NInv (H : Hypermap) [DecidableEq H.Dart] (c : Fin 4 → H.Dart) :
    H.Dart ⊕ Fin 8 → H.Dart ⊕ Fin 8
  | .inl d =>
    match cornerIdx c (H.node.inv d) with
    | some k => .inr ⟨k.val, by omega⟩
    | none => .inl (H.node.inv d)
  | .inr k =>
    if hk : k.val < 4 then
      .inl (c ⟨k.val, hk⟩)
    else
      .inr ⟨4 + (k.val + 3) % 4, by omega⟩

def addApex4N (H : Hypermap) [DecidableEq H.Dart] (c : Fin 4 → H.Dart)
    (hc_inj : ∀ i j : Fin 4, c i = c j → i = j) : Perm (H.Dart ⊕ Fin 8) where
  f := addApex4NF H c
  inv := addApex4NInv H c
  left_inv x := by
    cases x with
    | inl d =>
      dsimp only [addApex4NF, addApex4NInv]
      cases hci : cornerIdx c d with
      | some k =>
        dsimp only []
        rw [dif_pos (by omega)]
        exact congrArg Sum.inl (eq_of_cornerIdx_some hci).symm
      | none =>
        dsimp only []
        rw [H.node.left_inv, hci]
    | inr k =>
      dsimp only [addApex4NF, addApex4NInv]
      by_cases hk : k.val < 4
      · rw [dif_pos hk]
        dsimp only []
        rw [H.node.left_inv, cornerIdx_c c hc_inj ⟨k.val, hk⟩]
      · rw [dif_neg hk]
        dsimp only []
        have hk_lt := k.isLt
        have hk2 : ¬ (4 + (k.val + 1) % 4) < 4 := by omega
        rw [dif_neg hk2]
        exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))
  right_inv x := by
    cases x with
    | inl d =>
      dsimp only [addApex4NF, addApex4NInv]
      cases hci : cornerIdx c (H.node.inv d) with
      | some k =>
        dsimp only []
        rw [dif_pos (by omega)]
        have heq := eq_of_cornerIdx_some hci
        rw [← heq, H.node.right_inv]
      | none =>
        dsimp only []
        rw [hci, H.node.right_inv]
    | inr k =>
      dsimp only [addApex4NF, addApex4NInv]
      by_cases hk : k.val < 4
      · rw [dif_pos hk]
        dsimp only []
        rw [cornerIdx_c c hc_inj ⟨k.val, hk⟩]
      · rw [dif_neg hk]
        dsimp only []
        have hk_lt := k.isLt
        have hk2 : ¬ (4 + (k.val + 3) % 4) < 4 := by omega
        rw [dif_neg hk2]
        exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))

/-- Subdivide a face of `H` along 4 distinct corners `c 0..3` by inserting an apex vertex of degree 4
connected by 4 new spoke edges `(c k ↔ apex_k)`. -/
def addFaceApex4 (H : Hypermap) [DecidableEq H.Dart] (c : Fin 4 → H.Dart)
    (hc_inj : ∀ i j : Fin 4, c i = c j → i = j) : Hypermap where
  Dart := H.Dart ⊕ Fin 8
  edge := addApex4E H
  node := addApex4N H c hc_inj
  face := permInvComp (addApex4E H) (addApex4N H c hc_inj)
  edge_involution x := by
    cases x with
    | inl d => simp [addApex4E, H.edge_involution]
    | inr k => have hk_lt := k.isLt; exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))
  edge_node_face_id x := by
    change (addApex4E H).f ((addApex4N H c hc_inj).f
      ((addApex4N H c hc_inj).inv ((addApex4E H).inv x))) = x
    rw [(addApex4N H c hc_inj).right_inv, (addApex4E H).right_inv]

instance instDecidableEqAddFaceApex4Dart (H : Hypermap) [DecidableEq H.Dart]
    (c : Fin 4 → H.Dart) (hc_inj : ∀ i j : Fin 4, c i = c j → i = j) :
    DecidableEq (H.addFaceApex4 c hc_inj).Dart :=
  inferInstanceAs (DecidableEq (H.Dart ⊕ Fin 8))

def fin8Darts : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

theorem addFaceApex4_darts_complete (H : Hypermap) [DecidableEq H.Dart]
    (c : Fin 4 → H.Dart) (hc_inj : ∀ i j : Fin 4, c i = c j → i = j)
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts) :
    let darts' : List (H.addFaceApex4 c hc_inj).Dart := darts.map Sum.inl ++ fin8Darts.map Sum.inr
    darts'.Nodup ∧ (∀ x : (H.addFaceApex4 c hc_inj).Dart, x ∈ darts') ∧ darts'.length = darts.length + 8 := by
  intro darts'
  have h8_nd : fin8Darts.Nodup := by decide
  have h8_mem : ∀ k : Fin 8, k ∈ fin8Darts := by decide
  have hnd1 : (darts.map (@Sum.inl H.Dart (Fin 8))).Nodup :=
    List.Pairwise.map (@Sum.inl H.Dart (Fin 8)) (fun _ _ h heq => h (Sum.inl.inj heq)) h_nodup
  have hnd2 : (fin8Darts.map (@Sum.inr H.Dart (Fin 8))).Nodup :=
    List.Pairwise.map (@Sum.inr H.Dart (Fin 8)) (fun _ _ h heq => h (Sum.inr.inj heq)) h8_nd
  have hdisj : ∀ a ∈ darts.map (@Sum.inl H.Dart (Fin 8)),
      ∀ b ∈ fin8Darts.map (@Sum.inr H.Dart (Fin 8)), a ≠ b := by
    intro a ha b hb heq
    rcases List.mem_map.mp ha with ⟨x, _, rfl⟩
    rcases List.mem_map.mp hb with ⟨y, _, rfl⟩
    cases heq
  refine ⟨List.nodup_append.mpr ⟨hnd1, hnd2, hdisj⟩, ?_, ?_⟩
  · intro x
    cases x with
    | inl d => exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨d, h_all d, rfl⟩))
    | inr k => exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨k, h8_mem k, rfl⟩))
  · change (List.map (@Sum.inl H.Dart (Fin 8)) darts ++ List.map (@Sum.inr H.Dart (Fin 8)) fin8Darts).length = _
    rw [List.length_append, List.length_map, List.length_map]
    rfl

theorem addFaceApex4_edge_free (H : Hypermap) [DecidableEq H.Dart]
    (c : Fin 4 → H.Dart) (hc_inj : ∀ i j : Fin 4, c i = c j → i = j)
    (h_efree : ∀ d : H.Dart, H.edge.f d ≠ d) :
    ∀ x : (H.addFaceApex4 c hc_inj).Dart, (H.addFaceApex4 c hc_inj).edge.f x ≠ x := by
  intro x
  cases x with
  | inl d =>
    intro h
    exact h_efree d (Sum.inl.inj h)
  | inr k =>
    intro h
    have hv := congrArg Fin.val (Sum.inr.inj h)
    dsimp only [] at hv
    omega

theorem isPlanar_addFaceApex4 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (c : Fin 4 → H.Dart) {L : Nat}
    (hc : CyclicOrder4 H.face L (c 0) (c 1) (c 2) (c 3)) :
    let hc_inj : ∀ i j : Fin 4, c i = c j → i = j := fun i j hij => by
      have hd := cyclicOrder4_distinct hc
      rcases i with ⟨iv, hi⟩; rcases j with ⟨jv, hj⟩
      match iv, hi, jv, hj with
      | 0, _, 0, _ => rfl | 1, _, 1, _ => rfl | 2, _, 2, _ => rfl | 3, _, 3, _ => rfl
      | 0, _, 1, _ => exact absurd hij hd.1 | 1, _, 0, _ => exact absurd hij.symm hd.1
      | 0, _, 2, _ => exact absurd hij hd.2.1 | 2, _, 0, _ => exact absurd hij.symm hd.2.1
      | 0, _, 3, _ => exact absurd hij hd.2.2.1 | 3, _, 0, _ => exact absurd hij.symm hd.2.2.1
      | 1, _, 2, _ => exact absurd hij hd.2.2.2.1 | 2, _, 1, _ => exact absurd hij.symm hd.2.2.2.1
      | 1, _, 3, _ => exact absurd hij hd.2.2.2.2.1 | 3, _, 1, _ => exact absurd hij.symm hd.2.2.2.2.1
      | 2, _, 3, _ => exact absurd hij hd.2.2.2.2.2 | 3, _, 2, _ => exact absurd hij.symm hd.2.2.2.2.2
    let H' := H.addFaceApex4 c hc_inj
    let darts' : List H'.Dart := darts.map Sum.inl ++ fin8Darts.map Sum.inr
    H'.isPlanar darts'.length darts' = true := by
  classical
  intro hc_inj H' darts'
  obtain ⟨h_nd', h_all', h_len'⟩ := addFaceApex4_darts_complete H c hc_inj darts h_nodup h_all
  have hp := (eulerChar_le_two_mul_numComponents H darts h_nodup h_all (Nat.le_refl _)).2.mp h_planar
  have h_efree' := addFaceApex4_edge_free H c hc_inj hp.2
  have h_nonneg' := genusDeficit_nonneg H'.hypermapToTriple darts' h_nd' h_all' (Nat.le_refl _)
  -- 1. C' ≤ C
  have h_step_lift : ∀ u v : H.Dart, StepEN H.edge H.node u v →
      ReachEN H'.edge H'.node (Sum.inl u) (Sum.inl v) := by
    intro u v hs
    cases hs with
    | e_fwd => exact ⟨.step (.e_fwd (Sum.inl u)) (.refl _)⟩
    | e_bwd => exact ⟨.step (.e_bwd (Sum.inl u)) (.refl _)⟩
    | n_fwd =>
      change ReachEN H'.edge H'.node (Sum.inl u) (Sum.inl (H.node.f u))
      cases hci : cornerIdx c u with
      | none =>
        have hfn : H'.node.f (Sum.inl u) = Sum.inl (H.node.f u) := by
          change addApex4NF H c (Sum.inl u) = _; dsimp only [addApex4NF]; rw [hci]
        rw [← hfn]; exact ⟨.step (.n_fwd (Sum.inl u)) (.refl _)⟩
      | some k =>
        let k8 : Fin 8 := ⟨k.val, by omega⟩
        have hf1 : H'.node.f (Sum.inl u) = Sum.inr k8 := by
          change addApex4NF H c (Sum.inl u) = _; dsimp only [addApex4NF]; rw [hci]
        have hf2 : H'.node.f (Sum.inr k8) = Sum.inl (H.node.f u) := by
          change addApex4NF H c (Sum.inr k8) = _
          dsimp only [addApex4NF, k8]; rw [dif_pos (by omega)]
          have heq := eq_of_cornerIdx_some hci
          exact congrArg Sum.inl (congrArg H.node.f heq.symm)
        exact ⟨.step (hf1 ▸ StepEN.n_fwd (Sum.inl u)) (.step (hf2 ▸ StepEN.n_fwd (Sum.inr k8)) (.refl _))⟩
    | n_bwd =>
      change ReachEN H'.edge H'.node (Sum.inl u) (Sum.inl (H.node.inv u))
      cases hci : cornerIdx c (H.node.inv u) with
      | none =>
        have hbn : H'.node.inv (Sum.inl u) = Sum.inl (H.node.inv u) := by
          change addApex4NInv H c (Sum.inl u) = _; dsimp only [addApex4NInv]; rw [hci]
        rw [← hbn]; exact ⟨.step (.n_bwd (Sum.inl u)) (.refl _)⟩
      | some k =>
        let k8 : Fin 8 := ⟨k.val, by omega⟩
        have hb1 : H'.node.inv (Sum.inl u) = Sum.inr k8 := by
          change addApex4NInv H c (Sum.inl u) = _; dsimp only [addApex4NInv]; rw [hci]
        have hb2 : H'.node.inv (Sum.inr k8) = Sum.inl (H.node.inv u) := by
          change addApex4NInv H c (Sum.inr k8) = _
          dsimp only [addApex4NInv, k8]; rw [dif_pos (by omega)]
          exact congrArg Sum.inl (eq_of_cornerIdx_some hci).symm
        exact ⟨.step (hb1 ▸ StepEN.n_bwd (Sum.inl u)) (.step (hb2 ▸ StepEN.n_bwd (Sum.inr k8)) (.refl _))⟩
  have h_reach_lift : ∀ {u v : H.Dart}, ReachEN H.edge H.node u v →
      ReachEN H'.edge H'.node (Sum.inl u) (Sum.inl v) := by
    intro u v h
    rcases h with ⟨w⟩
    induction w with
    | refl => exact reachEN_refl _ _ _
    | step hs _ ih => exact reachEN_trans _ _ (h_step_lift _ _ hs) ih
  have hf01 : ReachEN H.edge H.node (c 0) (c 1) :=
    sameOrbit_f_imp_reachEN H.hypermapToTriple (cyclicOrder4_sameOrbit hc).1
  have hf02 : ReachEN H.edge H.node (c 0) (c 2) :=
    sameOrbit_f_imp_reachEN H.hypermapToTriple (cyclicOrder4_sameOrbit hc).2.1
  have hf03 : ReachEN H.edge H.node (c 0) (c 3) :=
    sameOrbit_f_imp_reachEN H.hypermapToTriple (cyclicOrder4_sameOrbit hc).2.2
  have hinr_reach : ∀ k : Fin 8, ReachEN H'.edge H'.node (Sum.inl (c 0)) (Sum.inr k) := by
    intro k
    have hck_n : ∀ m : Fin 4, ReachEN H'.edge H'.node (Sum.inl (c m)) (Sum.inr ⟨m.val, by omega⟩) := by
      intro m
      have hm : H'.node.f (Sum.inl (c m)) = Sum.inr ⟨m.val, by omega⟩ := by
        change addApex4NF H c (Sum.inl (c m)) = _
        dsimp only [addApex4NF]
        rw [cornerIdx_c c hc_inj m]
      rw [← hm]; exact ⟨.step (.n_fwd _) (.refl _)⟩
    rcases k with ⟨kv, hkv⟩
    by_cases hk : kv < 4
    · have h0m : ReachEN H.edge H.node (c 0) (c ⟨kv, hk⟩) := by
        match kv, hk with
        | 0, _ => exact reachEN_refl _ _ _
        | 1, _ => exact hf01
        | 2, _ => exact hf02
        | 3, _ => exact hf03
      exact reachEN_trans _ _ (h_reach_lift h0m) (hck_n ⟨kv, hk⟩)
    · have hk4 : kv - 4 < 4 := by omega
      let m : Fin 4 := ⟨kv - 4, hk4⟩
      have h0m : ReachEN H.edge H.node (c 0) (c m) := by
        dsimp only [m]
        match kv - 4, hk4 with
        | 0, _ => exact reachEN_refl _ _ _
        | 1, _ => exact hf01
        | 2, _ => exact hf02
        | 3, _ => exact hf03
      have hm_e : H'.edge.f (Sum.inr ⟨m.val, by omega⟩) = Sum.inr ⟨kv, hkv⟩ := by
        change (addApex4E H).f (Sum.inr ⟨m.val, by omega⟩) = Sum.inr ⟨kv, hkv⟩
        dsimp only [addApex4E]
        exact congrArg Sum.inr (Fin.ext (by dsimp only [m]; omega))
      exact reachEN_trans _ _ (reachEN_trans _ _ (h_reach_lift h0m) (hck_n m))
        (by rw [← hm_e]; exact ⟨.step (.e_fwd _) (.refl _)⟩)
  have hC_le : countRelClasses (ReachEN H'.edge H'.node) darts' ≤
      countRelClasses (ReachEN H.edge H.node) darts := by
    obtain ⟨reps, hlen_r, hcov_r, _⟩ := exists_cover_countRelClasses (ReachEN H.edge H.node)
      (reachEN_refl _ _) darts
    rw [← hlen_r, ← List.length_map Sum.inl]
    apply countRelClasses_le_of_cover (ReachEN H'.edge H'.node)
      (reachEN_refl _ _) (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
    intro x _
    cases x with
    | inl d =>
      obtain ⟨r, hr, hrd⟩ := hcov_r d (h_all d)
      exact ⟨Sum.inl r, List.mem_map.mpr ⟨r, hr, rfl⟩, h_reach_lift hrd⟩
    | inr k =>
      obtain ⟨r, hr, hrc⟩ := hcov_r (c 0) (h_all (c 0))
      exact ⟨Sum.inl r, List.mem_map.mpr ⟨r, hr, rfl⟩, reachEN_trans _ _ (h_reach_lift hrc) (hinr_reach k)⟩
  -- 2. E' = E + 4
  have hE_eq : countOrbits H'.edge darts'.length darts' =
      countOrbits H.edge darts.length darts + 4 := by
    have hl1 := length_eq_two_mul_countOrbits_of_involution H.edge H.edge_involution darts h_nodup h_all
      (fun d _ => hp.2 d) (Nat.le_refl _)
    have hl2 := length_eq_two_mul_countOrbits_of_involution H'.edge H'.edge_involution darts' h_nd' h_all'
      (fun d _ => h_efree' d) (Nat.le_refl _)
    have hlen_eq : darts'.length = darts.length + 8 := h_len'
    omega
  -- 3. V' ≥ V + 1
  have hV_ge : countOrbits H.node darts.length darts + 1 ≤ countOrbits H'.node darts'.length darts' := by
    let S_apex : H'.Dart → Bool := fun x =>
      match x with
      | .inl _ => false
      | .inr k => decide (4 ≤ k.val)
    have hS_apex : ∀ x : H'.Dart, S_apex (H'.node.f x) = S_apex x := by
      intro x
      cases x with
      | inl d =>
        change S_apex (addApex4NF H c (.inl d)) = false
        dsimp only [addApex4NF]
        cases cornerIdx c d with
        | none => rfl
        | some k => simp [S_apex]
      | inr k =>
        change S_apex (addApex4NF H c (.inr k)) = decide (4 ≤ k.val)
        dsimp only [addApex4NF]
        by_cases hk : k.val < 4
        · rw [dif_pos hk]; simp [S_apex, show ¬ 4 ≤ k.val by omega]
        · rw [dif_neg hk]; simp [S_apex, show 4 ≤ k.val by omega]
    have hV_part := countOrbits_partition_of_closed H'.node darts'.length darts' S_apex hS_apex
    have h_apex_pos : 1 ≤ countOrbits H'.node darts'.length (darts'.filter S_apex) := by
      have h4_mem : (.inr ⟨4, by omega⟩ : H'.Dart) ∈ darts'.filter S_apex :=
        List.mem_filter.mpr ⟨h_all' (.inr ⟨4, by omega⟩), rfl⟩
      cases hfl : darts'.filter S_apex with
      | nil => rw [hfl] at h4_mem; exact absurd h4_mem List.not_mem_nil
      | cons a as => exact countOrbits_pos_cons _ _ a as
    let projV : H'.Dart → Option H.Dart
      | .inl d => some d
      | .inr k => if hk : k.val < 4 then some (c ⟨k.val, hk⟩) else none
    have hproj_step : ∀ {x y : H'.Dart} {u v : H.Dart},
        H'.node.f x = y → projV x = some u → projV y = some v → SameOrbit H.node u v := by
      intro x y u v hxy hux hvy
      subst y
      cases x with
      | inl d =>
        have hdu : u = d := Option.some.inj hux.symm
        subst u
        have hy_eq : H'.node.f (Sum.inl d) = addApex4NF H c (Sum.inl d) := rfl
        rw [hy_eq] at hvy
        dsimp only [addApex4NF, projV] at hvy
        cases hci : cornerIdx c d with
        | none =>
          rw [hci] at hvy
          have hv : H.node.f d = v := Option.some.inj hvy
          rw [← hv]; exact sameOrbit_step H.node rfl
        | some k =>
          rw [hci] at hvy
          simp only at hvy
          rw [dif_pos (by omega)] at hvy
          have hv : c ⟨k.val, by omega⟩ = v := Option.some.inj hvy
          have hdc := eq_of_cornerIdx_some hci
          rw [← hv, ← hdc]; exact sameOrbit_refl H.node d
      | inr k =>
        by_cases hk : k.val < 4
        · dsimp only [projV] at hux; rw [dif_pos hk] at hux
          have hck : c ⟨k.val, hk⟩ = u := Option.some.inj hux
          have hy : H'.node.f (Sum.inr k) = Sum.inl (H.node.f (c ⟨k.val, hk⟩)) := by
            change addApex4NF H c (Sum.inr k) = _; dsimp only [addApex4NF]; rw [dif_pos hk]
          rw [hy] at hvy
          have hv : H.node.f (c ⟨k.val, hk⟩) = v := Option.some.inj hvy
          rw [← hv, ← hck]; exact sameOrbit_step H.node rfl
        · dsimp only [projV] at hux; rw [dif_neg hk] at hux; cases hux
    have hproj_same : ∀ {x y : H'.Dart} {u v : H.Dart},
        SameOrbit H'.node x y → projV x = some u → projV y = some v → SameOrbit H.node u v := by
      rintro x y u v ⟨k, hk⟩ hux hvy
      induction k generalizing x u with
      | zero =>
        change x = y at hk; subst hk
        rw [hux] at hvy; cases hvy; exact sameOrbit_refl H.node _
      | succ k ih =>
        rw [Perm.iter_succ_right] at hk
        cases hpn : projV (H'.node.f x) with
        | some w =>
          have h1 := hproj_step rfl hux hpn
          have h2 := ih hk hpn
          exact sameOrbit_trans H.node h1 h2
        | none =>
          have hfx_s : S_apex (H'.node.f x) = false := by
            rw [hS_apex]
            cases x with
            | inl _ => rfl
            | inr m =>
              dsimp only [projV] at hux
              by_cases hm : m.val < 4
              · exact decide_eq_false (by omega)
              · rw [dif_neg hm] at hux; cases hux
          exfalso
          cases hfx : H'.node.f x with
          | inl d => rw [hfx] at hpn; simp [projV] at hpn
          | inr m =>
            rw [hfx] at hpn hfx_s
            by_cases hm : m.val < 4
            · simp [projV, hm] at hpn
            · simp [S_apex, hm] at hfx_s
    have hV_le_sub : countOrbits H.node darts.length darts ≤
        countOrbits H'.node darts'.length (darts'.filter (fun x => !S_apex x)) := by
      let lV := darts'.filter (fun x => !S_apex x)
      rw [countOrbits_eq_countRelClasses H'.node darts' h_all' (Nat.le_refl _) lV,
          countOrbits_eq_countRelClasses H.node darts h_all (Nat.le_refl _) darts]
      obtain ⟨repsV, hlen_V, hcov_V, hmem_V⟩ := exists_cover_countRelClasses (SameOrbit H'.node)
        (sameOrbit_refl _) lV
      let repsH := repsV.filterMap projV
      have hlen_le : repsH.length ≤ repsV.length := by
        clear hlen_V hcov_V hmem_V
        induction repsV with
        | nil => simp [repsH]
        | cons r rs ih =>
          simp only [repsH, List.filterMap_cons]
          cases projV r <;> simp <;> omega
      have hcov_H : ∀ d ∈ darts, ∃ r ∈ repsH, SameOrbit H.node r d := by
        intro d hd
        have hinl : (.inl d : H'.Dart) ∈ lV := List.mem_filter.mpr ⟨h_all' (.inl d), rfl⟩
        obtain ⟨r', hr'_mem, hr'_orb⟩ := hcov_V (.inl d) hinl
        have hr'_lV : S_apex r' = false := by
          have := (List.mem_filter.mp (hmem_V r' hr'_mem)).2
          simpa using this
        have hpr : ∃ r0, projV r' = some r0 := by
          cases r' with
          | inl d0 => exact ⟨d0, rfl⟩
          | inr k =>
            have hk : k.val < 4 := by simp [S_apex] at hr'_lV; omega
            exact ⟨c ⟨k.val, hk⟩, by simp [projV, hk]⟩
        obtain ⟨r0, hr0⟩ := hpr
        refine ⟨r0, List.mem_filterMap.mpr ⟨r', hr'_mem, hr0⟩, ?_⟩
        exact hproj_same hr'_orb hr0 rfl
      have hcov_cnt := countRelClasses_le_of_cover (SameOrbit H.node)
        (sameOrbit_refl _) (sameOrbit_symm_of_complete _ darts h_all) (sameOrbit_trans _)
        repsH darts hcov_H
      omega
    omega
  -- 4. F' ≥ F + 3
  have hF_ge : countOrbits H.face darts.length darts + 3 ≤ countOrbits H'.face darts'.length darts' := by
    let inF0 : H.Dart → Bool := fun d => decide (SameOrbit H.face (c 0) d)
    let inF : H'.Dart → Bool := fun x =>
      match x with
      | .inl d => inF0 d
      | .inr _ => true
    have hH'_face_inl : ∀ d : H.Dart,
        H'.face.f (.inl d) =
          match cornerIdx c (H.face.f d) with
          | some k => .inr ⟨k.val, by omega⟩
          | none => .inl (H.face.f d) := by
      intro d
      change (addApex4N H c hc_inj).inv ((addApex4E H).inv (.inl d)) = _
      have hf_eq : H.node.inv (H.edge.inv d) = H.face.f d := by
        calc H.node.inv (H.edge.inv d)
            = H.node.inv (H.edge.inv (H.edge.f (H.node.f (H.face.f d)))) := by rw [H.edge_node_face_id]
          _ = H.node.inv (H.node.f (H.face.f d)) := by rw [H.edge.left_inv]
          _ = H.face.f d := H.node.left_inv _
      dsimp only [addApex4E, addApex4N, addApex4NInv]
      rw [hf_eq]
      rfl
    have h_inF0 : ∀ d, inF0 (H.face.f d) = inF0 d := by
      intro d
      simp only [inF0]
      exact Bool.eq_iff_iff.mpr (by
        simp only [decide_eq_true_eq]
        exact ⟨fun h => sameOrbit_trans H.face h (sameOrbit_symm_of_complete H.face darts h_all (sameOrbit_step H.face rfl)),
               fun h => sameOrbit_trans H.face h (sameOrbit_step H.face rfl)⟩)
    have h_inF : ∀ x : H'.Dart, inF (H'.face.f x) = inF x := by
      intro x
      cases x with
      | inl d =>
        rw [hH'_face_inl d]
        cases hci : cornerIdx c (H.face.f d) with
        | none =>
          dsimp only [inF]
          exact h_inF0 d
        | some k =>
          have hfk : H.face.f d = c k := eq_of_cornerIdx_some hci
          have h0k : SameOrbit H.face (c 0) (c k) := by
            rcases k with ⟨kv, hk⟩
            match kv, hk with
            | 0, _ => exact sameOrbit_refl _ _
            | 1, _ => exact (cyclicOrder4_sameOrbit hc).1
            | 2, _ => exact (cyclicOrder4_sameOrbit hc).2.1
            | 3, _ => exact (cyclicOrder4_sameOrbit hc).2.2
          have hd_in : SameOrbit H.face (c 0) d :=
            sameOrbit_trans H.face (by rw [← hfk] at h0k; exact h0k)
              (sameOrbit_symm_of_complete H.face darts h_all (sameOrbit_step H.face rfl))
          simp [inF, inF0, hd_in]
      | inr k =>
        have hk_lt := k.isLt
        by_cases hk : k.val < 4
        · have he : (addApex4E H).inv (Sum.inr k) = Sum.inr ⟨(k.val + 4) % 8, Nat.mod_lt _ (by omega)⟩ := rfl
          change inF ((addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr k))) = true
          rw [he]
          dsimp only [addApex4N, addApex4NInv]
          rw [dif_neg (by omega)]
        · have he : (addApex4E H).inv (Sum.inr k) = Sum.inr ⟨(k.val + 4) % 8, Nat.mod_lt _ (by omega)⟩ := rfl
          change inF ((addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr k))) = true
          rw [he]
          dsimp only [addApex4N, addApex4NInv]
          rw [dif_pos (by omega)]
          dsimp only [inF, inF0]
          apply decide_eq_true
          have hco := cyclicOrder4_sameOrbit hc
          have h0 : (k.val + 4) % 8 < 4 := by omega
          have hsub : ∀ (m : Nat) (hm : m < 4), (k.val + 4) % 8 = m →
              SameOrbit H.face (c 0) (c ⟨(k.val + 4) % 8, by omega⟩) := by
            intro m hm hmeq
            have hfin : (⟨(k.val + 4) % 8, by omega⟩ : Fin 4) = ⟨m, hm⟩ := Fin.ext hmeq
            rw [hfin]
            match m, hm with
            | 0, _ => exact sameOrbit_refl _ _
            | 1, _ => exact hco.1
            | 2, _ => exact hco.2.1
            | 3, _ => exact hco.2.2
          exact hsub ((k.val + 4) % 8) h0 rfl
    have hF_part0 := countOrbits_partition_of_closed H.face darts.length darts inF0 h_inF0
    have hF_part' := countOrbits_partition_of_closed H'.face darts'.length darts' inF h_inF
    have hF_in0 : countOrbits H.face darts.length (darts.filter inF0) = 1 := by
      have hc0 : c 0 ∈ darts.filter inF0 :=
        List.mem_filter.mpr ⟨h_all (c 0), decide_eq_true (sameOrbit_refl _ _)⟩
      have hge1 : 1 ≤ countOrbits H.face darts.length (darts.filter inF0) := by
        cases hfl : darts.filter inF0 with
        | nil => rw [hfl] at hc0; exact absurd hc0 List.not_mem_nil
        | cons u us => exact countOrbits_pos_cons _ _ u us
      have hle1 : countOrbits H.face darts.length (darts.filter inF0) ≤ 1 := by
        apply countOrbits_le_of_cover H.face darts h_all (Nat.le_refl _) [c 0] (darts.filter inF0)
        intro x hx
        exact ⟨c 0, List.mem_cons_self, of_decide_eq_true (List.mem_filter.mp hx).2⟩
      omega
    have h_outside_iter : ∀ (k : Nat) (d : H.Dart), ¬ SameOrbit H.face (c 0) d →
        Perm.iter H'.face k (.inl d) = .inl (Perm.iter H.face k d) := by
      intro k d hd
      induction k generalizing d with
      | zero => rfl
      | succ k ih =>
        rw [Perm.iter_succ_right H'.face k (Sum.inl d : H'.Dart), Perm.iter_succ_right H.face k d]
        have hfd : ¬ SameOrbit H.face (c 0) (H.face.f d) := fun h =>
          hd (sameOrbit_trans H.face h (sameOrbit_symm_of_complete H.face darts h_all (sameOrbit_step H.face rfl)))
        have hci : cornerIdx c (H.face.f d) = none := cornerIdx_eq_none_iff.mpr (fun m heq => by
          apply hfd; rw [heq]
          rcases m with ⟨mv, hm⟩
          match mv, hm with
          | 0, _ => exact sameOrbit_refl _ _
          | 1, _ => exact (cyclicOrder4_sameOrbit hc).1
          | 2, _ => exact (cyclicOrder4_sameOrbit hc).2.1
          | 3, _ => exact (cyclicOrder4_sameOrbit hc).2.2)
        have hstep : H'.face.f (.inl d) = .inl (H.face.f d) := by rw [hH'_face_inl, hci]
        rw [hstep, ih (H.face.f d) hfd]
    have hF_out_le : countOrbits H.face darts.length (darts.filter (fun x => !inF0 x)) ≤
        countOrbits H'.face darts'.length (darts'.filter (fun x => !inF x)) := by
      let lF0 := darts.filter (fun x => !inF0 x)
      let lF' := darts'.filter (fun x => !inF x)
      rw [countOrbits_eq_countRelClasses H'.face darts' h_all' (Nat.le_refl _) lF',
          countOrbits_eq_countRelClasses H.face darts h_all (Nat.le_refl _) lF0]
      obtain ⟨repsF', hlen_F', hcov_F', hmem_F'⟩ := exists_cover_countRelClasses (SameOrbit H'.face)
        (sameOrbit_refl _) lF'
      let unInl : H'.Dart → Option H.Dart
        | .inl d => some d
        | .inr _ => none
      let repsF := repsF'.filterMap unInl
      have hlen_le : repsF.length ≤ repsF'.length := by
        clear hlen_F' hcov_F' hmem_F'
        induction repsF' with
        | nil => simp [repsF]
        | cons r rs ih =>
          simp only [repsF, List.filterMap_cons]
          cases unInl r <;> simp <;> omega
      have hcov_F : ∀ d ∈ lF0, ∃ r ∈ repsF, SameOrbit H.face r d := by
        intro d hd
        have hd_not : ¬ SameOrbit H.face (c 0) d := by
          have := (List.mem_filter.mp hd).2
          simpa [inF0] using this
        have hinl : (.inl d : H'.Dart) ∈ lF' := by
          apply List.mem_filter.mpr
          refine ⟨h_all' (.inl d), ?_⟩
          simp [inF, inF0, hd_not]
        obtain ⟨r', hr'_mem, ⟨k, hk⟩⟩ := hcov_F' (.inl d) hinl
        have hr'_not : inF r' = false := by
          have := (List.mem_filter.mp (hmem_F' r' hr'_mem)).2
          simpa using this
        cases r' with
        | inr _ => simp [inF] at hr'_not
        | inl r0 =>
          have hr0_not : ¬ SameOrbit H.face (c 0) r0 := by
            simp [inF, inF0] at hr'_not; exact hr'_not
          have hiter := h_outside_iter k r0 hr0_not
          rw [hiter] at hk
          exact ⟨r0, List.mem_filterMap.mpr ⟨.inl r0, hr'_mem, rfl⟩, ⟨k, Sum.inl.inj hk⟩⟩
      have hcov_cnt := countRelClasses_le_of_cover (SameOrbit H.face)
        (sameOrbit_refl _) (sameOrbit_symm_of_complete _ darts h_all) (sameOrbit_trans _)
        repsF lF0 hcov_F
      omega
    -- Show countOrbits H'.face darts'.length (darts'.filter inF) ≥ 4 using faceSector
    let faceSector : H'.Dart → Nat := fun x =>
      match x with
      | .inr k =>
        if k.val = 0 then 3
        else if k.val = 1 then 0
        else if k.val = 2 then 1
        else if k.val = 3 then 2
        else if k.val = 4 then 0
        else if k.val = 5 then 1
        else if k.val = 6 then 2
        else 3
      | .inl d =>
        if ∃ t, t < hc.k1 ∧ Perm.iter H.face t (c 0) = d then 0
        else if ∃ t, t < hc.k2 ∧ Perm.iter H.face (hc.k1 + t) (c 0) = d then 1
        else if ∃ t, t < hc.k3 ∧ Perm.iter H.face (hc.k1 + hc.k2 + t) (c 0) = d then 2
        else if ∃ t, t < hc.k4 ∧ Perm.iter H.face (hc.k1 + hc.k2 + hc.k3 + t) (c 0) = d then 3
        else 4
    have hsec_0 : ∀ d, (∃ t, t < hc.k1 ∧ Perm.iter H.face t (c 0) = d) → faceSector (.inl d) = 0 := by
      intro d h; dsimp only [faceSector]; rw [if_pos h]
    have hsec_1 : ∀ d, (∃ t, t < hc.k2 ∧ Perm.iter H.face (hc.k1 + t) (c 0) = d) → faceSector (.inl d) = 1 := by
      intro d h
      dsimp only [faceSector]
      obtain ⟨t, ht, htd⟩ := h
      have hnot0 : ¬ ∃ t0, t0 < hc.k1 ∧ Perm.iter H.face t0 (c 0) = d := by
        rintro ⟨t0, ht0, ht0d⟩
        have := hc.inj_lt t0 (hc.k1 + t)
          (by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
          (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
          (ht0d.trans htd.symm)
        omega
      rw [if_neg hnot0, if_pos ⟨t, ht, htd⟩]
    have hsec_2 : ∀ d, (∃ t, t < hc.k3 ∧ Perm.iter H.face (hc.k1 + hc.k2 + t) (c 0) = d) → faceSector (.inl d) = 2 := by
      intro d h
      dsimp only [faceSector]
      obtain ⟨t, ht, htd⟩ := h
      have hnot0 : ¬ ∃ t0, t0 < hc.k1 ∧ Perm.iter H.face t0 (c 0) = d := by
        rintro ⟨t0, ht0, ht0d⟩
        have := hc.inj_lt t0 (hc.k1 + hc.k2 + t)
          (by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
          (by have := hc.hk4; have := hc.hsum; omega) (ht0d.trans htd.symm)
        omega
      have hnot1 : ¬ ∃ t1, t1 < hc.k2 ∧ Perm.iter H.face (hc.k1 + t1) (c 0) = d := by
        rintro ⟨t1, ht1, ht1d⟩
        have := hc.inj_lt (hc.k1 + t1) (hc.k1 + hc.k2 + t)
          (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
          (by have := hc.hk4; have := hc.hsum; omega) (ht1d.trans htd.symm)
        omega
      rw [if_neg hnot0, if_neg hnot1, if_pos ⟨t, ht, htd⟩]
    have hsec_3 : ∀ d, (∃ t, t < hc.k4 ∧ Perm.iter H.face (hc.k1 + hc.k2 + hc.k3 + t) (c 0) = d) → faceSector (.inl d) = 3 := by
      intro d h
      dsimp only [faceSector]
      obtain ⟨t, ht, htd⟩ := h
      have hnot0 : ¬ ∃ t0, t0 < hc.k1 ∧ Perm.iter H.face t0 (c 0) = d := by
        rintro ⟨t0, ht0, ht0d⟩
        have := hc.inj_lt t0 (hc.k1 + hc.k2 + hc.k3 + t)
          (by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
          (by have := hc.hsum; omega) (ht0d.trans htd.symm)
        omega
      have hnot1 : ¬ ∃ t1, t1 < hc.k2 ∧ Perm.iter H.face (hc.k1 + t1) (c 0) = d := by
        rintro ⟨t1, ht1, ht1d⟩
        have := hc.inj_lt (hc.k1 + t1) (hc.k1 + hc.k2 + hc.k3 + t)
          (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
          (by have := hc.hsum; omega) (ht1d.trans htd.symm)
        omega
      have hnot2 : ¬ ∃ t2, t2 < hc.k3 ∧ Perm.iter H.face (hc.k1 + hc.k2 + t2) (c 0) = d := by
        rintro ⟨t2, ht2, ht2d⟩
        have := hc.inj_lt (hc.k1 + hc.k2 + t2) (hc.k1 + hc.k2 + hc.k3 + t)
          (by have := hc.hk4; have := hc.hsum; omega)
          (by have := hc.hsum; omega) (ht2d.trans htd.symm)
        omega
      rw [if_neg hnot0, if_neg hnot1, if_neg hnot2, if_pos ⟨t, ht, htd⟩]
    have hsec_inv : ∀ x : H'.Dart, faceSector (H'.face.f x) = faceSector x := by
      intro x
      cases x with
      | inr k =>
        change faceSector ((addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr k))) = faceSector (Sum.inr k)
        rcases k with ⟨kv, hkv⟩
        match kv with
        | 0 =>
          have h1 : (addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr ⟨0, hkv⟩)) = Sum.inr 7 := by
            dsimp only [addApex4E, addApex4N, addApex4NInv]; rw [dif_neg (by omega)]; rfl
          rw [h1]; rfl
        | 1 =>
          have h1 : (addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr ⟨1, hkv⟩)) = Sum.inr 4 := by
            dsimp only [addApex4E, addApex4N, addApex4NInv]; rw [dif_neg (by omega)]; rfl
          rw [h1]; rfl
        | 2 =>
          have h1 : (addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr ⟨2, hkv⟩)) = Sum.inr 5 := by
            dsimp only [addApex4E, addApex4N, addApex4NInv]; rw [dif_neg (by omega)]; rfl
          rw [h1]; rfl
        | 3 =>
          have h1 : (addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr ⟨3, hkv⟩)) = Sum.inr 6 := by
            dsimp only [addApex4E, addApex4N, addApex4NInv]; rw [dif_neg (by omega)]; rfl
          rw [h1]; rfl
        | 4 =>
          have h1 : (addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr ⟨4, hkv⟩)) = Sum.inl (c 0) := by
            dsimp only [addApex4E, addApex4N, addApex4NInv]; rw [dif_pos (by omega)]; rfl
          rw [h1, hsec_0 (c 0) ⟨0, hc.hk1, rfl⟩]; rfl
        | 5 =>
          have h1 : (addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr ⟨5, hkv⟩)) = Sum.inl (c 1) := by
            dsimp only [addApex4E, addApex4N, addApex4NInv]; rw [dif_pos (by omega)]; rfl
          rw [h1, hsec_1 (c 1) ⟨0, hc.hk2, by simp [hc.hd1]⟩]; rfl
        | 6 =>
          have h1 : (addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr ⟨6, hkv⟩)) = Sum.inl (c 2) := by
            dsimp only [addApex4E, addApex4N, addApex4NInv]; rw [dif_pos (by omega)]; rfl
          rw [h1, hsec_2 (c 2) ⟨0, hc.hk3, by simp [hc.hd2]⟩]; rfl
        | 7 =>
          have h1 : (addApex4N H c hc_inj).inv ((addApex4E H).inv (Sum.inr ⟨7, hkv⟩)) = Sum.inl (c 3) := by
            dsimp only [addApex4E, addApex4N, addApex4NInv]; rw [dif_pos (by omega)]; rfl
          rw [h1, hsec_3 (c 3) ⟨0, hc.hk4, by simp [hc.hd3]⟩]; rfl
        | _ + 8 => exact absurd hkv (by omega)
      | inl d =>
        rw [hH'_face_inl d]
        dsimp only [faceSector]
        by_cases h0 : ∃ t, t < hc.k1 ∧ Perm.iter H.face t (c 0) = d
        · rw [if_pos h0]
          obtain ⟨t, ht, htd⟩ := h0
          have hfd : H.face.f d = Perm.iter H.face (t + 1) (c 0) := by
            rw [← htd, ← perm_iter_succ_left]
          by_cases hlast : t + 1 = hc.k1
          · have hfd1 : H.face.f d = c 1 := by rw [hfd, hlast, hc.hd1]
            rw [hfd1, cornerIdx_c c hc_inj 1]
            rfl
          · have hlt1 : t + 1 < hc.k1 := by omega
            have hltL : t + 1 < L := by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega
            have hci : cornerIdx c (H.face.f d) = none := cornerIdx_eq_none_iff.mpr (fun m heq => by
              rw [hfd] at heq
              rcases m with ⟨mv, hm⟩
              match mv, hm with
              | 0, _ =>
                have := hc.inj_lt (t + 1) 0 hltL (by omega) heq; omega
              | 1, _ =>
                have := hc.inj_lt (t + 1) hc.k1 hltL (by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
                  (heq.trans hc.hd1.symm); omega
              | 2, _ =>
                have := hc.inj_lt (t + 1) (hc.k1 + hc.k2) hltL (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
                  (heq.trans hc.hd2.symm); omega
              | 3, _ =>
                have := hc.inj_lt (t + 1) (hc.k1 + hc.k2 + hc.k3) hltL (by have := hc.hk4; have := hc.hsum; omega)
                  (heq.trans hc.hd3.symm); omega)
            rw [hci]
            exact hsec_0 (H.face.f d) ⟨t + 1, hlt1, hfd.symm⟩
        · rw [if_neg h0]
          by_cases h1 : ∃ t, t < hc.k2 ∧ Perm.iter H.face (hc.k1 + t) (c 0) = d
          · rw [if_pos h1]
            obtain ⟨t, ht, htd⟩ := h1
            have hfd : H.face.f d = Perm.iter H.face (hc.k1 + (t + 1)) (c 0) := by
              rw [← htd, ← perm_iter_succ_left, show hc.k1 + t + 1 = hc.k1 + (t + 1) by omega]
            by_cases hlast : t + 1 = hc.k2
            · have hfd2 : H.face.f d = c 2 := by
                rw [hfd, hlast, hc.hd2]
              rw [hfd2, cornerIdx_c c hc_inj 2]
              rfl
            · have hlt2 : t + 1 < hc.k2 := by omega
              have hltL : hc.k1 + (t + 1) < L := by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega
              have hci : cornerIdx c (H.face.f d) = none := cornerIdx_eq_none_iff.mpr (fun m heq => by
                rw [hfd] at heq
                rcases m with ⟨mv, hm⟩
                match mv, hm with
                | 0, _ =>
                  have := hc.inj_lt _ 0 hltL (by omega) heq; have := hc.hk1; omega
                | 1, _ =>
                  have := hc.inj_lt _ hc.k1 hltL (by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
                    (heq.trans hc.hd1.symm); omega
                | 2, _ =>
                  have := hc.inj_lt _ (hc.k1 + hc.k2) hltL (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
                    (heq.trans hc.hd2.symm); omega
                | 3, _ =>
                  have := hc.inj_lt _ (hc.k1 + hc.k2 + hc.k3) hltL (by have := hc.hk4; have := hc.hsum; omega)
                    (heq.trans hc.hd3.symm); omega)
              rw [hci]
              exact hsec_1 (H.face.f d) ⟨t + 1, hlt2, hfd.symm⟩
          · rw [if_neg h1]
            by_cases h2 : ∃ t, t < hc.k3 ∧ Perm.iter H.face (hc.k1 + hc.k2 + t) (c 0) = d
            · rw [if_pos h2]
              obtain ⟨t, ht, htd⟩ := h2
              have hfd : H.face.f d = Perm.iter H.face (hc.k1 + hc.k2 + (t + 1)) (c 0) := by
                rw [← htd, ← perm_iter_succ_left, show hc.k1 + hc.k2 + t + 1 = hc.k1 + hc.k2 + (t + 1) by omega]
              by_cases hlast : t + 1 = hc.k3
              · have hfd3 : H.face.f d = c 3 := by rw [hfd, hlast, hc.hd3]
                rw [hfd3, cornerIdx_c c hc_inj 3]
                rfl
              · have hlt3 : t + 1 < hc.k3 := by omega
                have hltL : hc.k1 + hc.k2 + (t + 1) < L := by have := hc.hk4; have := hc.hsum; omega
                have hci : cornerIdx c (H.face.f d) = none := cornerIdx_eq_none_iff.mpr (fun m heq => by
                  rw [hfd] at heq
                  rcases m with ⟨mv, hm⟩
                  match mv, hm with
                  | 0, _ =>
                    have := hc.inj_lt _ 0 hltL (by omega) heq; have := hc.hk1; have := hc.hk2; omega
                  | 1, _ =>
                    have := hc.inj_lt _ hc.k1 hltL (by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
                      (heq.trans hc.hd1.symm); omega
                  | 2, _ =>
                    have := hc.inj_lt _ (hc.k1 + hc.k2) hltL (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
                      (heq.trans hc.hd2.symm); omega
                  | 3, _ =>
                    have := hc.inj_lt _ (hc.k1 + hc.k2 + hc.k3) hltL (by have := hc.hk4; have := hc.hsum; omega)
                      (heq.trans hc.hd3.symm); omega)
                rw [hci]
                exact hsec_2 (H.face.f d) ⟨t + 1, hlt3, hfd.symm⟩
            · rw [if_neg h2]
              by_cases h3 : ∃ t, t < hc.k4 ∧ Perm.iter H.face (hc.k1 + hc.k2 + hc.k3 + t) (c 0) = d
              · rw [if_pos h3]
                obtain ⟨t, ht, htd⟩ := h3
                have hfd : H.face.f d = Perm.iter H.face (hc.k1 + hc.k2 + hc.k3 + (t + 1)) (c 0) := by
                  rw [← htd, ← perm_iter_succ_left,
                    show hc.k1 + hc.k2 + hc.k3 + t + 1 = hc.k1 + hc.k2 + hc.k3 + (t + 1) by omega]
                by_cases hlast : t + 1 = hc.k4
                · have hfd0 : H.face.f d = c 0 := by
                    rw [hfd, hlast]
                    have hs : hc.k1 + hc.k2 + hc.k3 + hc.k4 = L := hc.hsum
                    rw [hs, hc.period]
                  rw [hfd0, cornerIdx_c c hc_inj 0]
                  rfl
                · have hlt4 : t + 1 < hc.k4 := by omega
                  have hltL : hc.k1 + hc.k2 + hc.k3 + (t + 1) < L := by have := hc.hsum; omega
                  have hci : cornerIdx c (H.face.f d) = none := cornerIdx_eq_none_iff.mpr (fun m heq => by
                    rw [hfd] at heq
                    rcases m with ⟨mv, hm⟩
                    match mv, hm with
                    | 0, _ =>
                      have := hc.inj_lt _ 0 hltL (by omega) heq; have := hc.hk1; have := hc.hk2; have := hc.hk3; omega
                    | 1, _ =>
                      have := hc.inj_lt _ hc.k1 hltL (by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
                        (heq.trans hc.hd1.symm); omega
                    | 2, _ =>
                      have := hc.inj_lt _ (hc.k1 + hc.k2) hltL (by have := hc.hk3; have := hc.hk4; have := hc.hsum; omega)
                        (heq.trans hc.hd2.symm); omega
                    | 3, _ =>
                      have := hc.inj_lt _ (hc.k1 + hc.k2 + hc.k3) hltL (by have := hc.hk4; have := hc.hsum; omega)
                        (heq.trans hc.hd3.symm); omega)
                  rw [hci]
                  exact hsec_3 (H.face.f d) ⟨t + 1, hlt4, hfd.symm⟩
              · rw [if_neg h3]
                have hnotF : ¬ SameOrbit H.face (c 0) d := by
                  rintro ⟨m, hmd⟩
                  have hqm := Nat.div_add_mod m L
                  have hL_pos : 0 < L := by have := hc.hk1; have := hc.hsum; omega
                  have hr_lt : m % L < L := Nat.mod_lt m hL_pos
                  have hiter_mod : Perm.iter H.face (m % L) (c 0) = d := by
                    have hmul : m = (m / L) * L + m % L :=
                      (Nat.div_add_mod m L).symm.trans (by rw [Nat.mul_comm])
                    symm
                    calc d = Perm.iter H.face m (c 0) := hmd.symm
                      _ = Perm.iter H.face ((m / L) * L + m % L) (c 0) :=
                          congrArg (fun k => Perm.iter H.face k (c 0)) hmul
                      _ = Perm.iter H.face (m % L) (c 0) :=
                          perm_iter_mul_add_eq H.face hc.period (m / L) (m % L)
                  have hsum := hc.hsum
                  by_cases hlt1 : m % L < hc.k1
                  · exact h0 ⟨m % L, hlt1, hiter_mod⟩
                  · by_cases hlt2 : m % L < hc.k1 + hc.k2
                    · exact h1 ⟨m % L - hc.k1, by omega, by rw [show hc.k1 + (m % L - hc.k1) = m % L by omega]; exact hiter_mod⟩
                    · by_cases hlt3 : m % L < hc.k1 + hc.k2 + hc.k3
                      · exact h2 ⟨m % L - (hc.k1 + hc.k2), by omega, by rw [show hc.k1 + hc.k2 + (m % L - (hc.k1 + hc.k2)) = m % L by omega]; exact hiter_mod⟩
                      · exact h3 ⟨m % L - (hc.k1 + hc.k2 + hc.k3), by omega, by rw [show hc.k1 + hc.k2 + hc.k3 + (m % L - (hc.k1 + hc.k2 + hc.k3)) = m % L by omega]; exact hiter_mod⟩
                have hnotF' : ¬ SameOrbit H.face (c 0) (H.face.f d) := fun h =>
                  hnotF (sameOrbit_trans H.face h (sameOrbit_symm_of_complete H.face darts h_all (sameOrbit_step H.face rfl)))
                have hci : cornerIdx c (H.face.f d) = none := cornerIdx_eq_none_iff.mpr (fun m heq => by
                  apply hnotF'; rw [heq]
                  rcases m with ⟨mv, hm⟩
                  match mv, hm with
                  | 0, _ => exact sameOrbit_refl _ _
                  | 1, _ => exact (cyclicOrder4_sameOrbit hc).1
                  | 2, _ => exact (cyclicOrder4_sameOrbit hc).2.1
                  | 3, _ => exact (cyclicOrder4_sameOrbit hc).2.2)
                rw [hci]
                dsimp only [faceSector]
                have hn0 : ¬ ∃ t, t < hc.k1 ∧ Perm.iter H.face t (c 0) = H.face.f d := by
                  rintro ⟨t, _, ht⟩; exact hnotF' ⟨t, ht⟩
                have hn1 : ¬ ∃ t, t < hc.k2 ∧ Perm.iter H.face (hc.k1 + t) (c 0) = H.face.f d := by
                  rintro ⟨t, _, ht⟩; exact hnotF' ⟨hc.k1 + t, ht⟩
                have hn2 : ¬ ∃ t, t < hc.k3 ∧ Perm.iter H.face (hc.k1 + hc.k2 + t) (c 0) = H.face.f d := by
                  rintro ⟨t, _, ht⟩; exact hnotF' ⟨hc.k1 + hc.k2 + t, ht⟩
                have hn3 : ¬ ∃ t, t < hc.k4 ∧ Perm.iter H.face (hc.k1 + hc.k2 + hc.k3 + t) (c 0) = H.face.f d := by
                  rintro ⟨t, _, ht⟩; exact hnotF' ⟨hc.k1 + hc.k2 + hc.k3 + t, ht⟩
                rw [if_neg hn0, if_neg hn1, if_neg hn2, if_neg hn3]
    have hF_in4 : 4 ≤ countOrbits H'.face darts'.length (darts'.filter inF) := by
      let P0 : H'.Dart → Bool := fun x => decide (faceSector x = 0)
      let P1 : H'.Dart → Bool := fun x => decide (faceSector x = 1)
      let P2 : H'.Dart → Bool := fun x => decide (faceSector x = 2)
      have hP0 : ∀ x, P0 (H'.face.f x) = P0 x := fun x => by simp [P0, hsec_inv x]
      have hP1 : ∀ x, P1 (H'.face.f x) = P1 x := fun x => by simp [P1, hsec_inv x]
      have hP2 : ∀ x, P2 (H'.face.f x) = P2 x := fun x => by simp [P2, hsec_inv x]
      have hp0 := countOrbits_partition_of_closed H'.face darts'.length (darts'.filter inF) P0 hP0
      have hp1 := countOrbits_partition_of_closed H'.face darts'.length ((darts'.filter inF).filter (fun x => !P0 x)) P1 hP1
      have hp2 := countOrbits_partition_of_closed H'.face darts'.length
        (((darts'.filter inF).filter (fun x => !P0 x)).filter (fun x => !P1 x)) P2 hP2
      have hge0 : 1 ≤ countOrbits H'.face darts'.length ((darts'.filter inF).filter P0) := by
        have hm : (Sum.inr 4 : H'.Dart) ∈ (darts'.filter inF).filter P0 :=
          List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨h_all' (Sum.inr 4), rfl⟩, by simp [P0, faceSector]; decide⟩
        cases hfl : (darts'.filter inF).filter P0 with
        | nil => rw [hfl] at hm; exact absurd hm List.not_mem_nil
        | cons u us => exact countOrbits_pos_cons _ _ u us
      have hge1 : 1 ≤ countOrbits H'.face darts'.length (((darts'.filter inF).filter (fun x => !P0 x)).filter P1) := by
        have hm : (Sum.inr 5 : H'.Dart) ∈ ((darts'.filter inF).filter (fun x => !P0 x)).filter P1 :=
          List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨h_all' (Sum.inr 5), rfl⟩,
            by simp [P0, faceSector]; decide⟩, by simp [P1, faceSector]; decide⟩
        cases hfl : ((darts'.filter inF).filter (fun x => !P0 x)).filter P1 with
        | nil => rw [hfl] at hm; exact absurd hm List.not_mem_nil
        | cons u us => exact countOrbits_pos_cons _ _ u us
      have hge2 : 1 ≤ countOrbits H'.face darts'.length
          ((((darts'.filter inF).filter (fun x => !P0 x)).filter (fun x => !P1 x)).filter P2) := by
        have hm : (Sum.inr 6 : H'.Dart) ∈ (((darts'.filter inF).filter (fun x => !P0 x)).filter (fun x => !P1 x)).filter P2 :=
          List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_filter.mpr
            ⟨List.mem_filter.mpr ⟨h_all' (Sum.inr 6), rfl⟩,
              by simp [P0, faceSector]; decide⟩, by simp [P1, faceSector]; decide⟩,
            by simp [P2, faceSector]; decide⟩
        cases hfl : (((darts'.filter inF).filter (fun x => !P0 x)).filter (fun x => !P1 x)).filter P2 with
        | nil => rw [hfl] at hm; exact absurd hm List.not_mem_nil
        | cons u us => exact countOrbits_pos_cons _ _ u us
      have hge3 : 1 ≤ countOrbits H'.face darts'.length
          ((((darts'.filter inF).filter (fun x => !P0 x)).filter (fun x => !P1 x)).filter (fun x => !P2 x)) := by
        have hm : (Sum.inr 7 : H'.Dart) ∈
            (((darts'.filter inF).filter (fun x => !P0 x)).filter (fun x => !P1 x)).filter (fun x => !P2 x) :=
          List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨List.mem_filter.mpr
            ⟨List.mem_filter.mpr ⟨h_all' (Sum.inr 7), rfl⟩,
              by simp [P0, faceSector]; decide⟩, by simp [P1, faceSector]; decide⟩,
            by simp [P2, faceSector]; decide⟩
        cases hfl : (((darts'.filter inF).filter (fun x => !P0 x)).filter (fun x => !P1 x)).filter (fun x => !P2 x) with
        | nil => rw [hfl] at hm; exact absurd hm List.not_mem_nil
        | cons u us => exact countOrbits_pos_cons _ _ u us
      omega
    omega
  have hg'_zero : genusDeficit H'.hypermapToTriple darts'.length darts' = 0 := by
    have hp1 : genusDeficit H.hypermapToTriple darts.length darts = 0 := hp.1
    have hlen'_eq : darts'.length = darts.length + 8 := h_len'
    dsimp only [genusDeficit, hypermapToTriple] at hp1 h_nonneg' ⊢
    omega
  exact (eulerChar_le_two_mul_numComponents H' darts' h_nd' h_all' (Nat.le_refl _)).2.mpr ⟨hg'_zero, h_efree'⟩

end AddFaceApex4

section AlternatingWalksIntersection

private theorem WalkENIn.eLen_eq_mp {D : Type} {e n : Perm D} {P : D → Prop}
    {x y z : D} (h : y = z) (eqT : WalkENIn e n P x y = WalkENIn e n P x z)
    (w : WalkENIn e n P x y) :
    (eqT.mp w).eLen = w.eLen := by
  subst h; rfl

theorem WalkENIn.eLen_revOfInv {D : Type} {e n : Perm D} (he : ∀ z, e.f (e.f z) = z)
    {P : D → Prop} {x y : D} (w : WalkENIn e n P x y) :
    (w.revOfInv he).eLen = w.eLen := by
  induction w with
  | refl _ => rfl
  | @n_fwd y' w' hy ih =>
    simp only [WalkENIn.revOfInv, WalkENIn.eLen_trans, ih, WalkENIn.eLen]
    have h0 : (by
        have h1 : WalkENIn e n P (n.f y') (n.inv (n.f y')) :=
          WalkENIn.n_bwd (.refl hy) (by rw [n.left_inv]; exact walkENIn_right w')
        rwa [n.left_inv] at h1 : WalkENIn e n P (n.f y') y').eLen = 0 :=
      WalkENIn.eLen_eq_mp (n.left_inv y') _ _
    rw [h0]; omega
  | @n_bwd y' w' hy ih =>
    simp only [WalkENIn.revOfInv, WalkENIn.eLen_trans, ih, WalkENIn.eLen]
    have h0 : (by
        have h1 : WalkENIn e n P (n.inv y') (n.f (n.inv y')) :=
          WalkENIn.n_fwd (.refl hy) (by rw [n.right_inv]; exact walkENIn_right w')
        rwa [n.right_inv] at h1 : WalkENIn e n P (n.inv y') y').eLen = 0 :=
      WalkENIn.eLen_eq_mp (n.right_inv y') _ _
    rw [h0]; omega
  | @e_step y' w' hy ih =>
    simp only [WalkENIn.revOfInv, WalkENIn.eLen_trans, ih, WalkENIn.eLen]
    have h1_len : (by
        have h1 : WalkENIn e n P (e.f y') (e.f (e.f y')) :=
          WalkENIn.e_step (.refl hy) (by rw [he]; exact walkENIn_right w')
        rwa [he] at h1 : WalkENIn e n P (e.f y') y').eLen = 1 :=
      WalkENIn.eLen_eq_mp (he y') _ _
    rw [h1_len]; omega

/-- Vertex-orbit membership predicate along a `WalkENIn` walk. -/
def WalkENIn.HitsVertex {D : Type} {e n : Perm D} {P : D → Prop} {x y : D} :
    WalkENIn e n P x y → D → Prop
  | .refl _, z => SameOrbit n x z
  | .n_fwd w _, z => w.HitsVertex z
  | .n_bwd w _, z => w.HitsVertex z
  | .e_step (y := v) w _, z => w.HitsVertex z ∨ SameOrbit n (e.f v) z

private theorem WalkENIn.hitsVertex_eq_mp {D : Type} {e n : Perm D} {P : D → Prop}
    {x y z : D} (h : y = z) (eqT : WalkENIn e n P x y = WalkENIn e n P x z)
    (w : WalkENIn e n P x y) (u : D) :
    (eqT.mp w).HitsVertex u ↔ w.HitsVertex u := by
  subst h; rfl

theorem pred_of_sameOrbit {D : Type} {n : Perm D} {P : D → Prop}
    (hP : ∀ u, P (n.f u) ↔ P u) {x z : D} (hx : P x) (h : SameOrbit n x z) : P z := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => exact hx
  | succ k ih => rw [perm_iter_succ_left]; exact (hP _).mpr ih

theorem WalkENIn.hitsVertex_imp {D : Type} {e n : Perm D} {P : D → Prop}
    (hP : ∀ u, P (n.f u) ↔ P u) {x y : D} (w : WalkENIn e n P x y) {z : D}
    (hz : w.HitsVertex z) : P z := by
  induction w with
  | refl hx => exact pred_of_sameOrbit hP hx hz
  | n_fwd _ _ ih => exact ih hz
  | n_bwd _ _ ih => exact ih hz
  | e_step _ hy ih =>
    rcases hz with hz' | hOrb
    · exact ih hz'
    · exact pred_of_sameOrbit hP hy hOrb

theorem WalkENIn.hitsVertex_of_sameOrbit {D : Type} {e n : Perm D} {P : D → Prop}
    {x y : D} (w : WalkENIn e n P x y) {z u : D} (hz : w.HitsVertex z) (hzu : SameOrbit n z u) :
    w.HitsVertex u := by
  induction w with
  | refl _ => exact sameOrbit_trans n hz hzu
  | n_fwd _ _ ih => exact ih hz
  | n_bwd _ _ ih => exact ih hz
  | e_step _ _ ih =>
    rcases hz with hz' | hOrb
    · exact .inl (ih hz')
    · exact .inr (sameOrbit_trans n hOrb hzu)

theorem WalkENIn.hitsVertex_left {D : Type} {e n : Perm D} {P : D → Prop}
    {x y : D} (w : WalkENIn e n P x y) : w.HitsVertex x := by
  induction w with
  | refl _ => exact sameOrbit_refl n x
  | n_fwd _ _ ih => exact ih
  | n_bwd _ _ ih => exact ih
  | e_step _ _ ih => exact .inl ih

theorem WalkENIn.hitsVertex_right {D : Type} {e n : Perm D}
    (n_symm : ∀ {a b : D}, SameOrbit n a b → SameOrbit n b a)
    {P : D → Prop} {x y : D} (w : WalkENIn e n P x y) : w.HitsVertex y := by
  induction w with
  | refl _ => exact sameOrbit_refl n x
  | @n_fwd y' w' _ ih => exact w'.hitsVertex_of_sameOrbit ih (sameOrbit_step n rfl)
  | @n_bwd y' w' _ ih =>
    have hstep : SameOrbit n (n.inv y') y' := by
      have h1 : SameOrbit n (n.inv y') (n.f (n.inv y')) := sameOrbit_step n rfl
      rwa [n.right_inv] at h1
    exact w'.hitsVertex_of_sameOrbit ih (n_symm hstep)
  | e_step _ _ => exact .inr (sameOrbit_refl n _)

theorem WalkENIn.hitsVertex_trans {D : Type} {e n : Perm D}
    (n_symm : ∀ {a b : D}, SameOrbit n a b → SameOrbit n b a)
    {P : D → Prop} {x y w_end : D}
    (w1 : WalkENIn e n P x y) (w2 : WalkENIn e n P y w_end) {z : D} :
    (w1.trans w2).HitsVertex z ↔ w1.HitsVertex z ∨ w2.HitsVertex z := by
  induction w2 with
  | refl _ =>
    constructor
    · intro h; exact .inl h
    · rintro (h | h)
      · exact h
      · exact w1.hitsVertex_of_sameOrbit (w1.hitsVertex_right n_symm) h
  | n_fwd _ _ ih => exact ih
  | n_bwd _ _ ih => exact ih
  | @e_step v w' _ ih =>
    constructor
    · rintro (h | hOrb)
      · rcases ih.mp h with h1 | h2
        · exact .inl h1
        · exact .inr (.inl h2)
      · exact .inr (.inr hOrb)
    · rintro (h1 | h2)
      · exact .inl (ih.mpr (.inl h1))
      · rcases h2 with h2' | hOrb
        · exact .inl (ih.mpr (.inr h2'))
        · exact .inr hOrb

theorem WalkENIn.hitsVertex_revOfInv {D : Type} {e n : Perm D}
    (he : ∀ z, e.f (e.f z) = z)
    (n_symm : ∀ {a b : D}, SameOrbit n a b → SameOrbit n b a)
    {P : D → Prop} {x y : D} (w : WalkENIn e n P x y) {z : D} :
    (w.revOfInv he).HitsVertex z ↔ w.HitsVertex z := by
  induction w with
  | refl _ => exact Iff.rfl
  | @n_fwd v w' hy ih =>
    have ih' : (w'.revOfInv he).HitsVertex z ↔ w'.HitsVertex z := ih
    simp only [WalkENIn.revOfInv]
    rw [WalkENIn.hitsVertex_trans n_symm, propext ih']
    have hstep_hv :
        (by
          have h1 : WalkENIn e n P (n.f v) (n.inv (n.f v)) :=
            WalkENIn.n_bwd (.refl hy) (by rw [n.left_inv]; exact walkENIn_right w')
          rwa [n.left_inv] at h1 : WalkENIn e n P (n.f v) v).HitsVertex z ↔
        SameOrbit n (n.f v) z :=
      WalkENIn.hitsVertex_eq_mp (n.left_inv v) _ _ z
    rw [hstep_hv]
    constructor
    · rintro (hOrb | hw')
      · have hstep : SameOrbit n v (n.f v) := sameOrbit_step n rfl
        exact w'.hitsVertex_of_sameOrbit (w'.hitsVertex_right n_symm) (sameOrbit_trans n hstep hOrb)
      · exact hw'
    · intro hw'; exact .inr hw'
  | @n_bwd v w' hy ih =>
    have ih' : (w'.revOfInv he).HitsVertex z ↔ w'.HitsVertex z := ih
    simp only [WalkENIn.revOfInv]
    rw [WalkENIn.hitsVertex_trans n_symm, propext ih']
    have hstep_hv :
        (by
          have h1 : WalkENIn e n P (n.inv v) (n.f (n.inv v)) :=
            WalkENIn.n_fwd (.refl hy) (by rw [n.right_inv]; exact walkENIn_right w')
          rwa [n.right_inv] at h1 : WalkENIn e n P (n.inv v) v).HitsVertex z ↔
        SameOrbit n (n.inv v) z :=
      WalkENIn.hitsVertex_eq_mp (n.right_inv v) _ _ z
    rw [hstep_hv]
    constructor
    · rintro (hOrb | hw')
      · have hstep : SameOrbit n (n.inv v) v := by
          have h1 : SameOrbit n (n.inv v) (n.f (n.inv v)) := sameOrbit_step n rfl
          rwa [n.right_inv] at h1
        exact w'.hitsVertex_of_sameOrbit (w'.hitsVertex_right n_symm) (sameOrbit_trans n (n_symm hstep) hOrb)
      · exact hw'
    · intro hw'; exact .inr hw'
  | @e_step v w' hy ih =>
    have ih' : (w'.revOfInv he).HitsVertex z ↔ w'.HitsVertex z := ih
    simp only [WalkENIn.revOfInv]
    rw [WalkENIn.hitsVertex_trans n_symm, propext ih']
    have hstep_hv :
        (by
          have h1 : WalkENIn e n P (e.f v) (e.f (e.f v)) :=
            WalkENIn.e_step (.refl hy) (by rw [he]; exact walkENIn_right w')
          rwa [he] at h1 : WalkENIn e n P (e.f v) v).HitsVertex z ↔
        SameOrbit n (e.f v) z ∨ SameOrbit n (e.f (e.f v)) z :=
      WalkENIn.hitsVertex_eq_mp (he v) _ _ z
    rw [hstep_hv]
    constructor
    · rintro ((h1 | h2) | hw')
      · exact .inr h1
      · rw [he] at h2
        exact .inl (w'.hitsVertex_of_sameOrbit (w'.hitsVertex_right n_symm) h2)
      · exact .inl hw'
    · rintro (hw' | hOrb)
      · exact .inr hw'
      · exact .inl (.inl hOrb)

def WalkENIn.toHitsVertex {D : Type} {e n : Perm D}
    (n_symm : ∀ {a b : D}, SameOrbit n a b → SameOrbit n b a)
    {P : D → Prop} (hP : ∀ u, P (n.f u) ↔ P u) {x y : D} :
    (w : WalkENIn e n P x y) → WalkENIn e n (fun z => P z ∧ w.HitsVertex z) x y
  | .refl hx => .refl ⟨hx, sameOrbit_refl n x⟩
  | .n_fwd w hy =>
    .n_fwd (w.toHitsVertex n_symm hP)
      ⟨hy, w.hitsVertex_of_sameOrbit (w.hitsVertex_right n_symm) (sameOrbit_step n rfl)⟩
  | .n_bwd (y := v) w hy =>
    .n_bwd (w.toHitsVertex n_symm hP) ⟨hy, w.hitsVertex_of_sameOrbit (w.hitsVertex_right n_symm)
      (n_symm (by
        have h1 : SameOrbit n (n.inv v) (n.f (n.inv v)) := sameOrbit_step n rfl
        rwa [n.right_inv] at h1))⟩
  | .e_step (y := v) w hy =>
    .e_step ((w.toHitsVertex n_symm hP).mapPred (fun _ ⟨hp, hh⟩ => ⟨hp, .inl hh⟩))
      ⟨hy, .inr (sameOrbit_refl n (e.f v))⟩

theorem WalkENIn.reachENIn_hitsVertex {D : Type} {e n : Perm D}
    (n_symm : ∀ {a b : D}, SameOrbit n a b → SameOrbit n b a)
    {P : D → Prop} (hP : ∀ u, P (n.f u) ↔ P u) {x y : D}
    (w : WalkENIn e n P x y) {z : D} (hz : w.HitsVertex z) :
    ReachENIn e n (fun u => P u ∧ w.HitsVertex u) x z := by
  induction w generalizing z with
  | refl hx =>
    obtain ⟨k, rfl⟩ := hz
    have hP' : ∀ u, (P u ∧ SameOrbit n x u) ↔ (P (n.f u) ∧ SameOrbit n x (n.f u)) := fun u =>
      ⟨fun ⟨hp, hs⟩ => ⟨(hP u).mpr hp, sameOrbit_trans n hs (sameOrbit_step n rfl)⟩,
       fun ⟨hp, hs⟩ => ⟨(hP u).mp hp, sameOrbit_trans n hs (n_symm (sameOrbit_step n rfl))⟩⟩
    exact nonempty_walkENIn_iff_reachENIn.mp ⟨WalkENIn.ofSameOrbit e n (fun u => P u ∧ SameOrbit n x u)
      (fun u => (hP' u).symm) x ⟨hx, sameOrbit_refl n x⟩ k⟩
  | n_fwd _ _ ih => exact ih hz
  | n_bwd _ _ ih => exact ih hz
  | @e_step v w' hy ih =>
    rcases hz with hz' | hOrb
    · exact reachENIn_mono (fun _ ⟨hp, hh⟩ => ⟨hp, .inl hh⟩) (ih hz')
    · have hxv : ReachENIn e n (fun u => P u ∧ (WalkENIn.e_step w' hy).HitsVertex u) x v :=
        reachENIn_mono (fun _ ⟨hp, hh⟩ => ⟨hp, .inl hh⟩) (ih (w'.hitsVertex_right n_symm))
      have hve : ReachENIn e n (fun u => P u ∧ (WalkENIn.e_step w' hy).HitsVertex u) x (e.f v) :=
        .step_e hxv ⟨hy, .inr (sameOrbit_refl n (e.f v))⟩
      obtain ⟨k, rfl⟩ := hOrb
      have hP' : ∀ u, (P (n.f u) ∧ (w'.HitsVertex (n.f u) ∨ SameOrbit n (e.f v) (n.f u))) ↔
          (P u ∧ (w'.HitsVertex u ∨ SameOrbit n (e.f v) u)) := fun u => by
        constructor
        · rintro ⟨hp, hh | ho⟩
          · exact ⟨(hP u).mp hp, .inl (w'.hitsVertex_of_sameOrbit hh (n_symm (sameOrbit_step n rfl)))⟩
          · exact ⟨(hP u).mp hp, .inr (sameOrbit_trans n ho (n_symm (sameOrbit_step n rfl)))⟩
        · rintro ⟨hp, hh | ho⟩
          · exact ⟨(hP u).mpr hp, .inl (w'.hitsVertex_of_sameOrbit hh (sameOrbit_step n rfl))⟩
          · exact ⟨(hP u).mpr hp, .inr (sameOrbit_trans n ho (sameOrbit_step n rfl))⟩
      have hez : ReachENIn e n (fun u => P u ∧ (WalkENIn.e_step w' hy).HitsVertex u)
          (e.f v) (Perm.iter n k (e.f v)) :=
        nonempty_walkENIn_iff_reachENIn.mp ⟨WalkENIn.ofSameOrbit e n
          (fun u => P u ∧ (w'.HitsVertex u ∨ SameOrbit n (e.f v) u)) hP' (e.f v)
          ⟨hy, .inr (sameOrbit_refl n (e.f v))⟩ k⟩
      exact reachENIn_trans hve hez

theorem WalkENIn.splitAtHit {D : Type} {e n : Perm D}
    (n_symm : ∀ {a b : D}, SameOrbit n a b → SameOrbit n b a)
    {P : D → Prop} (hP : ∀ u, P (n.f u) ↔ P u) {x y : D}
    (w : WalkENIn e n P x y) {z : D} (hz : w.HitsVertex z) :
    ∃ (w1 : WalkENIn e n P x z) (w2 : WalkENIn e n P z y), w1.eLen + w2.eLen = w.eLen := by
  have hcast_len : ∀ {a b c : D} (h : b = c) (w' : WalkENIn e n P a b), (h ▸ w').eLen = w'.eLen := by
    intro a b c h w'; subst h; rfl
  induction w with
  | refl hx =>
    obtain ⟨k1, hk1⟩ := hz
    obtain ⟨k2, hk2⟩ := n_symm ⟨k1, hk1⟩
    let w1 : WalkENIn e n P x z := hk1 ▸ WalkENIn.ofSameOrbit e n P hP x hx k1
    let w2 : WalkENIn e n P z x := hk2 ▸ WalkENIn.ofSameOrbit e n P hP z (pred_of_sameOrbit hP hx ⟨k1, hk1⟩) k2
    refine ⟨w1, w2, ?_⟩
    have hl1 : w1.eLen = 0 := by
      dsimp only [w1]; rw [hcast_len hk1, WalkENIn.eLen_ofSameOrbit]
    have hl2 : w2.eLen = 0 := by
      dsimp only [w2]; rw [hcast_len hk2, WalkENIn.eLen_ofSameOrbit]
    rw [hl1, hl2]; rfl
  | n_fwd w' hy ih =>
    obtain ⟨w1, w2, hlen⟩ := ih hz
    exact ⟨w1, .n_fwd w2 hy, hlen⟩
  | n_bwd w' hy ih =>
    obtain ⟨w1, w2, hlen⟩ := ih hz
    exact ⟨w1, .n_bwd w2 hy, hlen⟩
  | @e_step v w' hy ih =>
    rcases hz with hz' | hOrb
    · obtain ⟨w1, w2, hlen⟩ := ih hz'
      refine ⟨w1, .e_step w2 hy, ?_⟩
      simp only [WalkENIn.eLen]; omega
    · obtain ⟨k1, hk1⟩ := hOrb
      obtain ⟨k2, hk2⟩ := n_symm ⟨k1, hk1⟩
      let w1 : WalkENIn e n P x z :=
        (WalkENIn.e_step w' hy).trans (hk1 ▸ WalkENIn.ofSameOrbit e n P hP (e.f v) hy k1)
      let w2 : WalkENIn e n P z (e.f v) :=
        hk2 ▸ WalkENIn.ofSameOrbit e n P hP z (pred_of_sameOrbit hP hy ⟨k1, hk1⟩) k2
      refine ⟨w1, w2, ?_⟩
      have hl1 : w1.eLen = w'.eLen + 1 := by
        dsimp only [w1]
        rw [WalkENIn.eLen_trans, hcast_len hk1, WalkENIn.eLen_ofSameOrbit]
        simp [WalkENIn.eLen]
      have hl2 : w2.eLen = 0 := by
        dsimp only [w2]; rw [hcast_len hk2, WalkENIn.eLen_ofSameOrbit]
      rw [hl1, hl2]; simp [WalkENIn.eLen]

theorem WalkENIn.splitFirstHit_hitsVertex {D : Type} {e n : Perm D} {P : D → Prop}
    (Q : D → Prop) [DecidablePred Q] (hQn : ∀ z, Q (n.f z) ↔ Q z)
    {x y : D} (hx_not : ¬ Q x) (w : WalkENIn e n P x y) :
    match w.splitFirstHit Q hQn hx_not with
    | .inl ⟨w_avoid, _⟩ => ∀ z, w_avoid.HitsVertex z → w.HitsVertex z
    | .inr ⟨_, _, _, w1, _, _⟩ => ∀ z, w1.HitsVertex z → w.HitsVertex z := by
  induction w with
  | refl _ => intro z hz; exact hz
  | n_fwd w' hy ih =>
    dsimp only [WalkENIn.splitFirstHit]
    cases h : w'.splitFirstHit Q hQn hx_not with
    | inl p =>
      rcases p with ⟨w_avoid, hlen⟩
      have ih' := ih; rw [h] at ih'
      intro z hz; exact ih' z hz
    | inr p =>
      rcases p with ⟨m, m', hinfo, w1, w2, hlen⟩
      have ih' := ih; rw [h] at ih'
      intro z hz; exact ih' z hz
  | n_bwd w' hy ih =>
    dsimp only [WalkENIn.splitFirstHit]
    cases h : w'.splitFirstHit Q hQn hx_not with
    | inl p =>
      rcases p with ⟨w_avoid, hlen⟩
      have ih' := ih; rw [h] at ih'
      intro z hz; exact ih' z hz
    | inr p =>
      rcases p with ⟨m, m', hinfo, w1, w2, hlen⟩
      have ih' := ih; rw [h] at ih'
      intro z hz; exact ih' z hz
  | @e_step v w' hy ih =>
    dsimp only [WalkENIn.splitFirstHit]
    cases h : w'.splitFirstHit Q hQn hx_not with
    | inl p =>
      rcases p with ⟨w_avoid, hlen⟩
      have ih' := ih; rw [h] at ih'
      by_cases hQ : Q (e.f v)
      · simp only [hQ, ↓reduceDIte]
        intro z hz; exact .inl (ih' z hz)
      · simp only [hQ, ↓reduceDIte]
        rintro z (hz | hOrb)
        · exact .inl (ih' z hz)
        · exact .inr hOrb
    | inr p =>
      rcases p with ⟨m, m', hinfo, w1, w2, hlen⟩
      have ih' := ih; rw [h] at ih'
      intro z hz; exact .inl (ih' z hz)

def firstIndexRel (P : Nat → Prop) [DecidablePred P] (start : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 => if P start then some start else firstIndexRel P (start + 1) fuel

theorem firstIndexRel_some_of_hit (P : Nat → Prop) [DecidablePred P] :
    ∀ (fuel start m : Nat), m < fuel → P (start + m) →
      ∃ r, firstIndexRel P start fuel = some r
  | 0, _, _, hm, _ => absurd hm (by omega)
  | fuel + 1, start, m, hm, hP => by
    dsimp only [firstIndexRel]
    by_cases hPs : P start
    · simp only [hPs, ↓reduceIte]; exact ⟨start, rfl⟩
    · simp only [hPs, ↓reduceIte]
      cases m with
      | zero => simp at hP; exact absurd hP hPs
      | succ m' =>
        have hP' : P ((start + 1) + m') := by rwa [show start + 1 + m' = start + (m' + 1) by omega]
        exact firstIndexRel_some_of_hit P fuel (start + 1) m' (by omega) hP'

theorem firstIndexRel_spec (P : Nat → Prop) [DecidablePred P] :
    ∀ (fuel start r : Nat), firstIndexRel P start fuel = some r →
      start ≤ r ∧ r < start + fuel ∧ P r ∧ (∀ j, start ≤ j → j < r → ¬ P j)
  | 0, _, _, h => by cases h
  | fuel + 1, start, r, h => by
    dsimp only [firstIndexRel] at h
    by_cases hPs : P start
    · simp only [hPs, ↓reduceIte] at h
      cases h
      exact ⟨Nat.le_refl _, by omega, hPs, fun j hj1 hj2 => by omega⟩
    · simp only [hPs, ↓reduceIte] at h
      obtain ⟨h1, h2, h3, h4⟩ := firstIndexRel_spec P fuel (start + 1) r h
      refine ⟨by omega, by omega, h3, fun j hj1 hj2 => ?_⟩
      by_cases hj : j = start
      · subst hj; exact hPs
      · exact h4 j (by omega) hj2

theorem exists_min_hit_lt {D : Type} (p : Perm D) (d0 d1 : D)
    (k : Nat) (hk : 1 ≤ k) (h_end : Perm.iter p k d0 = d1)
    (Q : D → Prop) [DecidablePred Q] (h_not : ¬ Q d0) (h_hit : Q d1) :
    ∃ t0 : Nat, t0 < k ∧ Q (Perm.iter p (t0 + 1) d0) ∧ ∀ t, t ≤ t0 → ¬ Q (Perm.iter p t d0) := by
  have hk_eq : Perm.iter p (1 + (k - 1)) d0 = d1 := by rwa [show 1 + (k - 1) = k by omega]
  obtain ⟨r, hr⟩ := firstIndexRel_some_of_hit (fun t => Q (Perm.iter p t d0)) k 1 (k - 1) (by omega)
    (by rw [hk_eq]; exact h_hit)
  obtain ⟨hr1, hr2, hrP, hr_min⟩ := firstIndexRel_spec (fun t => Q (Perm.iter p t d0)) k 1 r hr
  refine ⟨r - 1, by omega, by rwa [show r - 1 + 1 = r by omega], fun t ht => ?_⟩
  cases t with
  | zero => exact h_not
  | succ t' => exact hr_min (t' + 1) (by omega) (by omega)

def cyclicOrder4_sub0_of_0_k1 {D : Type} (p : Perm D) {L : Nat} {d0 d1 d2 d3 : D}
    (hc : CyclicOrder4 p L d0 d1 d2 d3) {t : Nat} (ht0 : 1 ≤ t) (htk : t < hc.k1) :
    CyclicOrder4 p L d0 (Perm.iter p t d0) d2 d3 where
  inj_lt := hc.inj_lt
  period := hc.period
  k1 := t
  k2 := hc.k1 - t + hc.k2
  k3 := hc.k3
  k4 := hc.k4
  hk1 := ht0
  hk2 := by have := hc.hk2; omega
  hk3 := hc.hk3
  hk4 := hc.hk4
  hsum := by have := hc.hsum; omega
  hd1 := rfl
  hd2 := by rw [show t + (hc.k1 - t + hc.k2) = hc.k1 + hc.k2 by omega]; exact hc.hd2
  hd3 := by rw [show t + (hc.k1 - t + hc.k2) + hc.k3 = hc.k1 + hc.k2 + hc.k3 by omega]; exact hc.hd3

def cyclicOrder4_sub1_of_0_k1 {D : Type} (p : Perm D) {L : Nat} {d0 d1 d2 d3 : D}
    (hc : CyclicOrder4 p L d0 d1 d2 d3) {t : Nat} (ht0 : 1 ≤ t) (htk : t < hc.k1) :
    CyclicOrder4 p L (Perm.iter p t d0) d1 d2 d3 where
  inj_lt := by
    intro i j hi hj heq
    rw [← perm_iter_add, ← perm_iter_add] at heq
    have htL : t < L := by have := hc.hk2; have := hc.hk3; have := hc.hk4; have := hc.hsum; omega
    have hshift : ∀ m, m < L → ∃ m', m' < L ∧ Perm.iter p (m + t) d0 = Perm.iter p m' d0 ∧
        (m + t < L → m' = m + t) ∧ (L ≤ m + t → m' = m + t - L) := by
      intro m hm
      by_cases hm_lt : m + t < L
      · exact ⟨m + t, hm_lt, rfl, fun _ => rfl, fun hle => by omega⟩
      · refine ⟨m + t - L, by omega, ?_, fun hlt => by omega, fun _ => rfl⟩
        calc Perm.iter p (m + t) d0
            = Perm.iter p ((m + t - L) + L) d0 := congrArg (fun k => Perm.iter p k d0) (by omega)
          _ = Perm.iter p (m + t - L) (Perm.iter p L d0) := perm_iter_add p _ _ d0
          _ = Perm.iter p (m + t - L) d0 := by rw [hc.period]
    obtain ⟨i', hi'L, hi'eq, hi'1, hi'2⟩ := hshift i hi
    obtain ⟨j', hj'L, hj'eq, hj'1, hj'2⟩ := hshift j hj
    have hij' : i' = j' := hc.inj_lt i' j' hi'L hj'L (by rw [← hi'eq, ← hj'eq, heq])
    by_cases hi_lt : i + t < L <;> by_cases hj_lt : j + t < L
    · have := hi'1 hi_lt; have := hj'1 hj_lt; omega
    · have := hi'1 hi_lt; have := hj'2 (by omega); omega
    · have := hi'2 (by omega); have := hj'1 hj_lt; omega
    · have := hi'2 (by omega); have := hj'2 (by omega); omega
  period := by
    calc Perm.iter p L (Perm.iter p t d0)
        = Perm.iter p (L + t) d0 := (perm_iter_add p L t d0).symm
      _ = Perm.iter p (t + L) d0 := by rw [Nat.add_comm]
      _ = Perm.iter p t (Perm.iter p L d0) := perm_iter_add p t L d0
      _ = Perm.iter p t d0 := by rw [hc.period]
  k1 := hc.k1 - t
  k2 := hc.k2
  k3 := hc.k3
  k4 := hc.k4 + t
  hk1 := by omega
  hk2 := hc.hk2
  hk3 := hc.hk3
  hk4 := by have := hc.hk4; omega
  hsum := by have := hc.hsum; omega
  hd1 := by rw [← perm_iter_add, show hc.k1 - t + t = hc.k1 by omega]; exact hc.hd1
  hd2 := by rw [← perm_iter_add, show hc.k1 - t + hc.k2 + t = hc.k1 + hc.k2 by omega]; exact hc.hd2
  hd3 := by rw [← perm_iter_add, show hc.k1 - t + hc.k2 + hc.k3 + t = hc.k1 + hc.k2 + hc.k3 by omega]; exact hc.hd3

def cyclicOrder4_replace2 {D : Type} (p : Perm D) {L : Nat} {d0 d1 d2 d3 : D}
    (hc : CyclicOrder4 p L d0 d1 d2 d3) {t : Nat}
    (ht1 : hc.k1 < t) (ht3 : t < hc.k1 + hc.k2 + hc.k3) :
    CyclicOrder4 p L d0 d1 (Perm.iter p t d0) d3 where
  inj_lt := hc.inj_lt
  period := hc.period
  k1 := hc.k1
  k2 := t - hc.k1
  k3 := hc.k1 + hc.k2 + hc.k3 - t
  k4 := hc.k4
  hk1 := hc.hk1
  hk2 := by omega
  hk3 := by omega
  hk4 := hc.hk4
  hsum := by have := hc.hsum; omega
  hd1 := hc.hd1
  hd2 := by rw [show hc.k1 + (t - hc.k1) = t by omega]
  hd3 := by rw [show hc.k1 + (t - hc.k1) + (hc.k1 + hc.k2 + hc.k3 - t) = hc.k1 + hc.k2 + hc.k3 by omega]; exact hc.hd3

structure CrossingQuad (H : Hypermap) where
  L : Nat
  d0 : H.Dart
  d1 : H.Dart
  d2 : H.Dart
  d3 : H.Dart
  hc : CyclicOrder4 H.face L d0 d1 d2 d3
  S1 : H.Dart → Prop
  hS1 : ∀ z, S1 (H.node.f z) ↔ S1 z
  S2 : H.Dart → Prop
  hS2 : ∀ z, S2 (H.node.f z) ↔ S2 z
  hdisj : ∀ z, ¬ (S1 z ∧ S2 z)
  w1 : WalkENIn H.edge H.node S1 d0 d2
  w2 : WalkENIn H.edge H.node S2 d1 d3

def CrossingQuad.rot {H : Hypermap} (q : CrossingQuad H) : CrossingQuad H where
  L := q.L
  d0 := q.d1
  d1 := q.d2
  d2 := q.d3
  d3 := q.d0
  hc := cyclicOrder4_rot H.face q.hc
  S1 := q.S2
  hS1 := q.hS2
  S2 := q.S1
  hS2 := q.hS1
  hdisj := fun z hz => q.hdisj z ⟨hz.2, hz.1⟩
  w1 := q.w2
  w2 := q.w1.revOfInv H.edge_involution

theorem CrossingQuad.eLen_rot {H : Hypermap} (q : CrossingQuad H) :
    q.rot.w1.eLen + q.rot.w2.eLen = q.w1.eLen + q.w2.eLen := by
  dsimp only [CrossingQuad.rot]
  rw [WalkENIn.eLen_revOfInv]
  omega

def IsMinQuad (H : Hypermap) (q : CrossingQuad H) : Prop :=
  ∀ q' : CrossingQuad H, q'.w1.eLen + q'.w2.eLen < q.w1.eLen + q.w2.eLen → False

theorem isMinQuad_rot {H : Hypermap} {q : CrossingQuad H} (hmin : IsMinQuad H q) :
    IsMinQuad H q.rot := fun q' hlt => hmin q' (by rw [← q.eLen_rot]; exact hlt)

theorem sector0_props (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (q : CrossingQuad H) (hmin : IsMinQuad H q)
    {t : Nat} (ht : t < q.hc.k1) :
    let u := Perm.iter H.face t q.d0
    ¬ SameOrbit H.node q.d2 u ∧
    ¬ SameOrbit H.node q.d3 u ∧
    (¬ SameOrbit H.node q.d1 u → ¬ q.w2.HitsVertex u) := by
  intro u
  have n_symm : ∀ {a b : H.Dart}, SameOrbit H.node a b → SameOrbit H.node b a :=
    sameOrbit_symm_of_complete H.node darts h_all
  have hd0_S1 : q.S1 q.d0 := walkENIn_left q.w1
  have hd2_S1 : q.S1 q.d2 := walkENIn_right q.w1
  have hd1_S2 : q.S2 q.d1 := walkENIn_left q.w2
  have hd3_S2 : q.S2 q.d3 := walkENIn_right q.w2
  have hno2 : ¬ SameOrbit H.node q.d2 u := by
    intro h2u
    have hu_S1 : q.S1 u := pred_of_sameOrbit q.hS1 hd2_S1 h2u
    have hav : ∀ z, q.S2 z → z ≠ u ∧ z ≠ q.d2 := fun z hz =>
      ⟨fun h => q.hdisj z ⟨h ▸ hu_S1, hz⟩, fun h => q.hdisj z ⟨h ▸ hd2_S1, hz⟩⟩
    cases t with
    | zero =>
      exact no_cross_arc_walk_pair H darts h_nodup h_all h_planar q.hc (n_symm h2u) q.S2 hav
        (nonempty_walkENIn_iff_reachENIn.mp ⟨q.w2⟩)
    | succ t' =>
      exact no_cross_arc_walk_pair H darts h_nodup h_all h_planar
        (cyclicOrder4_sub1_of_0_k1 H.face q.hc (by omega) ht) (n_symm h2u) q.S2 hav
        (nonempty_walkENIn_iff_reachENIn.mp ⟨q.w2⟩)
  refine ⟨hno2, ?_, ?_⟩
  · intro h3u
    have hu_S2 : q.S2 u := pred_of_sameOrbit q.hS2 hd3_S2 h3u
    cases t with
    | zero => exact q.hdisj q.d0 ⟨hd0_S1, hu_S2⟩
    | succ t' =>
      have hav : ∀ z, q.S1 z → z ≠ u ∧ z ≠ q.d3 := fun z hz =>
        ⟨fun h => q.hdisj z ⟨hz, h ▸ hu_S2⟩, fun h => q.hdisj z ⟨hz, h ▸ hd3_S2⟩⟩
      exact no_cross_arc_walk_pair H darts h_nodup h_all h_planar
        (cyclicOrder4_rot H.face (cyclicOrder4_sub0_of_0_k1 H.face q.hc (by omega) ht))
        (n_symm h3u) q.S1 hav
        (nonempty_walkENIn_iff_reachENIn.mp ⟨q.w1.revOfInv H.edge_involution⟩)
  · intro hnot1 hw2u
    cases t with
    | zero => exact q.hdisj q.d0 ⟨hd0_S1, q.w2.hitsVertex_imp q.hS2 hw2u⟩
    | succ t' =>
      obtain ⟨w2_pre, w2_suf, hlen2⟩ := q.w2.splitAtHit n_symm q.hS2 hw2u
      have hne0 : w2_pre.eLen ≠ 0 := fun hz0 =>
        hnot1 (sameOrbit_of_walkENIn_eLen_zero H.edge H.node darts h_all w2_pre hz0)
      have hc' := cyclicOrder4_sub0_of_0_k1 H.face q.hc (by omega) ht
      exact hmin ⟨q.L, q.d0, u, q.d2, q.d3, hc', q.S1, q.hS1, q.S2, q.hS2, q.hdisj, q.w1, w2_suf⟩ (by dsimp only; omega)

theorem sector12_avoids_Int1 (H : Hypermap) (q : CrossingQuad H) (hmin : IsMinQuad H q)
    {m1 : H.Dart} (Int1 : WalkENIn H.edge H.node (fun z => q.S1 z ∧ ¬ SameOrbit H.node q.d2 z) q.d0 m1)
    (hlen1 : Int1.eLen < q.w1.eLen)
    (n_symm : ∀ {a b : H.Dart}, SameOrbit H.node a b → SameOrbit H.node b a)
    {t : Nat} (ht1 : q.hc.k1 < t) (ht3 : t < q.hc.k1 + q.hc.k2 + q.hc.k3)
    (h_hit : Int1.HitsVertex (Perm.iter H.face t q.d0)) : False := by
  have hP1 : ∀ z, (q.S1 z ∧ ¬ SameOrbit H.node q.d2 z) ↔
      (q.S1 (H.node.f z) ∧ ¬ SameOrbit H.node q.d2 (H.node.f z)) := fun z =>
    ⟨fun ⟨hs, hn⟩ => ⟨(q.hS1 z).mpr hs, fun h => hn (sameOrbit_trans H.node h (n_symm (sameOrbit_step H.node rfl)))⟩,
     fun ⟨hs, hn⟩ => ⟨(q.hS1 z).mp hs, fun h => hn (sameOrbit_trans H.node h (sameOrbit_step H.node rfl))⟩⟩
  obtain ⟨w1_pre, w1_suf, hlen_pre⟩ := Int1.splitAtHit n_symm (fun z => (hP1 z).symm) h_hit
  have hc' := cyclicOrder4_replace2 H.face q.hc ht1 ht3
  exact hmin ⟨q.L, q.d0, q.d1, Perm.iter H.face t q.d0, q.d3, hc', q.S1, q.hS1, q.S2, q.hS2, q.hdisj,
    w1_pre.mapPred (fun _ h => h.1), q.w2⟩ (by dsimp only; rw [WalkENIn.eLen_mapPred]; omega)

theorem sector0_disjoint_sector1_or_2 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (q : CrossingQuad H) (hmin : IsMinQuad H q)
    {t0 : Nat} (ht0 : 1 ≤ t0) (ht0_k1 : t0 < q.hc.k1)
    {t : Nat} (ht1 : q.hc.k1 < t) (ht3 : t < q.hc.k1 + q.hc.k2 + q.hc.k3)
    (hnot1 : ¬ SameOrbit H.node q.d1 (Perm.iter H.face t0 q.d0))
    (h_eq : SameOrbit H.node (Perm.iter H.face t0 q.d0) (Perm.iter H.face t q.d0)) : False := by
  have n_symm : ∀ {a b : H.Dart}, SameOrbit H.node a b → SameOrbit H.node b a :=
    sameOrbit_symm_of_complete H.node darts h_all
  let u := Perm.iter H.face t0 q.d0
  let v := Perm.iter H.face t q.d0
  have hnow2 : ¬ q.w2.HitsVertex u :=
    (sector0_props H darts h_nodup h_all h_planar q hmin (by omega)).2.2 hnot1
  have hP2' : ∀ z, (q.S2 z ∧ q.w2.HitsVertex z) ↔ (q.S2 (H.node.f z) ∧ q.w2.HitsVertex (H.node.f z)) :=
    fun z => ⟨fun ⟨hs, hh⟩ => ⟨(q.hS2 z).mpr hs, q.w2.hitsVertex_of_sameOrbit hh (sameOrbit_step H.node rfl)⟩,
              fun ⟨hs, hh⟩ => ⟨(q.hS2 z).mp hs, q.w2.hitsVertex_of_sameOrbit hh (n_symm (sameOrbit_step H.node rfl))⟩⟩
  have hav : ∀ z, (q.S2 z ∧ q.w2.HitsVertex z) → z ≠ u ∧ z ≠ v := by
    intro z ⟨_, hhz⟩
    refine ⟨fun heq => by subst heq; exact hnow2 hhz,
            fun heq => by subst heq; exact hnow2 (q.w2.hitsVertex_of_sameOrbit hhz (n_symm h_eq))⟩
  let hc' := cyclicOrder4_replace2 H.face q.hc ht1 ht3
  have hc'' := cyclicOrder4_sub1_of_0_k1 H.face hc' ht0 ht0_k1
  exact no_cross_arc_walk_pair H darts h_nodup h_all h_planar hc'' h_eq
    (fun z => q.S2 z ∧ q.w2.HitsVertex z) hav
    (nonempty_walkENIn_iff_reachENIn.mp ⟨q.w2.toHitsVertex n_symm q.hS2⟩)

def WalkENIn.liftAddApex4 {H : Hypermap} [DecidableEq H.Dart] (c : Fin 4 → H.Dart)
    (hc_inj : ∀ i j : Fin 4, c i = c j → i = j)
    {Q : H.Dart → Prop} (hQn : ∀ z, Q (H.node.f z) ↔ Q z)
    (P' : (H.addFaceApex4 c hc_inj).Dart → Prop)
    (h_inl : ∀ d, Q d → P' (.inl d))
    (h_inr : ∀ k : Fin 4, Q (c k) → P' (.inr ⟨k.val, by omega⟩))
    {x y : H.Dart} :
    WalkENIn H.edge H.node Q x y →
      WalkENIn (H.addFaceApex4 c hc_inj).edge (H.addFaceApex4 c hc_inj).node P' (.inl x) (.inl y)
  | .refl hx => .refl (h_inl x hx)
  | .e_step (y := v) w' hy =>
    .e_step (WalkENIn.liftAddApex4 c hc_inj hQn P' h_inl h_inr w') (h_inl (H.edge.f v) hy)
  | .n_fwd (y := v) w' hy =>
    let H' := H.addFaceApex4 c hc_inj
    let ih := WalkENIn.liftAddApex4 c hc_inj hQn P' h_inl h_inr w'
    match hcv : cornerIdx c v with
    | none =>
      have hnf : H'.node.f (.inl v) = .inl (H.node.f v) := by
        change addApex4NF H c (.inl v) = .inl (H.node.f v)
        simp only [addApex4NF, hcv]
      hnf ▸ WalkENIn.n_fwd ih (by rw [hnf]; exact h_inl _ hy)
    | some k =>
      have hv_eq : v = c k := eq_of_cornerIdx_some hcv
      let mid : H'.Dart := .inr ⟨k.val, by omega⟩
      have hnf1 : H'.node.f (.inl v) = mid := by
        change addApex4NF H c (.inl v) = mid
        simp only [addApex4NF, hcv]; rfl
      have hnf2 : H'.node.f mid = .inl (H.node.f v) := by
        change addApex4NF H c mid = .inl (H.node.f v)
        have hkf : (⟨k.val, k.isLt⟩ : Fin 4) = k := Fin.ext rfl
        simp only [addApex4NF, mid, dif_pos k.isLt, hkf, hv_eq]
      have hmid : P' mid := h_inr k (by rw [← hv_eq]; exact walkENIn_right w')
      have hw1 : WalkENIn H'.edge H'.node P' (.inl x) mid :=
        hnf1 ▸ WalkENIn.n_fwd ih (by rw [hnf1]; exact hmid)
      hnf2 ▸ WalkENIn.n_fwd hw1 (by rw [hnf2]; exact h_inl _ hy)
  | .n_bwd (y := v) w' hy =>
    let H' := H.addFaceApex4 c hc_inj
    let ih := WalkENIn.liftAddApex4 c hc_inj hQn P' h_inl h_inr w'
    match hcu : cornerIdx c (H.node.inv v) with
    | none =>
      have hni : H'.node.inv (.inl v) = .inl (H.node.inv v) := by
        change addApex4NInv H c (.inl v) = .inl (H.node.inv v)
        simp only [addApex4NInv, hcu]
      hni ▸ WalkENIn.n_bwd ih (by rw [hni]; exact h_inl _ hy)
    | some k =>
      have hu_eq : H.node.inv v = c k := eq_of_cornerIdx_some hcu
      let mid : H'.Dart := .inr ⟨k.val, by omega⟩
      have hni1 : H'.node.inv (.inl v) = mid := by
        change addApex4NInv H c (.inl v) = mid
        simp only [addApex4NInv, hcu]; rfl
      have hni2 : H'.node.inv mid = .inl (H.node.inv v) := by
        change addApex4NInv H c mid = .inl (H.node.inv v)
        have hkf : (⟨k.val, k.isLt⟩ : Fin 4) = k := Fin.ext rfl
        simp only [addApex4NInv, mid, dif_pos k.isLt, hkf, hu_eq]
      have hmid : P' mid := h_inr k (by rw [← hu_eq]; exact hy)
      have hw1 : WalkENIn H'.edge H'.node P' (.inl x) mid :=
        hni1 ▸ WalkENIn.n_bwd ih (by rw [hni1]; exact hmid)
      hni2 ▸ WalkENIn.n_bwd hw1 (by rw [hni2]; exact h_inl _ hy)

theorem WalkENIn.reachENIn_liftAddApex4 {H : Hypermap} [DecidableEq H.Dart] (c : Fin 4 → H.Dart)
    (hc_inj : ∀ i j : Fin 4, c i = c j → i = j)
    {Q : H.Dart → Prop} (hQn : ∀ z, Q (H.node.f z) ↔ Q z)
    (P' : (H.addFaceApex4 c hc_inj).Dart → Prop)
    (h_inl : ∀ d, Q d → P' (.inl d))
    (h_inr : ∀ k : Fin 4, Q (c k) → P' (.inr ⟨k.val, by omega⟩))
    {x y : H.Dart} (hxy : ReachENIn H.edge H.node Q x y) :
    ReachENIn (H.addFaceApex4 c hc_inj).edge (H.addFaceApex4 c hc_inj).node P' (.inl x) (.inl y) := by
  obtain ⟨w⟩ := nonempty_walkENIn_iff_reachENIn.mpr hxy
  exact nonempty_walkENIn_iff_reachENIn.mp ⟨w.liftAddApex4 c hc_inj hQn P' h_inl h_inr⟩

theorem sector_disjoint_next (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (n_symm : ∀ {a b : H.Dart}, SameOrbit H.node a b → SameOrbit H.node b a)
    (q : CrossingQuad H) (hmin : IsMinQuad H q) (hmin_rot : IsMinQuad H q.rot)
    {ta tb : Nat} (hta : ta < q.hc.k1) (htb : tb < q.rot.hc.k1)
    (hav0 : ¬ SameOrbit H.node q.d1 (Perm.iter H.face ta q.d0))
    (h_eq : SameOrbit H.node (Perm.iter H.face ta q.d0) (Perm.iter H.face tb q.rot.d0)) : False := by
  cases tb with
  | zero => exact hav0 (n_symm h_eq)
  | succ tb' =>
    cases ta with
    | zero =>
      exact (sector0_props H darts h_nodup h_all h_planar q.rot hmin_rot htb).2.1 h_eq
    | succ ta' =>
      have hrot_d0 : Perm.iter H.face (tb' + 1) q.rot.d0 = Perm.iter H.face (q.hc.k1 + (tb' + 1)) q.d0 :=
        calc Perm.iter H.face (tb' + 1) q.rot.d0
            = Perm.iter H.face (tb' + 1) (Perm.iter H.face q.hc.k1 q.d0) :=
              congrArg (Perm.iter H.face (tb' + 1)) q.hc.hd1.symm
          _ = Perm.iter H.face (q.hc.k1 + (tb' + 1)) q.d0 := by rw [← perm_iter_add, Nat.add_comm]
      have hk_eq : q.rot.hc.k1 = q.hc.k2 := rfl
      have hk3 := q.hc.hk3
      rw [hrot_d0] at h_eq
      exact sector0_disjoint_sector1_or_2 H darts h_nodup h_all h_planar q hmin
        (by omega) hta (by omega) (by omega) hav0 h_eq

theorem sector_disjoint_opp (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (n_symm : ∀ {a b : H.Dart}, SameOrbit H.node a b → SameOrbit H.node b a)
    (q : CrossingQuad H) (hmin : IsMinQuad H q) (hmin2 : IsMinQuad H q.rot.rot)
    {ta tb : Nat} (hta : ta < q.hc.k1) (htb : tb < q.rot.rot.hc.k1)
    (hav0 : ¬ SameOrbit H.node q.d1 (Perm.iter H.face ta q.d0))
    (h_eq : SameOrbit H.node (Perm.iter H.face ta q.d0) (Perm.iter H.face tb q.rot.rot.d0)) : False := by
  cases tb with
  | zero =>
    exact (sector0_props H darts h_nodup h_all h_planar q hmin hta).1 (n_symm h_eq)
  | succ tb' =>
    cases ta with
    | zero =>
      exact (sector0_props H darts h_nodup h_all h_planar q.rot.rot hmin2 htb).1 h_eq
    | succ ta' =>
      have hrot_d0 : Perm.iter H.face (tb' + 1) q.rot.rot.d0 =
          Perm.iter H.face (q.hc.k1 + q.hc.k2 + (tb' + 1)) q.d0 :=
        calc Perm.iter H.face (tb' + 1) q.rot.rot.d0
            = Perm.iter H.face (tb' + 1) (Perm.iter H.face (q.hc.k1 + q.hc.k2) q.d0) :=
              congrArg (Perm.iter H.face (tb' + 1)) q.hc.hd2.symm
          _ = Perm.iter H.face (q.hc.k1 + q.hc.k2 + (tb' + 1)) q.d0 := by rw [← perm_iter_add, Nat.add_comm]
      have hk_eq : q.rot.rot.hc.k1 = q.hc.k3 := rfl
      have hk2 := q.hc.hk2
      rw [hrot_d0] at h_eq
      exact sector0_disjoint_sector1_or_2 H darts h_nodup h_all h_planar q hmin
        (by omega) hta (by omega) (by omega) hav0 h_eq

theorem alternating_walks_intersect_of_cyclic_face (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    {L : Nat} {d0 d1 d2 d3 : H.Dart} (hc : CyclicOrder4 H.face L d0 d1 d2 d3)
    (S1 S2 : H.Dart → Prop)
    (hS1_node : ∀ z, S1 (H.node.f z) ↔ S1 z)
    (hS2_node : ∀ z, S2 (H.node.f z) ↔ S2 z)
    (hw1 : ReachENIn H.edge H.node S1 d0 d2)
    (hw2 : ReachENIn H.edge H.node S2 d1 d3) :
    ∃ z : H.Dart, S1 z ∧ S2 z := by
  classical
  refine Classical.byContradiction fun hnone => ?_
  have hdisj_top : ∀ z, ¬ (S1 z ∧ S2 z) := fun z hz => hnone ⟨z, hz⟩
  have n_symm : ∀ {a b : H.Dart}, SameOrbit H.node a b → SameOrbit H.node b a :=
    sameOrbit_symm_of_complete H.node darts h_all
  have h_strong : ∀ N : Nat, ∀ q : CrossingQuad H, q.w1.eLen + q.w2.eLen = N → False := by
    intro N
    induction N using Nat.strongRecOn with
    | _ N ih =>
      intro q hN
      have hmin : IsMinQuad H q := fun q' hlt => ih (q'.w1.eLen + q'.w2.eLen) (by omega) q' rfl
      have hmin1 : IsMinQuad H q.rot := isMinQuad_rot hmin
      have hmin2 : IsMinQuad H q.rot.rot := isMinQuad_rot hmin1
      have hmin3 : IsMinQuad H q.rot.rot.rot := isMinQuad_rot hmin2
      have hmin4 : IsMinQuad H q.rot.rot.rot.rot := isMinQuad_rot hmin3
      -- 1. Corner disjointness
      have h0_2 : ¬ SameOrbit H.node q.d0 q.d2 := fun h =>
        (sector0_props H darts h_nodup h_all h_planar q hmin q.hc.hk1).1 (n_symm h)
      have h1_3 : ¬ SameOrbit H.node q.d1 q.d3 := fun h =>
        (sector0_props H darts h_nodup h_all h_planar q.rot hmin1 q.rot.hc.hk1).1 (n_symm h)
      have hc01 : ¬ SameOrbit H.node q.d1 q.d0 := fun h =>
        q.hdisj q.d0 ⟨walkENIn_left q.w1, pred_of_sameOrbit q.hS2 (walkENIn_left q.w2) h⟩
      have hc12 : ¬ SameOrbit H.node q.d2 q.d1 := fun h =>
        q.hdisj q.d1 ⟨pred_of_sameOrbit q.hS1 (walkENIn_right q.w1) h, walkENIn_left q.w2⟩
      have hc23 : ¬ SameOrbit H.node q.d3 q.d2 := fun h =>
        q.hdisj q.d2 ⟨walkENIn_right q.w1, pred_of_sameOrbit q.hS2 (walkENIn_right q.w2) h⟩
      have hc30 : ¬ SameOrbit H.node q.d0 q.d3 := fun h =>
        q.hdisj q.d3 ⟨pred_of_sameOrbit q.hS1 (walkENIn_left q.w1) h, walkENIn_right q.w2⟩
      -- 2. Split w1 before V(d2) -> Int1, and w2 before V(d3) -> Int2
      have hQ2_n : ∀ z, SameOrbit H.node q.d2 (H.node.f z) ↔ SameOrbit H.node q.d2 z := fun z =>
        ⟨fun h => sameOrbit_trans H.node h (n_symm (sameOrbit_step H.node rfl)),
         fun h => sameOrbit_trans H.node h (sameOrbit_step H.node rfl)⟩
      have hQ3_n : ∀ z, SameOrbit H.node q.d3 (H.node.f z) ↔ SameOrbit H.node q.d3 z := fun z =>
        ⟨fun h => sameOrbit_trans H.node h (n_symm (sameOrbit_step H.node rfl)),
         fun h => sameOrbit_trans H.node h (sameOrbit_step H.node rfl)⟩
      cases hres1 : q.w1.splitFirstHit (fun z => SameOrbit H.node q.d2 z) hQ2_n (fun h => h0_2 (n_symm h)) with
      | inl p => exact absurd (sameOrbit_refl H.node q.d2) (walkENIn_right p.1).2
      | inr p1 =>
      rcases p1 with ⟨m1, m1', hm1_info, Int1, w1_tail, hlen1_eq⟩
      have hInt1_hit : ∀ {z}, Int1.HitsVertex z → q.w1.HitsVertex z := by
        have hm := q.w1.splitFirstHit_hitsVertex (fun z => SameOrbit H.node q.d2 z) hQ2_n (fun h => h0_2 (n_symm h))
        rw [hres1] at hm; intro z hz; exact hm z hz
      cases hres2 : q.w2.splitFirstHit (fun z => SameOrbit H.node q.d3 z) hQ3_n (fun h => h1_3 (n_symm h)) with
      | inl p => exact absurd (sameOrbit_refl H.node q.d3) (walkENIn_right p.1).2
      | inr p2 =>
      rcases p2 with ⟨m2, m2', hm2_info, Int2, w2_tail, hlen2_eq⟩
      have hInt2_hit : ∀ {z}, Int2.HitsVertex z → q.w2.HitsVertex z := by
        have hm := q.w2.splitFirstHit_hitsVertex (fun z => SameOrbit H.node q.d3 z) hQ3_n (fun h => h1_3 (n_symm h))
        rw [hres2] at hm; intro z hz; exact hm z hz
      have hInt1_len : Int1.eLen < q.w1.eLen := by omega
      have hInt2_len : Int2.eLen < q.w2.eLen := by omega
      -- 3. Prefix cutoffs t0, t1, t2, t3 along the 4 sectors
      obtain ⟨t0, ht0_lt, ht0_hit, ht0_av⟩ :=
        exists_min_hit_lt H.face q.d0 q.d1 q.hc.k1 q.hc.hk1 q.hc.hd1
          (fun d => SameOrbit H.node q.d1 d) hc01 (sameOrbit_refl H.node q.d1)
      obtain ⟨t1, ht1_lt, ht1_hit, ht1_av⟩ :=
        exists_min_hit_lt H.face q.rot.d0 q.rot.d1 q.rot.hc.k1 q.rot.hc.hk1 q.rot.hc.hd1
          (fun d => SameOrbit H.node q.d2 d) hc12 (sameOrbit_refl H.node q.d2)
      obtain ⟨t2, ht2_lt, ht2_hit, ht2_av⟩ :=
        exists_min_hit_lt H.face q.rot.rot.d0 q.rot.rot.d1 q.rot.rot.hc.k1 q.rot.rot.hc.hk1 q.rot.rot.hc.hd1
          (fun d => SameOrbit H.node q.d3 d) hc23 (sameOrbit_refl H.node q.d3)
      obtain ⟨t3, ht3_lt, ht3_hit, ht3_av⟩ :=
        exists_min_hit_lt H.face q.rot.rot.rot.d0 q.rot.rot.rot.d1 q.rot.rot.rot.hc.k1
          q.rot.rot.rot.hc.hk1 q.rot.rot.rot.hc.hd1
          (fun d => SameOrbit H.node q.d0 d) hc30 (sameOrbit_refl H.node q.d0)
      -- 4. Sector predicates InP0..3 and block predicates InB0..3
      let P0_pt (t : Nat) := Perm.iter H.face t q.d0
      let P1_pt (t : Nat) := Perm.iter H.face t q.rot.d0
      let P2_pt (t : Nat) := Perm.iter H.face t q.rot.rot.d0
      let P3_pt (t : Nat) := Perm.iter H.face t q.rot.rot.rot.d0
      have hP1_align : ∀ t, P1_pt t = Perm.iter H.face (q.hc.k1 + t) q.d0 := fun t =>
        calc Perm.iter H.face t q.rot.d0
            = Perm.iter H.face t (Perm.iter H.face q.hc.k1 q.d0) :=
              congrArg (Perm.iter H.face t) q.hc.hd1.symm
          _ = Perm.iter H.face (q.hc.k1 + t) q.d0 := by rw [← perm_iter_add, Nat.add_comm]
      have hP2_align : ∀ t, P2_pt t = Perm.iter H.face (q.hc.k1 + q.hc.k2 + t) q.d0 := fun t =>
        calc Perm.iter H.face t q.rot.rot.d0
            = Perm.iter H.face t (Perm.iter H.face (q.hc.k1 + q.hc.k2) q.d0) :=
              congrArg (Perm.iter H.face t) q.hc.hd2.symm
          _ = Perm.iter H.face (q.hc.k1 + q.hc.k2 + t) q.d0 := by rw [← perm_iter_add, Nat.add_comm]
      have hP1_2_align : ∀ t, P2_pt t = Perm.iter H.face (q.rot.hc.k1 + t) q.rot.d0 := fun t =>
        calc Perm.iter H.face t q.rot.rot.d0
            = Perm.iter H.face t (Perm.iter H.face q.rot.hc.k1 q.rot.d0) :=
              congrArg (Perm.iter H.face t) q.rot.hc.hd1.symm
          _ = Perm.iter H.face (q.rot.hc.k1 + t) q.rot.d0 := by rw [← perm_iter_add, Nat.add_comm]
      have hP1_3_align : ∀ t, P3_pt t = Perm.iter H.face (q.rot.hc.k1 + q.rot.hc.k2 + t) q.rot.d0 := fun t =>
        calc Perm.iter H.face t q.rot.rot.rot.d0
            = Perm.iter H.face t (Perm.iter H.face (q.rot.hc.k1 + q.rot.hc.k2) q.rot.d0) :=
              congrArg (Perm.iter H.face t) q.rot.hc.hd2.symm
          _ = Perm.iter H.face (q.rot.hc.k1 + q.rot.hc.k2 + t) q.rot.d0 := by rw [← perm_iter_add, Nat.add_comm]
      let InP0 (z : H.Dart) : Prop := ∃ t ≤ t0, SameOrbit H.node (P0_pt t) z
      let InP1 (z : H.Dart) : Prop := ∃ t ≤ t1, SameOrbit H.node (P1_pt t) z
      let InP2 (z : H.Dart) : Prop := ∃ t ≤ t2, SameOrbit H.node (P2_pt t) z
      let InP3 (z : H.Dart) : Prop := ∃ t ≤ t3, SameOrbit H.node (P3_pt t) z
      let InB0 (z : H.Dart) : Prop := Int1.HitsVertex z ∨ InP0 z
      let InB1 (z : H.Dart) : Prop := Int2.HitsVertex z ∨ InP1 z
      let InB2 (z : H.Dart) : Prop := InP2 z
      let InB3 (z : H.Dart) : Prop := InP3 z
      -- Node invariance helpers
      have hP1_n : ∀ u, (q.S1 u ∧ ¬ SameOrbit H.node q.d2 u) ↔
          (q.S1 (H.node.f u) ∧ ¬ SameOrbit H.node q.d2 (H.node.f u)) := fun u =>
        ⟨fun ⟨hs, hn⟩ => ⟨(q.hS1 u).mpr hs, fun h => hn (sameOrbit_trans H.node h (n_symm (sameOrbit_step H.node rfl)))⟩,
         fun ⟨hs, hn⟩ => ⟨(q.hS1 u).mp hs, fun h => hn (sameOrbit_trans H.node h (sameOrbit_step H.node rfl))⟩⟩
      have hP2_n : ∀ u, (q.S2 u ∧ ¬ SameOrbit H.node q.d3 u) ↔
          (q.S2 (H.node.f u) ∧ ¬ SameOrbit H.node q.d3 (H.node.f u)) := fun u =>
        ⟨fun ⟨hs, hn⟩ => ⟨(q.hS2 u).mpr hs, fun h => hn (sameOrbit_trans H.node h (n_symm (sameOrbit_step H.node rfl)))⟩,
         fun ⟨hs, hn⟩ => ⟨(q.hS2 u).mp hs, fun h => hn (sameOrbit_trans H.node h (sameOrbit_step H.node rfl))⟩⟩
      have hInP_node : ∀ (base : H.Dart) (tmax : Nat) (u : H.Dart),
          (∃ t ≤ tmax, SameOrbit H.node (Perm.iter H.face t base) (H.node.f u)) ↔
          (∃ t ≤ tmax, SameOrbit H.node (Perm.iter H.face t base) u) := fun base tmax u =>
        ⟨fun ⟨t, ht, ho⟩ => ⟨t, ht, sameOrbit_trans H.node ho (n_symm (sameOrbit_step H.node rfl))⟩,
         fun ⟨t, ht, ho⟩ => ⟨t, ht, sameOrbit_trans H.node ho (sameOrbit_step H.node rfl)⟩⟩
      -- Pairwise disjointness among Int1, Int2, P0..3
      have h_Int1_Int2 : ∀ z, Int1.HitsVertex z → Int2.HitsVertex z → False := by
        intro z hz1 hz2
        exact q.hdisj z ⟨(Int1.hitsVertex_imp (fun u => (hP1_n u).symm) hz1).1,
                         (Int2.hitsVertex_imp (fun u => (hP2_n u).symm) hz2).1⟩
      have h_Int1_P1 : ∀ z, Int1.HitsVertex z → InP1 z → False := by
        rintro z hz1 ⟨t, ht, htz⟩
        have hz_orb := Int1.hitsVertex_of_sameOrbit hz1 (n_symm htz)
        cases t with
        | zero =>
          exact q.hdisj q.d1 ⟨(Int1.hitsVertex_imp (fun u => (hP1_n u).symm) hz_orb).1, walkENIn_left q.w2⟩
        | succ t' =>
          have hk12 : q.rot.hc.k1 = q.hc.k2 := rfl
          have hk3 := q.hc.hk3
          rw [hP1_align] at hz_orb
          exact sector12_avoids_Int1 H q hmin Int1 hInt1_len n_symm (by omega) (by omega) hz_orb
      have h_Int1_P2 : ∀ z, Int1.HitsVertex z → InP2 z → False := by
        rintro z hz1 ⟨t, ht, htz⟩
        have hz_orb := Int1.hitsVertex_of_sameOrbit hz1 (n_symm htz)
        cases t with
        | zero =>
          exact (Int1.hitsVertex_imp (fun u => (hP1_n u).symm) hz_orb).2 (sameOrbit_refl H.node q.d2)
        | succ t' =>
          have hk23 : q.rot.rot.hc.k1 = q.hc.k3 := rfl
          have hk2 := q.hc.hk2
          rw [hP2_align] at hz_orb
          exact sector12_avoids_Int1 H q hmin Int1 hInt1_len n_symm (by omega) (by omega) hz_orb
      have h_Int1_P3 : ∀ z, Int1.HitsVertex z → InP3 z → False := by
        rintro z hz1 ⟨t, ht, htz⟩
        have hz_orb := Int1.hitsVertex_of_sameOrbit hz1 (n_symm htz)
        have hw1_hit : q.w1.HitsVertex (P3_pt t) := hInt1_hit hz_orb
        have hw3_hit : q.rot.rot.rot.w2.HitsVertex (P3_pt t) := by
          change ((q.w1.revOfInv H.edge_involution).revOfInv H.edge_involution).HitsVertex (P3_pt t)
          rw [WalkENIn.hitsVertex_revOfInv H.edge_involution n_symm,
              WalkENIn.hitsVertex_revOfInv H.edge_involution n_symm]
          exact hw1_hit
        exact (sector0_props H darts h_nodup h_all h_planar q.rot.rot.rot hmin3 (by omega)).2.2
          (ht3_av t ht) hw3_hit
      have h_Int2_P0 : ∀ z, Int2.HitsVertex z → InP0 z → False := by
        rintro z hz2 ⟨t, ht, htz⟩
        have hz_orb := Int2.hitsVertex_of_sameOrbit hz2 (n_symm htz)
        exact (sector0_props H darts h_nodup h_all h_planar q hmin (by omega)).2.2
          (ht0_av t ht) (hInt2_hit hz_orb)
      have h_Int2_P2 : ∀ z, Int2.HitsVertex z → InP2 z → False := by
        rintro z hz2 ⟨t, ht, htz⟩
        have hz_orb := Int2.hitsVertex_of_sameOrbit hz2 (n_symm htz)
        cases t with
        | zero =>
          exact q.hdisj q.d2 ⟨walkENIn_right q.w1,
            (Int2.hitsVertex_imp (fun u => (hP2_n u).symm) hz_orb).1⟩
        | succ t' =>
          have hk23 : q.rot.rot.hc.k1 = q.rot.hc.k2 := rfl
          have hk3 := q.rot.hc.hk3
          rw [hP1_2_align] at hz_orb
          exact sector12_avoids_Int1 H q.rot hmin1 Int2 hInt2_len n_symm (by omega) (by omega) hz_orb
      have h_Int2_P3 : ∀ z, Int2.HitsVertex z → InP3 z → False := by
        rintro z hz2 ⟨t, ht, htz⟩
        have hz_orb := Int2.hitsVertex_of_sameOrbit hz2 (n_symm htz)
        cases t with
        | zero =>
          exact (Int2.hitsVertex_imp (fun u => (hP2_n u).symm) hz_orb).2 (sameOrbit_refl H.node q.d3)
        | succ t' =>
          have hk34 : q.rot.rot.rot.hc.k1 = q.rot.hc.k3 := rfl
          have hk2 := q.rot.hc.hk2
          rw [hP1_3_align] at hz_orb
          exact sector12_avoids_Int1 H q.rot hmin1 Int2 hInt2_len n_symm (by omega) (by omega) hz_orb
      have h_P0_P1 : ∀ z, InP0 z → InP1 z → False := by
        rintro z ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        exact sector_disjoint_next H darts h_nodup h_all h_planar n_symm q hmin hmin1
          (by omega) (by omega) (ht0_av ta hta) (sameOrbit_trans H.node ha (n_symm hb))
      have h_P1_P2 : ∀ z, InP1 z → InP2 z → False := by
        rintro z ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        exact sector_disjoint_next H darts h_nodup h_all h_planar n_symm q.rot hmin1 hmin2
          (by omega) (by omega) (ht1_av ta hta) (sameOrbit_trans H.node ha (n_symm hb))
      have h_P2_P3 : ∀ z, InP2 z → InP3 z → False := by
        rintro z ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        exact sector_disjoint_next H darts h_nodup h_all h_planar n_symm q.rot.rot hmin2 hmin3
          (by omega) (by omega) (ht2_av ta hta) (sameOrbit_trans H.node ha (n_symm hb))
      have h_P3_P0 : ∀ z, InP3 z → InP0 z → False := by
        rintro z ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        have htb' : tb < q.rot.rot.rot.rot.hc.k1 := ht0_lt |> fun h => by
          change tb < q.hc.k1; omega
        exact sector_disjoint_next H darts h_nodup h_all h_planar n_symm q.rot.rot.rot hmin3 hmin4
          (by omega) htb' (ht3_av ta hta) (sameOrbit_trans H.node ha (n_symm hb))
      have h_P0_P2 : ∀ z, InP0 z → InP2 z → False := by
        rintro z ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        exact sector_disjoint_opp H darts h_nodup h_all h_planar n_symm q hmin hmin2
          (by omega) (by omega) (ht0_av ta hta) (sameOrbit_trans H.node ha (n_symm hb))
      have h_P1_P3 : ∀ z, InP1 z → InP3 z → False := by
        rintro z ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        exact sector_disjoint_opp H darts h_nodup h_all h_planar n_symm q.rot hmin1 hmin3
          (by omega) (by omega) (ht1_av ta hta) (sameOrbit_trans H.node ha (n_symm hb))
      -- Block disjointness & node invariance
      have h_B0_B1 : ∀ z, InB0 z → InB1 z → False := by
        rintro z (h | h) (h' | h')
        · exact h_Int1_Int2 z h h'
        · exact h_Int1_P1 z h h'
        · exact h_Int2_P0 z h' h
        · exact h_P0_P1 z h h'
      have h_B0_B2 : ∀ z, InB0 z → InB2 z → False := by
        rintro z (h | h) h'; exact h_Int1_P2 z h h'; exact h_P0_P2 z h h'
      have h_B0_B3 : ∀ z, InB0 z → InB3 z → False := by
        rintro z (h | h) h'; exact h_Int1_P3 z h h'; exact h_P3_P0 z h' h
      have h_B1_B2 : ∀ z, InB1 z → InB2 z → False := by
        rintro z (h | h) h'; exact h_Int2_P2 z h h'; exact h_P1_P2 z h h'
      have h_B1_B3 : ∀ z, InB1 z → InB3 z → False := by
        rintro z (h | h) h'; exact h_Int2_P3 z h h'; exact h_P1_P3 z h h'
      have h_B2_B3 : ∀ z, InB2 z → InB3 z → False := h_P2_P3
      have hB0_n : ∀ u, InB0 (H.node.f u) ↔ InB0 u := fun u =>
        ⟨fun h => h.elim (fun hi => .inl (Int1.hitsVertex_of_sameOrbit hi (n_symm (sameOrbit_step H.node rfl))))
            (fun hp => .inr ((hInP_node q.d0 t0 u).mp hp)),
         fun h => h.elim (fun hi => .inl (Int1.hitsVertex_of_sameOrbit hi (sameOrbit_step H.node rfl)))
            (fun hp => .inr ((hInP_node q.d0 t0 u).mpr hp))⟩
      have hB1_n : ∀ u, InB1 (H.node.f u) ↔ InB1 u := fun u =>
        ⟨fun h => h.elim (fun hi => .inl (Int2.hitsVertex_of_sameOrbit hi (n_symm (sameOrbit_step H.node rfl))))
            (fun hp => .inr ((hInP_node q.rot.d0 t1 u).mp hp)),
         fun h => h.elim (fun hi => .inl (Int2.hitsVertex_of_sameOrbit hi (sameOrbit_step H.node rfl)))
            (fun hp => .inr ((hInP_node q.rot.d0 t1 u).mpr hp))⟩
      have hB2_n : ∀ u, InB2 (H.node.f u) ↔ InB2 u := hInP_node q.rot.rot.d0 t2
      have hB3_n : ∀ u, InB3 (H.node.f u) ↔ InB3 u := hInP_node q.rot.rot.rot.d0 t3
      -- 5. Construct H' = H.addFaceApex4 c hc_inj and K_5 minor
      let c : Fin 4 → H.Dart := fun k => match k with | 0 => q.d0 | 1 => q.d1 | 2 => q.d2 | 3 => q.d3
      have hc_c : CyclicOrder4 H.face q.L (c 0) (c 1) (c 2) (c 3) := q.hc
      have hc_pos_lt : ∀ k : Fin 4,
          (match k with | 0 => 0 | 1 => q.hc.k1 | 2 => q.hc.k1 + q.hc.k2 | 3 => q.hc.k1 + q.hc.k2 + q.hc.k3) < q.L := by
        intro k
        have h1 := q.hc.hk1; have h2 := q.hc.hk2; have h3 := q.hc.hk3; have h4 := q.hc.hk4; have hs := q.hc.hsum
        rcases k with ⟨kv, hk⟩
        match kv, hk with
        | 0, _ => dsimp only; omega
        | 1, _ => dsimp only; omega
        | 2, _ => dsimp only; omega
        | 3, _ => dsimp only; omega
      have hc_inj : ∀ i j : Fin 4, c i = c j → i = j := by
        intro ⟨iv, hiv⟩ ⟨jv, hjv⟩ heq
        let pos : Fin 4 → Nat := fun k => match k with
          | 0 => 0 | 1 => q.hc.k1 | 2 => q.hc.k1 + q.hc.k2 | 3 => q.hc.k1 + q.hc.k2 + q.hc.k3
        have hiter : ∀ k : Fin 4, Perm.iter H.face (pos k) q.d0 = c k := by
          intro ⟨kv, hkv⟩
          match kv, hkv with
          | 0, _ => rfl
          | 1, _ => exact q.hc.hd1
          | 2, _ => exact q.hc.hd2
          | 3, _ => exact q.hc.hd3
        have hp_eq := q.hc.inj_lt (pos ⟨iv, hiv⟩) (pos ⟨jv, hjv⟩)
          (hc_pos_lt ⟨iv, hiv⟩) (hc_pos_lt ⟨jv, hjv⟩)
          (by rw [hiter ⟨iv, hiv⟩, hiter ⟨jv, hjv⟩, heq])
        have h1 := q.hc.hk1; have h2 := q.hc.hk2; have h3 := q.hc.hk3
        match iv, hiv, jv, hjv with
        | 0, _, 0, _ => rfl
        | 1, _, 1, _ => rfl
        | 2, _, 2, _ => rfl
        | 3, _, 3, _ => rfl
        | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _
        | 1, _, 0, _ | 1, _, 2, _ | 1, _, 3, _
        | 2, _, 0, _ | 2, _, 1, _ | 2, _, 3, _
        | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ => dsimp only [pos] at hp_eq; omega
      let H' := H.addFaceApex4 c hc_inj
      let darts' : List H'.Dart := darts.map Sum.inl ++ fin8Darts.map Sum.inr
      obtain ⟨h_nd', h_all', _⟩ := addFaceApex4_darts_complete H c hc_inj darts h_nodup h_all
      have h_pl' := isPlanar_addFaceApex4 H darts h_nodup h_all h_planar c hc_c
      have hH'_e_inv : ∀ z : H'.Dart, H'.edge.f (H'.edge.f z) = z := by
        intro z
        change (addApex4E H).f ((addApex4E H).f z) = z
        cases z with
        | inl d => exact congrArg Sum.inl (H.edge_involution d)
        | inr k => have hk_lt := k.isLt; exact congrArg Sum.inr (Fin.ext (by dsimp only [addApex4E]; omega))
      have hH'_n_symm : ∀ {a b : H'.Dart}, SameOrbit H'.node a b → SameOrbit H'.node b a :=
        sameOrbit_symm_of_complete H'.node darts' h_all'
      let cls : H'.Dart → Option (Fin 5)
        | .inr k => if hk : k.val < 4 then some ⟨k.val, by omega⟩ else some 4
        | .inl d =>
          if InB0 d then some 0
          else if InB1 d then some 1
          else if InB2 d then some 2
          else if InB3 d then some 3
          else none
      have hcls_B0 : ∀ d, InB0 d → cls (.inl d) = some 0 := fun d h => by simp only [cls, if_pos h]
      have hcls_B1 : ∀ d, InB1 d → cls (.inl d) = some 1 := fun d h => by
        have h0 : ¬ InB0 d := fun h0 => h_B0_B1 d h0 h
        simp only [cls, if_neg h0, if_pos h]
      have hcls_B2 : ∀ d, InB2 d → cls (.inl d) = some 2 := fun d h => by
        have h0 : ¬ InB0 d := fun h0 => h_B0_B2 d h0 h
        have h1 : ¬ InB1 d := fun h1 => h_B1_B2 d h1 h
        simp only [cls, if_neg h0, if_neg h1, if_pos h]
      have hcls_B3 : ∀ d, InB3 d → cls (.inl d) = some 3 := fun d h => by
        have h0 : ¬ InB0 d := fun h0 => h_B0_B3 d h0 h
        have h1 : ¬ InB1 d := fun h1 => h_B1_B3 d h1 h
        have h2 : ¬ InB2 d := fun h2 => h_B2_B3 d h2 h
        simp only [cls, if_neg h0, if_neg h1, if_neg h2, if_pos h]
      have hB_c0 : InB0 (c 0) := .inr ⟨0, Nat.zero_le _, sameOrbit_refl H.node q.d0⟩
      have hB_c1 : InB1 (c 1) := .inr ⟨0, Nat.zero_le _, sameOrbit_refl H.node q.d1⟩
      have hB_c2 : InB2 (c 2) := ⟨0, Nat.zero_le _, sameOrbit_refl H.node q.d2⟩
      have hB_c3 : InB3 (c 3) := ⟨0, Nat.zero_le _, sameOrbit_refl H.node q.d3⟩
      have hcls_ck : ∀ k : Fin 4, cls (.inl (c k)) = some ⟨k.val, by omega⟩ := by
        intro ⟨kv, hk⟩
        by_cases h0 : kv = 0
        · subst h0; exact hcls_B0 (c 0) hB_c0
        · by_cases h1 : kv = 1
          · subst h1; exact hcls_B1 (c 1) hB_c1
          · by_cases h2 : kv = 2
            · subst h2; exact hcls_B2 (c 2) hB_c2
            · have h3 : kv = 3 := by omega
              subst h3; exact hcls_B3 (c 3) hB_c3
      have hcls_inl_node : ∀ d, cls (.inl (H.node.f d)) = cls (.inl d) := fun d => by
        simp only [cls, hB0_n d, hB1_n d, hB2_n d, hB3_n d]
      have hcls_node : ∀ z, cls (H'.node.f z) = cls z := by
        intro z
        change cls (addApex4NF H c z) = cls z
        cases z with
        | inl d =>
          dsimp only [addApex4NF]
          cases hcidx : cornerIdx c d with
          | none => exact hcls_inl_node d
          | some k =>
            have hd_eq : d = c k := eq_of_cornerIdx_some hcidx
            have hk4 : k.val < 4 := k.isLt
            simp only [cls, dif_pos hk4, hd_eq]
            exact (hcls_ck k).symm
        | inr k =>
          dsimp only [addApex4NF]
          by_cases hk4 : k.val < 4
          · simp only [dif_pos hk4]
            rw [hcls_inl_node, hcls_ck ⟨k.val, hk4⟩]
            simp only [cls, dif_pos hk4]
          · simp only [dif_neg hk4, cls]
            have hge4 : ¬ ((4 + (k.val + 1) % 4) < 4) := by omega
            simp only [dif_neg hge4]
      -- Connectivity of each K_5 block
      have reach_InP : ∀ (base : H.Dart) (tmax : Nat) (t : Nat), t ≤ tmax →
          ∀ z, SameOrbit H.node (Perm.iter H.face t base) z →
            ReachENIn H.edge H.node
              (fun u => ∃ s ≤ tmax, SameOrbit H.node (Perm.iter H.face s base) u) base z := by
        intro base tmax t
        induction t with
        | zero =>
          intro _ z hz
          obtain ⟨k, rfl⟩ := hz
          exact nonempty_walkENIn_iff_reachENIn.mp ⟨WalkENIn.ofSameOrbit H.edge H.node
            (fun u => ∃ s ≤ tmax, SameOrbit H.node (Perm.iter H.face s base) u)
            (hInP_node base tmax) base
            ⟨0, Nat.zero_le _, sameOrbit_refl H.node base⟩ k⟩
        | succ t' ih =>
          intro ht z hz
          let u := Perm.iter H.face t' base
          let v := Perm.iter H.face (t' + 1) base
          have h_bu : ReachENIn H.edge H.node
              (fun w => ∃ s ≤ tmax, SameOrbit H.node (Perm.iter H.face s base) w) base u :=
            ih (by omega) u (sameOrbit_refl H.node u)
          have he_v : H.node.f v = H.edge.f u := by
            have h1 := H.edge_node_face_id u
            have hv_def : H.face.f u = v := (perm_iter_succ_left H.face t' base).symm
            rw [hv_def] at h1
            calc H.node.f v = H.edge.f (H.edge.f (H.node.f v)) := (H.edge_involution _).symm
              _ = H.edge.f u := congrArg H.edge.f h1
          have h_be : ReachENIn H.edge H.node
              (fun w => ∃ s ≤ tmax, SameOrbit H.node (Perm.iter H.face s base) w) base (H.edge.f u) :=
            .step_e h_bu ⟨t' + 1, ht, he_v ▸ sameOrbit_step H.node rfl⟩
          have hni_e : H.node.inv (H.edge.f u) = v := by
            rw [← he_v, H.node.left_inv]
          have h_bv : ReachENIn H.edge H.node
              (fun w => ∃ s ≤ tmax, SameOrbit H.node (Perm.iter H.face s base) w) base v :=
            hni_e ▸ .step_n_bwd h_be ⟨t' + 1, ht, hni_e ▸ sameOrbit_refl H.node v⟩
          obtain ⟨k, rfl⟩ := hz
          exact reachENIn_trans h_bv (nonempty_walkENIn_iff_reachENIn.mp ⟨WalkENIn.ofSameOrbit H.edge H.node
            (fun w => ∃ s ≤ tmax, SameOrbit H.node (Perm.iter H.face s base) w)
            (hInP_node base tmax) v ⟨t' + 1, ht, sameOrbit_refl H.node v⟩ k⟩)
      have h_cls_conn : ∀ (i : Fin 5) (x y : H'.Dart),
          cls x = some i → cls y = some i →
          ReachENIn H'.edge H'.node (fun z => cls z = some i) x y := by
        intro i x y hx hy
        have hP_cls_n : ∀ z, cls (H'.node.f z) = some i ↔ cls z = some i := fun z => by
          rw [hcls_node]
        rcases Nat.lt_or_ge i.val 4 with hi4 | hi4
        · let rep : H'.Dart := .inl (c ⟨i.val, hi4⟩)
          have hrep : cls rep = some i := by
            simpa only [Fin.eta] using hcls_ck ⟨i.val, hi4⟩
          have hcls_inl_cases : ∀ d j, cls (.inl d) = some j →
              (j = 0 ∧ InB0 d) ∨ (j = 1 ∧ InB1 d) ∨ (j = 2 ∧ InB2 d) ∨ (j = 3 ∧ InB3 d) := by
            intro d j hj
            dsimp only [cls] at hj
            by_cases h0 : InB0 d
            · rw [if_pos h0] at hj; cases hj; exact .inl ⟨rfl, h0⟩
            · rw [if_neg h0] at hj
              by_cases h1 : InB1 d
              · rw [if_pos h1] at hj; cases hj; exact .inr (.inl ⟨rfl, h1⟩)
              · rw [if_neg h1] at hj
                by_cases h2 : InB2 d
                · rw [if_pos h2] at hj; cases hj; exact .inr (.inr (.inl ⟨rfl, h2⟩))
                · rw [if_neg h2] at hj
                  by_cases h3 : InB3 d
                  · rw [if_pos h3] at hj; cases hj; exact .inr (.inr (.inr ⟨rfl, h3⟩))
                  · rw [if_neg h3] at hj; cases hj
          have reach_rep : ∀ w : H'.Dart, cls w = some i →
              ReachENIn H'.edge H'.node (fun z => cls z = some i) rep w := by
            intro w hw
            cases w with
            | inr k =>
              by_cases hk4 : k.val < 4
              · have hki : (⟨k.val, by omega⟩ : Fin 5) = i := by
                  simp only [cls, dif_pos hk4] at hw; cases hw; rfl
                have hnf : H'.node.f rep = .inr k := by
                  change addApex4NF H c (.inl (c ⟨i.val, hi4⟩)) = .inr k
                  dsimp only [addApex4NF]
                  rw [cornerIdx_c c hc_inj ⟨i.val, hi4⟩]
                  exact congrArg Sum.inr (Fin.ext (by dsimp only; exact (congrArg Fin.val hki).symm))
                exact hnf ▸ .step_n_fwd (.refl hrep) (hnf ▸ hw)
              · simp only [cls, dif_neg hk4] at hw; cases hw; exfalso; omega
            | inl d =>
              have h_lift : ∀ {Q : H.Dart → Prop} (hQn : ∀ z, Q (H.node.f z) ↔ Q z)
                  (hQcls : ∀ u, Q u → cls (.inl u) = some i)
                  (hQ : ReachENIn H.edge H.node Q (c ⟨i.val, hi4⟩) d),
                  ReachENIn H'.edge H'.node (fun z => cls z = some i) rep (.inl d) := by
                intro Q hQn hQcls hQ
                exact WalkENIn.reachENIn_liftAddApex4 c hc_inj hQn
                  (fun z => cls z = some i) hQcls (fun k hk => by
                    simp only [cls, dif_pos k.isLt]
                    exact (hcls_ck k).symm.trans (hQcls (c k) hk)) hQ
              match h_iv : i.val, hi4 with
              | 0, _ =>
                have hi0 : i = 0 := Fin.ext h_iv
                have hc0 : q.d0 = c ⟨i.val, hi4⟩ := by
                  rw [show (⟨i.val, hi4⟩ : Fin 4) = 0 from Fin.ext h_iv]
                have hBd : InB0 d := by
                  rcases hcls_inl_cases d i hw with ⟨_, h⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
                  · exact h
                  · rw [hi0] at he; cases he
                  · rw [hi0] at he; cases he
                  · rw [hi0] at he; cases he
                rcases hBd with h_int | ⟨t, ht, htz⟩
                · exact @h_lift Int1.HitsVertex
                    (fun u => ⟨fun h => Int1.hitsVertex_of_sameOrbit h (n_symm (sameOrbit_step H.node rfl)),
                               fun h => Int1.hitsVertex_of_sameOrbit h (sameOrbit_step H.node rfl)⟩)
                    (fun u hu => by rw [hi0]; exact hcls_B0 u (.inl hu))
                    (hc0 ▸ reachENIn_mono (fun _ h => h.2)
                      (Int1.reachENIn_hitsVertex n_symm (fun u => (hP1_n u).symm) h_int))
                · exact @h_lift InB0 hB0_n (fun u hu => by rw [hi0]; exact hcls_B0 u hu)
                    (hc0 ▸ reachENIn_mono (fun _ h => Or.inr h) (reach_InP q.d0 t0 t ht d htz))
              | 1, _ =>
                have hi1 : i = 1 := Fin.ext h_iv
                have hc1 : q.rot.d0 = c ⟨i.val, hi4⟩ := by
                  rw [show (⟨i.val, hi4⟩ : Fin 4) = 1 from Fin.ext h_iv]; rfl
                have hBd : InB1 d := by
                  rcases hcls_inl_cases d i hw with ⟨he, _⟩ | ⟨_, h⟩ | ⟨he, _⟩ | ⟨he, _⟩
                  · rw [hi1] at he; cases he
                  · exact h
                  · rw [hi1] at he; cases he
                  · rw [hi1] at he; cases he
                rcases hBd with h_int | ⟨t, ht, htz⟩
                · exact @h_lift Int2.HitsVertex
                    (fun u => ⟨fun h => Int2.hitsVertex_of_sameOrbit h (n_symm (sameOrbit_step H.node rfl)),
                               fun h => Int2.hitsVertex_of_sameOrbit h (sameOrbit_step H.node rfl)⟩)
                    (fun u hu => by rw [hi1]; exact hcls_B1 u (.inl hu))
                    (hc1 ▸ reachENIn_mono (fun _ h => h.2)
                      (Int2.reachENIn_hitsVertex n_symm (fun u => (hP2_n u).symm) h_int))
                · exact @h_lift InB1 hB1_n (fun u hu => by rw [hi1]; exact hcls_B1 u hu)
                    (hc1 ▸ reachENIn_mono (fun _ h => Or.inr h) (reach_InP q.rot.d0 t1 t ht d htz))
              | 2, _ =>
                have hi2 : i = 2 := Fin.ext h_iv
                have hc2 : q.rot.rot.d0 = c ⟨i.val, hi4⟩ := by
                  rw [show (⟨i.val, hi4⟩ : Fin 4) = 2 from Fin.ext h_iv]; rfl
                have hBd : InB2 d := by
                  rcases hcls_inl_cases d i hw with ⟨he, _⟩ | ⟨he, _⟩ | ⟨_, h⟩ | ⟨he, _⟩
                  · rw [hi2] at he; cases he
                  · rw [hi2] at he; cases he
                  · exact h
                  · rw [hi2] at he; cases he
                obtain ⟨t, ht, htz⟩ := hBd
                exact @h_lift InB2 hB2_n (fun u hu => by rw [hi2]; exact hcls_B2 u hu)
                  (hc2 ▸ reach_InP q.rot.rot.d0 t2 t ht d htz)
              | 3, _ =>
                have hi3 : i = 3 := Fin.ext h_iv
                have hc3 : q.rot.rot.rot.d0 = c ⟨i.val, hi4⟩ := by
                  rw [show (⟨i.val, hi4⟩ : Fin 4) = 3 from Fin.ext h_iv]; rfl
                have hBd : InB3 d := by
                  rcases hcls_inl_cases d i hw with ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨_, h⟩
                  · rw [hi3] at he; cases he
                  · rw [hi3] at he; cases he
                  · rw [hi3] at he; cases he
                  · exact h
                obtain ⟨t, ht, htz⟩ := hBd
                exact h_lift hB3_n (fun u hu => by rw [hi3]; exact hcls_B3 u hu)
                  (hc3 ▸ reach_InP q.rot.rot.rot.d0 t3 t ht d htz)
          exact reachENIn_trans (reachENIn_symm_of_involution hH'_e_inv (reach_rep x hx)) (reach_rep y hy)
        · have hi4_eq : i = 4 := Fin.ext (by omega)
          subst hi4_eq
          let rep4 : H'.Dart := .inr ⟨4, by decide⟩
          have hrep4 : cls rep4 = some 4 := rfl
          have reach4 : ∀ w : H'.Dart, cls w = some 4 →
              ReachENIn H'.edge H'.node (fun z => cls z = some 4) rep4 w := by
            intro w hw
            cases w with
            | inl d =>
              exfalso; dsimp only [cls] at hw
              by_cases h0 : InB0 d
              · rw [if_pos h0] at hw; cases hw
              · rw [if_neg h0] at hw
                by_cases h1 : InB1 d
                · rw [if_pos h1] at hw; cases hw
                · rw [if_neg h1] at hw
                  by_cases h2 : InB2 d
                  · rw [if_pos h2] at hw; cases hw
                  · rw [if_neg h2] at hw
                    by_cases h3 : InB3 d
                    · rw [if_pos h3] at hw; cases hw
                    · rw [if_neg h3] at hw; cases hw
            | inr k =>
              have hk4 : ¬ k.val < 4 := by
                intro hlt; simp only [cls, dif_pos hlt] at hw
                have h4 := congrArg Fin.val (Option.some.inj hw)
                dsimp only at h4; omega
              have hstep : ∀ n : Nat, (hn : n < 4) →
                  ReachENIn H'.edge H'.node (fun z => cls z = some 4) rep4 (.inr ⟨4 + n, by omega⟩) := by
                intro n
                induction n with
                | zero => intro _; exact .refl hrep4
                | succ n' ih =>
                  intro hn
                  have hs1 := ih (by omega)
                  have hnf : H'.node.f (.inr ⟨4 + n', by omega⟩) = .inr ⟨4 + (n' + 1), by omega⟩ := by
                    change addApex4NF H c (.inr ⟨4 + n', by omega⟩) = .inr ⟨4 + (n' + 1), by omega⟩
                    have hnot : ¬ (4 + n' < 4) := by omega
                    simp only [addApex4NF, dif_neg hnot]
                    exact congrArg Sum.inr (Fin.ext (by dsimp only; omega))
                  have hc' : cls (.inr ⟨4 + (n' + 1), by omega⟩) = some 4 := by
                    have hnot : ¬ (4 + (n' + 1) < 4) := by omega
                    simp only [cls, dif_neg hnot]
                  exact hnf ▸ .step_n_fwd hs1 (hnf ▸ hc')
              have hfin : k = ⟨4 + (k.val - 4), by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hfin]
              exact hstep (k.val - 4) (by have := k.isLt; omega)
          exact reachENIn_trans (reachENIn_symm_of_involution hH'_e_inv (reach4 x hx)) (reach4 y hy)
      -- 10 K_5 minor edges
      let u0 := P0_pt t0
      let u1 := P1_pt t1
      let u2 := P2_pt t2
      let u3 := P3_pt t3
      have he_cyc : ∀ {base next : H.Dart} {t : Nat},
          SameOrbit H.node next (Perm.iter H.face (t + 1) base) →
          SameOrbit H.node next (H.edge.f (Perm.iter H.face t base)) := by
        intro base next t ht
        have heq : H.edge.f (Perm.iter H.face t base) = H.node.f (Perm.iter H.face (t + 1) base) := by
          have h1 := H.edge_node_face_id (Perm.iter H.face t base)
          have hfv : H.face.f (Perm.iter H.face t base) = Perm.iter H.face (t + 1) base :=
            (perm_iter_succ_left H.face t base).symm
          rw [hfv] at h1
          calc H.edge.f (Perm.iter H.face t base)
              = H.edge.f (H.edge.f (H.node.f (Perm.iter H.face (t + 1) base))) := by rw [h1]
            _ = H.node.f (Perm.iter H.face (t + 1) base) := H.edge_involution _
        rw [heq]
        exact sameOrbit_trans H.node ht (sameOrbit_step H.node rfl)
      let e_dart : (i j : Fin 5) → i < j → H'.Dart := fun ⟨iv, hi⟩ ⟨jv, hj⟩ hij =>
        match iv, jv with
        | 0, 1 => .inl u0
        | 1, 2 => .inl u1
        | 2, 3 => .inl u2
        | 0, 3 => .inl (H.edge.f u3)
        | 0, 2 => .inl m1
        | 1, 3 => .inl m2
        | 0, 4 => .inr ⟨0, by decide⟩
        | 1, 4 => .inr ⟨1, by decide⟩
        | 2, 4 => .inr ⟨2, by decide⟩
        | 3, 4 => .inr ⟨3, by decide⟩
        | _, _ => .inl q.d0
      have he_src : ∀ i j h, cls (e_dart i j h) = some i := by
        rintro ⟨iv, hi⟩ ⟨jv, hj⟩ hij
        have hij' : iv < jv := hij
        match iv, hi, jv, hj with
        | 0, _, 1, _ => exact hcls_B0 u0 (.inr ⟨t0, Nat.le_refl _, sameOrbit_refl H.node u0⟩)
        | 1, _, 2, _ => exact hcls_B1 u1 (.inr ⟨t1, Nat.le_refl _, sameOrbit_refl H.node u1⟩)
        | 2, _, 3, _ => exact hcls_B2 u2 ⟨t2, Nat.le_refl _, sameOrbit_refl H.node u2⟩
        | 0, _, 3, _ =>
          exact hcls_B0 (H.edge.f u3) (.inr ⟨0, Nat.zero_le _, he_cyc ht3_hit⟩)
        | 0, _, 2, _ => exact hcls_B0 m1 (.inl (Int1.hitsVertex_right n_symm))
        | 1, _, 3, _ => exact hcls_B1 m2 (.inl (Int2.hitsVertex_right n_symm))
        | 0, _, 4, _ => rfl
        | 1, _, 4, _ => rfl
        | 2, _, 4, _ => rfl
        | 3, _, 4, _ => rfl
        | 1, _, 0, _ | 2, _, 0, _ | 2, _, 1, _ | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _
        | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 4, _
        | 0, _, 0, _ | 1, _, 1, _ | 2, _, 2, _ | 3, _, 3, _ => omega
      have he_dst : ∀ i j h, cls (H'.edge.f (e_dart i j h)) = some j := by
        rintro ⟨iv, hi⟩ ⟨jv, hj⟩ hij
        have hij' : iv < jv := hij
        match iv, hi, jv, hj with
        | 0, _, 1, _ =>
          exact hcls_B1 (H.edge.f u0) (.inr ⟨0, Nat.zero_le _, he_cyc ht0_hit⟩)
        | 1, _, 2, _ =>
          exact hcls_B2 (H.edge.f u1) ⟨0, Nat.zero_le _, he_cyc ht1_hit⟩
        | 2, _, 3, _ =>
          exact hcls_B3 (H.edge.f u2) ⟨0, Nat.zero_le _, he_cyc ht2_hit⟩
        | 0, _, 3, _ =>
          have heq : H'.edge.f (.inl (H.edge.f u3)) = .inl u3 := by
            change (addApex4E H).f (.inl (H.edge.f u3)) = .inl u3
            exact congrArg Sum.inl (H.edge_involution u3)
          change cls (H'.edge.f (.inl (H.edge.f u3))) = _
          rw [heq]; exact hcls_B3 u3 ⟨t3, Nat.le_refl _, sameOrbit_refl H.node u3⟩
        | 0, _, 2, _ =>
          have heq : H'.edge.f (.inl m1) = .inl m1' := by
            change (addApex4E H).f (.inl m1) = .inl m1'
            exact congrArg Sum.inl hm1_info.2.2.2.2
          change cls (H'.edge.f (.inl m1)) = _
          rw [heq]; exact hcls_B2 m1' ⟨0, Nat.zero_le _, hm1_info.2.2.2.1⟩
        | 1, _, 3, _ =>
          have heq : H'.edge.f (.inl m2) = .inl m2' := by
            change (addApex4E H).f (.inl m2) = .inl m2'
            exact congrArg Sum.inl hm2_info.2.2.2.2
          change cls (H'.edge.f (.inl m2)) = _
          rw [heq]; exact hcls_B3 m2' ⟨0, Nat.zero_le _, hm2_info.2.2.2.1⟩
        | 0, _, 4, _ => rfl
        | 1, _, 4, _ => rfl
        | 2, _, 4, _ => rfl
        | 3, _, 4, _ => rfl
        | 1, _, 0, _ | 2, _, 0, _ | 2, _, 1, _ | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _
        | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 4, _
        | 0, _, 0, _ | 1, _, 1, _ | 2, _, 2, _ | 3, _, 3, _ => omega
      exact no_K5_minor_of_isPlanar H' darts' h_nd' h_all' h_pl' cls hcls_node h_cls_conn e_dart he_src he_dst
  let q0 : CrossingQuad H := ⟨L, d0, d1, d2, d3, hc, S1, hS1_node, S2, hS2_node, hdisj_top,
    nonempty_walkENIn_iff_reachENIn.mpr hw1 |> Classical.choice,
    nonempty_walkENIn_iff_reachENIn.mpr hw2 |> Classical.choice⟩
  exact h_strong (q0.w1.eLen + q0.w2.eLen) q0 rfl

end AlternatingWalksIntersection

/-- Lift a walk in `P` to record reachability from the starting dart along the prefix. -/
def WalkENIn.toReachPrefix {D : Type} {e n : Perm D} {P : D → Prop} {x y : D} :
    WalkENIn e n P x y → WalkENIn e n (fun z => P z ∧ ReachENIn e n P x z) x y
  | .refl hx => .refl ⟨hx, .refl hx⟩
  | .n_fwd w hy =>
    .n_fwd (WalkENIn.toReachPrefix w) ⟨hy, .step_n_fwd (nonempty_walkENIn_iff_reachENIn.mp ⟨w⟩) hy⟩
  | .n_bwd w hy =>
    .n_bwd (WalkENIn.toReachPrefix w) ⟨hy, .step_n_bwd (nonempty_walkENIn_iff_reachENIn.mp ⟨w⟩) hy⟩
  | .e_step w hy =>
    .e_step (WalkENIn.toReachPrefix w) ⟨hy, .step_e (nonempty_walkENIn_iff_reachENIn.mp ⟨w⟩) hy⟩

theorem reachENIn_toReachPrefix {D : Type} {e n : Perm D} {P : D → Prop} {x y : D}
    (h : ReachENIn e n P x y) :
    ReachENIn e n (fun z => P z ∧ ReachENIn e n P x z) x y := by
  obtain ⟨w⟩ := nonempty_walkENIn_iff_reachENIn.mpr h
  exact nonempty_walkENIn_iff_reachENIn.mp ⟨WalkENIn.toReachPrefix w⟩

/-- Build `CyclicOrder4` from four strictly increasing positions on a single cyclic orbit. -/
def cyclicOrder4_of_strictMono_pos {D : Type} (p : Perm D) {L : Nat} (base : D)
    (h_inj : ∀ i j, i < L → j < L → Perm.iter p i base = Perm.iter p j base → i = j)
    (h_per : Perm.iter p L base = base)
    {p0 p1 p2 p3 : Nat} (h01 : p0 < p1) (h12 : p1 < p2) (h23 : p2 < p3) (h3L : p3 < L) :
    CyclicOrder4 p L (Perm.iter p p0 base) (Perm.iter p p1 base)
      (Perm.iter p p2 base) (Perm.iter p p3 base) where
  inj_lt := by
    intro i j hi hj heq
    rw [← perm_iter_add, ← perm_iter_add] at heq
    have hshift : ∀ m, m < L → ∃ m', m' < L ∧ Perm.iter p (m + p0) base = Perm.iter p m' base ∧
        (m + p0 < L → m' = m + p0) ∧ (L ≤ m + p0 → m' = m + p0 - L) := by
      intro m hm
      by_cases hm_lt : m + p0 < L
      · exact ⟨m + p0, hm_lt, rfl, fun _ => rfl, fun hle => by omega⟩
      · refine ⟨m + p0 - L, by omega, ?_, fun hlt => by omega, fun _ => rfl⟩
        calc Perm.iter p (m + p0) base
            = Perm.iter p ((m + p0 - L) + L) base := congrArg (fun k => Perm.iter p k base) (by omega)
          _ = Perm.iter p (m + p0 - L) (Perm.iter p L base) := perm_iter_add p _ _ base
          _ = Perm.iter p (m + p0 - L) base := by rw [h_per]
    obtain ⟨i', hi'L, hi'eq, hi'1, hi'2⟩ := hshift i hi
    obtain ⟨j', hj'L, hj'eq, hj'1, hj'2⟩ := hshift j hj
    have hij' := h_inj i' j' hi'L hj'L (by rw [← hi'eq, ← hj'eq, heq])
    by_cases hi_lt : i + p0 < L <;> by_cases hj_lt : j + p0 < L
    · have := hi'1 hi_lt; have := hj'1 hj_lt; omega
    · have := hi'1 hi_lt; have := hj'2 (by omega); omega
    · have := hi'2 (by omega); have := hj'1 hj_lt; omega
    · have := hi'2 (by omega); have := hj'2 (by omega); omega
  period := by
    calc Perm.iter p L (Perm.iter p p0 base)
        = Perm.iter p (L + p0) base := (perm_iter_add p L p0 base).symm
      _ = Perm.iter p (p0 + L) base := by rw [Nat.add_comm]
      _ = Perm.iter p p0 (Perm.iter p L base) := perm_iter_add p p0 L base
      _ = Perm.iter p p0 base := by rw [h_per]
  k1 := p1 - p0
  k2 := p2 - p1
  k3 := p3 - p2
  k4 := L - (p3 - p0)
  hk1 := by omega
  hk2 := by omega
  hk3 := by omega
  hk4 := by omega
  hsum := by omega
  hd1 := by rw [← perm_iter_add, show p1 - p0 + p0 = p1 by omega]
  hd2 := by rw [← perm_iter_add, show p1 - p0 + (p2 - p1) + p0 = p2 by omega]
  hd3 := by rw [← perm_iter_add, show p1 - p0 + (p2 - p1) + (p3 - p2) + p0 = p3 by omega]

end Hypermap

namespace Math

open _root_.Hypermap

/-- Sequential two-pair Kempe swap on disjoint color pairs `(θ.a, θ.b)` and `(θ.c, θ.d)`. -/
def swapKempeClassUnion (H : Hypermap) (c : H.FaceColoring) (θ : ColorPairing)
    (S_ab S_cd : H.Dart → Bool)
    (h_ab : H.KempeClosed c θ.a θ.b S_ab)
    (h_cd : H.KempeClosed c θ.c θ.d S_cd) :
    { c' : H.FaceColoring //
        ∀ d, c'.color d = if (S_ab d || S_cd d) = true then θ.swap (c.color d) else c.color d } := by
  let c1 := H.kempeSwap_valid c θ.a θ.b S_ab h_ab
  have hd_distinct := θ.distinct
  have hc1_cd_iff : ∀ x, (c1.color x = θ.c ∨ c1.color x = θ.d) ↔ (c.color x = θ.c ∨ c.color x = θ.d) := by
    intro x
    dsimp only [c1, Hypermap.kempeSwap_valid, Hypermap.kempeSwap]
    by_cases hSx : S_ab x = true
    · simp only [hSx, ↓reduceIte, Hypermap.swapColor]
      have hxab := h_ab.2.1 x hSx
      rcases hxab with ha | hb
      · rw [if_pos ha]
        have hc1_not : θ.b ≠ θ.c ∧ θ.b ≠ θ.d := ⟨hd_distinct.2.2.2.1, hd_distinct.2.2.2.2.1⟩
        have hc_not : θ.a ≠ θ.c ∧ θ.a ≠ θ.d := ⟨hd_distinct.2.1, hd_distinct.2.2.1⟩
        constructor
        · rintro (h | h); exact absurd h hc1_not.1; exact absurd h hc1_not.2
        · rintro (h | h); exact absurd (ha.symm.trans h) hc_not.1; exact absurd (ha.symm.trans h) hc_not.2
      · by_cases hba : θ.b = θ.a
        · exact absurd hba.symm hd_distinct.1
        · rw [if_neg (by rw [hb]; exact fun h => hba h), if_pos hb]
          have hc1_not : θ.a ≠ θ.c ∧ θ.a ≠ θ.d := ⟨hd_distinct.2.1, hd_distinct.2.2.1⟩
          have hc_not : θ.b ≠ θ.c ∧ θ.b ≠ θ.d := ⟨hd_distinct.2.2.2.1, hd_distinct.2.2.2.2.1⟩
          constructor
          · rintro (h | h); exact absurd h hc1_not.1; exact absurd h hc1_not.2
          · rintro (h | h); exact absurd (hb.symm.trans h) hc_not.1; exact absurd (hb.symm.trans h) hc_not.2
    · simp only [Bool.not_eq_true] at hSx
      simp only [hSx]; exact Iff.rfl
  have h_cd' : H.KempeClosed c1 θ.c θ.d S_cd := by
    refine ⟨h_cd.1, ?_, ?_⟩
    · intro d hd; exact (hc1_cd_iff d).mpr (h_cd.2.1 d hd)
    · intro d hd1 hd2
      exact h_cd.2.2 d ((hc1_cd_iff d).mp hd1) ((hc1_cd_iff (H.edge.f d)).mp hd2)
  let c2 := H.kempeSwap_valid c1 θ.c θ.d S_cd h_cd'
  refine ⟨c2, fun d => ?_⟩
  dsimp only [c2, c1, Hypermap.kempeSwap_valid, Hypermap.kempeSwap, ColorPairing.swap, Hypermap.swapColor]
  by_cases hSab : S_ab d = true <;> by_cases hScd : S_cd d = true
  · exfalso
    rcases h_ab.2.1 d hSab with ha | hb <;> rcases h_cd.2.1 d hScd with hc | hd
    · exact hd_distinct.2.1 (ha.symm.trans hc)
    · exact hd_distinct.2.2.1 (ha.symm.trans hd)
    · exact hd_distinct.2.2.2.1 (hb.symm.trans hc)
    · exact hd_distinct.2.2.2.2.1 (hb.symm.trans hd)
  · simp only [Bool.not_eq_true] at hScd
    simp only [hSab, hScd, Bool.true_or, ↓reduceIte, Bool.false_eq_true]
    rcases h_ab.2.1 d hSab with ha | hb
    · simp only [ha, ↓reduceIte]
    · simp only [hb, if_neg hd_distinct.1.symm, ↓reduceIte]
  · simp only [Bool.not_eq_true] at hSab
    simp only [hSab, hScd, Bool.false_or, ↓reduceIte, Bool.false_eq_true]
    rcases h_cd.2.1 d hScd with hc | hd
    · simp only [hc, if_neg hd_distinct.2.1.symm, if_neg hd_distinct.2.2.2.1.symm, ↓reduceIte]
    · simp only [hd, if_neg hd_distinct.2.2.1.symm, if_neg hd_distinct.2.2.2.2.1.symm,
        if_neg hd_distinct.2.2.2.2.2.symm, ↓reduceIte]
  · simp only [Bool.not_eq_true] at hSab hScd
    simp only [hSab, hScd, Bool.false_eq_true, ↓reduceIte, Bool.or_self]

def abReach (T : Hypermap) (vc : T.VertexColoring) (θ : ColorPairing)
    (ringDart : Nat → T.Dart) (i j : Nat) : Prop :=
  ReachENIn T.edge T.node (fun z => vc.color z = θ.a ∨ vc.color z = θ.b)
    (ringDart i) (ringDart j)

def cdReach (T : Hypermap) (vc : T.VertexColoring) (θ : ColorPairing)
    (ringDart : Nat → T.Dart) (i j : Nat) : Prop :=
  ReachENIn T.edge T.node (fun z => vc.color z = θ.c ∨ vc.color z = θ.d)
    (ringDart i) (ringDart j)

theorem extendsToInterior_congr_ring {c : Configuration} {b1 b2 : BoundaryColoring c}
    (hb : ∀ i, i < c.ringSize → b1 i = b2 i) (h : extendsToInterior c b1) :
    extendsToInterior c b2 := by
  obtain ⟨full, hfull, hval⟩ := h
  exact ⟨full, fun i hi => (hfull i hi).trans (hb i hi), hval⟩

theorem isValidBoundaryColoring_congr_ring {c : Configuration} {b1 b2 : BoundaryColoring c}
    (hb : ∀ i, i < c.ringSize → b1 i = b2 i) (h : IsValidBoundaryColoring c b1) :
    IsValidBoundaryColoring c b2 := fun i j hi hj hadj => by
  rw [← hb i hi, ← hb j hj]; exact h i j hi hj hadj

theorem isJointPlanarRingPartition_congr_ring {c : Configuration} {b1 b2 : BoundaryColoring c}
    {θ : ColorPairing} {equiv_ab equiv_cd : Nat → Nat → Prop}
    (hb : ∀ i, i < c.ringSize → b1 i = b2 i)
    (h : IsJointPlanarRingPartition c b1 θ equiv_ab equiv_cd) :
    IsJointPlanarRingPartition c b2 θ equiv_ab equiv_cd where
  ab_refl i hi hc := h.ab_refl i hi (by rwa [hb i hi])
  ab_symm := h.ab_symm
  ab_trans := h.ab_trans
  ab_color i hi j hj heq := by rw [← hb i hi]; exact h.ab_color i hi j hj heq
  cd_refl i hi hc := h.cd_refl i hi (by rwa [hb i hi])
  cd_symm := h.cd_symm
  cd_trans := h.cd_trans
  cd_color i hi j hj heq := by rw [← hb i hi]; exact h.cd_color i hi j hj heq
  ab_adj i hi j hj hadj hbi hbj := h.ab_adj i hi j hj hadj (by rwa [hb i hi]) (by rwa [hb j hj])
  cd_adj i hi j hj hadj hbi hbj := h.cd_adj i hi j hj hadj (by rwa [hb i hi]) (by rwa [hb j hj])
  ab_noncross := h.ab_noncross
  cd_noncross := h.cd_noncross
  cross_ab_cd := h.cross_ab_cd
  cross_cd_ab := h.cross_cd_ab

theorem eliminated_congr_ring {c : Configuration} {b1 : BoundaryColoring c}
    (h : Eliminated c b1) :
    ∀ {b2 : BoundaryColoring c}, (∀ i, i < c.ringSize → b1 i = b2 i) → Eliminated c b2 := by
  induction h with
  | ext b h_ext =>
    intro b2 hb
    exact .ext b2 (extendsToInterior_congr_ring hb h_ext)
  | kempe b θ resp h_val h_swap h_next ih =>
    intro b2 hb
    have hb_symm : ∀ i, i < c.ringSize → b2 i = b i := fun i hi => (hb i hi).symm
    refine .kempe b2 θ resp (isValidBoundaryColoring_congr_ring hb h_val)
      (fun eab ecd hp =>
        let hvs := h_swap eab ecd (isJointPlanarRingPartition_congr_ring hb_symm hp)
        ⟨hvs.ring_only, hvs.respects_ab, hvs.respects_cd⟩)
      (fun eab ecd hp =>
        ih eab ecd (isJointPlanarRingPartition_congr_ring hb_symm hp) (fun i hi => by
          dsimp only [boundaryKempeSwap]
          rw [hb i hi]))

theorem cappedRing_isJointPlanarRingPartition_vertex (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_planar : T.isPlanar darts.length darts = true)
    (c : Configuration) (ringDart : Nat → T.Dart)
    (h_ring_cyc : ∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
      ∃ L, Nonempty (CyclicOrder4 T.face L (ringDart i) (ringDart j) (ringDart l) (ringDart m)))
    (h_ring_adj : ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true →
      ∃ u v, SameOrbit T.node (ringDart i) u ∧ SameOrbit T.node (ringDart j) v ∧ T.edge.f u = v)
    (vc : T.VertexColoring) (b : BoundaryColoring c) (hb : ∀ i, i < c.ringSize → vc.color (ringDart i) = b i)
    (θ : ColorPairing) :
    IsJointPlanarRingPartition c b θ (abReach T vc θ ringDart) (cdReach T vc θ ringDart) := by
  have n_symm : ∀ {a b : T.Dart}, SameOrbit T.node a b → SameOrbit T.node b a :=
    sameOrbit_symm_of_complete T.node darts h_all
  let Pab : T.Dart → Prop := fun z => vc.color z = θ.a ∨ vc.color z = θ.b
  let Pcd : T.Dart → Prop := fun z => vc.color z = θ.c ∨ vc.color z = θ.d
  have hPab_n : ∀ z, Pab (T.node.f z) ↔ Pab z := fun z => by
    simp only [Pab, vc.node_invariant z]
  have hPcd_n : ∀ z, Pcd (T.node.f z) ↔ Pcd z := fun z => by
    simp only [Pcd, vc.node_invariant z]
  have hP_adj : ∀ (P : T.Dart → Prop), (∀ z, P (T.node.f z) ↔ P z) →
      ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true →
        P (ringDart i) → P (ringDart j) → ReachENIn T.edge T.node P (ringDart i) (ringDart j) := by
    intro P hPn i j hi hj hadj hpi hpj
    obtain ⟨u, v, hui, hvj, huv⟩ := h_ring_adj i j hi hj hadj
    obtain ⟨ku, rfl⟩ := hui
    obtain ⟨kv, hkv⟩ := n_symm hvj
    have hPu : P (Perm.iter T.node ku (ringDart i)) :=
      pred_of_sameOrbit hPn hpi ⟨ku, rfl⟩
    have hPv : P (T.edge.f (Perm.iter T.node ku (ringDart i))) := by
      rw [huv]; exact pred_of_sameOrbit hPn hpj hvj
    have h_iu : ReachENIn T.edge T.node P (ringDart i) (Perm.iter T.node ku (ringDart i)) :=
      nonempty_walkENIn_iff_reachENIn.mp
        ⟨WalkENIn.ofSameOrbit T.edge T.node P hPn (ringDart i) hpi ku⟩
    have h_iv : ReachENIn T.edge T.node P (ringDart i) v := huv ▸ .step_e h_iu hPv
    have h_vj : ReachENIn T.edge T.node P v (ringDart j) := by
      rw [← hkv]
      exact nonempty_walkENIn_iff_reachENIn.mp
        ⟨WalkENIn.ofSameOrbit T.edge T.node P hPn v (huv ▸ hPv) kv⟩
    exact reachENIn_trans h_iv h_vj
  have h_pref_n : ∀ (P : T.Dart → Prop), (∀ z, P (T.node.f z) ↔ P z) → ∀ root z,
      (P (T.node.f z) ∧ ReachENIn T.edge T.node P root (T.node.f z)) ↔
      (P z ∧ ReachENIn T.edge T.node P root z) := fun P hPn root z => by
    constructor
    · rintro ⟨hp, hr⟩
      have hpz := (hPn z).mp hp
      exact ⟨hpz, (T.node.left_inv z) ▸ .step_n_bwd hr (by rw [T.node.left_inv]; exact hpz)⟩
    · rintro ⟨hp, hr⟩
      have hpnf := (hPn z).mpr hp
      exact ⟨hpnf, .step_n_fwd hr hpnf⟩
  refine
    { ab_refl := fun i hi hc => .refl (by rw [hb i hi]; exact hc)
      ab_symm := fun _ _ _ _ h => reachENIn_symm_of_involution T.edge_involution h
      ab_trans := fun _ _ _ _ _ _ h1 h2 => reachENIn_trans h1 h2
      ab_color := fun i hi _ _ h => by
        rw [← hb i hi]; exact (reachENIn_left h : Pab (ringDart i))
      cd_refl := fun i hi hc => .refl (by rw [hb i hi]; exact hc)
      cd_symm := fun _ _ _ _ h => reachENIn_symm_of_involution T.edge_involution h
      cd_trans := fun _ _ _ _ _ _ h1 h2 => reachENIn_trans h1 h2
      cd_color := fun i hi _ _ h => by
        rw [← hb i hi]; exact (reachENIn_left h : Pcd (ringDart i))
      ab_adj := fun i hi j hj hadj hbi hbj =>
        hP_adj Pab hPab_n i j hi hj hadj
          (by dsimp only [Pab]; rw [hb i hi]; exact hbi)
          (by dsimp only [Pab]; rw [hb j hj]; exact hbj)
      cd_adj := fun i hi j hj hadj hbi hbj =>
        hP_adj Pcd hPcd_n i j hi hj hadj
          (by dsimp only [Pcd]; rw [hb i hi]; exact hbi)
          (by dsimp only [Pcd]; rw [hb j hj]; exact hbj)
      ab_noncross := fun i j l m hij hjl hlm hm hil hjm => by
        obtain ⟨L, ⟨hc⟩⟩ := h_ring_cyc i j l m hij hjl hlm hm
        obtain ⟨z, ⟨_, hiz⟩, ⟨_, hjz⟩⟩ := alternating_walks_intersect_of_cyclic_face
          T darts h_nodup h_all h_planar hc
          (fun u => Pab u ∧ ReachENIn T.edge T.node Pab (ringDart i) u)
          (fun u => Pab u ∧ ReachENIn T.edge T.node Pab (ringDart j) u)
          (h_pref_n Pab hPab_n (ringDart i))
          (h_pref_n Pab hPab_n (ringDart j))
          (reachENIn_toReachPrefix hil)
          (reachENIn_toReachPrefix hjm)
        exact reachENIn_trans hiz (reachENIn_symm_of_involution T.edge_involution hjz)
      cd_noncross := fun i j l m hij hjl hlm hm hil hjm => by
        obtain ⟨L, ⟨hc⟩⟩ := h_ring_cyc i j l m hij hjl hlm hm
        obtain ⟨z, ⟨_, hiz⟩, ⟨_, hjz⟩⟩ := alternating_walks_intersect_of_cyclic_face
          T darts h_nodup h_all h_planar hc
          (fun u => Pcd u ∧ ReachENIn T.edge T.node Pcd (ringDart i) u)
          (fun u => Pcd u ∧ ReachENIn T.edge T.node Pcd (ringDart j) u)
          (h_pref_n Pcd hPcd_n (ringDart i))
          (h_pref_n Pcd hPcd_n (ringDart j))
          (reachENIn_toReachPrefix hil)
          (reachENIn_toReachPrefix hjm)
        exact reachENIn_trans hiz (reachENIn_symm_of_involution T.edge_involution hjz)
      cross_ab_cd := fun i j l m hij hjl hlm hm hil hjm => by
        obtain ⟨L, ⟨hc⟩⟩ := h_ring_cyc i j l m hij hjl hlm hm
        obtain ⟨z, hz1, hz2⟩ := alternating_walks_intersect_of_cyclic_face
          T darts h_nodup h_all h_planar hc Pab Pcd hPab_n hPcd_n hil hjm
        have hd := θ.distinct
        rcases hz1 with ha | hb' <;> rcases hz2 with hc' | hd'
        · exact hd.2.1 (ha.symm.trans hc')
        · exact hd.2.2.1 (ha.symm.trans hd')
        · exact hd.2.2.2.1 (hb'.symm.trans hc')
        · exact hd.2.2.2.2.1 (hb'.symm.trans hd')
      cross_cd_ab := fun i j l m hij hjl hlm hm hil hjm => by
        obtain ⟨L, ⟨hc⟩⟩ := h_ring_cyc i j l m hij hjl hlm hm
        obtain ⟨z, hz1, hz2⟩ := alternating_walks_intersect_of_cyclic_face
          T darts h_nodup h_all h_planar hc Pcd Pab hPcd_n hPab_n hil hjm
        have hd := θ.distinct
        rcases hz2 with ha | hb' <;> rcases hz1 with hc' | hd'
        · exact hd.2.1 (ha.symm.trans hc')
        · exact hd.2.2.1 (ha.symm.trans hd')
        · exact hd.2.2.2.1 (hb'.symm.trans hc')
        · exact hd.2.2.2.2.1 (hb'.symm.trans hd') }

theorem cappedRing_isJointPlanarRingPartition (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (c : Configuration) (ringDart : Nat → H.Dart)
    (h_ring_cyc : ∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
      ∃ L, Nonempty (CyclicOrder4 H.dual.face L (ringDart i) (ringDart j) (ringDart l) (ringDart m)))
    (h_ring_adj : ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true →
      ∃ u v, SameOrbit H.face (ringDart i) u ∧ SameOrbit H.face (ringDart j) v ∧ H.edge.f u = v)
    (col : H.FaceColoring) (b : BoundaryColoring c) (hb : ∀ i, i < c.ringSize → col.color (ringDart i) = b i)
    (θ : ColorPairing) :
    IsJointPlanarRingPartition c b θ
      (abReach H.dual (H.faceColoringToVertexColoringOfDual col) θ ringDart)
      (cdReach H.dual (H.faceColoringToVertexColoringOfDual col) θ ringDart) := by
  have h_dual_planar : H.dual.isPlanar darts.length darts = true := by
    rw [isPlanar_dual H darts h_nodup h_all (Nat.le_refl _)]; exact h_planar
  have f_symm : ∀ {a b : H.Dart}, SameOrbit H.face a b → SameOrbit H.face b a :=
    sameOrbit_symm_of_complete H.face darts h_all
  have h_adj' : ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true →
      ∃ u v, SameOrbit H.dual.node (ringDart i) u ∧
        SameOrbit H.dual.node (ringDart j) v ∧ H.dual.edge.f u = v := by
    intro i j hi hj hadj
    obtain ⟨u, v, hui, hvj, huv⟩ := h_ring_adj i j hi hj hadj
    have h_f_to_dn : ∀ {x y : H.Dart}, SameOrbit H.face x y → SameOrbit H.dual.node x y := by
      intro x y hxy
      obtain ⟨k, hk⟩ := f_symm hxy
      have h_inv_cancel : ∀ (n : Nat) (a : H.Dart),
          Perm.iter H.face.symm n (Perm.iter H.face n a) = a := by
        intro n
        induction n with
        | zero => intro _; rfl
        | succ n' ih =>
          intro a
          have h1 : Perm.iter H.face (n' + 1) a = H.face.f (Perm.iter H.face n' a) :=
            (perm_iter_succ_left H.face n' a).symm
          have h2 : Perm.iter H.face.symm (n' + 1) (H.face.f (Perm.iter H.face n' a)) =
              Perm.iter H.face.symm n' (H.face.inv (H.face.f (Perm.iter H.face n' a))) := by
            calc Perm.iter H.face.symm (n' + 1) (H.face.f (Perm.iter H.face n' a))
                = Perm.iter H.face.symm (n' + 1) _ := rfl
              _ = Perm.iter H.face.symm n' (Perm.iter H.face.symm 1 (H.face.f (Perm.iter H.face n' a))) :=
                perm_iter_add H.face.symm n' 1 _
              _ = Perm.iter H.face.symm n' (H.face.inv (H.face.f (Perm.iter H.face n' a))) := rfl
          rw [h1, h2, H.face.left_inv, ih]
      exact ⟨k, by
        change Perm.iter H.face.symm k x = y
        rw [← hk]; exact h_inv_cancel k y⟩
    exact ⟨u, v, h_f_to_dn hui, h_f_to_dn hvj, huv⟩
  exact cappedRing_isJointPlanarRingPartition_vertex H.dual darts h_nodup h_all h_dual_planar
    c ringDart h_ring_cyc h_adj' (H.faceColoringToVertexColoringOfDual col) b hb θ

theorem kempe_pullback_of_cappedRing (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (c : Configuration) (ringDart : Nat → H.Dart)
    (h_ring_cyc : ∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
      ∃ L, Nonempty (CyclicOrder4 H.dual.face L (ringDart i) (ringDart j) (ringDart l) (ringDart m)))
    (h_ring_adj : ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true →
      ∃ u v, SameOrbit H.face (ringDart i) u ∧ SameOrbit H.face (ringDart j) v ∧ H.edge.f u = v)
    (bnd_coloring : H.FaceColoring → BoundaryColoring c)
    (hbnd_eq : ∀ (col : H.FaceColoring) (i : Nat), i < c.ringSize → bnd_coloring col i = col.color (ringDart i)) :
    ∀ (col : H.FaceColoring), Eliminated c (bnd_coloring col) →
      ∃ (col' : H.FaceColoring) (ext : Nat → Color),
        (∀ i, i < c.ringSize → ext i = bnd_coloring col' i) ∧ IsValidConfigColoring c ext := by
  classical
  have h_part : ∀ (col : H.FaceColoring) (θ : ColorPairing),
      IsJointPlanarRingPartition c (bnd_coloring col) θ
        (abReach H.dual (H.faceColoringToVertexColoringOfDual col) θ ringDart)
        (cdReach H.dual (H.faceColoringToVertexColoringOfDual col) θ ringDart) :=
    fun col θ => cappedRing_isJointPlanarRingPartition H darts h_nodup h_all h_planar c ringDart
      h_ring_cyc h_ring_adj col (bnd_coloring col) (fun i hi => (hbnd_eq col i hi).symm) θ
  have h_pull : ∀ (b : BoundaryColoring c) (h_el : Eliminated c b) (col : H.FaceColoring),
      (∀ i, i < c.ringSize → b i = bnd_coloring col i) →
      ∃ (col' : H.FaceColoring) (ext : Nat → Color),
        (∀ i, i < c.ringSize → ext i = bnd_coloring col' i) ∧ IsValidConfigColoring c ext := by
    intro b h_el
    induction h_el with
    | ext b h_ext =>
      intro col hb
      obtain ⟨full, hfull, hval⟩ := extendsToInterior_congr_ring hb h_ext
      exact ⟨col, full, hfull, hval⟩
    | kempe b θ resp h_val h_swap h_next ih =>
      intro col hb
      have hb_symm : ∀ i, i < c.ringSize → bnd_coloring col i = b i := fun i hi => (hb i hi).symm
      let eab := abReach H.dual (H.faceColoringToVertexColoringOfDual col) θ ringDart
      let ecd := cdReach H.dual (H.faceColoringToVertexColoringOfDual col) θ ringDart
      have hp_b : IsJointPlanarRingPartition c b θ eab ecd :=
        isJointPlanarRingPartition_congr_ring hb_symm (h_part col θ)
      have h_vs := h_swap eab ecd hp_b
      let S_ring := resp eab ecd
      let S_ab : H.Dart → Bool := fun d =>
        decide (∃ i, i < c.ringSize ∧ S_ring i = true ∧
          ReachENIn H.dual.edge H.dual.node (fun z => col.color z = θ.a ∨ col.color z = θ.b) (ringDart i) d)
      let S_cd : H.Dart → Bool := fun d =>
        decide (∃ i, i < c.ringSize ∧ S_ring i = true ∧
          ReachENIn H.dual.edge H.dual.node (fun z => col.color z = θ.c ∨ col.color z = θ.d) (ringDart i) d)
      have h_closed : ∀ (a' b' : Color) (S' : H.Dart → Bool)
          (hS' : ∀ d, S' d = true ↔ ∃ i, i < c.ringSize ∧ S_ring i = true ∧
            ReachENIn H.dual.edge H.dual.node (fun z => col.color z = a' ∨ col.color z = b') (ringDart i) d),
          H.KempeClosed col a' b' S' := by
        intro a' b' S' hS'
        refine ⟨?_, ?_, ?_⟩
        · intro d
          apply Bool.eq_iff_iff.mpr
          rw [hS', hS']
          constructor
          · rintro ⟨i, hi, hSi, hreach⟩
            refine ⟨i, hi, hSi, ?_⟩
            have hcol_d : col.color d = a' ∨ col.color d = b' := by
              have hfd : col.color (H.face.f d) = a' ∨ col.color (H.face.f d) = b' :=
                @reachENIn_right _ H.dual.edge H.dual.node
                  (fun z => col.color z = a' ∨ col.color z = b') _ _ hreach
              rwa [col.face_invariant] at hfd
            have hf := ReachENIn.step_n_fwd hreach (by
              have hcol_inv : col.color (H.face.inv (H.face.f d)) = a' ∨
                  col.color (H.face.inv (H.face.f d)) = b' := by
                rw [H.face.left_inv]; exact hcol_d
              exact hcol_inv)
            change ReachENIn H.dual.edge H.dual.node _ (ringDart i) (H.face.inv (H.face.f d)) at hf
            rwa [H.face.left_inv] at hf
          · rintro ⟨i, hi, hSi, hreach⟩
            refine ⟨i, hi, hSi, .step_n_bwd hreach ?_⟩
            change col.color (H.face.f d) = a' ∨ col.color (H.face.f d) = b'
            rw [col.face_invariant]
            exact @reachENIn_right _ H.dual.edge H.dual.node
              (fun z => col.color z = a' ∨ col.color z = b') _ _ hreach
        · intro d hd
          obtain ⟨_, _, _, hr⟩ := (hS' d).mp hd
          exact @reachENIn_right _ H.dual.edge H.dual.node
            (fun z => col.color z = a' ∨ col.color z = b') _ _ hr
        · intro d hd hed
          apply Bool.eq_iff_iff.mpr
          rw [hS', hS']
          constructor
          · rintro ⟨i, hi, hSi, hreach⟩
            have hcol_inv : col.color (H.dual.edge.f (H.edge.f d)) = a' ∨
                col.color (H.dual.edge.f (H.edge.f d)) = b' := by
              change col.color (H.edge.f (H.edge.f d)) = a' ∨ col.color (H.edge.f (H.edge.f d)) = b'
              rw [H.edge_involution]; exact hd
            have h2 := ReachENIn.step_e hreach hcol_inv
            change ReachENIn H.dual.edge H.dual.node _ (ringDart i) (H.edge.f (H.edge.f d)) at h2
            rw [H.edge_involution] at h2
            exact ⟨i, hi, hSi, h2⟩
          · rintro ⟨i, hi, hSi, hreach⟩
            exact ⟨i, hi, hSi, .step_e hreach hed⟩
      have h_ab := h_closed θ.a θ.b S_ab (fun d => decide_eq_true_iff)
      have h_cd := h_closed θ.c θ.d S_cd (fun d => decide_eq_true_iff)
      obtain ⟨col_mid, hcol_mid⟩ := swapKempeClassUnion H col θ S_ab S_cd h_ab h_cd
      refine ih eab ecd hp_b col_mid fun j hj => ?_
      dsimp only [boundaryKempeSwap]
      rw [hbnd_eq col_mid j hj, hcol_mid (ringDart j), hb j hj, hbnd_eq col j hj]
      change (if S_ring j = true then θ.swap (col.color (ringDart j)) else col.color (ringDart j)) = _
      by_cases hSj : S_ring j = true
      · rw [if_pos hSj]
        by_cases hSab_cd : (S_ab (ringDart j) || S_cd (ringDart j)) = true
        · rw [if_pos hSab_cd]
        · have hSab_false : (S_ab (ringDart j) || S_cd (ringDart j)) = false :=
            Bool.eq_false_iff.mpr hSab_cd
          simp only [Bool.not_eq_true, Bool.or_eq_false_iff, S_ab, S_cd, decide_eq_false_iff_not] at hSab_cd
          dsimp only [ColorPairing.swap]
          have hna : col.color (ringDart j) ≠ θ.a := fun h => hSab_cd.1 ⟨j, hj, hSj, .refl (.inl h)⟩
          have hnb : col.color (ringDart j) ≠ θ.b := fun h => hSab_cd.1 ⟨j, hj, hSj, .refl (.inr h)⟩
          have hnc : col.color (ringDart j) ≠ θ.c := fun h => hSab_cd.2 ⟨j, hj, hSj, .refl (.inl h)⟩
          have hnd : col.color (ringDart j) ≠ θ.d := fun h => hSab_cd.2 ⟨j, hj, hSj, .refl (.inr h)⟩
          rw [if_neg hna, if_neg hnb, if_neg hnc, if_neg hnd, hSab_false, if_neg Bool.false_ne_true]
      · rw [if_neg hSj]
        have h_false : (S_ab (ringDart j) || S_cd (ringDart j)) = false := by
          rw [Bool.or_eq_false_iff]
          constructor
          · rw [decide_eq_false_iff_not]
            rintro ⟨i, hi, hSi, hreach⟩
            have heq_S : S_ring i = S_ring j := h_vs.respects_ab i hi j hj hreach
            rw [hSi] at heq_S; exact hSj heq_S.symm
          · rw [decide_eq_false_iff_not]
            rintro ⟨i, hi, hSi, hreach⟩
            have heq_S : S_ring i = S_ring j := h_vs.respects_cd i hi j hj hreach
            rw [hSi] at heq_S; exact hSj heq_S.symm
        rw [h_false, if_neg Bool.false_ne_true]
  exact fun col h_el => h_pull (bnd_coloring col) h_el col (fun _ _ => rfl)

end Math


