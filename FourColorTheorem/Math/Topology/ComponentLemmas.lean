module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Topology.OrbitLemmas
public import FourColorTheorem.Math.Topology.Euler
public import FourColorTheorem.Math.Topology.Paths
public import FourColorTheorem.Math.Topology.Jordan

@[expose] public section

/-!
# Connected Components, Walk Equivalence, and Dual Planarity (`ComponentLemmas`)

This module develops the complete theory of `Hypermap.getComponent`, `Hypermap.countComponents`,
and `Hypermap.isPlanar` on finite complete hypermaps, filling the gap alongside `OrbitLemmas.lean`:

1. **Walk Algebra & Duality**: `Walk.trans`, `Walk.symm`, permutation-iteration walks, and
   `walk_dual_iff_walk` (`Nonempty (Walk H.dual d x) ↔ Nonempty (Walk H d x)`).
2. **BFS Lyapunov Potential & Clean Termination**: `getComponentAux H queue visited fuel` obeys
   `queue.length + 5 * unvisitedCount darts visited ≤ fuel`, decreasing by `≥ 1` on visited hits
   and by `≥ 2` on new expansions, guaranteeing `fuel`-irrelevance for `fuel ≥ darts.length`.
3. **Exact Reachability Equivalence**: `(x ∈ getComponent H fuel d) ↔ Nonempty (Walk H d x)`
   for `fuel ≥ darts.length`, yielding reflexivity, symmetry, transitivity, orbit containment,
   and connectedness characterizations (`numComponents_eq_one_iff_of_complete`).
4. **Dual Planarity & Partition Additivity**: `countComponents_dual_of_complete`,
   `isPlanar_dual_of_complete`, additive splitting (`countOrbits_partition_of_closed`,
   `countComponents_partition_of_closed`), and order/element-invariance (`countOrbits_eq_of_iff_mem`,
   `countComponents_eq_of_iff_mem`).
-/

namespace Hypermap

set_option linter.unusedSectionVars false

private local instance instBEqDualDart_comp (H : Hypermap) [BEq H.Dart] : BEq H.dual.Dart := ‹BEq H.Dart›
private local instance instDecidableEqDualDart_comp (H : Hypermap) [DecidableEq H.Dart] : DecidableEq H.dual.Dart := ‹DecidableEq H.Dart›

section WalkAlgebra

/-- Inverse of `H.face` expresses as `edge ∘ node`. -/
theorem face_inv_eq_edge_node (H : Hypermap) (d : H.Dart) :
    H.face.inv d = H.edge.f (H.node.f d) := by
  have h := H.edge_node_face_id (H.face.inv d)
  rw [H.face.right_inv] at h
  exact h.symm

/-- Concatenation of hypermap walks. -/
def Walk.trans (H : Hypermap) : {x y z : H.Dart} → Walk H x y → Walk H y z → Walk H x z
  | _, _, _, Walk.refl _, w2 => w2
  | _, _, _, Walk.step s w1, w2 => Walk.step s (Walk.trans H w1 w2)

/-- Reversal of a hypermap walk via `Step.symm`. -/
def Walk.symm (H : Hypermap) : {x y : H.Dart} → Walk H x y → Walk H y x
  | _, _, Walk.refl d => Walk.refl d
  | _, _, Walk.step s w => Walk.snoc H (Walk.symm H w) (Step.symm H s)

/-- Build a walk by iterating any step-preserving permutation `k` times. -/
def Walk.ofPermIter (H : Hypermap) (p : Perm H.Dart)
    (h_step : ∀ u : H.Dart, Step H u (p.f u)) :
    ∀ (k : Nat) (d : H.Dart), Walk H d (Perm.iter p k d)
  | 0, d => Walk.refl d
  | k + 1, d =>
    Walk.step (h_step d) (by
      rw [Perm.iter_succ_right]
      exact Walk.ofPermIter H p h_step k (p.f d))

/-- Every step in `H.dual` is a step in `H`. -/
theorem step_of_step_dual (H : Hypermap) {d d' : H.Dart} (s : Step H.dual d d') : Step H d d' := by
  cases s with
  | node h => exact Step.faceInv h
  | nodeInv h => exact Step.face h
  | edge h => exact Step.edge h
  | face h => exact Step.nodeInv h
  | faceInv h => exact Step.node h

/-- Every step in `H` is a step in `H.dual`. -/
theorem step_dual_of_step (H : Hypermap) {d d' : H.Dart} (s : Step H d d') : Step H.dual d d' := by
  cases s with
  | node h => exact Step.faceInv h
  | nodeInv h => exact Step.face h
  | edge h => exact Step.edge h
  | face h => exact Step.nodeInv h
  | faceInv h => exact Step.node h

/-- Every walk in `H.dual` transports directly to a walk in `H`. -/
def walk_of_walk_dual (H : Hypermap) : {d x : H.Dart} → Walk H.dual d x → Walk H d x
  | _, _, @Walk.refl _ d => @Walk.refl H d
  | _, _, Walk.step s w => Walk.step (step_of_step_dual H s) (walk_of_walk_dual H w)

/-- Every walk in `H` transports directly to a walk in `H.dual`. -/
def walk_dual_of_walk (H : Hypermap) : {d x : H.Dart} → Walk H d x → Walk H.dual d x
  | _, _, @Walk.refl _ d => @Walk.refl H.dual d
  | _, _, Walk.step s w => Walk.step (step_dual_of_step H s) (walk_dual_of_walk H w)

/-- Exact walk-connectivity equivalence between `H.dual` and `H`. -/
theorem walk_dual_iff_walk (H : Hypermap) (d x : H.Dart) :
    Nonempty (Walk H.dual d x) ↔ Nonempty (Walk H d x) :=
  ⟨fun ⟨w⟩ => ⟨walk_of_walk_dual H w⟩, fun ⟨w⟩ => ⟨walk_dual_of_walk H w⟩⟩

/-- If a predicate `P` is closed under `H.edge.f`, `H.edge.inv`, `H.node.f`, and `H.node.inv`,
    then it is closed under `H.face.f`, `H.face.inv`, and every `Step H`. -/
theorem step_closed_of_edge_node_closed (H : Hypermap) (P : H.Dart → Prop)
    (hef : ∀ u, P u → P (H.edge.f u))
    (hei : ∀ u, P u → P (H.edge.inv u))
    (hnf : ∀ u, P u → P (H.node.f u))
    (hni : ∀ u, P u → P (H.node.inv u)) :
    ∀ {u v : H.Dart}, Step H u v → P u → P v := by
  intro u v s hu
  cases s with
  | node h => subst h; exact hnf u hu
  | nodeInv h => subst h; exact hni u hu
  | edge h => subst h; exact hef u hu
  | face h =>
    subst h
    rw [H.face_eq_node_inv_edge_inv]
    exact hni (H.edge.inv u) (hei u hu)
  | faceInv h =>
    subst h
    rw [face_inv_eq_edge_node]
    exact hef (H.node.f u) (hnf u hu)

/-- Any predicate closed under `Step H` is invariant along any `Walk H`. -/
theorem pred_end_of_walk_of_closed (H : Hypermap) (P : H.Dart → Prop)
    (h_step : ∀ {u v : H.Dart}, Step H u v → P u → P v) :
    ∀ {d x : H.Dart}, Walk H d x → P d → P x
  | _, _, Walk.refl _, hd => hd
  | _, _, Walk.step s w, hd => pred_end_of_walk_of_closed H P h_step w (h_step s hd)

end WalkAlgebra

section ListFilterPotential

variable {D : Type} [DecidableEq D]

/-- Boolean filter commutes. -/
theorem filter_comm {α : Type} (p q : α → Bool) (l : List α) :
    (l.filter p).filter q = (l.filter q).filter p := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    dsimp [List.filter]
    cases hp : p a <;> cases hq : q a <;> simp [List.filter, hp, hq, ih]

/-- Filtering again by a weaker predicate `q` (`p x → q x`) leaves `l.filter p` unchanged. -/
theorem filter_filter_eq_of_imp {α : Type} {p q : α → Bool} {l : List α}
    (h_imp : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).filter q = l.filter p := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have h_as : ∀ x ∈ as, p x = true → q x = true :=
      fun x hx => h_imp x (List.mem_cons_of_mem a hx)
    dsimp [List.filter]
    cases hpa : p a with
    | false =>
      dsimp
      exact ih h_as
    | true =>
      have hqa : q a = true := h_imp a List.mem_cons_self hpa
      dsimp
      simp [hqa, ih h_as]

/-- Filtered length monotonicity under pointwise implication. -/
theorem filter_length_le_of_imp {l : List D} {p q : D → Bool}
    (h_imp : ∀ x, q x = true → p x = true) :
    (l.filter q).length ≤ (l.filter p).length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a as ih =>
    dsimp [List.filter]
    cases hqa : q a with
    | false =>
      cases p a <;> dsimp
      · exact ih
      · exact Nat.le_trans ih (Nat.le_succ _)
    | true =>
      have hpa : p a = true := h_imp a hqa
      rw [hpa]
      exact Nat.succ_le_succ ih

/-- Strict decrease in filtered length when `q ≤ p` and at least one witness in `l` drops out. -/
theorem filter_length_lt_of_imp_of_exists {l : List D} {p q : D → Bool}
    (h_imp : ∀ x, q x = true → p x = true)
    (h_ex : ∃ y ∈ l, p y = true ∧ q y = false) :
    (l.filter q).length < (l.filter p).length := by
  obtain ⟨y, hy_mem, hy_p, hy_q⟩ := h_ex
  induction l with
  | nil => cases hy_mem
  | cons a as ih =>
    dsimp [List.filter]
    cases hpa : p a with
    | false =>
      have hqa : q a = false := by
        cases hq : q a with
        | false => rfl
        | true => rw [h_imp a hq] at hpa; contradiction
      rw [hqa]
      dsimp
      have hy_as : y ∈ as := by
        rcases List.mem_cons.mp hy_mem with rfl | htail
        · rw [hy_p] at hpa; contradiction
        · exact htail
      exact ih hy_as
    | true =>
      cases hqa : q a with
      | false =>
        dsimp
        exact Nat.lt_succ_of_le (filter_length_le_of_imp h_imp)
      | true =>
        dsimp
        have hy_as : y ∈ as := by
          rcases List.mem_cons.mp hy_mem with rfl | htail
          · rw [hy_q] at hqa; contradiction
          · exact htail
        exact Nat.succ_lt_succ (ih hy_as)

/-- Number of unvisited darts in `darts` (measured via filter length, works even without `Nodup`). -/
def unvisitedCount (darts visited : List D) : Nat :=
  (darts.filter (fun x => !visited.contains x)).length

/-- Adding an unvisited dart `d ∈ darts` strictly decreases `unvisitedCount`. -/
theorem unvisitedCount_cons_lt (darts visited : List D) {d : D}
    (hd_in : d ∈ darts) (hd_not : visited.contains d = false) :
    unvisitedCount darts (d :: visited) + 1 ≤ unvisitedCount darts visited := by
  dsimp [unvisitedCount]
  apply filter_length_lt_of_imp_of_exists
  · intro x hx
    simp at hx ⊢
    exact hx.2
  · refine ⟨d, hd_in, ?_, ?_⟩
    · rw [hd_not]; rfl
    · simp

/-- `unvisitedCount` never exceeds `darts.length`. -/
theorem unvisitedCount_le_length (darts visited : List D) :
    unvisitedCount darts visited ≤ darts.length := by
  dsimp [unvisitedCount]
  exact filter_length_le _ darts

/-- At the start of BFS (`visited = []`), `unvisitedCount darts [] = darts.length`. -/
theorem unvisitedCount_nil (darts : List D) :
    unvisitedCount darts [] = darts.length := by
  dsimp [unvisitedCount]
  simp

end ListFilterPotential

section GetComponentAuxTheory

/-- Every dart already in `visited` remains in `getComponentAux H queue visited fuel`. -/
theorem visited_subset_getComponentAux (H : Hypermap) [BEq H.Dart]
    (queue visited : List H.Dart) (fuel : Nat) :
    ∀ x ∈ visited, x ∈ getComponentAux H queue visited fuel := by
  induction fuel generalizing queue visited with
  | zero =>
    intro x hx
    exact hx
  | succ f ih =>
    cases queue with
    | nil =>
      intro x hx
      exact hx
    | cons d ds =>
      dsimp [getComponentAux]
      split
      · exact ih ds visited
      · intro x hx
        exact ih _ (d :: visited) x (List.mem_cons_of_mem d hx)

/-- `getComponentAux` preserves duplicate-freedom (`Nodup`) of `visited`. -/
theorem getComponentAux_nodup (H : Hypermap) [DecidableEq H.Dart]
    (queue visited : List H.Dart) (fuel : Nat) (h_nd : visited.Nodup) :
    (getComponentAux H queue visited fuel).Nodup := by
  induction fuel generalizing queue visited with
  | zero => exact h_nd
  | succ f ih =>
    cases queue with
    | nil => exact h_nd
    | cons d ds =>
      dsimp [getComponentAux]
      cases hc : visited.contains d with
      | true =>
        dsimp
        exact ih ds visited h_nd
      | false =>
        dsimp
        apply ih
        refine List.nodup_cons.mpr ⟨?_, h_nd⟩
        intro hm
        have ht : visited.contains d = true := List.contains_iff_mem.mpr hm
        rw [ht] at hc
        contradiction

/-- `getComponent H fuel d` is always duplicate-free (`Nodup`). -/
theorem getComponent_nodup (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart) :
    (getComponent H fuel d).Nodup :=
  getComponentAux_nodup H [d] [] (5 * fuel + 1) List.nodup_nil

/-- Every dart returned by `getComponentAux` is walk-reachable from `start`, provided all initial
    `queue` and `visited` darts are walk-reachable from `start`. -/
theorem getComponentAux_walk_sound (H : Hypermap) [BEq H.Dart] (start : H.Dart) :
    ∀ (fuel : Nat) (queue visited : List H.Dart),
      (∀ q ∈ queue, Nonempty (Walk H start q)) →
      (∀ v ∈ visited, Nonempty (Walk H start v)) →
      ∀ x ∈ getComponentAux H queue visited fuel, Nonempty (Walk H start x)
  | 0, _, _, _, hv, x, hx => hv x hx
  | _ + 1, [], _, _, hv, x, hx => hv x hx
  | f + 1, d :: ds, visited, hq, hv, x, hx => by
    dsimp [getComponentAux] at hx
    split at hx
    · exact getComponentAux_walk_sound H start f ds visited
        (fun q hmem => hq q (List.mem_cons_of_mem d hmem)) hv x hx
    · have hd : Nonempty (Walk H start d) := hq d List.mem_cons_self
      obtain ⟨wd⟩ := hd
      have hq' : ∀ q ∈ H.edge.f d :: H.edge.inv d :: H.node.f d :: H.node.inv d :: ds,
          Nonempty (Walk H start q) := by
        intro q hmem
        rcases List.mem_cons.mp hmem with rfl | hmem1
        · exact ⟨Walk.snoc H wd (Step.edge rfl)⟩
        · rcases List.mem_cons.mp hmem1 with rfl | hmem2
          · rw [H.edge_inv_eq_edge d]
            exact ⟨Walk.snoc H wd (Step.edge rfl)⟩
          · rcases List.mem_cons.mp hmem2 with rfl | hmem3
            · exact ⟨Walk.snoc H wd (Step.node rfl)⟩
            · rcases List.mem_cons.mp hmem3 with rfl | htail
              · exact ⟨Walk.snoc H wd (Step.nodeInv rfl)⟩
              · exact hq q (List.mem_cons_of_mem d htail)
      have hv' : ∀ v ∈ d :: visited, Nonempty (Walk H start v) := by
        intro v hvmem
        rcases List.mem_cons.mp hvmem with rfl | htail
        · exact ⟨wd⟩
        · exact hv v htail
      exact getComponentAux_walk_sound H start f _ (d :: visited) hq' hv' x hx

/-- Soundness of `getComponent`: every dart in `getComponent H fuel d` is reachable by a walk from `d`. -/
theorem mem_getComponent_imp_walk (H : Hypermap) [BEq H.Dart] (fuel : Nat) (d x : H.Dart)
    (hx : x ∈ getComponent H fuel d) : Nonempty (Walk H d x) :=
  getComponentAux_walk_sound H d (5 * fuel + 1) [d] []
    (fun q hq => by
      rcases List.mem_singleton.mp hq with rfl
      exact ⟨Walk.refl _⟩)
    (fun _ hv => by cases hv)
    x hx

/-- BFS queue-visited closure invariant: every already-visited dart has all 4 of its
    edge/node neighbors already in `queue` or in `visited`. -/
def VisitedClosed (H : Hypermap) (queue visited : List H.Dart) : Prop :=
  ∀ v ∈ visited,
    (H.edge.f v ∈ queue ∨ H.edge.f v ∈ visited) ∧
    (H.edge.inv v ∈ queue ∨ H.edge.inv v ∈ visited) ∧
    (H.node.f v ∈ queue ∨ H.node.f v ∈ visited) ∧
    (H.node.inv v ∈ queue ∨ H.node.inv v ∈ visited)

theorem visitedClosed_nil (H : Hypermap) (queue : List H.Dart) :
    VisitedClosed H queue [] :=
  fun _ hv => by cases hv

theorem visitedClosed_skip (H : Hypermap) [DecidableEq H.Dart]
    {d : H.Dart} {ds visited : List H.Dart}
    (hd_vis : d ∈ visited) (h_vc : VisitedClosed H (d :: ds) visited) :
    VisitedClosed H ds visited := by
  intro v hv
  have hmem : ∀ z, (z ∈ d :: ds ∨ z ∈ visited) → (z ∈ ds ∨ z ∈ visited) := by
    intro z hz
    rcases hz with hz_q | hz_v
    · rcases List.mem_cons.mp hz_q with rfl | hz_ds
      · exact Or.inr hd_vis
      · exact Or.inl hz_ds
    · exact Or.inr hz_v
  obtain ⟨h1, h2, h3, h4⟩ := h_vc v hv
  exact ⟨hmem _ h1, hmem _ h2, hmem _ h3, hmem _ h4⟩

theorem visitedClosed_expand (H : Hypermap)
    (d : H.Dart) (ds visited : List H.Dart)
    (h_vc : VisitedClosed H (d :: ds) visited) :
    VisitedClosed H (H.edge.f d :: H.edge.inv d :: H.node.f d :: H.node.inv d :: ds) (d :: visited) := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv_tail
  · refine ⟨Or.inl List.mem_cons_self, Or.inl ?_, Or.inl ?_, Or.inl ?_⟩
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · have hmem : ∀ z, (z ∈ d :: ds ∨ z ∈ visited) →
        (z ∈ H.edge.f d :: H.edge.inv d :: H.node.f d :: H.node.inv d :: ds ∨ z ∈ d :: visited) := by
      intro z hz
      rcases hz with hz_q | hz_v
      · rcases List.mem_cons.mp hz_q with rfl | hz_ds
        · exact Or.inr List.mem_cons_self
        · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz_ds))))
      · exact Or.inr (List.mem_cons_of_mem d hz_v)
    obtain ⟨h1, h2, h3, h4⟩ := h_vc v hv_tail
    exact ⟨hmem _ h1, hmem _ h2, hmem _ h3, hmem _ h4⟩

/-- Under the Lyapunov potential bound `queue.length + 5 * unvisitedCount darts visited ≤ fuel`,
    every element of `queue` enters the output of `getComponentAux`. -/
theorem queue_subset_getComponentAux_of_bound (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts) :
    ∀ (fuel : Nat) (queue visited : List H.Dart),
      queue.length + 5 * unvisitedCount darts visited ≤ fuel →
      ∀ q ∈ queue, q ∈ getComponentAux H queue visited fuel
  | 0, queue, _, h_pot, _, hq => by
    have hq_len : queue.length = 0 := by omega
    cases queue with
    | nil => cases hq
    | cons _ _ => simp at hq_len
  | _ + 1, [], _, _, _, hq => by cases hq
  | f + 1, d :: ds, visited, h_pot, q, hq => by
    dsimp [getComponentAux]
    cases hc : visited.contains d with
    | true =>
      dsimp
      have h_pot' : ds.length + 5 * unvisitedCount darts visited ≤ f := by
        simp only [List.length_cons] at h_pot
        omega
      rcases List.mem_cons.mp hq with rfl | hq_ds
      · exact visited_subset_getComponentAux H ds visited f q (List.contains_iff_mem.mp hc)
      · exact queue_subset_getComponentAux_of_bound H darts h_all f ds visited h_pot' q hq_ds
    | false =>
      dsimp
      have h_unvis := unvisitedCount_cons_lt darts visited (h_all d) hc
      have h_pot' : (H.edge.f d :: H.edge.inv d :: H.node.f d :: H.node.inv d :: ds).length +
          5 * unvisitedCount darts (d :: visited) ≤ f := by
        simp only [List.length_cons] at h_pot ⊢
        omega
      rcases List.mem_cons.mp hq with h_eq | hq_ds
      · rw [h_eq]
        exact visited_subset_getComponentAux H _ (d :: visited) f d List.mem_cons_self
      · apply queue_subset_getComponentAux_of_bound H darts h_all f _ (d :: visited) h_pot'
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq_ds)))

/-- Under `VisitedClosed` and the Lyapunov potential bound, the final visited list returned by
    `getComponentAux` is closed under `edge.f`, `edge.inv`, `node.f`, and `node.inv`. -/
theorem getComponentAux_closed_of_bound (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts) :
    ∀ (fuel : Nat) (queue visited : List H.Dart),
      VisitedClosed H queue visited →
      queue.length + 5 * unvisitedCount darts visited ≤ fuel →
      let V := getComponentAux H queue visited fuel
      ∀ v ∈ V, H.edge.f v ∈ V ∧ H.edge.inv v ∈ V ∧ H.node.f v ∈ V ∧ H.node.inv v ∈ V
  | 0, queue, visited, h_vc, h_pot => by
    have hq_len : queue.length = 0 := by omega
    have hq_nil : queue = [] := List.length_eq_zero_iff.mp hq_len
    subst hq_nil
    dsimp [getComponentAux]
    intro v hv
    obtain ⟨h1, h2, h3, h4⟩ := h_vc v hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases h1 with hm | hm
      · cases hm
      · exact hm
    · rcases h2 with hm | hm
      · cases hm
      · exact hm
    · rcases h3 with hm | hm
      · cases hm
      · exact hm
    · rcases h4 with hm | hm
      · cases hm
      · exact hm
  | _ + 1, [], visited, h_vc, _ => by
    dsimp [getComponentAux]
    intro v hv
    obtain ⟨h1, h2, h3, h4⟩ := h_vc v hv
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases h1 with hm | hm
      · cases hm
      · exact hm
    · rcases h2 with hm | hm
      · cases hm
      · exact hm
    · rcases h3 with hm | hm
      · cases hm
      · exact hm
    · rcases h4 with hm | hm
      · cases hm
      · exact hm
  | f + 1, d :: ds, visited, h_vc, h_pot => by
    dsimp [getComponentAux]
    cases hc : visited.contains d with
    | true =>
      dsimp
      have h_vc' : VisitedClosed H ds visited :=
        visitedClosed_skip H (List.contains_iff_mem.mp hc) h_vc
      have h_pot' : ds.length + 5 * unvisitedCount darts visited ≤ f := by
        simp only [List.length_cons] at h_pot
        omega
      exact getComponentAux_closed_of_bound H darts h_all f ds visited h_vc' h_pot'
    | false =>
      dsimp
      have h_vc' := visitedClosed_expand H d ds visited h_vc
      have h_unvis := unvisitedCount_cons_lt darts visited (h_all d) hc
      have h_pot' : (H.edge.f d :: H.edge.inv d :: H.node.f d :: H.node.inv d :: ds).length +
          5 * unvisitedCount darts (d :: visited) ≤ f := by
        simp only [List.length_cons] at h_pot ⊢
        omega
      exact getComponentAux_closed_of_bound H darts h_all f _ (d :: visited) h_vc' h_pot'

/-- Under the Lyapunov potential bound, `getComponentAux` is strictly independent of extra fuel. -/
theorem getComponentAux_fuel_eq_of_bound (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts) :
    ∀ (fuel1 fuel2 : Nat) (queue visited : List H.Dart),
      queue.length + 5 * unvisitedCount darts visited ≤ fuel1 →
      fuel1 ≤ fuel2 →
      getComponentAux H queue visited fuel2 = getComponentAux H queue visited fuel1
  | 0, fuel2, queue, visited, h_pot, _ => by
    have hq_len : queue.length = 0 := by omega
    have hq_nil : queue = [] := List.length_eq_zero_iff.mp hq_len
    subst hq_nil
    cases fuel2 <;> rfl
  | f1 + 1, fuel2, queue, visited, h_pot, h_le => by
    obtain ⟨f2, rfl⟩ : ∃ f2, fuel2 = f2 + 1 := ⟨fuel2 - 1, by omega⟩
    have hf_le : f1 ≤ f2 := by omega
    cases queue with
    | nil => rfl
    | cons d ds =>
      dsimp [getComponentAux]
      cases hc : visited.contains d with
      | true =>
        dsimp
        have h_pot' : ds.length + 5 * unvisitedCount darts visited ≤ f1 := by
          simp only [List.length_cons] at h_pot
          omega
        exact getComponentAux_fuel_eq_of_bound H darts h_all f1 f2 ds visited h_pot' hf_le
      | false =>
        dsimp
        have h_unvis := unvisitedCount_cons_lt darts visited (h_all d) hc
        have h_pot' : (H.edge.f d :: H.edge.inv d :: H.node.f d :: H.node.inv d :: ds).length +
            5 * unvisitedCount darts (d :: visited) ≤ f1 := by
          simp only [List.length_cons] at h_pot ⊢
          omega
        exact getComponentAux_fuel_eq_of_bound H darts h_all f1 f2 _ (d :: visited) h_pot' hf_le

end GetComponentAuxTheory

section GetComponentTheory

private theorem getComponent_init_bound {D : Type} [DecidableEq D] (darts : List D) (d : D)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    ([d] : List D).length + 5 * unvisitedCount darts [] ≤ 5 * fuel + 1 := by
  rw [unvisitedCount_nil]
  dsimp [List.length]
  omega

/-- Every dart unconditionally belongs to its own `getComponent`. -/
theorem mem_getComponent_self (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart) :
    d ∈ getComponent H fuel d := by
  dsimp [getComponent, getComponentAux]
  exact visited_subset_getComponentAux H _ [d] (5 * fuel) d List.mem_cons_self

/-- Boolean `.contains` reflexivity for `getComponent`. -/
theorem getComponent_contains_self (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart) :
    (getComponent H fuel d).contains d = true :=
  List.contains_iff_mem.mpr (mem_getComponent_self H fuel d)

/-- Unconditional fuel-independence of `getComponent` on any complete dart list (`darts.length ≤ fuel`). -/
theorem getComponent_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d : H.Dart) :
    getComponent H fuel d = getComponent H darts.length d := by
  dsimp [getComponent]
  exact getComponentAux_fuel_eq_of_bound H darts h_all
    (5 * darts.length + 1) (5 * fuel + 1) [d] []
    (getComponent_init_bound darts d (Nat.le_refl _))
    (by omega)

/-- Closure of `getComponent H fuel d` under `edge`, `node`, `face`, and every `Step H`
    whenever `darts.length ≤ fuel`. -/
theorem getComponent_step_closed_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d : H.Dart) :
    ∀ {u v : H.Dart}, Step H u v → u ∈ getComponent H fuel d → v ∈ getComponent H fuel d := by
  intro u v s hu
  have h_en := getComponentAux_closed_of_bound H darts h_all (5 * fuel + 1) [d] []
    (visitedClosed_nil H [d]) (getComponent_init_bound darts d h_le)
  exact step_closed_of_edge_node_closed H (fun x => x ∈ getComponent H fuel d)
    (fun w hw => (h_en w hw).1)
    (fun w hw => (h_en w hw).2.1)
    (fun w hw => (h_en w hw).2.2.1)
    (fun w hw => (h_en w hw).2.2.2) s hu

/-- Any walk from `d` to `x` witnesses `x ∈ getComponent H fuel d` on a complete dart list. -/
theorem walk_imp_mem_getComponent (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {d x : H.Dart} (w : Walk H d x) :
    x ∈ getComponent H fuel d :=
  pred_end_of_walk_of_closed H (fun y => y ∈ getComponent H fuel d)
    (fun s hy => getComponent_step_closed_of_complete H darts h_all h_le d s hy)
    w (mem_getComponent_self H fuel d)

/-- **Fundamental Component–Walk Equivalence**:
    On any complete dart list (`darts.length ≤ fuel`), `x ∈ getComponent H fuel d ↔ Nonempty (Walk H d x)`. -/
theorem mem_getComponent_iff_walk (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d x : H.Dart) :
    x ∈ getComponent H fuel d ↔ Nonempty (Walk H d x) :=
  ⟨mem_getComponent_imp_walk H fuel d x,
   fun ⟨w⟩ => walk_imp_mem_getComponent H darts h_all h_le w⟩

/-- Boolean `.contains` characterization of `getComponent` as walk reachability. -/
theorem getComponent_contains_iff_walk (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d x : H.Dart) :
    (getComponent H fuel d).contains x = true ↔ Nonempty (Walk H d x) :=
  List.contains_iff_mem.trans (mem_getComponent_iff_walk H darts h_all h_le d x)

/-- Symmetry of `getComponent` membership on complete dart lists. -/
theorem mem_getComponent_symm_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u v : H.Dart}
    (hv : v ∈ getComponent H fuel u) :
    u ∈ getComponent H fuel v := by
  rw [mem_getComponent_iff_walk H darts h_all h_le] at hv ⊢
  obtain ⟨w⟩ := hv
  exact ⟨Walk.symm H w⟩

/-- Transitivity of `getComponent` membership on complete dart lists. -/
theorem mem_getComponent_trans_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u v w : H.Dart}
    (huv : v ∈ getComponent H fuel u) (hvw : w ∈ getComponent H fuel v) :
    w ∈ getComponent H fuel u := by
  rw [mem_getComponent_iff_walk H darts h_all h_le] at huv hvw ⊢
  obtain ⟨w1⟩ := huv
  obtain ⟨w2⟩ := hvw
  exact ⟨Walk.trans H w1 w2⟩

/-- Symmetry of `(getComponent H fuel _).contains _` on complete dart lists. -/
theorem getComponent_contains_symm_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart) :
    (getComponent H fuel u).contains v = (getComponent H fuel v).contains u := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact ⟨mem_getComponent_symm_of_complete H darts h_all h_le,
         mem_getComponent_symm_of_complete H darts h_all h_le⟩

/-- Transitivity of `(getComponent H fuel _).contains _` on complete dart lists. -/
theorem getComponent_contains_trans_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u v w : H.Dart}
    (huv : (getComponent H fuel u).contains v = true)
    (hvw : (getComponent H fuel v).contains w = true) :
    (getComponent H fuel u).contains w = true := by
  rw [List.contains_iff_mem] at huv hvw ⊢
  exact mem_getComponent_trans_of_complete H darts h_all h_le huv hvw

/-- Two darts in the same component induce identical `.contains` predicates. -/
theorem getComponent_contains_eq_of_mem_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u v : H.Dart}
    (hv : v ∈ getComponent H fuel u) (x : H.Dart) :
    (getComponent H fuel v).contains x = (getComponent H fuel u).contains x := by
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, List.contains_iff_mem]
  exact ⟨fun hx => mem_getComponent_trans_of_complete H darts h_all h_le hv hx,
         fun hx => mem_getComponent_trans_of_complete H darts h_all h_le
           (mem_getComponent_symm_of_complete H darts h_all h_le hv) hx⟩

/-- Two darts in the same component have identical `getComponent` list lengths. -/
theorem getComponent_length_eq_of_mem_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u v : H.Dart}
    (hv : v ∈ getComponent H fuel u) :
    (getComponent H fuel v).length = (getComponent H fuel u).length := by
  apply nodup_length_eq_of_iff_mem (getComponent_nodup H fuel v) (getComponent_nodup H fuel u)
  intro x
  have h1 := getComponent_contains_eq_of_mem_of_complete H darts h_all h_le hv x
  exact ⟨fun h => List.contains_iff_mem.mp (h1 ▸ List.contains_iff_mem.mpr h),
         fun h => List.contains_iff_mem.mp (h1.symm ▸ List.contains_iff_mem.mpr h)⟩

/-- Every node orbit of a member of a component stays inside that component. -/
theorem getOrbit_node_subset_getComponent_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {d x y : H.Dart}
    (hx : x ∈ getComponent H fuel d) (hy : y ∈ getOrbit H.node fuel x) :
    y ∈ getComponent H fuel d := by
  obtain ⟨k, _, rfl⟩ := mem_getOrbit_imp_exists_iter H.node fuel x y hy
  have hw := Walk.ofPermIter H H.node (fun _ => Step.node rfl) k x
  exact mem_getComponent_trans_of_complete H darts h_all h_le hx
    (walk_imp_mem_getComponent H darts h_all h_le hw)

/-- Every edge orbit of a member of a component stays inside that component. -/
theorem getOrbit_edge_subset_getComponent_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {d x y : H.Dart}
    (hx : x ∈ getComponent H fuel d) (hy : y ∈ getOrbit H.edge fuel x) :
    y ∈ getComponent H fuel d := by
  obtain ⟨k, _, rfl⟩ := mem_getOrbit_imp_exists_iter H.edge fuel x y hy
  have hw := Walk.ofPermIter H H.edge (fun _ => Step.edge rfl) k x
  exact mem_getComponent_trans_of_complete H darts h_all h_le hx
    (walk_imp_mem_getComponent H darts h_all h_le hw)

/-- Every face orbit of a member of a component stays inside that component. -/
theorem getOrbit_face_subset_getComponent_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {d x y : H.Dart}
    (hx : x ∈ getComponent H fuel d) (hy : y ∈ getOrbit H.face fuel x) :
    y ∈ getComponent H fuel d := by
  obtain ⟨k, _, rfl⟩ := mem_getOrbit_imp_exists_iter H.face fuel x y hy
  have hw := Walk.ofPermIter H H.face (fun _ => Step.face rfl) k x
  exact mem_getComponent_trans_of_complete H darts h_all h_le hx
    (walk_imp_mem_getComponent H darts h_all h_le hw)

end GetComponentTheory

section CountOrbitsPartitionAndExtensionality

variable {D : Type} [DecidableEq D]

/-- `countOrbitsAux` is independent of `steps` once `l.length ≤ steps`. -/
theorem countOrbitsAux_steps_eq (p : Perm D) (fuel : Nat)
    {steps1 steps2 : Nat} (l : List D)
    (h1 : l.length ≤ steps1) (h2 : l.length ≤ steps2) :
    countOrbitsAux p fuel steps1 l = countOrbitsAux p fuel steps2 l := by
  induction steps1 generalizing steps2 l with
  | zero =>
    cases l with
    | nil => cases steps2 <;> rfl
    | cons _ _ => dsimp at h1; omega
  | succ s1 ih =>
    cases l with
    | nil => cases steps2 <;> rfl
    | cons d ds =>
      cases steps2 with
      | zero => dsimp at h2; omega
      | succ s2 =>
        dsimp [countOrbitsAux]
        congr 1
        have h_flt : (ds.filter (fun x => !((getOrbit p fuel d).contains x))).length ≤ ds.length :=
          filter_length_le _ ds
        dsimp at h1 h2
        exact ih _ (by omega) (by omega)

/-- Step equation for `countOrbits` on `d :: ds`. -/
theorem countOrbits_cons (p : Perm D) (fuel : Nat) (d : D) (ds : List D) :
    countOrbits p fuel (d :: ds) =
      1 + countOrbits p fuel (ds.filter (fun x => !((getOrbit p fuel d).contains x))) := by
  dsimp [countOrbits, countOrbitsAux]
  congr 1
  have h_flt : (ds.filter (fun x => !((getOrbit p fuel d).contains x))).length ≤ ds.length :=
    filter_length_le _ ds
  exact countOrbitsAux_steps_eq p fuel _ h_flt (Nat.le_refl _)

/-- Every member of `getOrbit p fuel d` agrees on any `p`-invariant boolean predicate `S`. -/
theorem mem_getOrbit_pred_eq_of_closed (p : Perm D) (S : D → Bool)
    (hS : ∀ x, S (p.f x) = S x) (fuel : Nat) {d x : D} (hx : x ∈ getOrbit p fuel d) :
    S x = S d := by
  obtain ⟨k, _, rfl⟩ := mem_getOrbit_imp_exists_iter p fuel d x hx
  have h_iter : ∀ m, S (Perm.iter p m d) = S d := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Perm.iter_succ, hS, ih]
  exact h_iter k

private theorem countOrbits_partition_aux (p : Perm D) (fuel : Nat) (S : D → Bool)
    (hS : ∀ x, S (p.f x) = S x) :
    ∀ (n : Nat) (l : List D), l.length ≤ n →
      countOrbits p fuel l = countOrbits p fuel (l.filter S) + countOrbits p fuel (l.filter (fun x => !S x))
  | 0, l, hlen => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hnil
    rfl
  | n + 1, [], _ => rfl
  | n + 1, d :: ds, hlen => by
    have hlen_ds : ds.length ≤ n := by dsimp at hlen; omega
    let orb := getOrbit p fuel d
    let ds' := ds.filter (fun x => !orb.contains x)
    have hds'_len : ds'.length ≤ n := Nat.le_trans (filter_length_le _ ds) hlen_ds
    have h_ih := countOrbits_partition_aux p fuel S hS n ds' hds'_len
    have h_main : countOrbits p fuel (d :: ds) = 1 + countOrbits p fuel ds' :=
      countOrbits_cons p fuel d ds
    cases hSd : S d with
    | true =>
      have h_f1 : (d :: ds).filter S = d :: ds.filter S := by
        dsimp [List.filter]; rw [hSd]
      have h_f2 : (d :: ds).filter (fun x => !S x) = ds.filter (fun x => !S x) := by
        dsimp [List.filter]; rw [hSd]; rfl
      have h_c1 : countOrbits p fuel (d :: ds.filter S) =
          1 + countOrbits p fuel ((ds.filter S).filter (fun x => !orb.contains x)) :=
        countOrbits_cons p fuel d (ds.filter S)
      have h_comm : (ds.filter S).filter (fun x => !orb.contains x) = ds'.filter S :=
        filter_comm S (fun x => !orb.contains x) ds
      have h_keep : ds'.filter (fun x => !S x) = ds.filter (fun x => !S x) := by
        dsimp [ds']
        rw [filter_comm]
        apply filter_filter_eq_of_imp
        intro x _ hnx
        have hSx : S x = false := by cases h : S x <;> simp_all
        cases hc : orb.contains x with
        | false => rfl
        | true =>
          have h_eq := mem_getOrbit_pred_eq_of_closed p S hS fuel (List.contains_iff_mem.mp hc)
          rw [hSx, hSd] at h_eq
          contradiction
      rw [h_main, h_f1, h_f2, h_c1, h_comm, ← h_keep, h_ih]
      omega
    | false =>
      have h_f1 : (d :: ds).filter S = ds.filter S := by
        dsimp [List.filter]; rw [hSd]
      have h_f2 : (d :: ds).filter (fun x => !S x) = d :: ds.filter (fun x => !S x) := by
        dsimp [List.filter]; rw [hSd]; rfl
      have h_c2 : countOrbits p fuel (d :: ds.filter (fun x => !S x)) =
          1 + countOrbits p fuel ((ds.filter (fun x => !S x)).filter (fun x => !orb.contains x)) :=
        countOrbits_cons p fuel d (ds.filter (fun x => !S x))
      have h_comm : (ds.filter (fun x => !S x)).filter (fun x => !orb.contains x) =
          ds'.filter (fun x => !S x) :=
        filter_comm (fun x => !S x) (fun x => !orb.contains x) ds
      have h_keep : ds'.filter S = ds.filter S := by
        dsimp [ds']
        rw [filter_comm]
        apply filter_filter_eq_of_imp
        intro x _ hSx
        cases hc : orb.contains x with
        | false => rfl
        | true =>
          have h_eq := mem_getOrbit_pred_eq_of_closed p S hS fuel (List.contains_iff_mem.mp hc)
          rw [hSx, hSd] at h_eq
          contradiction
      rw [h_main, h_f1, h_f2, h_c2, h_comm, ← h_keep, h_ih]
      omega

/-- **Orbit Partition Additivity**: any `p`-invariant predicate `S` splits `countOrbits p fuel l`
    additively across `l.filter S` and `l.filter (!S ·)`. -/
theorem countOrbits_partition_of_closed (p : Perm D) (fuel : Nat) (l : List D) (S : D → Bool)
    (hS : ∀ x, S (p.f x) = S x) :
    countOrbits p fuel l = countOrbits p fuel (l.filter S) + countOrbits p fuel (l.filter (fun x => !S x)) :=
  countOrbits_partition_aux p fuel S hS l.length l (Nat.le_refl _)

private theorem pred_getOrbit_closed_of_closes (p : Perm D) (fuel : Nat) (a : D)
    (h_closes : orbitClosesWithin p a a fuel) :
    ∀ x : D, (getOrbit p fuel a).contains (p.f x) = (getOrbit p fuel a).contains x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [List.contains_iff_mem, List.contains_iff_mem]
  refine ⟨fun hpx => ?_, fun hx => getOrbit_closed_under_f p fuel a h_closes x hx⟩
  have hinv := getOrbit_closed_under_inv p fuel a h_closes (p.f x) hpx
  rwa [p.left_inv] at hinv

private theorem countOrbits_eq_one_of_all_in_orbit (p : Perm D) (fuel : Nat) (a : D)
    (h_closes : orbitClosesWithin p a a fuel) (l : List D) (hne : l ≠ [])
    (h_in : ∀ x ∈ l, x ∈ getOrbit p fuel a) :
    countOrbits p fuel l = 1 := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons d ds =>
    rw [countOrbits_cons]
    have hd_orb : d ∈ getOrbit p fuel a := h_in d List.mem_cons_self
    have h_flt : ds.filter (fun x => !((getOrbit p fuel d).contains x)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have hx_orb : x ∈ getOrbit p fuel a := h_in x (List.mem_cons_of_mem d hx)
      have hx_d : x ∈ getOrbit p fuel d :=
        (mem_getOrbit_iff_of_mem p fuel h_closes hd_orb x).mpr hx_orb
      simpa using hx_d
    rw [h_flt]
    rfl

/-- Peel off the orbit of ANY element `a ∈ l` first in `countOrbits`. -/
theorem countOrbits_eq_one_add_filter_of_mem (p : Perm D) (fuel : Nat) (l : List D) (a : D)
    (ha : a ∈ l) (h_closes : orbitClosesWithin p a a fuel) :
    countOrbits p fuel l =
      1 + countOrbits p fuel (l.filter (fun x => !((getOrbit p fuel a).contains x))) := by
  have hS := pred_getOrbit_closed_of_closes p fuel a h_closes
  rw [countOrbits_partition_of_closed p fuel l (fun x => (getOrbit p fuel a).contains x) hS]
  have h_ne : l.filter (fun x => (getOrbit p fuel a).contains x) ≠ [] := by
    intro hnil
    have ha_flt : a ∈ l.filter (fun x => (getOrbit p fuel a).contains x) :=
      List.mem_filter.mpr ⟨ha, getOrbit_contains_self p fuel a⟩
    rw [hnil] at ha_flt
    cases ha_flt
  have h_one := countOrbits_eq_one_of_all_in_orbit p fuel a h_closes
    (l.filter (fun x => (getOrbit p fuel a).contains x)) h_ne
    (fun x hx => List.contains_iff_mem.mp (List.mem_filter.mp hx).2)
  rw [h_one]

private theorem countOrbits_eq_of_iff_mem_aux (p : Perm D) (fuel : Nat) :
    ∀ (n : Nat) (l1 l2 : List D),
      l1.length ≤ n →
      (∀ x, x ∈ l1 ↔ x ∈ l2) →
      (∀ x ∈ l1, orbitClosesWithin p x x fuel) →
      countOrbits p fuel l1 = countOrbits p fuel l2
  | 0, l1, l2, hlen, hiff, _ => by
    have h1 : l1 = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst h1
    have h2 : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons y _ => exact False.elim (by simpa using (hiff y).mpr List.mem_cons_self)
    subst h2
    rfl
  | n + 1, [], l2, _, hiff, _ => by
    have h2 : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons y _ => exact False.elim (by simpa using (hiff y).mpr List.mem_cons_self)
    subst h2
    rfl
  | n + 1, a :: as, l2, hlen, hiff, h_closes => by
    have ha_l1 : a ∈ a :: as := List.mem_cons_self
    have ha_l2 : a ∈ l2 := (hiff a).mp ha_l1
    have hc_a : orbitClosesWithin p a a fuel := h_closes a ha_l1
    rw [countOrbits_cons p fuel a as,
        countOrbits_eq_one_add_filter_of_mem p fuel l2 a ha_l2 hc_a]
    congr 1
    let as' := as.filter (fun x => !((getOrbit p fuel a).contains x))
    let l2' := l2.filter (fun x => !((getOrbit p fuel a).contains x))
    have has'_len : as'.length ≤ n := by
      have h_le := filter_length_le (fun x => !((getOrbit p fuel a).contains x)) as
      dsimp [as'] at h_le ⊢
      dsimp at hlen
      omega
    have hiff' : ∀ x, x ∈ as' ↔ x ∈ l2' := by
      intro x
      dsimp [as', l2']
      rw [List.mem_filter, List.mem_filter]
      constructor
      · intro ⟨hxa, hnc⟩
        exact ⟨(hiff x).mp (List.mem_cons_of_mem a hxa), hnc⟩
      · intro ⟨hxl2, hnc⟩
        have hne : x ≠ a := by
          intro h_eq
          subst h_eq
          rw [getOrbit_contains_self p fuel x] at hnc
          contradiction
        have hx_l1 := (hiff x).mpr hxl2
        rcases List.mem_cons.mp hx_l1 with rfl | hxa
        · exact False.elim (hne rfl)
        · exact ⟨hxa, hnc⟩
    have h_closes' : ∀ x ∈ as', orbitClosesWithin p x x fuel :=
      fun x hx => h_closes x (List.mem_cons_of_mem a (List.mem_filter.mp hx).1)
    exact countOrbits_eq_of_iff_mem_aux p fuel n as' l2' has'_len hiff' h_closes'

/-- **Set-Extensionality of `countOrbits`**:
    if `l1` and `l2` contain the same elements and every element's orbit closes within `fuel`,
    then `countOrbits p fuel l1 = countOrbits p fuel l2` (in particular, invariant under `List.Perm`). -/
theorem countOrbits_eq_of_iff_mem (p : Perm D) (fuel : Nat) (l1 l2 : List D)
    (hiff : ∀ x, x ∈ l1 ↔ x ∈ l2)
    (h_closes : ∀ x ∈ l1, orbitClosesWithin p x x fuel) :
    countOrbits p fuel l1 = countOrbits p fuel l2 :=
  countOrbits_eq_of_iff_mem_aux p fuel l1.length l1 l2 (Nat.le_refl _) hiff h_closes

/-- `countOrbits` extensionality on complete dart lists (`darts.length ≤ fuel`). -/
theorem countOrbits_eq_of_iff_mem_of_complete (p : Perm D) (darts l1 l2 : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (hiff : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    countOrbits p fuel l1 = countOrbits p fuel l2 :=
  countOrbits_eq_of_iff_mem p fuel l1 l2 hiff
    (fun x _ => orbitClosesWithin_mono p x x (orbitClosesWithin_of_complete p darts h_all x) h_le)

end CountOrbitsPartitionAndExtensionality

section CountComponentsAndDuality

/-- `countComponentsAux` is independent of `steps` once `l.length ≤ steps`. -/
theorem countComponentsAux_steps_eq (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat)
    {steps1 steps2 : Nat} (l : List H.Dart)
    (h1 : l.length ≤ steps1) (h2 : l.length ≤ steps2) :
    countComponentsAux H fuel steps1 l = countComponentsAux H fuel steps2 l := by
  induction steps1 generalizing steps2 l with
  | zero =>
    cases l with
    | nil => cases steps2 <;> rfl
    | cons _ _ => dsimp at h1; omega
  | succ s1 ih =>
    cases l with
    | nil => cases steps2 <;> rfl
    | cons d ds =>
      cases steps2 with
      | zero => dsimp at h2; omega
      | succ s2 =>
        dsimp [countComponentsAux]
        congr 1
        have h_flt : (ds.filter (fun x => !((getComponent H fuel d).contains x))).length ≤ ds.length :=
          filter_length_le _ ds
        dsimp at h1 h2
        exact ih _ (by omega) (by omega)

/-- Step equation for `countComponents` on `d :: ds`. -/
theorem countComponents_cons (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat)
    (d : H.Dart) (ds : List H.Dart) :
    countComponents H fuel (d :: ds) =
      1 + countComponents H fuel (ds.filter (fun x => !((getComponent H fuel d).contains x))) := by
  dsimp [countComponents, countComponentsAux]
  congr 1
  have h_flt : (ds.filter (fun x => !((getComponent H fuel d).contains x))).length ≤ ds.length :=
    filter_length_le _ ds
  exact countComponentsAux_steps_eq H fuel _ h_flt (Nat.le_refl _)

/-- Unconditional fuel-independence of `countComponentsAux` on complete dart lists (`darts.length ≤ fuel`). -/
theorem countComponentsAux_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (steps : Nat) (l : List H.Dart) :
    countComponentsAux H fuel steps l = countComponentsAux H darts.length steps l := by
  induction steps generalizing l with
  | zero => rfl
  | succ s ih =>
    cases l with
    | nil => rfl
    | cons d ds =>
      dsimp [countComponentsAux]
      rw [getComponent_fuel_eq_of_complete H darts h_all h_le d]
      congr 1
      exact ih _

/-- Unconditional fuel-independence of `countComponents` on complete dart lists (`darts.length ≤ fuel`). -/
theorem countComponents_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l : List H.Dart) :
    countComponents H fuel l = countComponents H darts.length l :=
  countComponentsAux_fuel_eq_of_complete H darts h_all h_le l.length l

/-- Unconditional fuel-independence of `isPlanar` on complete dart lists (`darts.length ≤ fuel`). -/
theorem isPlanar_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    H.isPlanar fuel darts = H.isPlanar darts.length darts := by
  dsimp [Hypermap.isPlanar]
  rw [countOrbits_fuel_eq_of_complete H.node darts darts h_all h_le,
      countOrbits_fuel_eq_of_complete H.edge darts darts h_all h_le,
      countOrbits_fuel_eq_of_complete H.face darts darts h_all h_le,
      countComponents_fuel_eq_of_complete H darts h_all h_le darts]

/-- Boolean `.contains` of `getComponent` is invariant under passing to `H.dual`. -/
theorem getComponent_dual_contains_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d x : H.Dart) :
    (getComponent H.dual fuel d).contains x = (getComponent H fuel d).contains x := by
  apply Bool.eq_iff_iff.mpr
  have h1 : (getComponent H.dual fuel d).contains x = true ↔ Nonempty (Walk H.dual d x) :=
    getComponent_contains_iff_walk H.dual darts h_all h_le d x
  have h2 : (getComponent H fuel d).contains x = true ↔ Nonempty (Walk H d x) :=
    getComponent_contains_iff_walk H darts h_all h_le d x
  exact h1.trans ((walk_dual_iff_walk H d x).trans h2.symm)

/-- Equality of `countComponentsAux` for `H.dual` and `H` on complete dart lists (`darts.length ≤ fuel`). -/
theorem countComponentsAux_dual_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (steps : Nat) (l : List H.Dart) :
    countComponentsAux H.dual fuel steps l = countComponentsAux H fuel steps l := by
  induction steps generalizing l with
  | zero => rfl
  | succ s ih =>
    cases l with
    | nil => rfl
    | cons d ds =>
      dsimp [countComponentsAux]
      have h_pred : (fun x => !((getComponent H.dual fuel d).contains x)) =
          (fun x => !((getComponent H fuel d).contains x)) := by
        funext x
        rw [getComponent_dual_contains_eq_of_complete H darts h_all h_le d x]
      rw [h_pred]
      congr 1
      exact ih _

/-- Unconditional equality of `countComponents` for `H.dual` and `H` on complete dart lists. -/
theorem countComponents_dual_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l : List H.Dart) :
    countComponents H.dual fuel l = countComponents H fuel l :=
  countComponentsAux_dual_of_complete H darts h_all h_le l.length l

/-- Unconditional equality of `numComponents` for `H.dual` and `H` on complete dart lists. -/
theorem numComponents_dual_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l : List H.Dart) :
    numComponents H.dual fuel l = numComponents H fuel l :=
  countComponents_dual_of_complete H darts h_all h_le l

/-- **Dual Planarity Equivalence (`isPlanar H.dual = isPlanar H`)**:
    On any complete dart list (`∀ d : H.Dart, d ∈ darts`, `darts.length ≤ fuel`),
    `H.dual` is planar if and only if `H` is planar. -/
theorem isPlanar_dual_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    H.dual.isPlanar fuel darts = H.isPlanar fuel darts := by
  have hN := numNodes_dual_of_complete H darts darts h_all h_le
  have hF := numFaces_dual_of_complete H darts darts h_all h_le
  have hC := countComponents_dual_of_complete H darts h_all h_le darts
  dsimp [Hypermap.isPlanar]
  dsimp [numNodes, numFaces] at hN hF
  have hE : countOrbits H.dual.edge fuel darts = countOrbits H.edge fuel darts := rfl
  rw [hN, hF, hC, hE]
  congr 1
  omega

/-- Any non-empty list has positive component count (`1 ≤ countComponents H fuel l`). -/
theorem numComponents_pos_of_ne_nil (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat)
    (l : List H.Dart) (hne : l ≠ []) :
    1 ≤ numComponents H fuel l := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons d ds =>
    dsimp [numComponents]
    rw [countComponents_cons H fuel d ds]
    omega

/-- Any element reachable in `getComponent H fuel d` has the same value under a step-invariant predicate `S`. -/
theorem mem_getComponent_pred_eq_of_closed (H : Hypermap) [BEq H.Dart] (S : H.Dart → Bool)
    (he : ∀ x, S (H.edge.f x) = S x) (hn : ∀ x, S (H.node.f x) = S x)
    (fuel : Nat) {d x : H.Dart} (hx : x ∈ getComponent H fuel d) :
    S x = S d := by
  obtain ⟨w⟩ := mem_getComponent_imp_walk H fuel d x hx
  have hei : ∀ u, S (H.edge.inv u) = S u := fun u => by
    have h := he (H.edge.inv u)
    rw [H.edge.right_inv] at h
    exact h.symm
  have hni : ∀ u, S (H.node.inv u) = S u := fun u => by
    have h := hn (H.node.inv u)
    rw [H.node.right_inv] at h
    exact h.symm
  have h_step : ∀ {u v : H.Dart}, Step H u v → S u = S d → S v = S d := by
    intro u v s hu
    exact step_closed_of_edge_node_closed H (fun y => S y = S d)
      (fun w hw => (he w).trans hw)
      (fun w hw => (hei w).trans hw)
      (fun w hw => (hn w).trans hw)
      (fun w hw => (hni w).trans hw) s hu
  exact pred_end_of_walk_of_closed H (fun y => S y = S d) h_step w rfl

private theorem countComponents_partition_aux (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (S : H.Dart → Bool)
    (he : ∀ x, S (H.edge.f x) = S x) (hn : ∀ x, S (H.node.f x) = S x) :
    ∀ (n : Nat) (l : List H.Dart), l.length ≤ n →
      countComponents H fuel l =
        countComponents H fuel (l.filter S) + countComponents H fuel (l.filter (fun x => !S x))
  | 0, l, hlen => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst hnil
    rfl
  | n + 1, [], _ => rfl
  | n + 1, d :: ds, hlen => by
    have hlen_ds : ds.length ≤ n := by dsimp at hlen; omega
    let comp := getComponent H fuel d
    let ds' := ds.filter (fun x => !comp.contains x)
    have hds'_len : ds'.length ≤ n := Nat.le_trans (filter_length_le _ ds) hlen_ds
    have h_ih := countComponents_partition_aux H fuel S he hn n ds' hds'_len
    have h_main : countComponents H fuel (d :: ds) = 1 + countComponents H fuel ds' :=
      countComponents_cons H fuel d ds
    cases hSd : S d with
    | true =>
      have h_f1 : (d :: ds).filter S = d :: ds.filter S := by
        dsimp [List.filter]; rw [hSd]
      have h_f2 : (d :: ds).filter (fun x => !S x) = ds.filter (fun x => !S x) := by
        dsimp [List.filter]; rw [hSd]; rfl
      have h_c1 : countComponents H fuel (d :: ds.filter S) =
          1 + countComponents H fuel ((ds.filter S).filter (fun x => !comp.contains x)) :=
        countComponents_cons H fuel d (ds.filter S)
      have h_comm : (ds.filter S).filter (fun x => !comp.contains x) = ds'.filter S :=
        filter_comm S (fun x => !comp.contains x) ds
      have h_keep : ds'.filter (fun x => !S x) = ds.filter (fun x => !S x) := by
        dsimp [ds']
        rw [filter_comm]
        apply filter_filter_eq_of_imp
        intro x _ hnx
        have hSx : S x = false := by cases h : S x <;> simp_all
        cases hc : comp.contains x with
        | false => rfl
        | true =>
          have h_eq := mem_getComponent_pred_eq_of_closed H S he hn fuel (List.contains_iff_mem.mp hc)
          rw [hSx, hSd] at h_eq
          contradiction
      rw [h_main, h_f1, h_f2, h_c1, h_comm, ← h_keep, h_ih]
      omega
    | false =>
      have h_f1 : (d :: ds).filter S = ds.filter S := by
        dsimp [List.filter]; rw [hSd]
      have h_f2 : (d :: ds).filter (fun x => !S x) = d :: ds.filter (fun x => !S x) := by
        dsimp [List.filter]; rw [hSd]; rfl
      have h_c2 : countComponents H fuel (d :: ds.filter (fun x => !S x)) =
          1 + countComponents H fuel ((ds.filter (fun x => !S x)).filter (fun x => !comp.contains x)) :=
        countComponents_cons H fuel d (ds.filter (fun x => !S x))
      have h_comm : (ds.filter (fun x => !S x)).filter (fun x => !comp.contains x) =
          ds'.filter (fun x => !S x) :=
        filter_comm (fun x => !S x) (fun x => !comp.contains x) ds
      have h_keep : ds'.filter S = ds.filter S := by
        dsimp [ds']
        rw [filter_comm]
        apply filter_filter_eq_of_imp
        intro x _ hSx
        cases hc : comp.contains x with
        | false => rfl
        | true =>
          have h_eq := mem_getComponent_pred_eq_of_closed H S he hn fuel (List.contains_iff_mem.mp hc)
          rw [hSx, hSd] at h_eq
          contradiction
      rw [h_main, h_f1, h_f2, h_c2, h_comm, ← h_keep, h_ih]
      omega

/-- **Component Partition Additivity**: any edge/node-closed predicate `S` splits
    `countComponents H fuel l` additively across `l.filter S` and `l.filter (!S ·)`. -/
theorem countComponents_partition_of_closed (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (l : List H.Dart) (S : H.Dart → Bool)
    (he : ∀ x, S (H.edge.f x) = S x) (hn : ∀ x, S (H.node.f x) = S x) :
    countComponents H fuel l =
      countComponents H fuel (l.filter S) + countComponents H fuel (l.filter (fun x => !S x)) :=
  countComponents_partition_aux H fuel S he hn l.length l (Nat.le_refl _)

private theorem pred_getComponent_closed_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (a : H.Dart) :
    (∀ x : H.Dart, (getComponent H fuel a).contains (H.edge.f x) = (getComponent H fuel a).contains x) ∧
    (∀ x : H.Dart, (getComponent H fuel a).contains (H.node.f x) = (getComponent H fuel a).contains x) := by
  constructor <;> intro x <;> apply Bool.eq_iff_iff.mpr <;>
    rw [List.contains_iff_mem, List.contains_iff_mem]
  · refine ⟨fun hfx => ?_, fun hx =>
      getComponent_step_closed_of_complete H darts h_all h_le a (Step.edge rfl) hx⟩
    have hback := getComponent_step_closed_of_complete H darts h_all h_le a (Step.edge rfl) hfx
    rwa [H.edge_involution] at hback
  · refine ⟨fun hfx => ?_, fun hx =>
      getComponent_step_closed_of_complete H darts h_all h_le a (Step.node rfl) hx⟩
    exact getComponent_step_closed_of_complete H darts h_all h_le a (Step.node_back H x) hfx

private theorem countComponents_eq_one_of_all_in_comp (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (a : H.Dart) (l : List H.Dart) (hne : l ≠ [])
    (h_in : ∀ x ∈ l, x ∈ getComponent H fuel a) :
    countComponents H fuel l = 1 := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons d ds =>
    rw [countComponents_cons]
    have hd_comp : d ∈ getComponent H fuel a := h_in d List.mem_cons_self
    have h_flt : ds.filter (fun x => !((getComponent H fuel d).contains x)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have hx_comp : x ∈ getComponent H fuel a := h_in x (List.mem_cons_of_mem d hx)
      have hx_d : x ∈ getComponent H fuel d :=
        List.contains_iff_mem.mp ((getComponent_contains_eq_of_mem_of_complete H darts h_all h_le hd_comp x).symm ▸
          List.contains_iff_mem.mpr hx_comp)
      simpa using hx_d
    rw [h_flt]
    rfl

/-- Peel off the connected component of ANY element `a ∈ l` first in `countComponents`. -/
theorem countComponents_eq_one_add_filter_of_mem (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l : List H.Dart) (a : H.Dart) (ha : a ∈ l) :
    countComponents H fuel l =
      1 + countComponents H fuel (l.filter (fun x => !((getComponent H fuel a).contains x))) := by
  have ⟨he, hn⟩ := pred_getComponent_closed_of_complete H darts h_all h_le a
  rw [countComponents_partition_of_closed H fuel l (fun x => (getComponent H fuel a).contains x) he hn]
  have h_ne : l.filter (fun x => (getComponent H fuel a).contains x) ≠ [] := by
    intro hnil
    have ha_flt : a ∈ l.filter (fun x => (getComponent H fuel a).contains x) :=
      List.mem_filter.mpr ⟨ha, getComponent_contains_self H fuel a⟩
    rw [hnil] at ha_flt
    cases ha_flt
  have h_one := countComponents_eq_one_of_all_in_comp H darts h_all h_le a
    (l.filter (fun x => (getComponent H fuel a).contains x)) h_ne
    (fun x hx => List.contains_iff_mem.mp (List.mem_filter.mp hx).2)
  rw [h_one]

private theorem countComponents_eq_of_iff_mem_aux (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    ∀ (n : Nat) (l1 l2 : List H.Dart),
      l1.length ≤ n →
      (∀ x, x ∈ l1 ↔ x ∈ l2) →
      countComponents H fuel l1 = countComponents H fuel l2
  | 0, l1, l2, hlen, hiff => by
    have h1 : l1 = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst h1
    have h2 : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons y _ => exact False.elim (by simpa using (hiff y).mpr List.mem_cons_self)
    subst h2
    rfl
  | _ + 1, [], l2, _, hiff => by
    have h2 : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons y _ => exact False.elim (by simpa using (hiff y).mpr List.mem_cons_self)
    subst h2
    rfl
  | n + 1, a :: as, l2, hlen, hiff => by
    have ha_l1 : a ∈ a :: as := List.mem_cons_self
    have ha_l2 : a ∈ l2 := (hiff a).mp ha_l1
    rw [countComponents_cons H fuel a as,
        countComponents_eq_one_add_filter_of_mem H darts h_all h_le l2 a ha_l2]
    congr 1
    let as' := as.filter (fun x => !((getComponent H fuel a).contains x))
    let l2' := l2.filter (fun x => !((getComponent H fuel a).contains x))
    have has'_len : as'.length ≤ n := by
      have h_le_flt := filter_length_le (fun x => !((getComponent H fuel a).contains x)) as
      dsimp [as'] at h_le_flt ⊢
      dsimp at hlen
      omega
    have hiff' : ∀ x, x ∈ as' ↔ x ∈ l2' := by
      intro x
      dsimp [as', l2']
      rw [List.mem_filter, List.mem_filter]
      constructor
      · intro ⟨hxa, hnc⟩
        exact ⟨(hiff x).mp (List.mem_cons_of_mem a hxa), hnc⟩
      · intro ⟨hxl2, hnc⟩
        have hne : x ≠ a := by
          intro h_eq
          subst h_eq
          rw [getComponent_contains_self H fuel x] at hnc
          contradiction
        have hx_l1 := (hiff x).mpr hxl2
        rcases List.mem_cons.mp hx_l1 with rfl | hxa
        · exact False.elim (hne rfl)
        · exact ⟨hxa, hnc⟩
    exact countComponents_eq_of_iff_mem_aux H darts h_all h_le n as' l2' has'_len hiff'

/-- **Set-Extensionality of `countComponents`**:
    on a complete dart list (`darts.length ≤ fuel`), `countComponents H fuel l1 = countComponents H fuel l2`
    whenever `l1` and `l2` contain the same darts. -/
theorem countComponents_eq_of_iff_mem_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l1 l2 : List H.Dart)
    (hiff : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    countComponents H fuel l1 = countComponents H fuel l2 :=
  countComponents_eq_of_iff_mem_aux H darts h_all h_le l1.length l1 l2 (Nat.le_refl _) hiff

/-- Exact connectedness characterization for a non-empty complete hypermap:
    `numComponents H fuel darts = 1 ↔ ∀ x y : H.Dart, Nonempty (Walk H x y)`. -/
theorem numComponents_eq_one_iff_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts) (hne : darts ≠ [])
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    numComponents H fuel darts = 1 ↔ ∀ x y : H.Dart, Nonempty (Walk H x y) := by
  cases darts with
  | nil => exact False.elim (hne rfl)
  | cons d ds =>
    dsimp [numComponents]
    rw [countComponents_cons H fuel d ds]
    constructor
    · intro h_one x y
      have h_zero : countComponents H fuel (ds.filter (fun z => !((getComponent H fuel d).contains z))) = 0 := by
        omega
      have h_nil : ds.filter (fun z => !((getComponent H fuel d).contains z)) = [] := by
        by_cases h_em : ds.filter (fun z => !((getComponent H fuel d).contains z)) = []
        · exact h_em
        · have h_pos := numComponents_pos_of_ne_nil H fuel _ h_em
          dsimp [numComponents] at h_pos
          omega
      have hall_in : ∀ z : H.Dart, z ∈ getComponent H fuel d := by
        intro z
        rcases List.mem_cons.mp (h_all z) with rfl | hz_ds
        · exact mem_getComponent_self H fuel z
        · cases hcz : (getComponent H fuel d).contains z with
          | true => exact List.contains_iff_mem.mp hcz
          | false =>
            have hmem : z ∈ ds.filter (fun w => !((getComponent H fuel d).contains w)) :=
              List.mem_filter.mpr ⟨hz_ds, by rw [hcz]; rfl⟩
            rw [h_nil] at hmem
            cases hmem
      have hx : Nonempty (Walk H d x) := mem_getComponent_imp_walk H fuel d x (hall_in x)
      have hy : Nonempty (Walk H d y) := mem_getComponent_imp_walk H fuel d y (hall_in y)
      obtain ⟨wx⟩ := hx
      obtain ⟨wy⟩ := hy
      exact ⟨Walk.trans H (Walk.symm H wx) wy⟩
    · intro h_conn
      have h_nil : ds.filter (fun z => !((getComponent H fuel d).contains z)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro z _
        have hz : z ∈ getComponent H fuel d :=
          (mem_getComponent_iff_walk H (d :: ds) h_all h_le d z).mpr (h_conn d z)
        simpa using hz
      rw [h_nil]
      rfl

end CountComponentsAndDuality

end Hypermap
