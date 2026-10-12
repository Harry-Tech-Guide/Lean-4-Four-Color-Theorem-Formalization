import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring

namespace Hypermap

variable {D : Type} [DecidableEq D]

/-- Removes a dart `d` from its cycle in `p`: the predecessor of `d` now maps directly
    to the successor of `d`, and `d` itself becomes a fixed point.

    Uses `DecidableEq` (not an arbitrary `BEq`): with an unlawful `BEq` the result is
    not provably a permutation. -/
def bypass (p : Perm D) (d : D) : Perm D :=
  { f := fun x => if x = d then d else if p.f x = d then p.f d else p.f x,
    inv := fun x => if x = d then d else if p.inv x = d then p.inv d else p.inv x,
    left_inv := by
      intro x
      by_cases hx : x = d
      · subst hx; simp
      · by_cases hpx : p.f x = d
        · have hx' : p.inv d = x := by rw [← hpx]; exact p.left_inv x
          have hpd : p.f d ≠ d := by
            intro h
            have h2 := p.left_inv d
            rw [h] at h2
            exact hx (hx'.symm.trans h2)
          simp [hx, hpx, hpd, p.left_inv d, hx']
        · simp [hx, hpx, p.left_inv x],
    right_inv := by
      intro x
      by_cases hx : x = d
      · subst hx; simp
      · by_cases hpx : p.inv x = d
        · have hx' : p.f d = x := by rw [← hpx]; exact p.right_inv x
          have hpd : p.inv d ≠ d := by
            intro h
            have h2 := p.right_inv d
            rw [h] at h2
            exact hx (hx'.symm.trans h2)
          simp [hx, hpx, hpd, p.right_inv d, hx']
        · simp [hx, hpx, p.right_inv x] }

/-- Bypassing a dart of an involution yields an involution. -/
theorem bypass_involution (p : Perm D) (hp : ∀ x, p.f (p.f x) = x) (d : D) :
    ∀ x, (bypass p d).f ((bypass p d).f x) = x := by
  intro x
  simp only [bypass]
  by_cases hx : x = d
  · subst hx; simp
  · by_cases hpx : p.f x = d
    · have hxd : p.f d = x := by rw [← hpx]; exact hp x
      simp [hx, hpx, hxd]
    · simp [hx, hpx, hp x]

/-- Bypassing a dart does not affect any dart other than d and the predecessor of d. -/
theorem bypass_apply_of_ne (p : Perm D) (d x : D) (hx : x ≠ d) (hpx : p.f x ≠ d) :
    (bypass p d).f x = p.f x := by
  dsimp [bypass]
  by_cases h : x = d
  · exact False.elim (hx h)
  · by_cases hp : p.f x = d
    · exact False.elim (hpx hp)
    · simp [h, hp]

/-- Bypassing a dart d makes d a fixed point. -/
theorem bypass_apply_self (p : Perm D) (d : D) :
    (bypass p d).f d = d := by
  dsimp [bypass]
  simp

/-- The face permutation determined by edge and node: `face = node⁻¹ ∘ edge⁻¹`. -/
def faceOf (e n : Perm D) : Perm D :=
  { f := fun x => n.inv (e.inv x),
    inv := fun x => e.f (n.f x),
    left_inv := fun x => by simp only [Perm.right_inv],
    right_inv := fun x => by simp only [Perm.left_inv] }

/-- Deletes the edge `{d, edge d}`: both darts are detached from their edge and node
    cycles (they become fixed points), and the face permutation is recomputed. -/
def deleteEdge (H : Hypermap) [DecidableEq H.Dart] (d : H.Dart) : Hypermap :=
  { Dart := H.Dart,
    edge := bypass (bypass H.edge d) (H.edge.f d),
    node := bypass (bypass H.node d) (H.edge.f d),
    face := faceOf (bypass (bypass H.edge d) (H.edge.f d)) (bypass (bypass H.node d) (H.edge.f d)),
    edge_involution :=
      bypass_involution _ (bypass_involution H.edge H.edge_involution d) (H.edge.f d),
    edge_node_face_id := fun x => by simp only [faceOf, Perm.right_inv] }

/-- Edge contraction is edge deletion in the dual map. -/
def contractEdge (H : Hypermap) [DecidableEq H.Dart] (d : H.Dart) : Hypermap :=
  have : DecidableEq H.dual.Dart := inferInstanceAs (DecidableEq H.Dart)
  (H.dual.deleteEdge d).dual

/-- Excises a list of darts from a hypermap by iteratively deleting their edges. -/
def exciseDarts (H : Hypermap) [DecidableEq H.Dart] : List H.Dart → Hypermap
  | [] => H
  | d :: ds => exciseDarts (H.deleteEdge d) ds

/-- Excises an embedded configuration from a hypermap by deleting all internal darts.
    The internal darts are those with indices from ringSize to totalNodes - 1. -/
def exciseConfiguration (H : Hypermap) [DecidableEq H.Dart] (c : Math.Configuration) (f : Nat → H.Dart) : Hypermap :=
  let internalIndices := List.range c.interiorSize |>.map (fun i => c.ringSize + i)
  let internalDarts := internalIndices.map f
  exciseDarts H internalDarts

/-- Edge deletion step operating directly on permutations of a fixed type `D`. -/
def deleteEdgePerms {D : Type} [DecidableEq D] (edge node : Perm D) (d : D) : Perm D × Perm D :=
  let e' := bypass (bypass edge d) (edge.f d)
  let n' := bypass (bypass node d) (edge.f d)
  (e', n')

/-- Iterative permutation excision on a fixed dart type. -/
def excisePerms {D : Type} [DecidableEq D] : Perm D × Perm D → List D → Perm D × Perm D
  | p, [] => p
  | (e, n), d :: ds => excisePerms (deleteEdgePerms e n d) ds

/-- Deleting edges preserves the involution property of the edge permutation. -/
theorem deleteEdgePerms_involution {D : Type} [DecidableEq D] (e n : Perm D) (he : ∀ x, e.f (e.f x) = x) (d : D) :
    ∀ x, (deleteEdgePerms e n d).1.f ((deleteEdgePerms e n d).1.f x) = x :=
  bypass_involution _ (bypass_involution e he d) (e.f d)

/-- Full list excision preserves the edge involution property. -/
theorem excisePerms_involution {D : Type} [DecidableEq D] (l : List D) :
    ∀ (e n : Perm D), (∀ x, e.f (e.f x) = x) →
      ∀ x, (excisePerms (e, n) l).1.f ((excisePerms (e, n) l).1.f x) = x := by
  induction l with
  | nil =>
    intro e _ he x
    exact he x
  | cons d ds ih =>
    intro e n he x
    dsimp [excisePerms]
    have he' := deleteEdgePerms_involution e n he d
    exact ih _ _ he' x

/-- Edge deletion preserves the edge permutation on darts outside the edge {d, edge d}. -/
theorem deleteEdgePerms_edge_apply_of_ne {D : Type} [DecidableEq D]
    (e n : Perm D) (he : ∀ y, e.f (e.f y) = y) (d x : D)
    (hxd : x ≠ d) (hxed : e.f x ≠ d) :
    (deleteEdgePerms e n d).1.f x = e.f x := by
  dsimp [deleteEdgePerms]
  have h_x_ne_ed : x ≠ e.f d := by
    intro h
    have : e.f x = e.f (e.f d) := by rw [h]
    rw [he d] at this
    exact hxed this
  have h2 : (bypass e d).f x ≠ e.f d := by
    rw [bypass_apply_of_ne e d x hxd hxed]
    intro h
    have : e.f (e.f x) = e.f (e.f d) := by rw [h]
    rw [he x, he d] at this
    exact hxd this
  rw [bypass_apply_of_ne (bypass e d) (e.f d) x h_x_ne_ed h2]
  exact bypass_apply_of_ne e d x hxd hxed

/-- Iterative edge deletion preserves the edge permutation on any dart that is not excised
    and whose edge partner is not excised. -/
theorem excisePerms_edge_apply_of_not_mem {D : Type} [DecidableEq D]
    (l : List D) :
    ∀ (e n : Perm D), (∀ y, e.f (e.f y) = y) →
      ∀ x, (∀ d ∈ l, x ≠ d ∧ e.f x ≠ d) →
        (excisePerms (e, n) l).1.f x = e.f x := by
  induction l with
  | nil =>
    intro e _ _ x _
    rfl
  | cons d ds ih =>
    intro e n he x hx
    dsimp [excisePerms]
    have hd_mem : d ∈ d :: ds := List.Mem.head ds
    have ⟨hxd, hxed⟩ := hx d hd_mem
    have he' := deleteEdgePerms_involution e n he d
    have h_del := deleteEdgePerms_edge_apply_of_ne e n he d x hxd hxed
    have hx_ds : ∀ d' ∈ ds, x ≠ d' ∧ (deleteEdgePerms e n d).1.f x ≠ d' := by
      intro d' hd'
      have hd'_mem : d' ∈ d :: ds := List.Mem.tail d hd'
      have ⟨hxd', hxed'⟩ := hx d' hd'_mem
      rw [h_del]
      exact ⟨hxd', hxed'⟩
    have ih_app := ih (deleteEdgePerms e n d).1 (deleteEdgePerms e n d).2 he' x hx_ds
    rw [ih_app, h_del]

/-- Excision of an embedded configuration yielding a hypermap with definitionally identical dart type. -/
def exciseFixed (H : Hypermap) [DecidableEq H.Dart] (c : Math.Configuration) (f : Nat → H.Dart) : Hypermap :=
  let internalIndices := List.range c.interiorSize |>.map (fun i => c.ringSize + i)
  let internalDarts := internalIndices.map f
  let p := excisePerms (H.edge, H.node) internalDarts
  { Dart := H.Dart,
    edge := p.1,
    node := p.2,
    face := faceOf p.1 p.2,
    edge_involution := excisePerms_involution internalDarts H.edge H.node H.edge_involution,
    edge_node_face_id := fun x => by simp only [faceOf, Perm.right_inv] }

/-- Excision preserves the edge permutation on any dart that is not internal
    and whose edge partner is not internal. -/
theorem exciseFixed_edge_apply_of_not_mem (H : Hypermap) [DecidableEq H.Dart]
    (c : Math.Configuration) (f : Nat → H.Dart) (x : H.Dart)
    (hx : ∀ d ∈ (List.range c.interiorSize |>.map (fun i => c.ringSize + i)).map f, x ≠ d ∧ H.edge.f x ≠ d) :
    (exciseFixed H c f).edge.f x = H.edge.f x := by
  dsimp [exciseFixed]
  exact excisePerms_edge_apply_of_not_mem _ H.edge H.node H.edge_involution x hx

/-- Boundary darts (with indices < ringSize) never belong to the internal darts list
    whenever the embedding f is injective. -/
theorem not_mem_internalDarts_of_lt_ringSize {D : Type} (c : Math.Configuration) (f : Nat → D)
    (h_inj : ∀ i < c.totalNodes, ∀ j < c.totalNodes, i ≠ j → f i ≠ f j)
    (i : Nat) (hi : i < c.ringSize) :
    f i ∉ (List.range c.interiorSize |>.map (fun k => c.ringSize + k)).map f := by
  intro h_mem
  rw [List.mem_map] at h_mem
  rcases h_mem with ⟨k_idx, hk_idx, h_eq⟩
  rw [List.mem_map] at hk_idx
  rcases hk_idx with ⟨k, hk, hk_eq⟩
  rw [List.mem_range] at hk
  subst hk_eq
  have hi_total : i < c.totalNodes := by
    dsimp [Math.Configuration.totalNodes]
    omega
  have hk_total : c.ringSize + k < c.totalNodes := by
    dsimp [Math.Configuration.totalNodes]
    omega
  have h_ne : i ≠ c.ringSize + k := by omega
  have h_f_ne := h_inj i hi_total (c.ringSize + k) hk_total h_ne
  exact h_f_ne h_eq.symm

/-- Recursively erases a list of excised darts from the dart list. -/
def eraseAllDarts {D : Type} [BEq D] : List D → List D → List D
  | darts, [] => darts
  | darts, d :: ds => eraseAllDarts (darts.erase d) ds

/-- Erasing darts can only decrease or preserve list length. -/
theorem eraseAllDarts_length_le {D : Type} [BEq D] (darts : List D) (excised : List D) :
    (eraseAllDarts darts excised).length ≤ darts.length := by
  induction excised generalizing darts with
  | nil =>
    dsimp [eraseAllDarts]
    exact Nat.le_refl _
  | cons d ds ih =>
    dsimp [eraseAllDarts]
    have h1 := ih (darts.erase d)
    have h2 := List.length_erase_le d darts
    omega

/-- Erasing a non-empty list of excised darts containing at least one dart from the list
    strictly decreases the dart count. -/
theorem eraseAllDarts_strictly_smaller {D : Type} [BEq D] [LawfulBEq D] (darts : List D) (d : D) (ds : List D)
    (hd : d ∈ darts) :
    (eraseAllDarts darts (d :: ds)).length < darts.length := by
  dsimp [eraseAllDarts]
  have hLe := eraseAllDarts_length_le (darts.erase d) ds
  have hLt : (darts.erase d).length < darts.length := by
    have hlen := List.length_erase_of_mem hd
    have hpos := List.length_pos_of_mem hd
    omega
  omega

theorem mem_erase_of_ne {D : Type} [BEq D] [LawfulBEq D] {x d : D} (h : d ≠ x) {l : List D} (hd : d ∈ l) :
    d ∈ l.erase x := by
  rw [List.mem_erase_of_ne h]
  exact hd

/-- Erasing any list of darts containing at least one element of `darts` strictly decreases length. -/
theorem eraseAllDarts_strictly_smaller_of_mem {D : Type} [BEq D] [LawfulBEq D] (darts : List D) (l : List D) (d : D)
    (hd_l : d ∈ l) (hd_darts : d ∈ darts) :
    (eraseAllDarts darts l).length < darts.length := by
  induction l generalizing darts with
  | nil =>
    contradiction
  | cons x xs ih =>
    dsimp [eraseAllDarts]
    by_cases hx : d = x
    · subst hx
      exact eraseAllDarts_strictly_smaller darts d xs hd_darts
    · have hd_xs : d ∈ xs := by
        cases hd_l with
        | head => exact False.elim (hx rfl)
        | tail _ h => exact h
      have hd_erased : d ∈ darts.erase x := mem_erase_of_ne hx hd_darts
      have ih_sub := ih (darts.erase x) hd_xs hd_erased
      have hle := List.length_erase_le x darts
      omega

/-- Excising an embedded configuration with strictly positive interior size strictly reduces dart count. -/
theorem exciseConfiguration_strictly_smaller {D : Type} [DecidableEq D]
    (darts : List D) (c : Math.Configuration) (h_int : c.interiorSize > 0)
    (f : Nat → D) (hf_mem : ∀ i < c.totalNodes, f i ∈ darts) :
    let internalIndices := List.range c.interiorSize |>.map (fun i => c.ringSize + i)
    let internalDarts := internalIndices.map f
    (eraseAllDarts darts internalDarts).length < darts.length := by
  dsimp
  have h_pos : 0 < c.interiorSize := h_int
  have h_range : 0 ∈ List.range c.interiorSize := List.mem_range.mpr h_pos
  have h_idx_mem : c.ringSize ∈ (List.range c.interiorSize).map (fun i => c.ringSize + i) := by
    apply List.mem_map_of_mem (fun i => c.ringSize + i) h_range
  have h_dart_mem : f c.ringSize ∈ ((List.range c.interiorSize).map (fun i => c.ringSize + i)).map f := by
    apply List.mem_map_of_mem f h_idx_mem
  have h_f_in_darts : f c.ringSize ∈ darts := by
    apply hf_mem c.ringSize
    dsimp [Math.Configuration.totalNodes]
    omega
  exact eraseAllDarts_strictly_smaller_of_mem darts _ (f c.ringSize) h_dart_mem h_f_in_darts

/-- Boundary coloring restriction of a face coloring of the excised map. -/
def configBoundaryColoring (H : Hypermap) (c : Math.Configuration) (f : Nat → H.Dart) (col : FaceColoring H) : Math.BoundaryColoring c :=
  fun i => col.color (f i)

/-- Topologically glued dart color: internal darts take their color from `ext`,
    exterior and boundary darts take their color from `col`. -/
def gluedColor (H : Hypermap) [DecidableEq H.Dart] (c : Math.Configuration) (f : Nat → H.Dart)
    (col : FaceColoring H) (ext : Nat → Color) (d : H.Dart) : Color :=
  match (List.range c.interiorSize).find? (fun i => f (c.ringSize + i) = d) with
  | some i => ext (c.ringSize + i)
  | none => col.color d

end Hypermap
