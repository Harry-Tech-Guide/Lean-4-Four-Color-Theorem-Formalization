import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.Reducibility

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

end Hypermap
