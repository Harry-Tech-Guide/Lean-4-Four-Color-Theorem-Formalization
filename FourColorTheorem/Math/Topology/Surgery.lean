import FourColorTheorem.Math.Hypermap

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

end Hypermap
