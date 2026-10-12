import FourColorTheorem.Math.Topology.Surgery
import FourColorTheorem.Math.Planarity

namespace Hypermap

variable {D : Type} [DecidableEq D]

/-- A permutation p has a fixed point at d if p.f d = d. -/
def IsFixedPoint (p : Perm D) (d : D) : Prop :=
  p.f d = d

/-- Two permutations with the same forward and inverse maps are equal
    (the proof fields are equal by proof irrelevance). -/
theorem perm_ext {E : Type} (p q : Perm E) (hf : p.f = q.f) (hinv : p.inv = q.inv) : p = q := by
  cases p
  cases q
  dsimp at hf hinv
  subst hf
  subst hinv
  rfl

theorem fixed_inv {E : Type} (p : Perm E) (d : E) (h : IsFixedPoint p d) : p.inv d = d := by
  have h2 := p.left_inv d
  unfold IsFixedPoint at h
  rw [h] at h2
  exact h2

/-- After bypassing, `d` is a fixed point. -/
theorem bypass_self (p : Perm D) (d : D) : IsFixedPoint (bypass p d) d := by
  simp [IsFixedPoint, bypass]

/-- The predecessor of `d` is redirected to the successor of `d`. -/
theorem bypass_apply_pred (p : Perm D) (d x : D) (hx : x ≠ d) (hpx : p.f x = d) :
    (bypass p d).f x = p.f d := by
  simp [bypass, hx, hpx]

theorem bypass_fixed_point_f (p : Perm D) (d : D) :
    IsFixedPoint p d → (bypass p d).f = p.f := by
  intro h
  funext x
  by_cases hx : x = d
  · subst hx; simp [bypass, show p.f x = x from h]
  · by_cases hpx : p.f x = d
    · -- p.f x = d = p.f d forces x = d
      exfalso
      apply hx
      have h1 := p.left_inv x
      rw [hpx] at h1
      exact h1.symm.trans (fixed_inv p d h)
    · exact bypass_apply_of_ne p d x hx hpx

theorem bypass_fixed_point_inv (p : Perm D) (d : D) :
    IsFixedPoint p d → (bypass p d).inv = p.inv := by
  intro h
  have h_inv := fixed_inv p d h
  funext x
  by_cases hx : x = d
  · subst hx; simp [bypass, h_inv]
  · by_cases hpx : p.inv x = d
    · exfalso
      apply hx
      have h1 := p.right_inv x
      rw [hpx] at h1
      exact h1.symm.trans h
    · simp [bypass, hx, hpx]

/-- Bypassing a fixed point leaves the permutation completely unchanged. -/
theorem bypass_fixed_point (p : Perm D) (d : D) :
    IsFixedPoint p d → bypass p d = p := by
  intro h
  exact perm_ext (bypass p d) p (bypass_fixed_point_f p d h) (bypass_fixed_point_inv p d h)

/-- Bypassing is idempotent. -/
theorem bypass_bypass (p : Perm D) (d : D) : bypass (bypass p d) d = bypass p d :=
  bypass_fixed_point (bypass p d) d (bypass_self p d)

theorem countOrbits_nil (p : Perm D) (fuel : Nat) : countOrbits p fuel [] = 0 := by
  rw [countOrbits]

theorem countComponents_nil (H : Hypermap) [BEq H.Dart] (fuel : Nat) :
    countComponents H fuel [] = 0 := by
  rw [countComponents]

theorem countOrbits_singleton (p : Perm D) (fuel : Nat) (d : D) :
    countOrbits p fuel [d] = 1 := by
  rw [countOrbits]
  simp [countOrbits_nil]

theorem countComponents_singleton (H : Hypermap) [BEq H.Dart] (fuel : Nat) (d : H.Dart) :
    countComponents H fuel [d] = 1 := by
  rw [countComponents]
  simp [countComponents_nil]

theorem getOrbit_fixed_point (p : Perm D) (d : D) (fuel : Nat) (h : IsFixedPoint p d) :
    getOrbit p (fuel + 1) d = [d] := by
  dsimp [getOrbit, getOrbitAux]
  have hf : p.f d = d := h
  have hbeq : (p.f d == d) = true := by
    change (if p.f d = d then true else false) = true
    rw [hf]
    simp
  rw [hbeq]
  rfl

theorem bypass_getOrbit_self (p : Perm D) (d : D) (fuel : Nat) :
    getOrbit (bypass p d) (fuel + 1) d = [d] :=
  getOrbit_fixed_point (bypass p d) d fuel (bypass_self p d)

theorem getOrbitAux_acc_subset (p : Perm D) (start current : D) (acc : List D) (fuel : Nat) :
    ∀ x ∈ acc, x ∈ getOrbitAux p start current acc fuel := by
  induction fuel generalizing current acc with
  | zero =>
    intro x hx
    dsimp [getOrbitAux]
    exact List.Mem.tail current hx
  | succ fuel ih =>
    intro x hx
    dsimp [getOrbitAux]
    split
    · exact List.Mem.tail current hx
    · apply ih
      exact List.Mem.tail current hx

theorem mem_getOrbitAux_current (p : Perm D) (start current : D) (acc : List D) (fuel : Nat) :
    current ∈ getOrbitAux p start current acc fuel := by
  induction fuel generalizing current acc with
  | zero =>
    dsimp [getOrbitAux]
    exact List.Mem.head acc
  | succ fuel _ =>
    dsimp [getOrbitAux]
    split
    · exact List.Mem.head acc
    · apply getOrbitAux_acc_subset
      exact List.Mem.head acc

theorem mem_getOrbit_self (p : Perm D) (fuel : Nat) (d : D) :
    d ∈ getOrbit p fuel d :=
  mem_getOrbitAux_current p d d [] fuel

end Hypermap
