import FourColorTheorem.Math.Topology.Surgery
import FourColorTheorem.Math.Planarity

namespace Hypermap

set_option linter.unusedSectionVars false

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

theorem countOrbits_nil (p : Perm D) (fuel : Nat) : countOrbits p fuel [] = 0 := rfl

theorem countComponents_nil (H : Hypermap) [BEq H.Dart] (fuel : Nat) :
    countComponents H fuel [] = 0 := rfl

theorem countOrbits_singleton (p : Perm D) (fuel : Nat) (d : D) :
    countOrbits p fuel [d] = 1 := rfl

theorem countComponents_singleton (H : Hypermap) [BEq H.Dart] (fuel : Nat) (d : H.Dart) :
    countComponents H fuel [d] = 1 := rfl

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

/-!
### Permutation Iteration, Orbit Closure, and Fuel-Independence
-/

/-- Iterate a permutation `p` `n` times starting from `d`. -/
def Perm.iter {E : Type} (p : Perm E) : Nat → E → E
  | 0, d => d
  | n + 1, d => p.f (Perm.iter p n d)

@[simp] theorem Perm.iter_zero {E : Type} (p : Perm E) (d : E) :
    Perm.iter p 0 d = d := rfl

@[simp] theorem Perm.iter_succ {E : Type} (p : Perm E) (n : Nat) (d : E) :
    Perm.iter p (n + 1) d = p.f (Perm.iter p n d) := rfl

/-- `Perm.iter p (n + 1) d = Perm.iter p n (p.f d)`. -/
theorem Perm.iter_succ_right {E : Type} (p : Perm E) (n : Nat) (d : E) :
    Perm.iter p (n + 1) d = Perm.iter p n (p.f d) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    dsimp [Perm.iter]
    exact congrArg p.f (ih d)

/-- Addition law for permutation iteration: `p^(m + n)(d) = p^m(p^n(d))`. -/
theorem Perm.iter_add {E : Type} (p : Perm E) (m n : Nat) (d : E) :
    Perm.iter p (m + n) d = Perm.iter p m (Perm.iter p n d) := by
  induction m with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ m ih =>
    rw [Nat.succ_add]
    dsimp [Perm.iter]
    rw [ih]

/-- `Perm.iter p n` is injective for every `n`. -/
theorem Perm.iter_inj {E : Type} (p : Perm E) (n : Nat) {x y : E}
    (h : Perm.iter p n x = Perm.iter p n y) : x = y := by
  induction n with
  | zero => exact h
  | succ n ih =>
    dsimp [Perm.iter] at h
    have h' : p.inv (p.f (Perm.iter p n x)) = p.inv (p.f (Perm.iter p n y)) :=
      congrArg p.inv h
    rw [p.left_inv, p.left_inv] at h'
    exact ih h'

/-- Iterating `p.symm` undoes `Perm.iter p n`. -/
theorem Perm.iter_symm_left_inv {E : Type} (p : Perm E) (n : Nat) (d : E) :
    Perm.iter p.symm n (Perm.iter p n d) = d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    rw [Perm.iter_succ_right p n d]
    have h_step := ih (p.f d)
    dsimp [Perm.iter]
    rw [h_step]
    exact p.left_inv d

/-- Predicate witnessing that the orbit from `current` hits `start` within `fuel` steps. -/
def orbitClosesWithin (p : Perm D) (start current : D) : Nat → Prop
  | 0 => False
  | fuel + 1 => p.f current = start ∨ orbitClosesWithin p start (p.f current) fuel

theorem orbitClosesWithin_mono (p : Perm D) (start current : D) {fuel1 fuel2 : Nat}
    (h_closes : orbitClosesWithin p start current fuel1) (h_le : fuel1 ≤ fuel2) :
    orbitClosesWithin p start current fuel2 := by
  induction fuel1 generalizing current fuel2 with
  | zero => contradiction
  | succ f1 ih =>
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      rcases h_closes with h_now | h_later
      · exact Or.inl h_now
      · exact Or.inr (ih (p.f current) h_later (Nat.le_of_succ_le_succ h_le))

/-- Equivalence between `orbitClosesWithin` and existence of a period `< fuel`. -/
theorem orbitClosesWithin_iff_exists_iter (p : Perm D) (start current : D) (fuel : Nat) :
    orbitClosesWithin p start current fuel ↔
      ∃ k < fuel, Perm.iter p (k + 1) current = start := by
  induction fuel generalizing current with
  | zero =>
    constructor
    · intro h; contradiction
    · rintro ⟨k, hk, _⟩; omega
  | succ fuel ih =>
    dsimp [orbitClosesWithin]
    rw [ih (p.f current)]
    constructor
    · rintro (h0 | ⟨k, hk, hiter⟩)
      · refine ⟨0, Nat.zero_lt_succ fuel, ?_⟩
        exact h0
      · refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
        change Perm.iter p (k + 1 + 1) current = start
        rw [Perm.iter_succ_right p (k + 1) current]
        exact hiter
    · rintro ⟨k, hk, hiter⟩
      cases k with
      | zero =>
        exact Or.inl hiter
      | succ k' =>
        right
        refine ⟨k', Nat.lt_of_succ_lt_succ hk, ?_⟩
        rw [← Perm.iter_succ_right p (k' + 1) current]
        exact hiter

/-- Fuel-Independence Theorem for `getOrbitAux`:
    Once `orbitClosesWithin p start current fuel1` holds, increasing fuel to any `fuel2 ≥ fuel1`
    produces the exact same list. -/
theorem getOrbitAux_fuel_eq_of_closes (p : Perm D) (start current : D) (acc : List D)
    {fuel1 fuel2 : Nat} (h_closes : orbitClosesWithin p start current fuel1)
    (h_le : fuel1 ≤ fuel2) :
    getOrbitAux p start current acc fuel2 = getOrbitAux p start current acc fuel1 := by
  induction fuel1 generalizing current acc fuel2 with
  | zero => contradiction
  | succ f1 ih =>
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      dsimp [getOrbitAux]
      by_cases h_hit : p.f current = start
      · have hbeq : (p.f current == start) = true := by
          change (if p.f current = start then true else false) = true
          rw [h_hit]; simp
        rw [hbeq]
        rfl
      · have hbeq : (p.f current == start) = false := by
          change (if p.f current = start then true else false) = false
          rw [if_neg h_hit]
        rw [hbeq]
        dsimp
        rcases h_closes with h_now | h_later
        · exact False.elim (h_hit h_now)
        · exact ih (p.f current) (current :: acc) h_later (Nat.le_of_succ_le_succ h_le)

/-- Fuel-Independence Theorem for `getOrbit`:
    If `d`'s orbit closes within `fuel1` steps (`∃ k < fuel1, Perm.iter p (k + 1) d = d`),
    then `getOrbit p fuel2 d = getOrbit p fuel1 d` for all `fuel2 ≥ fuel1`. -/
theorem getOrbit_fuel_eq_of_closes (p : Perm D) (d : D) {fuel1 fuel2 : Nat}
    (h_closes : orbitClosesWithin p d d fuel1) (h_le : fuel1 ≤ fuel2) :
    getOrbit p fuel2 d = getOrbit p fuel1 d :=
  getOrbitAux_fuel_eq_of_closes p d d [] h_closes h_le

/-- Every element of `getOrbitAux p start current acc fuel` is either in `acc`
    or of the form `Perm.iter p k current` for some `k ≤ fuel`. -/
theorem mem_getOrbitAux_imp_acc_or_iter (p : Perm D) (start current : D) (acc : List D) (fuel : Nat) :
    ∀ x ∈ getOrbitAux p start current acc fuel,
      x ∈ acc ∨ ∃ k ≤ fuel, x = Perm.iter p k current := by
  induction fuel generalizing current acc with
  | zero =>
    intro x hx
    dsimp [getOrbitAux] at hx
    rcases List.mem_cons.mp hx with rfl | h_acc
    · right; exact ⟨0, Nat.le_refl 0, rfl⟩
    · left; exact h_acc
  | succ fuel ih =>
    intro x hx
    dsimp [getOrbitAux] at hx
    split at hx
    · rcases List.mem_cons.mp hx with rfl | h_acc
      · right; exact ⟨0, Nat.zero_le _, rfl⟩
      · left; exact h_acc
    · rcases ih (p.f current) (current :: acc) x hx with h_in_cons | ⟨k, hk, h_iter⟩
      · rcases List.mem_cons.mp h_in_cons with rfl | h_acc
        · right; exact ⟨0, Nat.zero_le _, rfl⟩
        · left; exact h_acc
      · right
        refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        rw [Perm.iter_succ_right p k current]
        exact h_iter

/-- Every element of `getOrbit p fuel d` is an iterate `Perm.iter p k d` with `k ≤ fuel`. -/
theorem mem_getOrbit_imp_exists_iter (p : Perm D) (fuel : Nat) (d x : D)
    (hx : x ∈ getOrbit p fuel d) :
    ∃ k ≤ fuel, x = Perm.iter p k d := by
  rcases mem_getOrbitAux_imp_acc_or_iter p d d [] fuel x hx with h_nil | h_iter
  · contradiction
  · exact h_iter

/-- Closure invariant for `getOrbitAux`: if `start ∈ current :: acc`, every `x ∈ acc` has
    `p.f x ∈ current :: acc`, and `orbitClosesWithin p start current fuel` holds, then the
    resulting list is closed under `p.f`. -/
theorem getOrbitAux_closed_under_f (p : Perm D) (start current : D) (acc : List D) (fuel : Nat)
    (h_start : start ∈ current :: acc)
    (h_acc : ∀ x ∈ acc, p.f x ∈ current :: acc)
    (h_closes : orbitClosesWithin p start current fuel) :
    ∀ x ∈ getOrbitAux p start current acc fuel,
      p.f x ∈ getOrbitAux p start current acc fuel := by
  induction fuel generalizing current acc with
  | zero => contradiction
  | succ fuel ih =>
    dsimp [getOrbitAux]
    by_cases h_hit : p.f current = start
    · have hbeq : (p.f current == start) = true := by
        change (if p.f current = start then true else false) = true
        rw [h_hit]; simp
      rw [hbeq]
      dsimp
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx_acc
      · rw [h_hit]
        exact h_start
      · exact h_acc x hx_acc
    · have hbeq : (p.f current == start) = false := by
        change (if p.f current = start then true else false) = false
        rw [if_neg h_hit]
      rw [hbeq]
      dsimp
      rcases h_closes with h_now | h_later
      · exact False.elim (h_hit h_now)
      · apply ih (p.f current) (current :: acc)
        · exact List.Mem.tail (p.f current) h_start
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy_acc
          · exact List.Mem.head _
          · exact List.Mem.tail (p.f current) (h_acc y hy_acc)
        · exact h_later

/-- When `orbitClosesWithin p d d fuel` holds, `getOrbit p fuel d` is closed under `p.f`. -/
theorem getOrbit_closed_under_f (p : Perm D) (fuel : Nat) (d : D)
    (h_closes : orbitClosesWithin p d d fuel) :
    ∀ x ∈ getOrbit p fuel d, p.f x ∈ getOrbit p fuel d := by
  apply getOrbitAux_closed_under_f p d d [] fuel
  · exact List.Mem.head []
  · intro x hx; contradiction
  · exact h_closes

/-- When `orbitClosesWithin p d d fuel` holds, every iterate `Perm.iter p k d` belongs to `getOrbit p fuel d`. -/
theorem iter_mem_getOrbit_of_closes (p : Perm D) (fuel : Nat) (d : D)
    (h_closes : orbitClosesWithin p d d fuel) (k : Nat) :
    Perm.iter p k d ∈ getOrbit p fuel d := by
  induction k with
  | zero =>
    exact mem_getOrbit_self p fuel d
  | succ k ih =>
    dsimp [Perm.iter]
    exact getOrbit_closed_under_f p fuel d h_closes (Perm.iter p k d) ih

/-- Exact characterization of `getOrbit` membership when the orbit closes within `fuel` steps:
    `x ∈ getOrbit p fuel d` if and only if `x` is in the mathematical orbit `{p^k(d) | k ∈ ℕ}`. -/
theorem mem_getOrbit_iff_exists_iter (p : Perm D) (fuel : Nat) (d x : D)
    (h_closes : orbitClosesWithin p d d fuel) :
    x ∈ getOrbit p fuel d ↔ ∃ k : Nat, x = Perm.iter p k d := by
  constructor
  · intro hx
    rcases mem_getOrbit_imp_exists_iter p fuel d x hx with ⟨k, _, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact iter_mem_getOrbit_of_closes p fuel d h_closes k

/-- Transitivity of orbit membership when `d1`'s orbit closes within `fuel` steps. -/
theorem mem_getOrbit_trans (p : Perm D) (fuel : Nat) {d1 d2 d3 : D}
    (h_closes : orbitClosesWithin p d1 d1 fuel)
    (h12 : d2 ∈ getOrbit p fuel d1) (h23 : d3 ∈ getOrbit p fuel d2) :
    d3 ∈ getOrbit p fuel d1 := by
  rcases (mem_getOrbit_iff_exists_iter p fuel d1 d2 h_closes).mp h12 with ⟨k1, rfl⟩
  rcases mem_getOrbit_imp_exists_iter p fuel (Perm.iter p k1 d1) d3 h23 with ⟨k2, _, rfl⟩
  rw [← Perm.iter_add p k2 k1 d1]
  exact iter_mem_getOrbit_of_closes p fuel d1 h_closes (k2 + k1)

/-- Commutativity of permutation iterates: `p^m(p^n(d)) = p^n(p^m(d))`. -/
theorem Perm.iter_comm {E : Type} (p : Perm E) (m n : Nat) (d : E) :
    Perm.iter p m (Perm.iter p n d) = Perm.iter p n (Perm.iter p m d) := by
  rw [← Perm.iter_add, Nat.add_comm, Perm.iter_add]

/-- Any multiple of a period `T` of `d` also fixes `d`: `p^(q * T)(d) = d`. -/
theorem Perm.iter_mul_period {E : Type} (p : Perm E) {T : Nat} {d : E}
    (hT : Perm.iter p T d = d) (q : Nat) :
    Perm.iter p (q * T) d = d := by
  induction q with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ q ih =>
    have h_split : (q + 1) * T = T + q * T := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [h_split, Perm.iter_add, ih, hT]

/-- If `d1`'s orbit closes within `fuel` steps and `d2 ∈ getOrbit p fuel d1`,
    then `d2`'s orbit also closes within `fuel` steps with the exact same period. -/
theorem orbitClosesWithin_of_mem_getOrbit (p : Perm D) (fuel : Nat) {d1 d2 : D}
    (h_closes : orbitClosesWithin p d1 d1 fuel) (h12 : d2 ∈ getOrbit p fuel d1) :
    orbitClosesWithin p d2 d2 fuel := by
  rcases (orbitClosesWithin_iff_exists_iter p d1 d1 fuel).mp h_closes with ⟨m, hm, h_per⟩
  rcases mem_getOrbit_imp_exists_iter p fuel d1 d2 h12 with ⟨k, _, rfl⟩
  apply (orbitClosesWithin_iff_exists_iter p (Perm.iter p k d1) (Perm.iter p k d1) fuel).mpr
  refine ⟨m, hm, ?_⟩
  rw [Perm.iter_comm p (m + 1) k d1, h_per]

/-- Symmetry of orbit membership when `d1`'s orbit closes within `fuel` steps:
    if `d2 ∈ getOrbit p fuel d1`, then `d1 ∈ getOrbit p fuel d2`. -/
theorem mem_getOrbit_symm (p : Perm D) (fuel : Nat) {d1 d2 : D}
    (h_closes : orbitClosesWithin p d1 d1 fuel) (h12 : d2 ∈ getOrbit p fuel d1) :
    d1 ∈ getOrbit p fuel d2 := by
  have h_closes2 := orbitClosesWithin_of_mem_getOrbit p fuel h_closes h12
  rcases (orbitClosesWithin_iff_exists_iter p d1 d1 fuel).mp h_closes with ⟨m, _, h_per⟩
  rcases mem_getOrbit_imp_exists_iter p fuel d1 d2 h12 with ⟨k, _, rfl⟩
  have h_return : Perm.iter p (k * m) (Perm.iter p k d1) = d1 := by
    rw [← Perm.iter_add p (k * m) k d1]
    have h_factor : k * m + k = k * (m + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    rw [h_factor]
    exact Perm.iter_mul_period p h_per k
  have h_mem := iter_mem_getOrbit_of_closes p fuel (Perm.iter p k d1) h_closes2 (k * m)
  rwa [h_return] at h_mem

theorem Perm.symm_symm {E : Type} (p : Perm E) : p.symm.symm = p := by
  cases p
  rfl

/-- If `d`'s orbit under `p` closes within `fuel` steps, then `d`'s orbit under `p.symm`
    also closes within `fuel` steps. -/
theorem orbitClosesWithin_symm_perm (p : Perm D) (fuel : Nat) (d : D)
    (h_closes : orbitClosesWithin p d d fuel) :
    orbitClosesWithin p.symm d d fuel := by
  rcases (orbitClosesWithin_iff_exists_iter p d d fuel).mp h_closes with ⟨m, hm, h_per⟩
  apply (orbitClosesWithin_iff_exists_iter p.symm d d fuel).mpr
  refine ⟨m, hm, ?_⟩
  have h_inv := Perm.iter_symm_left_inv p (m + 1) d
  rw [h_per] at h_inv
  exact h_inv

/-- Equivalence of orbits under `p` and `p.symm`:
    when `orbitClosesWithin p d d fuel` holds, `getOrbit p.symm fuel d` and `getOrbit p fuel d`
    contain the exact same elements (`x ∈ getOrbit p.symm fuel d ↔ x ∈ getOrbit p fuel d`). -/
theorem mem_getOrbit_symm_perm_iff (p : Perm D) (fuel : Nat) (d x : D)
    (h_closes : orbitClosesWithin p d d fuel) :
    x ∈ getOrbit p.symm fuel d ↔ x ∈ getOrbit p fuel d := by
  have h_closes_symm := orbitClosesWithin_symm_perm p fuel d h_closes
  constructor
  · intro hx
    rcases (orbitClosesWithin_iff_exists_iter p.symm d d fuel).mp h_closes_symm with ⟨m, _, h_per⟩
    rcases mem_getOrbit_imp_exists_iter p.symm fuel d x hx with ⟨k, _, rfl⟩
    have h_return : Perm.iter p.symm (k * m) (Perm.iter p.symm k d) = d := by
      rw [← Perm.iter_add p.symm (k * m) k d]
      have h_factor : k * m + k = k * (m + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [h_factor]
      exact Perm.iter_mul_period p.symm h_per k
    have h_fwd : Perm.iter p (k * m) d = Perm.iter p.symm k d := by
      have h_inv := Perm.iter_symm_left_inv p.symm (k * m) (Perm.iter p.symm k d)
      rw [Perm.symm_symm p, h_return] at h_inv
      exact h_inv
    have h_mem := iter_mem_getOrbit_of_closes p fuel d h_closes (k * m)
    rwa [h_fwd] at h_mem
  · intro hx
    rcases (orbitClosesWithin_iff_exists_iter p d d fuel).mp h_closes with ⟨m, _, h_per⟩
    rcases mem_getOrbit_imp_exists_iter p fuel d x hx with ⟨k, _, rfl⟩
    have h_return : Perm.iter p (k * m) (Perm.iter p k d) = d := by
      rw [← Perm.iter_add p (k * m) k d]
      have h_factor : k * m + k = k * (m + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [h_factor]
      exact Perm.iter_mul_period p h_per k
    have h_bwd : Perm.iter p.symm (k * m) d = Perm.iter p k d := by
      have h_inv := Perm.iter_symm_left_inv p (k * m) (Perm.iter p k d)
      rw [h_return] at h_inv
      exact h_inv
    have h_mem := iter_mem_getOrbit_of_closes p.symm fuel d h_closes_symm (k * m)
    rwa [h_bwd] at h_mem

/-- Boolean `.contains` equality for `getOrbit p.symm` and `getOrbit p` when the orbit closes. -/
theorem getOrbit_symm_contains_eq (p : Perm D) (fuel : Nat) (d x : D)
    (h_closes : orbitClosesWithin p d d fuel) :
    (getOrbit p.symm fuel d).contains x = (getOrbit p fuel d).contains x := by
  by_cases hx : x ∈ getOrbit p fuel d
  · have hx_symm : x ∈ getOrbit p.symm fuel d :=
      (mem_getOrbit_symm_perm_iff p fuel d x h_closes).mpr hx
    rw [List.contains_iff_mem.mpr hx, List.contains_iff_mem.mpr hx_symm]
  · have hx_symm : x ∉ getOrbit p.symm fuel d :=
      fun h => hx ((mem_getOrbit_symm_perm_iff p fuel d x h_closes).mp h)
    cases h1 : (getOrbit p.symm fuel d).contains x with
    | true => exact False.elim (hx_symm (List.contains_iff_mem.mp h1))
    | false =>
      cases h2 : (getOrbit p fuel d).contains x with
      | true => exact False.elim (hx (List.contains_iff_mem.mp h2))
      | false => rfl

/-- Fuel-independence of `countOrbitsAux` when all darts in `l` have orbits closing within `fuel1`. -/
theorem countOrbitsAux_fuel_eq_of_closes (p : Perm D) {fuel1 fuel2 : Nat}
    (steps : Nat) (l : List D)
    (h_closes : ∀ d ∈ l, orbitClosesWithin p d d fuel1)
    (h_le : fuel1 ≤ fuel2) :
    countOrbitsAux p fuel2 steps l = countOrbitsAux p fuel1 steps l := by
  induction steps generalizing l with
  | zero => rfl
  | succ steps ih =>
    cases l with
    | nil => rfl
    | cons d ds =>
      dsimp [countOrbitsAux]
      have hd_closes : orbitClosesWithin p d d fuel1 := h_closes d (List.Mem.head ds)
      rw [getOrbit_fuel_eq_of_closes p d hd_closes h_le]
      congr 1
      apply ih
      intro x hx
      have hx_ds : x ∈ ds := (List.mem_filter.mp hx).1
      exact h_closes x (List.Mem.tail d hx_ds)

/-- Fuel-independence of `countOrbits` when all darts in `l` have orbits closing within `fuel1`. -/
theorem countOrbits_fuel_eq_of_closes (p : Perm D) {fuel1 fuel2 : Nat} (l : List D)
    (h_closes : ∀ d ∈ l, orbitClosesWithin p d d fuel1)
    (h_le : fuel1 ≤ fuel2) :
    countOrbits p fuel2 l = countOrbits p fuel1 l :=
  countOrbitsAux_fuel_eq_of_closes p l.length l h_closes h_le

/-- Symmetry of `countOrbitsAux` under `p.symm`:
    when all darts in `l` have orbits closing within `fuel`, `p.symm` and `p` have the exact same orbit count. -/
theorem countOrbitsAux_symm_perm (p : Perm D) (fuel steps : Nat) (l : List D)
    (h_closes : ∀ d ∈ l, orbitClosesWithin p d d fuel) :
    countOrbitsAux p.symm fuel steps l = countOrbitsAux p fuel steps l := by
  induction steps generalizing l with
  | zero => rfl
  | succ steps ih =>
    cases l with
    | nil => rfl
    | cons d ds =>
      dsimp [countOrbitsAux]
      have hd_closes : orbitClosesWithin p d d fuel := h_closes d (List.Mem.head ds)
      have h_pred : (fun x => !((getOrbit p.symm fuel d).contains x)) =
          (fun x => !((getOrbit p fuel d).contains x)) := by
        funext x
        rw [getOrbit_symm_contains_eq p fuel d x hd_closes]
      rw [h_pred]
      congr 1
      apply ih
      intro x hx
      have hx_ds : x ∈ ds := (List.mem_filter.mp hx).1
      exact h_closes x (List.Mem.tail d hx_ds)

/-- Symmetry of `countOrbits` under `p.symm`:
    when all darts in `l` have orbits closing within `fuel`, `countOrbits p.symm fuel l = countOrbits p fuel l`. -/
theorem countOrbits_symm_perm (p : Perm D) (fuel : Nat) (l : List D)
    (h_closes : ∀ d ∈ l, orbitClosesWithin p d d fuel) :
    countOrbits p.symm fuel l = countOrbits p fuel l :=
  countOrbitsAux_symm_perm p fuel l.length l h_closes

/-!
### Finite Pigeonhole Principle and Automatic Orbit Closure on Complete Dart Lists
-/

/-- Finite Pigeonhole Lemma on lists: any duplicate-free list `l` whose elements all belong
    to `darts` has `l.length ≤ darts.length`. -/
theorem nodup_length_le_of_subset (l darts : List D)
    (hl : l.Nodup) (h_sub : ∀ x ∈ l, x ∈ darts) :
    l.length ≤ darts.length := by
  induction l generalizing darts with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    have hx_mem : x ∈ darts := h_sub x (List.Mem.head xs)
    have h_not_mem : x ∉ xs := (List.nodup_cons.mp hl).1
    have h_xs_nodup : xs.Nodup := (List.nodup_cons.mp hl).2
    have h_sub_erase : ∀ y ∈ xs, y ∈ darts.erase x := by
      intro y hy
      have hy_ne : y ≠ x := fun h_eq => h_not_mem (h_eq ▸ hy)
      exact List.mem_erase_of_ne hy_ne |>.mpr (h_sub y (List.Mem.tail x hy))
    have h_ih := ih (darts.erase x) h_xs_nodup h_sub_erase
    have h_erase_len := List.length_erase_of_mem hx_mem
    have h_pos : darts.length > 0 := List.length_pos_of_mem hx_mem
    dsimp
    omega

/-- List of the first `n` iterates `[d, p(d), p^2(d), ..., p^(n-1)(d)]`. -/
def iterList (p : Perm D) (d : D) : Nat → List D
  | 0 => []
  | n + 1 => d :: iterList p (p.f d) n

theorem iterList_length (p : Perm D) (d : D) (n : Nat) :
    (iterList p d n).length = n := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    dsimp [iterList]
    rw [ih (p.f d)]

theorem mem_iterList_imp_exists_iter (p : Perm D) (d : D) (n : Nat) (x : D)
    (hx : x ∈ iterList p d n) :
    ∃ k < n, x = Perm.iter p k d := by
  induction n generalizing d with
  | zero => contradiction
  | succ n ih =>
    dsimp [iterList] at hx
    rcases List.mem_cons.mp hx with rfl | hx_tail
    · exact ⟨0, Nat.zero_lt_succ n, rfl⟩
    · rcases ih (p.f d) hx_tail with ⟨k, hk, rfl⟩
      refine ⟨k + 1, Nat.succ_lt_succ hk, ?_⟩
      exact (Perm.iter_succ_right p k d).symm

/-- If `p.f d`'s orbit closes within `fuel` steps, then `d`'s orbit also closes within `fuel` steps. -/
theorem orbitClosesWithin_of_step (p : Perm D) (d : D) (fuel : Nat)
    (h_step : orbitClosesWithin p (p.f d) (p.f d) fuel) :
    orbitClosesWithin p d d fuel := by
  rcases (orbitClosesWithin_iff_exists_iter p (p.f d) (p.f d) fuel).mp h_step with ⟨k, hk, h_per⟩
  apply (orbitClosesWithin_iff_exists_iter p d d fuel).mpr
  refine ⟨k, hk, ?_⟩
  rw [← Perm.iter_succ_right p (k + 1) d] at h_per
  dsimp [Perm.iter] at h_per
  have h_inv := congrArg p.inv h_per
  rw [p.left_inv, p.left_inv] at h_inv
  exact h_inv

/-- If `d`'s orbit does not close within `n` steps, then the first `n + 1` iterates in `iterList`
    are pairwise distinct (`Nodup`). -/
theorem iterList_nodup_of_not_closes (p : Perm D) (d : D) (n : Nat)
    (h_not : ¬ orbitClosesWithin p d d n) :
    (iterList p d (n + 1)).Nodup := by
  induction n generalizing d with
  | zero =>
    dsimp [iterList]
    simp [List.Nodup]
  | succ m ih =>
    change (d :: iterList p (p.f d) (m + 1)).Nodup
    apply List.nodup_cons.mpr
    constructor
    · intro hd_mem
      rcases mem_iterList_imp_exists_iter p (p.f d) (m + 1) d hd_mem with ⟨k, hk, h_eq⟩
      rw [← Perm.iter_succ_right p k d] at h_eq
      have h_closes : orbitClosesWithin p d d (m + 1) :=
        (orbitClosesWithin_iff_exists_iter p d d (m + 1)).mpr ⟨k, hk, h_eq.symm⟩
      exact h_not h_closes
    · apply ih (p.f d)
      intro h_step
      have h_d_m : orbitClosesWithin p d d m := orbitClosesWithin_of_step p d m h_step
      exact h_not (orbitClosesWithin_mono p d d h_d_m (Nat.le_succ m))

/-- Pigeonhole Orbit Closure Theorem:
    If `darts` contains every element of `D`, then for every permutation `p : Perm D`
    and every `d : D`, the orbit of `d` under `p` closes within `darts.length` steps. -/
theorem orbitClosesWithin_of_complete (p : Perm D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) (d : D) :
    orbitClosesWithin p d d darts.length := by
  by_cases h_closes : orbitClosesWithin p d d darts.length
  · exact h_closes
  · exfalso
    have h_nodup := iterList_nodup_of_not_closes p d darts.length h_closes
    have h_sub : ∀ x ∈ iterList p d (darts.length + 1), x ∈ darts := fun x _ => h_all x
    have h_le := nodup_length_le_of_subset (iterList p d (darts.length + 1)) darts h_nodup h_sub
    rw [iterList_length] at h_le
    omega

/-- Unconditional fuel-independence of `getOrbit` on any complete dart list:
    for all `fuel ≥ darts.length`, `getOrbit p fuel d = getOrbit p darts.length d`. -/
theorem getOrbit_fuel_eq_of_complete (p : Perm D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) (d : D) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    getOrbit p fuel d = getOrbit p darts.length d :=
  getOrbit_fuel_eq_of_closes p d (orbitClosesWithin_of_complete p darts h_all d) h_le

/-- Unconditional fuel-independence of `countOrbits` on any complete dart list:
    for all `fuel ≥ darts.length`, `countOrbits p fuel l = countOrbits p darts.length l`. -/
theorem countOrbits_fuel_eq_of_complete (p : Perm D) (darts l : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    countOrbits p fuel l = countOrbits p darts.length l := by
  apply countOrbits_fuel_eq_of_closes p l ?_ h_le
  intro d _
  exact orbitClosesWithin_of_complete p darts h_all d

/-- Unconditional `p.symm` invariance of `countOrbits` on any complete dart list:
    for all `fuel ≥ darts.length`, `countOrbits p.symm fuel l = countOrbits p fuel l`. -/
theorem countOrbits_symm_of_complete (p : Perm D) (darts l : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    countOrbits p.symm fuel l = countOrbits p fuel l := by
  apply countOrbits_symm_perm p fuel l
  intro d _
  exact orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le

/-- Double dual of a hypermap is the original hypermap: `H.dual.dual = H`. -/
theorem dual_dual (H : Hypermap) : H.dual.dual = H := by
  cases H
  rfl

/-!
### Stage B.1: Orbit Equivalence, Duplicate-Freeness (`Nodup`), and Orbit Partition Counting
-/

/-- Exact equivalence of `getOrbit` membership for any two darts in the same closed orbit:
    if `d1`'s orbit closes within `fuel` steps and `d2 ∈ getOrbit p fuel d1`,
    then `x ∈ getOrbit p fuel d2 ↔ x ∈ getOrbit p fuel d1`. -/
theorem mem_getOrbit_iff_of_mem (p : Perm D) (fuel : Nat) {d1 d2 : D}
    (h_closes : orbitClosesWithin p d1 d1 fuel) (h12 : d2 ∈ getOrbit p fuel d1) (x : D) :
    x ∈ getOrbit p fuel d2 ↔ x ∈ getOrbit p fuel d1 := by
  have h_closes2 := orbitClosesWithin_of_mem_getOrbit p fuel h_closes h12
  have h21 := mem_getOrbit_symm p fuel h_closes h12
  constructor
  · intro hx
    exact mem_getOrbit_trans p fuel h_closes h12 hx
  · intro hx
    exact mem_getOrbit_trans p fuel h_closes2 h21 hx

/-- Boolean `.contains` equality for `getOrbit` of two darts in the same closed orbit. -/
theorem getOrbit_contains_eq_of_mem (p : Perm D) (fuel : Nat) {d1 d2 : D}
    (h_closes : orbitClosesWithin p d1 d1 fuel) (h12 : d2 ∈ getOrbit p fuel d1) (x : D) :
    (getOrbit p fuel d2).contains x = (getOrbit p fuel d1).contains x := by
  by_cases hx : x ∈ getOrbit p fuel d1
  · have hx2 : x ∈ getOrbit p fuel d2 := (mem_getOrbit_iff_of_mem p fuel h_closes h12 x).mpr hx
    rw [List.contains_iff_mem.mpr hx, List.contains_iff_mem.mpr hx2]
  · have hx2 : x ∉ getOrbit p fuel d2 :=
      fun h => hx ((mem_getOrbit_iff_of_mem p fuel h_closes h12 x).mp h)
    cases h1 : (getOrbit p fuel d2).contains x with
    | true => exact False.elim (hx2 (List.contains_iff_mem.mp h1))
    | false =>
      cases h2 : (getOrbit p fuel d1).contains x with
      | true => exact False.elim (hx (List.contains_iff_mem.mp h2))
      | false => rfl

/-- Auxiliary duplicate-freeness invariant for `getOrbitAux`:
    if `(current :: acc).Nodup` and every element `y ∈ current :: acc` other than `start`
    has a `p.f`-predecessor in `acc`, then `(getOrbitAux p start current acc fuel).Nodup`. -/
theorem getOrbitAux_nodup (p : Perm D) (start current : D) (acc : List D) (fuel : Nat)
    (h_nodup : (current :: acc).Nodup)
    (h_pred : ∀ y ∈ current :: acc, y ≠ start → ∃ x ∈ acc, p.f x = y) :
    (getOrbitAux p start current acc fuel).Nodup := by
  induction fuel generalizing current acc with
  | zero =>
    dsimp [getOrbitAux]
    exact h_nodup
  | succ fuel ih =>
    dsimp [getOrbitAux]
    by_cases h_hit : p.f current = start
    · have hbeq : (p.f current == start) = true := by
        change (if p.f current = start then true else false) = true
        rw [h_hit]; simp
      rw [hbeq]
      exact h_nodup
    · have hbeq : (p.f current == start) = false := by
        change (if p.f current = start then true else false) = false
        rw [if_neg h_hit]
      rw [hbeq]
      dsimp
      have h_not_in : p.f current ∉ current :: acc := by
        intro h_in
        rcases h_pred (p.f current) h_in h_hit with ⟨x, hx_acc, hx_eq⟩
        have h_x_eq : x = current := by
          have h_inv := congrArg p.inv hx_eq
          rw [p.left_inv, p.left_inv] at h_inv
          exact h_inv
        subst h_x_eq
        exact (List.nodup_cons.mp h_nodup).1 hx_acc
      apply ih (p.f current) (current :: acc)
      · exact List.nodup_cons.mpr ⟨h_not_in, h_nodup⟩
      · intro y hy_mem hy_ne
        rcases List.mem_cons.mp hy_mem with rfl | hy_tail
        · exact ⟨current, List.Mem.head acc, rfl⟩
        · rcases h_pred y hy_tail hy_ne with ⟨x, hx_acc, hx_eq⟩
          exact ⟨x, List.Mem.tail current hx_acc, hx_eq⟩

/-- Every orbit list `getOrbit p fuel d` is unconditionally duplicate-free (`Nodup`). -/
theorem getOrbit_nodup (p : Perm D) (fuel : Nat) (d : D) :
    (getOrbit p fuel d).Nodup := by
  apply getOrbitAux_nodup p d d [] fuel
  · simp [List.Nodup]
  · intro y hy hy_ne
    rcases List.mem_cons.mp hy with rfl | h_nil
    · exact False.elim (hy_ne rfl)
    · contradiction

/-- Two duplicate-free lists with identical membership have the exact same length. -/
theorem nodup_length_eq_of_iff_mem {l1 l2 : List D}
    (hl1 : l1.Nodup) (hl2 : l2.Nodup) (h_iff : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    l1.length = l2.length := by
  have h12 := nodup_length_le_of_subset l1 l2 hl1 (fun x hx => (h_iff x).mp hx)
  have h21 := nodup_length_le_of_subset l2 l1 hl2 (fun x hx => (h_iff x).mpr hx)
  omega

/-- Any two darts in the same closed orbit have `getOrbit` lists of identical length. -/
theorem getOrbit_length_eq_of_mem (p : Perm D) (fuel : Nat) {d1 d2 : D}
    (h_closes : orbitClosesWithin p d1 d1 fuel) (h12 : d2 ∈ getOrbit p fuel d1) :
    (getOrbit p fuel d2).length = (getOrbit p fuel d1).length :=
  nodup_length_eq_of_iff_mem (getOrbit_nodup p fuel d2) (getOrbit_nodup p fuel d1)
    (mem_getOrbit_iff_of_mem p fuel h_closes h12)

/-- For any closed orbit, `getOrbit p.symm fuel d` and `getOrbit p fuel d` have identical length. -/
theorem getOrbit_symm_length_eq (p : Perm D) (fuel : Nat) (d : D)
    (h_closes : orbitClosesWithin p d d fuel) :
    (getOrbit p.symm fuel d).length = (getOrbit p fuel d).length :=
  nodup_length_eq_of_iff_mem (getOrbit_nodup p.symm fuel d) (getOrbit_nodup p fuel d)
    (mem_getOrbit_symm_perm_iff p fuel d · h_closes)

/-- Filtering a list by a Boolean predicate `P` and its negation `!P` partitions its length. -/
theorem length_eq_filter_add_filter_not (P : D → Bool) (l : List D) :
    l.length = (l.filter P).length + (l.filter (fun x => !(P x))).length := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    dsimp [List.filter]
    cases hP : P d <;> simp <;> omega

/-- Filtering a duplicate-free list preserves `Nodup`. -/
theorem nodup_filter (P : D → Bool) {l : List D} (hl : l.Nodup) :
    (l.filter P).Nodup := by
  induction l with
  | nil => exact hl
  | cons d ds ih =>
    have hd_not : d ∉ ds := (List.nodup_cons.mp hl).1
    have hds_nodup : ds.Nodup := (List.nodup_cons.mp hl).2
    dsimp [List.filter]
    cases hP : P d
    · dsimp
      exact ih hds_nodup
    · dsimp
      apply List.nodup_cons.mpr
      refine ⟨?_, ih hds_nodup⟩
      intro h_mem
      exact hd_not (List.mem_filter.mp h_mem).1

/-- When `l.Nodup`, `orb.Nodup`, and `orb ⊆ l`, filtering out `orb` reduces `l.length` by `orb.length`. -/
theorem length_eq_orb_add_filter_not_contains {l orb : List D}
    (hl : l.Nodup) (horb : orb.Nodup) (h_sub : ∀ x ∈ orb, x ∈ l) :
    l.length = orb.length + (l.filter (fun x => !(orb.contains x))).length := by
  have h_part := length_eq_filter_add_filter_not (fun x => orb.contains x) l
  have h_eq_orb : (l.filter (fun x => orb.contains x)).length = orb.length := by
    apply nodup_length_eq_of_iff_mem (nodup_filter _ hl) horb
    intro x
    rw [List.mem_filter, List.contains_iff_mem]
    constructor
    · exact fun h => h.2
    · exact fun hx => ⟨h_sub x hx, hx⟩
  omega

/-- Auxiliary theorem for uniform orbit lengths:
    if `l.Nodup`, `l.length ≤ steps`, every `d ∈ l` has a closed orbit of length `k` contained in `l`,
    then `l.length = k * countOrbitsAux p fuel steps l`. -/
theorem length_eq_mul_countOrbitsAux_of_uniform (p : Perm D) (fuel k steps : Nat) (l : List D)
    (h_steps : l.length ≤ steps)
    (hl_nodup : l.Nodup)
    (h_closes : ∀ d ∈ l, orbitClosesWithin p d d fuel)
    (h_sub : ∀ d ∈ l, ∀ x ∈ getOrbit p fuel d, x ∈ l)
    (h_unif : ∀ d ∈ l, (getOrbit p fuel d).length = k) :
    l.length = k * countOrbitsAux p fuel steps l := by
  induction steps generalizing l with
  | zero =>
    cases l with
    | nil =>
      rfl
    | cons d ds =>
      dsimp at h_steps
      omega
  | succ steps ih =>
    cases l with
    | nil =>
      rfl
    | cons d ds =>
      dsimp [countOrbitsAux]
      have hd_mem : d ∈ d :: ds := List.Mem.head ds
      have hd_closes : orbitClosesWithin p d d fuel := h_closes d hd_mem
      have hd_len : (getOrbit p fuel d).length = k := h_unif d hd_mem
      have hd_sub : ∀ x ∈ getOrbit p fuel d, x ∈ d :: ds := h_sub d hd_mem
      have h_part := length_eq_orb_add_filter_not_contains hl_nodup (getOrbit_nodup p fuel d) hd_sub
      have hd_in_orb : (getOrbit p fuel d).contains d = true :=
        List.contains_iff_mem.mpr (mem_getOrbit_self p fuel d)
      have h_filter_cons :
          (d :: ds).filter (fun x => !((getOrbit p fuel d).contains x)) =
            ds.filter (fun x => !((getOrbit p fuel d).contains x)) := by
        dsimp [List.filter]
        rw [hd_in_orb]
        rfl
      rw [h_filter_cons] at h_part
      let rest := ds.filter (fun x => !((getOrbit p fuel d).contains x))
      have h_rest_steps : rest.length ≤ steps := by
        have h_pos : (getOrbit p fuel d).length ≥ 1 :=
          List.length_pos_of_mem (mem_getOrbit_self p fuel d)
        dsimp [rest]
        dsimp at h_steps h_part
        omega
      have h_rest_nodup : rest.Nodup :=
        nodup_filter _ (List.nodup_cons.mp hl_nodup).2
      have h_rest_closes : ∀ y ∈ rest, orbitClosesWithin p y y fuel := by
        intro y hy
        exact h_closes y (List.Mem.tail d (List.mem_filter.mp hy).1)
      have h_rest_sub : ∀ y ∈ rest, ∀ x ∈ getOrbit p fuel y, x ∈ rest := by
        intro y hy x hx
        have hy_ds : y ∈ ds := (List.mem_filter.mp hy).1
        have hy_not_orb := (List.mem_filter.mp hy).2
        have hx_in_all : x ∈ d :: ds := h_sub y (List.Mem.tail d hy_ds) x hx
        have hx_not_in_orb : x ∉ getOrbit p fuel d := by
          intro hx_orb
          have hy_orb : y ∈ getOrbit p fuel d := by
            have hy_in_x : y ∈ getOrbit p fuel x :=
              mem_getOrbit_symm p fuel (h_closes y (List.Mem.tail d hy_ds)) hx
            exact mem_getOrbit_trans p fuel hd_closes hx_orb hy_in_x
          have h_true : (getOrbit p fuel d).contains y = true :=
            List.contains_iff_mem.mpr hy_orb
          rw [h_true] at hy_not_orb
          contradiction
        have hx_ne_d : x ≠ d := by
          intro h_eq
          subst h_eq
          exact hx_not_in_orb (mem_getOrbit_self p fuel x)
        have hx_ds : x ∈ ds := by
          rcases List.mem_cons.mp hx_in_all with rfl | hx_tail
          · exact False.elim (hx_ne_d rfl)
          · exact hx_tail
        apply List.mem_filter.mpr
        refine ⟨hx_ds, ?_⟩
        cases h_c : (getOrbit p fuel d).contains x with
        | false => rfl
        | true => exact False.elim (hx_not_in_orb (List.contains_iff_mem.mp h_c))
      have h_rest_unif : ∀ y ∈ rest, (getOrbit p fuel y).length = k := by
        intro y hy
        exact h_unif y (List.Mem.tail d (List.mem_filter.mp hy).1)
      have h_ih := ih rest h_rest_steps h_rest_nodup h_rest_closes h_rest_sub h_rest_unif
      rw [hd_len] at h_part
      change (d :: ds).length = k + rest.length at h_part
      rw [h_ih] at h_part
      rw [Nat.mul_add, Nat.mul_one]
      dsimp at h_part
      omega

/-- Uniform Orbit Length Theorem:
    if `l.Nodup` and every `d ∈ l` has a closed orbit of length `k` contained in `l`,
    then `l.length = k * countOrbits p fuel l`. -/
theorem length_eq_mul_countOrbits_of_uniform (p : Perm D) (fuel k : Nat) (l : List D)
    (hl_nodup : l.Nodup)
    (h_closes : ∀ d ∈ l, orbitClosesWithin p d d fuel)
    (h_sub : ∀ d ∈ l, ∀ x ∈ getOrbit p fuel d, x ∈ l)
    (h_unif : ∀ d ∈ l, (getOrbit p fuel d).length = k) :
    l.length = k * countOrbits p fuel l :=
  length_eq_mul_countOrbitsAux_of_uniform p fuel k l.length l
    (Nat.le_refl _) hl_nodup h_closes h_sub h_unif

/-- Special case of `length_eq_mul_countOrbits_of_uniform` on a complete dart list (`darts.Nodup` and `∀ d, d ∈ darts`):
    if every dart `d ∈ darts` has `(getOrbit p fuel d).length = k` for `fuel ≥ darts.length`,
    then `darts.length = k * countOrbits p fuel darts`. -/
theorem length_eq_mul_countOrbits_of_complete (p : Perm D) (darts : List D) (k : Nat)
    (h_nodup : darts.Nodup) (h_all : ∀ x : D, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_unif : ∀ d ∈ darts, (getOrbit p fuel d).length = k) :
    darts.length = k * countOrbits p fuel darts := by
  apply length_eq_mul_countOrbits_of_uniform p fuel k darts h_nodup
  · intro d _
    exact orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le
  · intro d _ x _
    exact h_all x
  · exact h_unif

/-- For any involution `p` (`∀ x, p.f (p.f x) = x`) and any non-fixed point `d` (`p.f d ≠ d`),
    `getOrbit p fuel d = [p.f d, d]` for all `fuel ≥ 1`. -/
theorem getOrbit_involution_of_ne (p : Perm D) (he : ∀ x, p.f (p.f x) = x) (d : D)
    (hne : p.f d ≠ d) {fuel : Nat} (h_pos : 1 ≤ fuel) :
    getOrbit p fuel d = [p.f d, d] := by
  cases fuel with
  | zero => omega
  | succ f =>
    dsimp [getOrbit, getOrbitAux]
    have hbeq1 : (p.f d == d) = false := by
      change (if p.f d = d then true else false) = false
      rw [if_neg hne]
    rw [hbeq1]
    dsimp
    cases f with
    | zero => rfl
    | succ f' =>
      dsimp [getOrbitAux]
      have hbeq2 : (p.f (p.f d) == d) = true := by
        change (if p.f (p.f d) = d then true else false) = true
        rw [he d]
        simp
      rw [hbeq2]
      rfl

/-- For any involution `p` and any non-fixed point `d` (`p.f d ≠ d`),
    `(getOrbit p fuel d).length = 2` for all `fuel ≥ 1`. -/
theorem getOrbit_involution_length_two (p : Perm D) (he : ∀ x, p.f (p.f x) = x) (d : D)
    (hne : p.f d ≠ d) {fuel : Nat} (h_pos : 1 ≤ fuel) :
    (getOrbit p fuel d).length = 2 := by
  rw [getOrbit_involution_of_ne p he d hne h_pos]
  rfl

/-- For any fixed-point-free involution `p` on a complete dart list `darts`,
    `darts.length = 2 * countOrbits p fuel darts` for all `fuel ≥ darts.length`. -/
theorem length_eq_two_mul_countOrbits_of_involution (p : Perm D) (he : ∀ x, p.f (p.f x) = x)
    (darts : List D) (h_nodup : darts.Nodup) (h_all : ∀ x : D, x ∈ darts)
    (h_free : ∀ d ∈ darts, p.f d ≠ d) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    darts.length = 2 * countOrbits p fuel darts := by
  cases h_darts : darts with
  | nil =>
    rfl
  | cons d0 ds =>
    subst h_darts
    have h_pos : 1 ≤ fuel := by
      dsimp at h_le
      omega
    apply length_eq_mul_countOrbits_of_complete p (d0 :: ds) 2 h_nodup h_all h_le
    intro d hd
    exact getOrbit_involution_length_two p he d (h_free d hd) h_pos

/-- Canonical list of orbit representatives extracted in the same order as `countOrbitsAux`. -/
def canonicalOrbitsAux (p : Perm D) (fuel : Nat) : Nat → List D → List D
  | 0, _ => []
  | _ + 1, [] => []
  | steps + 1, d :: ds =>
    let orb := getOrbit p fuel d
    d :: canonicalOrbitsAux p fuel steps (ds.filter (fun x => !(orb.contains x)))

/-- Canonical list of orbit representatives for `l`. -/
def canonicalOrbits (p : Perm D) (fuel : Nat) (l : List D) : List D :=
  canonicalOrbitsAux p fuel l.length l

/-- The length of `canonicalOrbitsAux` is identically `countOrbitsAux`. -/
theorem canonicalOrbitsAux_length (p : Perm D) (fuel steps : Nat) (l : List D) :
    (canonicalOrbitsAux p fuel steps l).length = countOrbitsAux p fuel steps l := by
  induction steps generalizing l with
  | zero => rfl
  | succ steps ih =>
    cases l with
    | nil => rfl
    | cons d ds =>
      dsimp [canonicalOrbitsAux, countOrbitsAux]
      rw [ih]
      omega

/-- The length of `canonicalOrbits` is identically `countOrbits`. -/
theorem canonicalOrbits_length (p : Perm D) (fuel : Nat) (l : List D) :
    (canonicalOrbits p fuel l).length = countOrbits p fuel l :=
  canonicalOrbitsAux_length p fuel l.length l

/-- Sum of `(getOrbit p fuel v).length` over a list of representatives `vs`. -/
def sumOrbitLengths (p : Perm D) (fuel : Nat) : List D → Nat
  | [] => 0
  | v :: vs => (getOrbit p fuel v).length + sumOrbitLengths p fuel vs

theorem sumOrbitLengths_append (p : Perm D) (fuel : Nat) (l1 l2 : List D) :
    sumOrbitLengths p fuel (l1 ++ l2) = sumOrbitLengths p fuel l1 + sumOrbitLengths p fuel l2 := by
  induction l1 with
  | nil =>
    dsimp [sumOrbitLengths]
    omega
  | cons v vs ih =>
    dsimp [sumOrbitLengths]
    rw [ih]
    omega

theorem sumOrbitLengths_reverse (p : Perm D) (fuel : Nat) (l : List D) :
    sumOrbitLengths p fuel l.reverse = sumOrbitLengths p fuel l := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    rw [List.reverse_cons, sumOrbitLengths_append]
    dsimp [sumOrbitLengths]
    rw [ih]
    omega

/-- Handshaking / Orbit Partition Sum Theorem for `canonicalOrbitsAux`:
    if `l.Nodup`, `l.length ≤ steps`, and every `d ∈ l` has a closed orbit contained in `l`,
    then summing `(getOrbit p fuel v).length` over `canonicalOrbitsAux p fuel steps l` equals `l.length`. -/
theorem sumOrbitLengths_canonicalOrbitsAux_eq_length (p : Perm D) (fuel steps : Nat) (l : List D)
    (h_steps : l.length ≤ steps)
    (hl_nodup : l.Nodup)
    (h_closes : ∀ d ∈ l, orbitClosesWithin p d d fuel)
    (h_sub : ∀ d ∈ l, ∀ x ∈ getOrbit p fuel d, x ∈ l) :
    sumOrbitLengths p fuel (canonicalOrbitsAux p fuel steps l) = l.length := by
  induction steps generalizing l with
  | zero =>
    cases l with
    | nil => rfl
    | cons d ds =>
      dsimp at h_steps
      omega
  | succ steps ih =>
    cases l with
    | nil => rfl
    | cons d ds =>
      dsimp [canonicalOrbitsAux, sumOrbitLengths]
      have hd_mem : d ∈ d :: ds := List.Mem.head ds
      have hd_closes : orbitClosesWithin p d d fuel := h_closes d hd_mem
      have hd_sub : ∀ x ∈ getOrbit p fuel d, x ∈ d :: ds := h_sub d hd_mem
      have h_part := length_eq_orb_add_filter_not_contains hl_nodup (getOrbit_nodup p fuel d) hd_sub
      have hd_in_orb : (getOrbit p fuel d).contains d = true :=
        List.contains_iff_mem.mpr (mem_getOrbit_self p fuel d)
      have h_filter_cons :
          (d :: ds).filter (fun x => !((getOrbit p fuel d).contains x)) =
            ds.filter (fun x => !((getOrbit p fuel d).contains x)) := by
        dsimp [List.filter]
        rw [hd_in_orb]
        rfl
      rw [h_filter_cons] at h_part
      let rest := ds.filter (fun x => !((getOrbit p fuel d).contains x))
      have h_rest_steps : rest.length ≤ steps := by
        have h_pos : (getOrbit p fuel d).length ≥ 1 :=
          List.length_pos_of_mem (mem_getOrbit_self p fuel d)
        dsimp [rest]
        dsimp at h_steps h_part
        omega
      have h_rest_nodup : rest.Nodup :=
        nodup_filter _ (List.nodup_cons.mp hl_nodup).2
      have h_rest_closes : ∀ y ∈ rest, orbitClosesWithin p y y fuel := by
        intro y hy
        exact h_closes y (List.Mem.tail d (List.mem_filter.mp hy).1)
      have h_rest_sub : ∀ y ∈ rest, ∀ x ∈ getOrbit p fuel y, x ∈ rest := by
        intro y hy x hx
        have hy_ds : y ∈ ds := (List.mem_filter.mp hy).1
        have hy_not_orb := (List.mem_filter.mp hy).2
        have hx_in_all : x ∈ d :: ds := h_sub y (List.Mem.tail d hy_ds) x hx
        have hx_not_in_orb : x ∉ getOrbit p fuel d := by
          intro hx_orb
          have hy_orb : y ∈ getOrbit p fuel d := by
            have hy_in_x : y ∈ getOrbit p fuel x :=
              mem_getOrbit_symm p fuel (h_closes y (List.Mem.tail d hy_ds)) hx
            exact mem_getOrbit_trans p fuel hd_closes hx_orb hy_in_x
          have h_true : (getOrbit p fuel d).contains y = true :=
            List.contains_iff_mem.mpr hy_orb
          rw [h_true] at hy_not_orb
          contradiction
        have hx_ne_d : x ≠ d := by
          intro h_eq
          subst h_eq
          exact hx_not_in_orb (mem_getOrbit_self p fuel x)
        have hx_ds : x ∈ ds := by
          rcases List.mem_cons.mp hx_in_all with rfl | hx_tail
          · exact False.elim (hx_ne_d rfl)
          · exact hx_tail
        apply List.mem_filter.mpr
        refine ⟨hx_ds, ?_⟩
        cases h_c : (getOrbit p fuel d).contains x with
        | false => rfl
        | true => exact False.elim (hx_not_in_orb (List.contains_iff_mem.mp h_c))
      have h_ih := ih rest h_rest_steps h_rest_nodup h_rest_closes h_rest_sub
      change (d :: ds).length = (getOrbit p fuel d).length + rest.length at h_part
      rw [← h_ih] at h_part
      exact h_part.symm

/-- Handshaking / Orbit Partition Sum Theorem for `canonicalOrbits`:
    if `l.Nodup` and every `d ∈ l` has a closed orbit contained in `l`,
    then `sumOrbitLengths p fuel (canonicalOrbits p fuel l) = l.length`. -/
theorem sumOrbitLengths_canonicalOrbits_eq_length (p : Perm D) (fuel : Nat) (l : List D)
    (hl_nodup : l.Nodup)
    (h_closes : ∀ d ∈ l, orbitClosesWithin p d d fuel)
    (h_sub : ∀ d ∈ l, ∀ x ∈ getOrbit p fuel d, x ∈ l) :
    sumOrbitLengths p fuel (canonicalOrbits p fuel l) = l.length :=
  sumOrbitLengths_canonicalOrbitsAux_eq_length p fuel l.length l
    (Nat.le_refl _) hl_nodup h_closes h_sub

/-- Handshaking / Orbit Partition Sum Theorem on a complete dart list (`darts.Nodup` and `∀ x, x ∈ darts`):
    for all `fuel ≥ darts.length`, `sumOrbitLengths p fuel (canonicalOrbits p fuel darts) = darts.length`. -/
theorem sumOrbitLengths_canonicalOrbits_of_complete (p : Perm D) (darts : List D)
    (h_nodup : darts.Nodup) (h_all : ∀ x : D, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    sumOrbitLengths p fuel (canonicalOrbits p fuel darts) = darts.length := by
  apply sumOrbitLengths_canonicalOrbits_eq_length p fuel darts h_nodup
  · intro d _
    exact orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le
  · intro d _ x _
    exact h_all x

theorem filter_length_le (P : D → Bool) (l : List D) :
    (l.filter P).length ≤ l.length := by
  have h := length_eq_filter_add_filter_not P l
  omega

/-- Once `steps ≥ l.length`, `canonicalOrbitsAux p fuel steps l` is independent of `steps`. -/
theorem canonicalOrbitsAux_steps_eq (p : Perm D) (fuel : Nat) {steps1 steps2 : Nat} (l : List D)
    (h1 : l.length ≤ steps1) (h2 : l.length ≤ steps2) :
    canonicalOrbitsAux p fuel steps1 l = canonicalOrbitsAux p fuel steps2 l := by
  induction steps1 generalizing steps2 l with
  | zero =>
    cases l with
    | nil =>
      cases steps2 <;> rfl
    | cons d ds =>
      dsimp at h1
      omega
  | succ s1 ih =>
    cases l with
    | nil =>
      cases steps2 <;> rfl
    | cons d ds =>
      cases steps2 with
      | zero =>
        dsimp at h2
        omega
      | succ s2 =>
        dsimp [canonicalOrbitsAux]
        congr 1
        have h_flt : (ds.filter (fun x => !((getOrbit p fuel d).contains x))).length ≤ ds.length :=
          filter_length_le _ ds
        dsimp at h1 h2
        exact ih _ (by omega) (by omega)

/-- Step equation for `canonicalOrbits` on `d :: ds`. -/
theorem canonicalOrbits_cons (p : Perm D) (fuel : Nat) (d : D) (ds : List D) :
    canonicalOrbits p fuel (d :: ds) =
      d :: canonicalOrbits p fuel (ds.filter (fun x => !((getOrbit p fuel d).contains x))) := by
  dsimp [canonicalOrbits, canonicalOrbitsAux]
  congr 1
  have h_flt : (ds.filter (fun x => !((getOrbit p fuel d).contains x))).length ≤ ds.length :=
    filter_length_le _ ds
  exact canonicalOrbitsAux_steps_eq p fuel _ h_flt (Nat.le_refl _)

theorem not_contains_append_eq (orb visited : List D) (x : D) :
    (!(orb ++ visited).contains x) = ((!orb.contains x) && (!visited.contains x)) := by
  by_cases h1 : x ∈ orb
  · have hc1 : orb.contains x = true := List.contains_iff_mem.mpr h1
    have hc_app : (orb ++ visited).contains x = true :=
      List.contains_iff_mem.mpr (List.mem_append_left visited h1)
    rw [hc1, hc_app]
    rfl
  · by_cases h2 : x ∈ visited
    · have hc2 : visited.contains x = true := List.contains_iff_mem.mpr h2
      have hc_app : (orb ++ visited).contains x = true :=
        List.contains_iff_mem.mpr (List.mem_append_right orb h2)
      cases hc1 : orb.contains x with
      | true => exact False.elim (h1 (List.contains_iff_mem.mp hc1))
      | false =>
        rw [hc2, hc_app]
        rfl
    · have hc1 : orb.contains x = false := by
        cases h : orb.contains x with
        | false => rfl
        | true => exact False.elim (h1 (List.contains_iff_mem.mp h))
      have hc2 : visited.contains x = false := by
        cases h : visited.contains x with
        | false => rfl
        | true => exact False.elim (h2 (List.contains_iff_mem.mp h))
      have hc_app : (orb ++ visited).contains x = false := by
        cases h : (orb ++ visited).contains x with
        | false => rfl
        | true =>
          rcases List.mem_append.mp (List.contains_iff_mem.mp h) with ha | hb
          · exact False.elim (h1 ha)
          · exact False.elim (h2 hb)
      rw [hc1, hc2, hc_app]
      rfl

theorem filter_not_contains_append (ds orb visited : List D) :
    ds.filter (fun x => !(orb ++ visited).contains x) =
      (ds.filter (fun x => !visited.contains x)).filter (fun x => !orb.contains x) := by
  induction ds with
  | nil => rfl
  | cons a as ih =>
    dsimp [List.filter]
    rw [not_contains_append_eq orb visited a]
    cases hv : visited.contains a <;> cases ho : orb.contains a
    · change a :: as.filter (fun x => !(orb ++ visited).contains x) =
        (a :: as.filter (fun x => !visited.contains x)).filter (fun x => !orb.contains x)
      dsimp [List.filter]
      rw [ho, ih]
      rfl
    · change as.filter (fun x => !(orb ++ visited).contains x) =
        (a :: as.filter (fun x => !visited.contains x)).filter (fun x => !orb.contains x)
      dsimp [List.filter]
      rw [ho]
      exact ih
    · exact ih
    · exact ih

theorem filter_not_contains_nil (l : List D) :
    l.filter (fun x => !([] : List D).contains x) = l := by
  simp

/-!
### Stage C.1: Orbit `.contains` Equivalence Relation & Length Invariance on Complete Dart Lists
-/

/-- Every dart belongs to its own `getOrbit` (boolean `.contains` form). -/
theorem getOrbit_contains_self (p : Perm D) (fuel : Nat) (d : D) :
    (getOrbit p fuel d).contains d = true :=
  List.contains_iff_mem.mpr (mem_getOrbit_self p fuel d)

/-- Symmetry of `(getOrbit p fuel _).contains _` for any two closed orbits. -/
theorem getOrbit_contains_symm (p : Perm D) (fuel : Nat) {d1 d2 : D}
    (h_closes1 : orbitClosesWithin p d1 d1 fuel)
    (h_closes2 : orbitClosesWithin p d2 d2 fuel) :
    (getOrbit p fuel d1).contains d2 = (getOrbit p fuel d2).contains d1 := by
  by_cases h12 : d2 ∈ getOrbit p fuel d1
  · have h21 : d1 ∈ getOrbit p fuel d2 := mem_getOrbit_symm p fuel h_closes1 h12
    rw [List.contains_iff_mem.mpr h12, List.contains_iff_mem.mpr h21]
  · have h21 : d1 ∉ getOrbit p fuel d2 :=
      fun h => h12 (mem_getOrbit_symm p fuel h_closes2 h)
    cases hc1 : (getOrbit p fuel d1).contains d2 with
    | true => exact False.elim (h12 (List.contains_iff_mem.mp hc1))
    | false =>
      cases hc2 : (getOrbit p fuel d2).contains d1 with
      | true => exact False.elim (h21 (List.contains_iff_mem.mp hc2))
      | false => rfl

/-- Unconditional symmetry of `(getOrbit p fuel _).contains _` on a complete dart list (`darts.length ≤ fuel`). -/
theorem getOrbit_contains_symm_of_complete (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : D) :
    (getOrbit p fuel u).contains v = (getOrbit p fuel v).contains u := by
  have hc_u := orbitClosesWithin_mono p u u (orbitClosesWithin_of_complete p darts h_all u) h_le
  have hc_v := orbitClosesWithin_mono p v v (orbitClosesWithin_of_complete p darts h_all v) h_le
  exact getOrbit_contains_symm p fuel hc_u hc_v

/-- Unconditional transitivity of `(getOrbit p fuel _).contains _` on a complete dart list (`darts.length ≤ fuel`). -/
theorem getOrbit_contains_trans_of_complete (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u v w : D}
    (huv : (getOrbit p fuel u).contains v = true)
    (hvw : (getOrbit p fuel v).contains w = true) :
    (getOrbit p fuel u).contains w = true := by
  have hc_u := orbitClosesWithin_mono p u u (orbitClosesWithin_of_complete p darts h_all u) h_le
  have h_mem_uv : v ∈ getOrbit p fuel u := List.contains_iff_mem.mp huv
  rw [← getOrbit_contains_eq_of_mem p fuel hc_u h_mem_uv w]
  exact hvw

/-- Unconditional orbit length invariance for any member `d ∈ getOrbit p fuel u` on a complete dart list. -/
theorem getOrbit_length_eq_of_complete_mem (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d : D}
    (h_mem : d ∈ getOrbit p fuel u) :
    (getOrbit p fuel d).length = (getOrbit p fuel u).length := by
  have hc_u := orbitClosesWithin_mono p u u (orbitClosesWithin_of_complete p darts h_all u) h_le
  exact getOrbit_length_eq_of_mem p fuel hc_u h_mem

/-!
### Stage D.1: Inverse Permutation Orbits & Canonical Orbit Representative Partition
-/

/-- Unconditional `.contains` equality for `getOrbit p.symm` and `getOrbit p` on a complete dart list (`darts.length ≤ fuel`). -/
theorem getOrbit_symm_contains_eq_of_complete (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d x : D) :
    (getOrbit p.symm fuel d).contains x = (getOrbit p fuel d).contains x := by
  have hc := orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le
  exact getOrbit_symm_contains_eq p fuel d x hc

/-- Unconditional orbit length equality for `getOrbit p.symm` and `getOrbit p` on a complete dart list (`darts.length ≤ fuel`). -/
theorem getOrbit_symm_length_eq_of_complete (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d : D) :
    (getOrbit p.symm fuel d).length = (getOrbit p fuel d).length := by
  have hc := orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le
  exact getOrbit_symm_length_eq p fuel d hc

/-- Unconditional `countOrbits` equality for `p.symm` and `p` on a complete dart list (`darts.length ≤ fuel`). -/
theorem countOrbits_symm_perm_of_complete (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l : List D) :
    countOrbits p.symm fuel l = countOrbits p fuel l := by
  apply countOrbits_symm_perm p fuel l
  intro d _
  exact orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le

/-- Every representative in `canonicalOrbitsAux p fuel steps l` is an element of `l`. -/
theorem mem_of_mem_canonicalOrbitsAux (p : Perm D) (fuel steps : Nat) (l : List D) {v : D}
    (hv : v ∈ canonicalOrbitsAux p fuel steps l) : v ∈ l := by
  induction steps generalizing l with
  | zero => cases hv
  | succ steps ih =>
    cases l with
    | nil => cases hv
    | cons d ds =>
      dsimp [canonicalOrbitsAux] at hv
      rcases List.mem_cons.mp hv with rfl | h_tail
      · exact List.Mem.head ds
      · exact List.Mem.tail d (List.mem_filter.mp (ih _ h_tail)).1

/-- Every representative in `canonicalOrbits p fuel l` is an element of `l`. -/
theorem mem_of_mem_canonicalOrbits (p : Perm D) (fuel : Nat) (l : List D) {v : D}
    (hv : v ∈ canonicalOrbits p fuel l) : v ∈ l :=
  mem_of_mem_canonicalOrbitsAux p fuel l.length l hv

/-- `canonicalOrbitsAux p fuel steps l` is always duplicate-free (`Nodup`). -/
theorem canonicalOrbitsAux_nodup (p : Perm D) (fuel steps : Nat) (l : List D) :
    (canonicalOrbitsAux p fuel steps l).Nodup := by
  induction steps generalizing l with
  | zero => exact List.Pairwise.nil
  | succ steps ih =>
    cases l with
    | nil => exact List.Pairwise.nil
    | cons d ds =>
      dsimp [canonicalOrbitsAux]
      refine List.nodup_cons.mpr ⟨?_, ih _⟩
      intro h_in
      have h_flt := mem_of_mem_canonicalOrbitsAux p fuel steps _ h_in
      have h_not_orb := (List.mem_filter.mp h_flt).2
      rw [getOrbit_contains_self p fuel d] at h_not_orb
      contradiction

/-- `canonicalOrbits p fuel l` is always duplicate-free (`Nodup`). -/
theorem canonicalOrbits_nodup (p : Perm D) (fuel : Nat) (l : List D) :
    (canonicalOrbits p fuel l).Nodup :=
  canonicalOrbitsAux_nodup p fuel l.length l

theorem filter_eq_nil_of_forall_false (P : D → Bool) (l : List D)
    (h : ∀ x ∈ l, P x = false) : l.filter P = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [List.filter]
    rw [h x (List.Mem.head xs)]
    exact ih (fun y hy => h y (List.Mem.tail x hy))

/-- On a complete dart list (`darts.length ≤ fuel`), for any `w ∈ l` with `l.length ≤ steps`,
    filtering `canonicalOrbitsAux p fuel steps l` by `(getOrbit p fuel w).contains` yields a singleton `[v₀]`. -/
theorem exists_singleton_filter_canonicalOrbitsAux (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (steps : Nat) (l : List D) (h_steps : l.length ≤ steps)
    (w : D) (hw : w ∈ l) :
    ∃ v₀ : D,
      (canonicalOrbitsAux p fuel steps l).filter (fun v => (getOrbit p fuel w).contains v) = [v₀] := by
  induction steps generalizing l with
  | zero =>
    cases l with
    | nil => cases hw
    | cons d ds =>
      dsimp at h_steps
      omega
  | succ steps ih =>
    cases l with
    | nil => cases hw
    | cons d ds =>
      dsimp [canonicalOrbitsAux, List.filter]
      cases hc : (getOrbit p fuel w).contains d with
      | true =>
        refine ⟨d, ?_⟩
        dsimp
        congr 1
        apply filter_eq_nil_of_forall_false
        intro v hv
        have hv_flt := mem_of_mem_canonicalOrbitsAux p fuel steps _ hv
        have hv_not_d := (List.mem_filter.mp hv_flt).2
        cases h_wv : (getOrbit p fuel w).contains v with
        | false => rfl
        | true =>
          have h_dw : (getOrbit p fuel d).contains w = true := by
            rw [getOrbit_contains_symm_of_complete p darts h_all h_le d w]
            exact hc
          have h_dv : (getOrbit p fuel d).contains v = true :=
            getOrbit_contains_trans_of_complete p darts h_all h_le h_dw h_wv
          rw [h_dv] at hv_not_d
          contradiction
      | false =>
        dsimp
        have h_flt_len : (ds.filter (fun x => !((getOrbit p fuel d).contains x))).length ≤ steps := by
          have h1 := filter_length_le (fun x => !((getOrbit p fuel d).contains x)) ds
          dsimp at h_steps
          omega
        have hw_flt : w ∈ ds.filter (fun x => !((getOrbit p fuel d).contains x)) := by
          rcases List.mem_cons.mp hw with rfl | hw_ds
          · rw [getOrbit_contains_self p fuel w] at hc
            contradiction
          · apply List.mem_filter.mpr
            refine ⟨hw_ds, ?_⟩
            rw [getOrbit_contains_symm_of_complete p darts h_all h_le d w, hc]
            rfl
        exact ih _ h_flt_len hw_flt

/-- On a complete dart list (`darts.length ≤ fuel`), for any dart `w : D`,
    there is a unique canonical representative `v₀` in `canonicalOrbits p fuel darts` belonging to `w`'s orbit. -/
theorem exists_singleton_filter_canonicalOrbits (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (w : D) :
    ∃ v₀ : D,
      (canonicalOrbits p fuel darts).filter (fun v => (getOrbit p fuel w).contains v) = [v₀] :=
  exists_singleton_filter_canonicalOrbitsAux p darts h_all h_le darts.length darts (Nat.le_refl _) w (h_all w)

theorem filter_append_eq (P : D → Bool) (l1 l2 : List D) :
    (l1 ++ l2).filter P = l1.filter P ++ l2.filter P := by
  induction l1 with
  | nil => rfl
  | cons x xs ih =>
    dsimp [List.filter]
    cases P x <;> simp [ih]

theorem filter_reverse_length (P : D → Bool) (l : List D) :
    (l.reverse.filter P).length = (l.filter P).length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, filter_append_eq]
    dsimp [List.filter]
    cases P x <;> simp <;> omega

/-- On a complete dart list (`darts.length ≤ fuel`), for any dart `w : D`,
    filtering `(canonicalOrbits p fuel1 darts).reverse` by `(getOrbit p fuel w).contains` has length `1`. -/
theorem filter_canonicalOrbits_reverse_length_eq_one (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel1 fuel : Nat} (h_le1 : darts.length ≤ fuel1) (h_le : darts.length ≤ fuel) (w : D) :
    (((canonicalOrbits p fuel1 darts).reverse).filter (fun v => (getOrbit p fuel w).contains v)).length = 1 := by
  rw [filter_reverse_length]
  have h_pred : (fun v => (getOrbit p fuel w).contains v) = (fun v => (getOrbit p fuel1 w).contains v) := by
    funext v
    rw [getOrbit_fuel_eq_of_complete p darts h_all w h_le,
        getOrbit_fuel_eq_of_complete p darts h_all w h_le1]
  rw [h_pred]
  rcases exists_singleton_filter_canonicalOrbits p darts h_all h_le1 w with ⟨v₀, hv₀⟩
  rw [hv₀]
  rfl

/-- When `orbitClosesWithin p d d fuel` holds, `getOrbit p fuel d` is closed under `p.inv`. -/
theorem getOrbit_closed_under_inv (p : Perm D) (fuel : Nat) (d : D)
    (h_closes : orbitClosesWithin p d d fuel) :
    ∀ x ∈ getOrbit p fuel d, p.inv x ∈ getOrbit p fuel d := by
  intro x hx
  have h_closes_symm := orbitClosesWithin_symm_perm p fuel d h_closes
  have hx_symm : x ∈ getOrbit p.symm fuel d :=
    (mem_getOrbit_symm_perm_iff p fuel d x h_closes).mpr hx
  have hinv_symm : p.symm.f x ∈ getOrbit p.symm fuel d :=
    getOrbit_closed_under_f p.symm fuel d h_closes_symm x hx_symm
  exact (mem_getOrbit_symm_perm_iff p fuel d (p.inv x) h_closes).mp hinv_symm

/-- On a complete dart list (`darts.length ≤ fuel`), `getOrbit p fuel d` is closed under `p.f`. -/
theorem getOrbit_closed_under_f_of_complete (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {d x : D}
    (hx : x ∈ getOrbit p fuel d) :
    p.f x ∈ getOrbit p fuel d :=
  getOrbit_closed_under_f p fuel d
    (orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le) x hx

/-- On a complete dart list (`darts.length ≤ fuel`), `getOrbit p fuel d` is closed under `p.inv`. -/
theorem getOrbit_closed_under_inv_of_complete (p : Perm D)
    (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {d x : D}
    (hx : x ∈ getOrbit p fuel d) :
    p.inv x ∈ getOrbit p fuel d :=
  getOrbit_closed_under_inv p fuel d
    (orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_all d) h_le) x hx

end Hypermap
