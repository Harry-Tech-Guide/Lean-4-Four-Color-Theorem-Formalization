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

end Hypermap
