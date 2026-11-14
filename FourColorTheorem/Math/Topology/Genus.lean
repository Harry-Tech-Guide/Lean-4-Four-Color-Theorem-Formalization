/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Topology.ComponentLemmas
import FourColorTheorem.Math.Topology.Surgery
import FourColorTheorem.Math.Topology.SubtypeSurgery

/-!
# Combinatorial Genus Deficit, Euler Inequality, and Planar Surgery Preservation (`Genus`)

This module establishes the permutation-triple genus theory for finite hypermaps:

1. **Transpositions & Orbit Split/Merge (`swapPerm`, `swapCompLeft`, `swapCompRight`)**:
   Composing a permutation with a 2-cycle `(a, b)` splits an orbit when `a, b` lie in the
   same orbit (`+1` orbit) and merges two orbits when `a, b` lie in distinct orbits (`-1` orbit).
   Moreover, `bypass p d = swapCompLeft p d (p.f d)`.
2. **Permutation Triples (`PermTriple D`) & `(e, n)`-Component BFS (`countPairComps`)**:
   Generalizing hypermaps by dropping the involution axiom `e² = id`, while preserving
   `e ∘ n ∘ f = id` and matching `Hypermap.countComponents` on every complete hypermap.
3. **Non-Negativity of Genus Deficit (`genusDeficit_nonneg`) & Euler Inequality**:
   Every permutation triple satisfies `0 ≤ |D| + 2C - (V + E + F)`, yielding
   `EulerChar H ≤ 2 * numComponents H` and the exact characterization
   `isPlanar H = true ↔ genusDeficit H = 0 ∧ (∀ d, H.edge.f d ≠ d)`.
4. **Planar Surgery Preservation**:
   - Component-closed excision (`exciseSubtype_isPlanar`),
   - Edge deletion (`deleteEdgeSubtype_isPlanar`),
   - Degree-2 vertex smoothing (`smoothDeg2Subtype_isPlanar`).
-/

namespace Hypermap

set_option linter.unusedSectionVars false

section SwapPermAndBypass

variable {D : Type}

/-- Pointwise swap transposition `(a, b)` on `D`. -/
def swapFun [DecidableEq D] (a b x : D) : D :=
  if x = a then b else if x = b then a else x

@[simp]
theorem swapFun_left [DecidableEq D] (a b : D) : swapFun a b a = b := by
  dsimp [swapFun]
  rw [if_pos rfl]

@[simp]
theorem swapFun_right [DecidableEq D] (a b : D) : swapFun a b b = a := by
  dsimp [swapFun]
  split
  · rename_i h; exact h
  · rw [if_pos rfl]

theorem swapFun_of_ne [DecidableEq D] {a b x : D} (ha : x ≠ a) (hb : x ≠ b) :
    swapFun a b x = x := by
  dsimp [swapFun]
  rw [if_neg ha, if_neg hb]

theorem swapFun_invol [DecidableEq D] (a b x : D) :
    swapFun a b (swapFun a b x) = x := by
  dsimp [swapFun]
  by_cases hxa : x = a
  · subst hxa
    rw [if_pos rfl]
    split
    · rename_i h; exact h
    · rw [if_pos rfl]
  · rw [if_neg hxa]
    by_cases hxb : x = b
    · subst hxb
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hxb, if_neg hxa, if_neg hxb]

/-- Permutation representing transposition `(a, b)`. -/
def swapPerm [DecidableEq D] (a b : D) : Perm D where
  f := swapFun a b
  inv := swapFun a b
  left_inv := swapFun_invol a b
  right_inv := swapFun_invol a b

/-- Left-composed transposition `swapFun a b ∘ p`. -/
def swapCompLeft [DecidableEq D] (p : Perm D) (a b : D) : Perm D where
  f := fun x => swapFun a b (p.f x)
  inv := fun x => p.inv (swapFun a b x)
  left_inv := fun x => by simp only [swapFun_invol, p.left_inv]
  right_inv := fun x => by simp only [p.right_inv, swapFun_invol]

/-- Right-composed transposition `p ∘ swapFun a b`. -/
def swapCompRight [DecidableEq D] (p : Perm D) (a b : D) : Perm D where
  f := fun x => p.f (swapFun a b x)
  inv := fun x => swapFun a b (p.inv x)
  left_inv := fun x => by simp only [p.left_inv, swapFun_invol]
  right_inv := fun x => by simp only [swapFun_invol, p.right_inv]

theorem swapCompRight_symm [DecidableEq D] (p : Perm D) (a b : D) :
    (swapCompRight p a b).symm = swapCompLeft p.symm a b := rfl

theorem swapCompLeft_symm [DecidableEq D] (p : Perm D) (a b : D) :
    (swapCompLeft p a b).symm = swapCompRight p.symm a b := rfl

theorem swapCompLeft_same [DecidableEq D] (p : Perm D) (a : D) :
    swapCompLeft p a a = p := by
  apply perm_ext
  · funext x
    dsimp [swapCompLeft, swapFun]
    split <;> simp_all
  · funext x
    dsimp [swapCompLeft, swapFun]
    split <;> simp_all

/-- `bypass p d` equals `swapCompLeft p d (p.f d)`. -/
theorem bypass_eq_swapCompLeft [DecidableEq D] (p : Perm D) (d : D) :
    bypass p d = swapCompLeft p d (p.f d) := by
  have hf : (bypass p d).f = (swapCompLeft p d (p.f d)).f := by
    funext x
    dsimp [bypass, swapCompLeft]
    by_cases hxd : x = d
    · subst hxd
      rw [if_pos rfl, swapFun_right]
    · rw [if_neg hxd]
      by_cases hpx : p.f x = d
      · rw [if_pos hpx, hpx, swapFun_left]
      · rw [if_neg hpx]
        have hpx2 : p.f x ≠ p.f d := fun h => hxd (by
          have hi := congrArg p.inv h
          rwa [p.left_inv, p.left_inv] at hi)
        rw [swapFun_of_ne hpx hpx2]
  apply perm_ext _ _ hf
  funext y
  have h1 := (bypass p d).right_inv y
  have h2 := congrFun hf ((bypass p d).inv y)
  rw [h2] at h1
  have h3 := congrArg (swapCompLeft p d (p.f d)).inv h1
  rw [(swapCompLeft p d (p.f d)).left_inv] at h3
  exact h3

end SwapPermAndBypass

section OrbitSplitMerge

variable {D : Type}

theorem perm_iter_inj [DecidableEq D] (p : Perm D) (n : Nat) {x y : D}
    (h : Perm.iter p n x = Perm.iter p n y) : x = y :=
  Perm.iter_inj p n h

theorem perm_iter_mul_add_eq (p : Perm D) {L : Nat} {d : D}
    (h_period : Perm.iter p L d = d) :
    ∀ (q r : Nat), Perm.iter p (q * L + r) d = Perm.iter p r d
  | 0, r => by simp
  | q + 1, r => by
    have h_eq : (q + 1) * L + r = (q * L + r) + L := by
      rw [Nat.succ_mul]
      omega
    rw [h_eq, Perm.iter_add, h_period]
    exact perm_iter_mul_add_eq p h_period q r

private theorem getOrbitAux_length_le_of_iter [BEq D] [LawfulBEq D] (p : Perm D) (start : D) :
    ∀ (m : Nat) (current : D) (acc : List D) (fuel : Nat),
      Perm.iter p (m + 1) current = start →
      (getOrbitAux p start current acc fuel).length ≤ acc.length + m + 1
  | m, current, acc, 0, _ => by
    dsimp [getOrbitAux]
    omega
  | 0, current, acc, fuel + 1, h_eq => by
    have hp : p.f current = start := by simpa [Perm.iter] using h_eq
    dsimp [getOrbitAux]
    rw [if_pos (beq_iff_eq.mpr hp)]
    dsimp
    omega
  | m + 1, current, acc, fuel + 1, h_eq => by
    dsimp [getOrbitAux]
    cases hc : (p.f current == start)
    · dsimp
      have h_iter' : Perm.iter p (m + 1) (p.f current) = start := by
        rw [← h_eq]
        exact (Perm.iter_add p (m + 1) 1 current).symm
      have h_ih := getOrbitAux_length_le_of_iter p start m (p.f current) (current :: acc) fuel h_iter'
      dsimp at h_ih
      omega
    · dsimp
      omega

/-- Minimal positive period bound: if `Perm.iter p k d = d` with `1 ≤ k`,
    then `(getOrbit p fuel d).length ≤ k`. -/
theorem getOrbit_length_le_of_iter_eq_self [BEq D] [LawfulBEq D] (p : Perm D)
    (fuel : Nat) {k : Nat} {d : D} (hk : 1 ≤ k) (h_iter : Perm.iter p k d = d) :
    (getOrbit p fuel d).length ≤ k := by
  have hk1 : (k - 1) + 1 = k := by omega
  rw [← hk1] at h_iter
  have h_le := getOrbitAux_length_le_of_iter p d (k - 1) d [] fuel h_iter
  dsimp [getOrbit] at h_le ⊢
  omega

/-- Periodicity & distinctness package for `getOrbit p fuel d`:
    for indices `i, j < (getOrbit p fuel d).length`, `Perm.iter p i d = Perm.iter p j d` implies `i = j`. -/
theorem perm_iter_inj_of_lt_getOrbit_length [DecidableEq D] (p : Perm D)
    {fuel : Nat} {d : D}
    {i j : Nat} (hi : i < (getOrbit p fuel d).length) (hj : j < (getOrbit p fuel d).length)
    (h_eq : Perm.iter p i d = Perm.iter p j d) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · have h_diff : j = i + (j - i) := by omega
    rw [h_diff, Perm.iter_add] at h_eq
    have h_id : d = Perm.iter p (j - i) d := by
      apply Perm.iter_inj p i
      exact h_eq
    have h_le := getOrbit_length_le_of_iter_eq_self p fuel (by omega) h_id.symm
    omega
  · rfl
  · have h_diff : i = j + (i - j) := by omega
    rw [h_diff, Perm.iter_add] at h_eq
    have h_id : d = Perm.iter p (i - j) d := by
      apply Perm.iter_inj p j
      exact h_eq.symm
    have h_le := getOrbit_length_le_of_iter_eq_self p fuel (by omega) h_id.symm
    omega

theorem getOrbit_length_pos [DecidableEq D] (p : Perm D) {fuel : Nat} (h_fuel : 1 ≤ fuel) (d : D) :
    1 ≤ (getOrbit p fuel d).length := by
  cases fuel with
  | zero => omega
  | succ f' =>
    dsimp [getOrbit, getOrbitAux]
    cases hc : (p.f d == d)
    · dsimp
      have h_mem : d ∈ getOrbitAux p d (p.f d) [d] f' :=
        getOrbitAux_acc_subset p d (p.f d) [d] f' d List.mem_cons_self
      cases h_l : getOrbitAux p d (p.f d) [d] f' with
      | nil => rw [h_l] at h_mem; cases h_mem
      | cons _ _ => simp
    · dsimp
      omega

theorem mem_getOrbit_iff_exists_lt_length [DecidableEq D] (p : Perm D)
    {fuel : Nat} (h_fuel : 1 ≤ fuel) (h_closes : orbitClosesWithin p d d fuel) (x : D) :
    x ∈ getOrbit p fuel d ↔ ∃ i : Nat, i < (getOrbit p fuel d).length ∧ Perm.iter p i d = x := by
  constructor
  · intro hx
    obtain ⟨k, _, hkx⟩ := mem_getOrbit_imp_exists_iter p fuel d x hx
    let L := (getOrbit p fuel d).length
    have hL_pos : 0 < L := getOrbit_length_pos p h_fuel d
    have h_per : Perm.iter p L d = d := perm_iter_length_getOrbit_eq_self p fuel d h_closes
    refine ⟨k % L, Nat.mod_lt k hL_pos, ?_⟩
    have hk_eq : k = (k / L) * L + k % L := by
      rw [Nat.mul_comm, Nat.div_add_mod]
    rw [hk_eq, perm_iter_mul_add_eq p h_per] at hkx
    exact hkx.symm
  · rintro ⟨i, _, rfl⟩
    exact iter_mem_getOrbit_of_closes p fuel d h_closes i

private theorem getOrbitAux_eq_of_agree_on_closed [BEq D] [LawfulBEq D] (p q : Perm D)
    (S : D → Bool) (hS_p : ∀ x, S (p.f x) = S x) (h_agree : ∀ x, S x = true → p.f x = q.f x)
    (start : D) :
    ∀ (fuel : Nat) (current : D) (acc : List D),
      S current = true →
      getOrbitAux p start current acc fuel = getOrbitAux q start current acc fuel
  | 0, current, acc, _ => rfl
  | fuel + 1, current, acc, hSc => by
    dsimp [getOrbitAux]
    have hpf : p.f current = q.f current := h_agree current hSc
    have hSpc : S (p.f current) = true := by rw [hS_p current, hSc]
    rw [hpf]
    cases hc : (q.f current == start)
    · dsimp
      rw [← hpf]
      exact getOrbitAux_eq_of_agree_on_closed p q S hS_p h_agree start fuel (p.f current) (current :: acc) hSpc
    · rfl

theorem getOrbit_eq_of_agree_on_closed [DecidableEq D] (p q : Perm D)
    (S : D → Bool) (hS_p : ∀ x, S (p.f x) = S x) (h_agree : ∀ x, S x = true → p.f x = q.f x)
    (fuel : Nat) {d : D} (hSd : S d = true) :
    getOrbit p fuel d = getOrbit q fuel d :=
  getOrbitAux_eq_of_agree_on_closed p q S hS_p h_agree d fuel d [] hSd

private theorem countOrbitsAux_eq_of_pred_getOrbit_eq [DecidableEq D] (p q : Perm D) (fuel : Nat)
    (S : D → Bool) (h_orb : ∀ x, S x = true → getOrbit p fuel x = getOrbit q fuel x) :
    ∀ (steps : Nat) (l : List D), (∀ x ∈ l, S x = true) →
      countOrbitsAux p fuel steps l = countOrbitsAux q fuel steps l
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | steps + 1, d :: ds, h_all => by
    dsimp [countOrbitsAux]
    have hSd : S d = true := h_all d List.mem_cons_self
    rw [h_orb d hSd]
    congr 1
    apply countOrbitsAux_eq_of_pred_getOrbit_eq p q fuel S h_orb steps
    intro x hx
    exact h_all x (List.mem_cons_of_mem d (List.mem_filter.mp hx).1)

theorem countOrbits_eq_of_pred_getOrbit_eq [DecidableEq D] (p q : Perm D) (fuel : Nat)
    (S : D → Bool) (h_orb : ∀ x, S x = true → getOrbit p fuel x = getOrbit q fuel x)
    (l : List D) (h_all : ∀ x ∈ l, S x = true) :
    countOrbits p fuel l = countOrbits q fuel l :=
  countOrbitsAux_eq_of_pred_getOrbit_eq p q fuel S h_orb l.length l h_all

private theorem countOrbits_eq_one_of_all_mem_orbit [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (a : D) (l : List D) (hne : l ≠ []) (h_in : ∀ x ∈ l, x ∈ getOrbit p fuel a) :
    countOrbits p fuel l = 1 := by
  have h_closes : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
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

private theorem countOrbits_eq_two_of_two_orbits [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (a b : D) (h_ab : b ∉ getOrbit p fuel a)
    (l : List D) (ha : a ∈ l) (hb : b ∈ l)
    (h_sub : ∀ x ∈ l, x ∈ getOrbit p fuel a ∨ x ∈ getOrbit p fuel b) :
    countOrbits p fuel l = 2 := by
  have hca : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  rw [countOrbits_eq_one_add_filter_of_mem p fuel l a ha hca]
  let l' := l.filter (fun x => !((getOrbit p fuel a).contains x))
  have hb' : b ∈ l' := by
    rw [List.mem_filter]
    refine ⟨hb, ?_⟩
    cases hc : (getOrbit p fuel a).contains b with
    | false => rfl
    | true => exact False.elim (h_ab (List.contains_iff_mem.mp hc))
  have hne' : l' ≠ [] := fun hnil => by rw [hnil] at hb'; cases hb'
  have h_in' : ∀ x ∈ l', x ∈ getOrbit p fuel b := by
    intro x hx
    rw [List.mem_filter] at hx
    rcases h_sub x hx.1 with hxa | hxb
    · have hc : (getOrbit p fuel a).contains x = true := List.contains_iff_mem.mpr hxa
      rw [hc] at hx
      cases hx.2
    · exact hxb
  have h_one := countOrbits_eq_one_of_all_mem_orbit p darts h_all h_le b l' hne' h_in'
  dsimp [l'] at h_one
  rw [h_one]

private theorem swapCompLeft_iter_prefix [DecidableEq D] (p : Perm D) (a b : D)
    (m : Nat) (d : D)
    (h_bound : ∀ t : Nat, t < m → Perm.iter p (t + 1) d ≠ a ∧ Perm.iter p (t + 1) d ≠ b) :
    Perm.iter (swapCompLeft p a b) m d = Perm.iter p m d := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [Perm.iter_succ, Perm.iter_succ]
    have h_ih := ih (fun t ht => h_bound t (Nat.lt_succ_of_lt ht))
    rw [h_ih]
    have h_ne := h_bound k (Nat.lt_succ_self k)
    have h_pf : p.f (Perm.iter p k d) ≠ a ∧ p.f (Perm.iter p k d) ≠ b := by
      simpa [Perm.iter_succ] using h_ne
    dsimp [swapCompLeft]
    exact swapFun_of_ne h_pf.1 h_pf.2

/-- **Orbit Split Theorem (`swapCompLeft`, same orbit)**:
    if `b ∈ getOrbit p fuel a` and `a ≠ b` on a complete dart list (`darts.length ≤ fuel`),
    then `swapCompLeft p a b` splits `a`'s orbit into two, increasing `countOrbits` by `1`. -/
theorem countOrbits_swapCompLeft_same [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (hab : a ≠ b) (hb : b ∈ getOrbit p fuel a) :
    countOrbits (swapCompLeft p a b) fuel darts = countOrbits p fuel darts + 1 := by
  have h_darts_ne : darts ≠ [] := fun hnil => by have := h_all a; rw [hnil] at this; cases this
  have h_fuel : 1 ≤ fuel := by
    cases darts with
    | nil => exact False.elim (h_darts_ne rfl)
    | cons _ _ => dsimp at h_le; omega
  let q := swapCompLeft p a b
  have hca_p : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  have hca_q : orbitClosesWithin q a a fuel :=
    orbitClosesWithin_mono q a a (orbitClosesWithin_of_complete q darts h_all a) h_le
  have hcb_q : orbitClosesWithin q b b fuel :=
    orbitClosesWithin_mono q b b (orbitClosesWithin_of_complete q darts h_all b) h_le
  let L := (getOrbit p fuel a).length
  have hL_pos : 1 ≤ L := getOrbit_length_pos p h_fuel a
  have hL_per : Perm.iter p L a = a := perm_iter_length_getOrbit_eq_self p fuel a hca_p
  obtain ⟨k, hk_lt, hka⟩ := (mem_getOrbit_iff_exists_lt_length p h_fuel hca_p b).mp hb
  have hk_pos : 1 ≤ k := by
    by_cases hk0 : k = 0
    · subst hk0; exact False.elim (hab hka)
    · omega
  -- 1. Q-iterates from `a` match `p`-iterates up to `k - 1`, then cycle at `k`:
  have hq_a_pref : ∀ i ≤ k - 1, Perm.iter q i a = Perm.iter p i a := by
    intro i hi
    apply swapCompLeft_iter_prefix p a b i a
    intro t ht
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
  have hq_a_per : Perm.iter q k a = a := by
    have hk1 : k = (k - 1) + 1 := by omega
    rw [hk1, Perm.iter_succ, hq_a_pref (k - 1) (Nat.le_refl _)]
    dsimp [q, swapCompLeft]
    have hp : p.f (Perm.iter p (k - 1) a) = b := by
      have : p.f (Perm.iter p (k - 1) a) = Perm.iter p k a := by rw [← Perm.iter_succ, ← hk1]
      rw [this, hka]
    rw [hp, swapFun_right]
  have h_mem_qa_iff : ∀ x, x ∈ getOrbit q fuel a ↔ ∃ r < k, Perm.iter p r a = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨m, _, rfl⟩ := mem_getOrbit_imp_exists_iter q fuel a x hx
      let r := m % k
      have hr_lt : r < k := Nat.mod_lt m (by omega)
      have hm_eq : m = (m / k) * k + r := by
        rw [Nat.mul_comm, Nat.div_add_mod]
      refine ⟨r, hr_lt, ?_⟩
      rw [hm_eq, perm_iter_mul_add_eq q hq_a_per, hq_a_pref r (by omega)]
    · rintro ⟨r, hr_lt, rfl⟩
      rw [← hq_a_pref r (by omega)]
      exact iter_mem_getOrbit_of_closes q fuel a hca_q r
  -- 2. Q-iterates from `b` match `Perm.iter p (k + j) a` up to `L - k - 1`, then cycle back to `b`:
  have hq_b_pref : ∀ j ≤ L - k - 1, Perm.iter q j b = Perm.iter p (k + j) a := by
    intro j hj
    rw [← hka]
    have : ∀ s : Nat, s ≤ L - k - 1 → Perm.iter q s (Perm.iter p k a) = Perm.iter p (k + s) a := by
      intro s hs
      rw [swapCompLeft_iter_prefix p a b s (Perm.iter p k a)]
      · rw [← Perm.iter_add, Nat.add_comm s k]
      · intro t ht
        have hkt_lt_L : k + (t + 1) < L := by omega
        have h_eq_t : Perm.iter p (t + 1) (Perm.iter p k a) = Perm.iter p (k + (t + 1)) a := by
          rw [← Perm.iter_add, Nat.add_comm (t + 1) k]
        rw [h_eq_t]
        refine ⟨?_, ?_⟩
        · intro heq
          have := perm_iter_inj_of_lt_getOrbit_length p hkt_lt_L hL_pos heq
          omega
        · intro heq
          rw [← hka] at heq
          have := perm_iter_inj_of_lt_getOrbit_length p hkt_lt_L hk_lt heq
          omega
    exact this j hj
  have hq_b_per : Perm.iter q (L - k) b = b := by
    have hlk1 : L - k = (L - k - 1) + 1 := by omega
    rw [hlk1, Perm.iter_succ, hq_b_pref (L - k - 1) (Nat.le_refl _)]
    dsimp [q, swapCompLeft]
    have h_sum : k + (L - k - 1) + 1 = L := by omega
    have hp : p.f (Perm.iter p (k + (L - k - 1)) a) = a := by
      have : p.f (Perm.iter p (k + (L - k - 1)) a) = Perm.iter p (k + (L - k - 1) + 1) a := by
        rw [← Perm.iter_succ]
      rw [this, h_sum, hL_per]
    rw [hp, swapFun_left]
  have h_mem_qb_iff : ∀ x, x ∈ getOrbit q fuel b ↔ ∃ j < L - k, Perm.iter p (k + j) a = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨m, _, rfl⟩ := mem_getOrbit_imp_exists_iter q fuel b x hx
      let j := m % (L - k)
      have hj_lt : j < L - k := Nat.mod_lt m (by omega)
      have hm_eq : m = (m / (L - k)) * (L - k) + j := by
        rw [Nat.mul_comm, Nat.div_add_mod]
      refine ⟨j, hj_lt, ?_⟩
      rw [hm_eq, perm_iter_mul_add_eq q hq_b_per, hq_b_pref j (by omega)]
    · rintro ⟨j, hj_lt, rfl⟩
      rw [← hq_b_pref j (by omega)]
      exact iter_mem_getOrbit_of_closes q fuel b hcb_q j
  -- 3. `b ∉ getOrbit q fuel a` and `getOrbit p fuel a = getOrbit q fuel a ∪ getOrbit q fuel b`:
  have hb_not_qa : b ∉ getOrbit q fuel a := by
    intro hmem
    obtain ⟨r, hr_lt, hrb⟩ := (h_mem_qa_iff b).mp hmem
    rw [← hka] at hrb
    have := perm_iter_inj_of_lt_getOrbit_length p (Nat.lt_trans hr_lt hk_lt) hk_lt hrb
    omega
  -- 4. Partition `darts` by `S x := (getOrbit p fuel a).contains x`:
  let S : D → Bool := fun x => (getOrbit p fuel a).contains x
  have hS_p : ∀ x, S (p.f x) = S x := by
    intro x
    dsimp [S]
    cases hc1 : (getOrbit p fuel a).contains (p.f x) <;> cases hc2 : (getOrbit p fuel a).contains x
    · rfl
    · have h2 := List.contains_iff_mem.mp hc2
      have h1 := getOrbit_closed_under_f p fuel a hca_p x h2
      rw [List.contains_iff_mem.mpr h1] at hc1
      cases hc1
    · have h1 := List.contains_iff_mem.mp hc1
      have hinv := getOrbit_closed_under_inv p fuel a hca_p (p.f x) h1
      rw [p.left_inv] at hinv
      rw [List.contains_iff_mem.mpr hinv] at hc2
      cases hc2
    · rfl
  have hS_q : ∀ x, S (q.f x) = S x := by
    intro x
    have ha_in : a ∈ getOrbit p fuel a := mem_getOrbit_self p fuel a
    have hb_in : b ∈ getOrbit p fuel a := hb
    have hswap_in : ∀ y, (y ∈ getOrbit p fuel a) ↔ (swapFun a b y ∈ getOrbit p fuel a) := by
      intro y
      by_cases hya : y = a
      · subst hya; simp [ha_in, hb_in]
      · by_cases hyb : y = b
        · subst hyb; simp [ha_in, hb_in]
        · rw [swapFun_of_ne hya hyb]
    dsimp [S, q, swapCompLeft]
    have hp := hS_p x
    dsimp [S] at hp
    cases hc1 : (getOrbit p fuel a).contains (swapFun a b (p.f x)) <;>
        cases hc2 : (getOrbit p fuel a).contains x
    · rfl
    · have h2 := List.contains_iff_mem.mp hc2
      have hp1 : (getOrbit p fuel a).contains (p.f x) = true := by rw [hp, hc2]
      have hpx := List.contains_iff_mem.mp hp1
      have hspx := (hswap_in (p.f x)).mp hpx
      rw [List.contains_iff_mem.mpr hspx] at hc1
      cases hc1
    · have h1 := List.contains_iff_mem.mp hc1
      have hpx := (hswap_in (p.f x)).mpr h1
      have hcpx : (getOrbit p fuel a).contains (p.f x) = true := List.contains_iff_mem.mpr hpx
      rw [hp] at hcpx
      rw [hcpx] at hc2
      cases hc2
    · rfl
  rw [countOrbits_partition_of_closed p fuel darts S hS_p,
      countOrbits_partition_of_closed q fuel darts S hS_q]
  -- Outside `S`, `p` and `q` agree identically:
  have h_agree_out : ∀ x, (!S x) = true → p.f x = q.f x := by
    intro x hx
    have hnot : x ∉ getOrbit p fuel a := by
      intro hm
      rw [show S x = true from List.contains_iff_mem.mpr hm] at hx
      cases hx
    have hpx_not : p.f x ∉ getOrbit p fuel a := by
      intro hm
      have hinv := getOrbit_closed_under_inv p fuel a hca_p (p.f x) hm
      rw [p.left_inv] at hinv
      exact hnot hinv
    have hne_a : p.f x ≠ a := fun heq => hpx_not (heq ▸ mem_getOrbit_self p fuel a)
    have hne_b : p.f x ≠ b := fun heq => hpx_not (heq ▸ hb)
    dsimp [q, swapCompLeft]
    exact (swapFun_of_ne hne_a hne_b).symm
  have h_nS_p : ∀ x, (!S (p.f x)) = (!S x) := fun x => by rw [hS_p x]
  have h_out_eq : countOrbits p fuel (darts.filter (fun x => !S x)) =
      countOrbits q fuel (darts.filter (fun x => !S x)) := by
    apply countOrbits_eq_of_pred_getOrbit_eq p q fuel (fun x => !S x)
    · intro x hx
      exact getOrbit_eq_of_agree_on_closed p q (fun y => !S y) h_nS_p h_agree_out fuel hx
    · intro x hx
      exact (List.mem_filter.mp hx).2
  -- Inside `S`, `p` has 1 orbit and `q` has 2 orbits:
  have h_in_p : countOrbits p fuel (darts.filter S) = 1 := by
    apply countOrbits_eq_one_of_all_mem_orbit p darts h_all h_le a
    · intro hnil
      have ha_in : a ∈ darts.filter S :=
        List.mem_filter.mpr ⟨h_all a, List.contains_iff_mem.mpr (mem_getOrbit_self p fuel a)⟩
      rw [hnil] at ha_in
      cases ha_in
    · intro x hx
      exact List.contains_iff_mem.mp (List.mem_filter.mp hx).2
  have h_in_q : countOrbits q fuel (darts.filter S) = 2 := by
    apply countOrbits_eq_two_of_two_orbits q darts h_all h_le a b hb_not_qa
    · exact List.mem_filter.mpr ⟨h_all a, List.contains_iff_mem.mpr (mem_getOrbit_self p fuel a)⟩
    · exact List.mem_filter.mpr ⟨h_all b, List.contains_iff_mem.mpr hb⟩
    · intro x hx
      have hx_pa : x ∈ getOrbit p fuel a := List.contains_iff_mem.mp (List.mem_filter.mp hx).2
      obtain ⟨i, hi_lt, rfl⟩ := (mem_getOrbit_iff_exists_lt_length p h_fuel hca_p x).mp hx_pa
      by_cases hik : i < k
      · exact Or.inl ((h_mem_qa_iff _).mpr ⟨i, hik, rfl⟩)
      · have hik_ge : k ≤ i := Nat.le_of_not_lt hik
        refine Or.inr ((h_mem_qb_iff _).mpr ⟨i - k, by omega, ?_⟩)
        have : k + (i - k) = i := by omega
        rw [this]
  rw [h_in_p, h_in_q, h_out_eq]
  omega

/-- **Orbit Merge Theorem (`swapCompLeft`, distinct orbits)**:
    if `b ∉ getOrbit p fuel a` on a complete dart list (`darts.length ≤ fuel`),
    then `swapCompLeft p a b` merges the orbits of `a` and `b`, decreasing `countOrbits` by `1`. -/
theorem countOrbits_swapCompLeft_diff [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (h_ab : b ∉ getOrbit p fuel a) :
    countOrbits (swapCompLeft p a b) fuel darts + 1 = countOrbits p fuel darts := by
  have hab : a ≠ b := fun h_eq => h_ab (h_eq ▸ mem_getOrbit_self p fuel a)
  have h_darts_ne : darts ≠ [] := fun hnil => by have := h_all a; rw [hnil] at this; cases this
  have h_fuel : 1 ≤ fuel := by
    cases darts with
    | nil => exact False.elim (h_darts_ne rfl)
    | cons _ _ => dsimp at h_le; omega
  let q := swapCompLeft p a b
  have hca_p : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  have hcb_p : orbitClosesWithin p b b fuel :=
    orbitClosesWithin_mono p b b (orbitClosesWithin_of_complete p darts h_all b) h_le
  have hca_q : orbitClosesWithin q a a fuel :=
    orbitClosesWithin_mono q a a (orbitClosesWithin_of_complete q darts h_all a) h_le
  have ha_not_pb : a ∉ getOrbit p fuel b := by
    intro hm
    exact h_ab (mem_getOrbit_symm p fuel hcb_p hm)
  let La := (getOrbit p fuel a).length
  let Lb := (getOrbit p fuel b).length
  have hLa_per : Perm.iter p La a = a := perm_iter_length_getOrbit_eq_self p fuel a hca_p
  have hLb_per : Perm.iter p Lb b = b := perm_iter_length_getOrbit_eq_self p fuel b hcb_p
  have hLa_pos : 1 ≤ La := getOrbit_length_pos p h_fuel a
  have hLb_pos : 1 ≤ Lb := getOrbit_length_pos p h_fuel b
  -- 1. Q-iterates from `a` match `p` up to `La - 1`, then step to `b`:
  have hq_a_pref : ∀ i ≤ La - 1, Perm.iter q i a = Perm.iter p i a := by
    intro i hi
    apply swapCompLeft_iter_prefix p a b i a
    intro t ht
    have ht1_lt : t + 1 < La := by omega
    refine ⟨?_, ?_⟩
    · intro heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht1_lt hLa_pos heq
      omega
    · intro heq
      have hmem : b ∈ getOrbit p fuel a := heq ▸ iter_mem_getOrbit_of_closes p fuel a hca_p (t + 1)
      exact h_ab hmem
  have hq_a_to_b : Perm.iter q La a = b := by
    have h1 : La = (La - 1) + 1 := by omega
    rw [h1, Perm.iter_succ, hq_a_pref (La - 1) (Nat.le_refl _)]
    dsimp [q, swapCompLeft]
    have hp : p.f (Perm.iter p (La - 1) a) = a := by
      have : p.f (Perm.iter p (La - 1) a) = Perm.iter p La a := by rw [← Perm.iter_succ, ← h1]
      rw [this, hLa_per]
    rw [hp, swapFun_left]
  -- 2. Q-iterates from `b` match `p` up to `Lb - 1`:
  have hq_b_pref : ∀ j ≤ Lb - 1, Perm.iter q j b = Perm.iter p j b := by
    intro j hj
    apply swapCompLeft_iter_prefix p a b j b
    intro t ht
    have ht1_lt : t + 1 < Lb := by omega
    refine ⟨?_, ?_⟩
    · intro heq
      have hmem : a ∈ getOrbit p fuel b := heq ▸ iter_mem_getOrbit_of_closes p fuel b hcb_p (t + 1)
      exact ha_not_pb hmem
    · intro heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht1_lt hLb_pos heq
      omega
  -- 3. Every element of `getOrbit p fuel a ∪ getOrbit p fuel b` lies in `getOrbit q fuel a`:
  have h_pa_sub_qa : ∀ x ∈ getOrbit p fuel a, x ∈ getOrbit q fuel a := by
    intro x hx
    obtain ⟨i, hi_lt, rfl⟩ := (mem_getOrbit_iff_exists_lt_length p h_fuel hca_p x).mp hx
    rw [← hq_a_pref i (by omega)]
    exact iter_mem_getOrbit_of_closes q fuel a hca_q i
  have h_pb_sub_qa : ∀ x ∈ getOrbit p fuel b, x ∈ getOrbit q fuel a := by
    intro x hx
    obtain ⟨j, hj_lt, rfl⟩ := (mem_getOrbit_iff_exists_lt_length p h_fuel hcb_p x).mp hx
    rw [← hq_b_pref j (by omega), ← hq_a_to_b, ← Perm.iter_add]
    exact iter_mem_getOrbit_of_closes q fuel a hca_q (j + La)
  -- 4. Partition `darts` by `S x := (getOrbit p fuel a).contains x || (getOrbit p fuel b).contains x`:
  let S : D → Bool := fun x => (getOrbit p fuel a).contains x || (getOrbit p fuel b).contains x
  have hS_iff : ∀ x, S x = true ↔ x ∈ getOrbit p fuel a ∨ x ∈ getOrbit p fuel b := by
    intro x
    dsimp [S]
    rw [Bool.or_eq_true, List.contains_iff_mem, List.contains_iff_mem]
  have hS_p : ∀ x, S (p.f x) = S x := by
    intro x
    cases h1 : S (p.f x) <;> cases h2 : S x
    · rfl
    · have hm : x ∈ getOrbit p fuel a ∨ x ∈ getOrbit p fuel b := (hS_iff x).mp h2
      have hpm : p.f x ∈ getOrbit p fuel a ∨ p.f x ∈ getOrbit p fuel b :=
        hm.elim (fun h => Or.inl (getOrbit_closed_under_f p fuel a hca_p x h))
                (fun h => Or.inr (getOrbit_closed_under_f p fuel b hcb_p x h))
      rw [(hS_iff (p.f x)).mpr hpm] at h1; cases h1
    · have hpm : p.f x ∈ getOrbit p fuel a ∨ p.f x ∈ getOrbit p fuel b := (hS_iff (p.f x)).mp h1
      have hm : x ∈ getOrbit p fuel a ∨ x ∈ getOrbit p fuel b :=
        hpm.elim (fun h => Or.inl (by have := getOrbit_closed_under_inv p fuel a hca_p (p.f x) h; rwa [p.left_inv] at this))
                 (fun h => Or.inr (by have := getOrbit_closed_under_inv p fuel b hcb_p (p.f x) h; rwa [p.left_inv] at this))
      rw [(hS_iff x).mpr hm] at h2; cases h2
    · rfl
  have hS_q : ∀ x, S (q.f x) = S x := by
    intro x
    have ha_s : S a = true := (hS_iff a).mpr (Or.inl (mem_getOrbit_self p fuel a))
    have hb_s : S b = true := (hS_iff b).mpr (Or.inr (mem_getOrbit_self p fuel b))
    have hswap_s : ∀ y, S (swapFun a b y) = S y := by
      intro y
      by_cases hya : y = a
      · subst hya; simp [ha_s, hb_s]
      · by_cases hyb : y = b
        · subst hyb; simp [ha_s, hb_s]
        · rw [swapFun_of_ne hya hyb]
    dsimp [q, swapCompLeft]
    rw [hswap_s, hS_p]
  rw [countOrbits_partition_of_closed p fuel darts S hS_p,
      countOrbits_partition_of_closed q fuel darts S hS_q]
  have h_agree_out : ∀ x, (!S x) = true → p.f x = q.f x := by
    intro x hx
    have hnot : ¬ (x ∈ getOrbit p fuel a ∨ x ∈ getOrbit p fuel b) := by
      intro hm
      rw [(hS_iff x).mpr hm] at hx
      cases hx
    have hpx_not : ¬ (p.f x ∈ getOrbit p fuel a ∨ p.f x ∈ getOrbit p fuel b) := by
      intro hpm
      apply hnot
      exact hpm.elim (fun h => Or.inl (by have := getOrbit_closed_under_inv p fuel a hca_p (p.f x) h; rwa [p.left_inv] at this))
                     (fun h => Or.inr (by have := getOrbit_closed_under_inv p fuel b hcb_p (p.f x) h; rwa [p.left_inv] at this))
    have hne_a : p.f x ≠ a := fun heq => hpx_not (Or.inl (heq ▸ mem_getOrbit_self p fuel a))
    have hne_b : p.f x ≠ b := fun heq => hpx_not (Or.inr (heq ▸ mem_getOrbit_self p fuel b))
    dsimp [q, swapCompLeft]
    exact (swapFun_of_ne hne_a hne_b).symm
  have h_nS_p : ∀ x, (!S (p.f x)) = (!S x) := fun x => by rw [hS_p x]
  have h_out_eq : countOrbits q fuel (darts.filter (fun x => !S x)) =
      countOrbits p fuel (darts.filter (fun x => !S x)) := by
    symm
    apply countOrbits_eq_of_pred_getOrbit_eq p q fuel (fun x => !S x)
    · intro x hx
      exact getOrbit_eq_of_agree_on_closed p q (fun y => !S y) h_nS_p h_agree_out fuel hx
    · intro x hx
      exact (List.mem_filter.mp hx).2
  have h_in_q : countOrbits q fuel (darts.filter S) = 1 := by
    apply countOrbits_eq_one_of_all_mem_orbit q darts h_all h_le a
    · intro hnil
      have ha_in : a ∈ darts.filter S :=
        List.mem_filter.mpr ⟨h_all a, (hS_iff a).mpr (Or.inl (mem_getOrbit_self p fuel a))⟩
      rw [hnil] at ha_in
      cases ha_in
    · intro x hx
      rcases (hS_iff x).mp (List.mem_filter.mp hx).2 with hxa | hxb
      · exact h_pa_sub_qa x hxa
      · exact h_pb_sub_qa x hxb
  have h_in_p : countOrbits p fuel (darts.filter S) = 2 := by
    apply countOrbits_eq_two_of_two_orbits p darts h_all h_le a b h_ab
    · exact List.mem_filter.mpr ⟨h_all a, (hS_iff a).mpr (Or.inl (mem_getOrbit_self p fuel a))⟩
    · exact List.mem_filter.mpr ⟨h_all b, (hS_iff b).mpr (Or.inr (mem_getOrbit_self p fuel b))⟩
    · intro x hx
      exact (hS_iff x).mp (List.mem_filter.mp hx).2
  rw [h_in_q, h_in_p, h_out_eq]
  omega

/-- Membership in the merged `swapCompLeft p a b` orbit when `a, b` were in distinct `p`-orbits. -/
theorem mem_getOrbit_swapCompLeft_diff [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (h_ab : b ∉ getOrbit p fuel a) :
    b ∈ getOrbit (swapCompLeft p a b) fuel a := by
  have hab : a ≠ b := fun h_eq => h_ab (h_eq ▸ mem_getOrbit_self p fuel a)
  have h_darts_ne : darts ≠ [] := fun hnil => by have := h_all a; rw [hnil] at this; cases this
  have h_fuel : 1 ≤ fuel := by
    cases darts with
    | nil => exact False.elim (h_darts_ne rfl)
    | cons _ _ => dsimp at h_le; omega
  let q := swapCompLeft p a b
  have hca_p : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  have hca_q : orbitClosesWithin q a a fuel :=
    orbitClosesWithin_mono q a a (orbitClosesWithin_of_complete q darts h_all a) h_le
  let La := (getOrbit p fuel a).length
  have hLa_per : Perm.iter p La a = a := perm_iter_length_getOrbit_eq_self p fuel a hca_p
  have hLa_pos : 1 ≤ La := getOrbit_length_pos p h_fuel a
  have hq_a_pref : ∀ i ≤ La - 1, Perm.iter q i a = Perm.iter p i a := by
    intro i hi
    apply swapCompLeft_iter_prefix p a b i a
    intro t ht
    have ht1_lt : t + 1 < La := by omega
    refine ⟨?_, ?_⟩
    · intro heq
      have := perm_iter_inj_of_lt_getOrbit_length p ht1_lt hLa_pos heq
      omega
    · intro heq
      exact h_ab (heq ▸ iter_mem_getOrbit_of_closes p fuel a hca_p (t + 1))
  have hq_a_to_b : Perm.iter q La a = b := by
    have h1 : La = (La - 1) + 1 := by omega
    rw [h1, Perm.iter_succ, hq_a_pref (La - 1) (Nat.le_refl _)]
    dsimp [q, swapCompLeft]
    have hp : p.f (Perm.iter p (La - 1) a) = a := by
      have : p.f (Perm.iter p (La - 1) a) = Perm.iter p La a := by rw [← Perm.iter_succ, ← h1]
      rw [this, hLa_per]
    rw [hp, swapFun_left]
  have h_mem := iter_mem_getOrbit_of_closes q fuel a hca_q La
  rwa [hq_a_to_b] at h_mem

/-- **Orbit Split Theorem (`swapCompRight`, same orbit)**: -/
theorem countOrbits_swapCompRight_same [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (hab : a ≠ b) (hb : b ∈ getOrbit p fuel a) :
    countOrbits (swapCompRight p a b) fuel darts = countOrbits p fuel darts + 1 := by
  have hca_p : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  have hb_symm : b ∈ getOrbit p.symm fuel a := (mem_getOrbit_symm_perm_iff p fuel a b hca_p).mpr hb
  have h1 := countOrbits_symm_of_complete (swapCompRight p a b) darts darts h_all h_le
  rw [swapCompRight_symm] at h1
  rw [← h1]
  rw [countOrbits_swapCompLeft_same p.symm darts h_all h_le hab hb_symm]
  rw [countOrbits_symm_of_complete p darts darts h_all h_le]

/-- **Orbit Merge Theorem (`swapCompRight`, distinct orbits)**: -/
theorem countOrbits_swapCompRight_diff [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (h_ab : b ∉ getOrbit p fuel a) :
    countOrbits (swapCompRight p a b) fuel darts + 1 = countOrbits p fuel darts := by
  have hca_p : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  have h_ab_symm : b ∉ getOrbit p.symm fuel a := fun hm =>
    h_ab ((mem_getOrbit_symm_perm_iff p fuel a b hca_p).mp hm)
  have h1 := countOrbits_symm_of_complete (swapCompRight p a b) darts darts h_all h_le
  rw [swapCompRight_symm] at h1
  rw [← h1]
  have h_m := countOrbits_swapCompLeft_diff p.symm darts h_all h_le h_ab_symm
  rwa [countOrbits_symm_of_complete p darts darts h_all h_le] at h_m

/-- When `b ∉ getOrbit p fuel a`, `a` and `b` are merged into the same orbit of `swapCompRight p a b`. -/
theorem mem_getOrbit_swapCompRight_diff [DecidableEq D] (p : Perm D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    {a b : D} (h_ab : b ∉ getOrbit p fuel a) :
    b ∈ getOrbit (swapCompRight p a b) fuel a := by
  have hca_p : orbitClosesWithin p a a fuel :=
    orbitClosesWithin_mono p a a (orbitClosesWithin_of_complete p darts h_all a) h_le
  have hca_q : orbitClosesWithin (swapCompRight p a b) a a fuel :=
    orbitClosesWithin_mono (swapCompRight p a b) a a
      (orbitClosesWithin_of_complete (swapCompRight p a b) darts h_all a) h_le
  have h_ab_symm : b ∉ getOrbit p.symm fuel a := fun hm =>
    h_ab ((mem_getOrbit_symm_perm_iff p fuel a b hca_p).mp hm)
  have hm := mem_getOrbit_swapCompLeft_diff p.symm darts h_all h_le h_ab_symm
  rw [← swapCompRight_symm] at hm
  exact (mem_getOrbit_symm_perm_iff (swapCompRight p a b) fuel a b hca_q).mp hm

end OrbitSplitMerge

section PermTripleAndWalkEN

/-- Generalized hypermap triple dropping `e² = id` while keeping `e ∘ n ∘ f = id`. -/
structure PermTriple (D : Type) where
  e : Perm D
  n : Perm D
  f : Perm D
  enf_id : ∀ x : D, e.f (n.f (f.f x)) = x

/-- Embed any `Hypermap` as a `PermTriple H.Dart`. -/
def hypermapToTriple (H : Hypermap) : PermTriple H.Dart where
  e := H.edge
  n := H.node
  f := H.face
  enf_id := H.edge_node_face_id

/-- Cyclic rotation `(e, n, f) ↦ (n, f, e)` of a permutation triple. -/
def PermTriple.rot {D : Type} (T : PermTriple D) : PermTriple D where
  e := T.n
  n := T.f
  f := T.e
  enf_id := fun x => by
    have h := T.enf_id (T.e.f x)
    have hi := congrArg T.e.inv h
    rwa [T.e.left_inv, T.e.left_inv] at hi

theorem PermTriple.f_eq_n_inv_e_inv {D : Type} (T : PermTriple D) (x : D) :
    T.f.f x = T.n.inv (T.e.inv x) := by
  have h := T.enf_id x
  have h1 := congrArg T.e.inv h
  rw [T.e.left_inv] at h1
  have h2 := congrArg T.n.inv h1
  rwa [T.n.left_inv] at h2

theorem PermTriple.f_inv_eq_e_n {D : Type} (T : PermTriple D) (x : D) :
    T.f.inv x = T.e.f (T.n.f x) := by
  have h := T.enf_id (T.f.inv x)
  rw [T.f.right_inv] at h
  exact h.symm

/-- Single `(e, n)`-walk step generated by `e, e⁻¹, n, n⁻¹`. -/
inductive StepEN {D : Type} (e n : Perm D) : D → D → Type
  | e_fwd (x : D) : StepEN e n x (e.f x)
  | e_bwd (x : D) : StepEN e n x (e.inv x)
  | n_fwd (x : D) : StepEN e n x (n.f x)
  | n_bwd (x : D) : StepEN e n x (n.inv x)

/-- Walks along `(e, e⁻¹, n, n⁻¹)`. -/
inductive WalkEN {D : Type} (e n : Perm D) : D → D → Type
  | refl (x : D) : WalkEN e n x x
  | step {x y z : D} (s : StepEN e n x y) (w : WalkEN e n y z) : WalkEN e n x z

def StepEN.symm {D : Type} (e n : Perm D) : {x y : D} → StepEN e n x y → StepEN e n y x
  | x, _, StepEN.e_fwd _ => by
      have h : StepEN e n (e.f x) (e.inv (e.f x)) := StepEN.e_bwd (e.f x)
      rwa [e.left_inv x] at h
  | x, _, StepEN.e_bwd _ => by
      have h : StepEN e n (e.inv x) (e.f (e.inv x)) := StepEN.e_fwd (e.inv x)
      rwa [e.right_inv x] at h
  | x, _, StepEN.n_fwd _ => by
      have h : StepEN e n (n.f x) (n.inv (n.f x)) := StepEN.n_bwd (n.f x)
      rwa [n.left_inv x] at h
  | x, _, StepEN.n_bwd _ => by
      have h : StepEN e n (n.inv x) (n.f (n.inv x)) := StepEN.n_fwd (n.inv x)
      rwa [n.right_inv x] at h

def WalkEN.trans {D : Type} (e n : Perm D) : {x y z : D} → WalkEN e n x y → WalkEN e n y z → WalkEN e n x z
  | _, _, _, WalkEN.refl _, w2 => w2
  | _, _, _, WalkEN.step s w1, w2 => WalkEN.step s (WalkEN.trans e n w1 w2)

def WalkEN.snoc {D : Type} (e n : Perm D) {x y z : D} (w : WalkEN e n x y) (s : StepEN e n y z) : WalkEN e n x z :=
  WalkEN.trans e n w (WalkEN.step s (WalkEN.refl z))

def WalkEN.symm {D : Type} (e n : Perm D) : {x y : D} → WalkEN e n x y → WalkEN e n y x
  | _, _, WalkEN.refl x => WalkEN.refl x
  | _, _, WalkEN.step s w => WalkEN.snoc e n (WalkEN.symm e n w) (StepEN.symm e n s)

end PermTripleAndWalkEN

section RelClassesAndEquiv

variable {D : Type}

/-- Filter equivalence on lists when predicates agree on all list members. -/
theorem filter_ext_of_mem {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.filter p = l.filter q
  | [], _ => rfl
  | x :: xs, h => by
    have hx : p x = q x := h x List.mem_cons_self
    have hxs := filter_ext_of_mem p q xs (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.filter]
    rw [hx]
    cases q x <;> simp [hxs]

private def countRelClassesAux (R : D → D → Prop) [DecidableRel R] : Nat → List D → Nat
  | 0, _ => 0
  | _, [] => 0
  | fuel + 1, d :: ds => 1 + countRelClassesAux R fuel (ds.filter (fun x => !decide (R d x)))

private theorem countRelClassesAux_eq_of_le (R : D → D → Prop) [DecidableRel R] :
    ∀ (m n : Nat) (l : List D), l.length ≤ m → l.length ≤ n →
      countRelClassesAux R m l = countRelClassesAux R n l
  | 0, 0, [], _, _ => rfl
  | 0, _ + 1, [], _, _ => rfl
  | _ + 1, 0, [], _, _ => rfl
  | _ + 1, _ + 1, [], _, _ => rfl
  | 0, _, _ :: _, hm, _ => by dsimp at hm; omega
  | _, 0, _ :: _, _, hn => by dsimp at hn; omega
  | m + 1, n + 1, d :: ds, hm, hn => by
    dsimp [countRelClassesAux]
    congr 1
    have hflt := List.length_filter_le (fun x => !decide (R d x)) ds
    exact countRelClassesAux_eq_of_le R m n _ (by dsimp at hm; omega) (by dsimp at hn; omega)

/-- Count distinct `R`-equivalence classes represented in `l`. -/
def countRelClasses (R : D → D → Prop) [DecidableRel R] (l : List D) : Nat :=
  countRelClassesAux R l.length l

theorem countRelClasses_nil (R : D → D → Prop) [DecidableRel R] :
    countRelClasses R [] = 0 := rfl

theorem countRelClasses_cons (R : D → D → Prop) [DecidableRel R] (d : D) (ds : List D) :
    countRelClasses R (d :: ds) =
      1 + countRelClasses R (ds.filter (fun x => !decide (R d x))) := by
  dsimp [countRelClasses, countRelClassesAux]
  congr 1
  exact countRelClassesAux_eq_of_le R ds.length (ds.filter (fun x => !decide (R d x))).length _
    (List.length_filter_le _ ds) (Nat.le_refl _)

theorem countRelClasses_le_length (R : D → D → Prop) [DecidableRel R] :
    ∀ (n : Nat) (l : List D), l.length ≤ n → countRelClasses R l ≤ l.length
  | 0, l, h => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    subst hnil; rw [countRelClasses_nil]; omega
  | _ + 1, [], _ => by rw [countRelClasses_nil]; omega
  | n + 1, d :: ds, h => by
    rw [countRelClasses_cons]
    have h1 := List.length_filter_le (fun x => !decide (R d x)) ds
    have h2 := countRelClasses_le_length R n (ds.filter (fun x => !decide (R d x))) (by dsimp at h; omega)
    dsimp at *; omega

private theorem countRelClasses_partition_aux (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    (S : D → Bool) (hS : ∀ {x y}, R x y → S x = S y) :
    ∀ (n : Nat) (l : List D), l.length ≤ n →
      countRelClasses R l = countRelClasses R (l.filter S) + countRelClasses R (l.filter (fun x => !S x))
  | 0, l, h => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    subst hnil; simp [countRelClasses_nil]
  | _ + 1, [], _ => by simp [countRelClasses_nil]
  | n + 1, d :: ds, h => by
    have hlen : ds.length ≤ n := by dsimp at h; omega
    let ds' := ds.filter (fun x => !decide (R d x))
    have hds'_len : ds'.length ≤ n := Nat.le_trans (List.length_filter_le _ ds) hlen
    have h_ih := countRelClasses_partition_aux R h_refl h_symm h_trans S hS n ds' hds'_len
    have h_main := countRelClasses_cons R d ds
    cases hSd : S d with
    | true =>
      have h_f1 : (d :: ds).filter S = d :: ds.filter S := by dsimp [List.filter]; rw [hSd]
      have h_f2 : (d :: ds).filter (fun x => !S x) = ds.filter (fun x => !S x) := by
        dsimp [List.filter]; rw [hSd]; rfl
      have h_c1 := countRelClasses_cons R d (ds.filter S)
      have h_comm : (ds.filter S).filter (fun x => !decide (R d x)) = ds'.filter S :=
        filter_comm S (fun x => !decide (R d x)) ds
      have h_keep : ds'.filter (fun x => !S x) = ds.filter (fun x => !S x) := by
        dsimp [ds']
        rw [filter_comm]
        apply filter_filter_eq_of_imp
        intro x _ hnx
        have hSx : S x = false := by cases hx : S x <;> simp_all
        by_cases hR : R d x
        · have h_eq := hS hR; rw [hSd, hSx] at h_eq; cases h_eq
        · simp [hR]
      rw [h_main, h_f1, h_f2, h_c1, h_comm, ← h_keep, h_ih]
      omega
    | false =>
      have h_f1 : (d :: ds).filter S = ds.filter S := by dsimp [List.filter]; rw [hSd]
      have h_f2 : (d :: ds).filter (fun x => !S x) = d :: ds.filter (fun x => !S x) := by
        dsimp [List.filter]; rw [hSd]; rfl
      have h_c2 := countRelClasses_cons R d (ds.filter (fun x => !S x))
      have h_comm : (ds.filter (fun x => !S x)).filter (fun x => !decide (R d x)) = ds'.filter (fun x => !S x) :=
        filter_comm (fun x => !S x) (fun x => !decide (R d x)) ds
      have h_keep : ds'.filter S = ds.filter S := by
        dsimp [ds']
        rw [filter_comm]
        apply filter_filter_eq_of_imp
        intro x _ hSx
        by_cases hR : R d x
        · have h_eq := hS hR; rw [hSd, hSx] at h_eq; cases h_eq
        · simp [hR]
      rw [h_main, h_f1, h_f2, h_c2, h_comm, ← h_keep, h_ih]
      omega

theorem countRelClasses_partition_of_closed (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    (S : D → Bool) (hS : ∀ {x y}, R x y → S x = S y) (l : List D) :
    countRelClasses R l = countRelClasses R (l.filter S) + countRelClasses R (l.filter (fun x => !S x)) :=
  countRelClasses_partition_aux R h_refl h_symm h_trans S hS l.length l (Nat.le_refl _)

theorem countRelClasses_eq_one_of_forall (R : D → D → Prop) [DecidableRel R]
    (a : D) (h_all : ∀ x ∈ l, R a x) (hne : l ≠ [])
    (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z) :
    countRelClasses R l = 1 := by
  cases l with
  | nil => exact False.elim (hne rfl)
  | cons d ds =>
    rw [countRelClasses_cons]
    have hda : R d a := h_symm (h_all d List.mem_cons_self)
    have h_flt : ds.filter (fun x => !decide (R d x)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have hdx : R d x := h_trans hda (h_all x (List.mem_cons_of_mem d hx))
      simp [hdx]
    rw [h_flt, countRelClasses_nil]

theorem countRelClasses_eq_one_add_filter_of_mem (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    (l : List D) (a : D) (ha : a ∈ l) :
    countRelClasses R l = 1 + countRelClasses R (l.filter (fun x => !decide (R a x))) := by
  let S : D → Bool := fun x => decide (R a x)
  have hS : ∀ {x y}, R x y → S x = S y := by
    intro x y hxy
    dsimp [S]
    by_cases hx : R a x
    · simp [hx, h_trans hx hxy]
    · have hy : ¬R a y := fun hy => hx (h_trans hy (h_symm hxy))
      simp [hx, hy]
  rw [countRelClasses_partition_of_closed R h_refl h_symm h_trans S hS l]
  have h_ne : l.filter S ≠ [] := by
    intro hnil
    have ha_flt : a ∈ l.filter S := List.mem_filter.mpr ⟨ha, by simp [S, h_refl a]⟩
    rw [hnil] at ha_flt
    cases ha_flt
  have h_one := countRelClasses_eq_one_of_forall R a
    (fun x hx => by simpa [S] using (List.mem_filter.mp hx).2) h_ne h_symm h_trans
  rw [h_one]

private theorem countRelClasses_eq_of_iff_mem_aux (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z) :
    ∀ (n : Nat) (l1 l2 : List D), l1.length ≤ n → (∀ x, x ∈ l1 ↔ x ∈ l2) →
      countRelClasses R l1 = countRelClasses R l2
  | 0, l1, l2, hlen, hiff => by
    have h1 : l1 = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    subst h1
    have h2 : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons y _ => exact False.elim (by simpa using (hiff y).mpr List.mem_cons_self)
    subst h2; rfl
  | _ + 1, [], l2, _, hiff => by
    have h2 : l2 = [] := by
      cases l2 with
      | nil => rfl
      | cons y _ => exact False.elim (by simpa using (hiff y).mpr List.mem_cons_self)
    subst h2; rfl
  | n + 1, a :: as, l2, hlen, hiff => by
    have ha_l2 : a ∈ l2 := (hiff a).mp List.mem_cons_self
    rw [countRelClasses_cons, countRelClasses_eq_one_add_filter_of_mem R h_refl h_symm h_trans l2 a ha_l2]
    congr 1
    let as' := as.filter (fun x => !decide (R a x))
    let l2' := l2.filter (fun x => !decide (R a x))
    have has'_len : as'.length ≤ n := by
      have h_le := List.length_filter_le (fun x => !decide (R a x)) as
      dsimp [as'] at h_le ⊢; dsimp at hlen; omega
    have hiff' : ∀ x, x ∈ as' ↔ x ∈ l2' := by
      intro x
      dsimp [as', l2']
      rw [List.mem_filter, List.mem_filter]
      constructor
      · intro ⟨hxa, hnc⟩; exact ⟨(hiff x).mp (List.mem_cons_of_mem a hxa), hnc⟩
      · intro ⟨hxl2, hnc⟩
        have hne : x ≠ a := by
          intro h_eq; subst h_eq; simp [h_refl x] at hnc
        rcases List.mem_cons.mp ((hiff x).mpr hxl2) with rfl | hxa
        · exact False.elim (hne rfl)
        · exact ⟨hxa, hnc⟩
    exact countRelClasses_eq_of_iff_mem_aux R h_refl h_symm h_trans n as' l2' has'_len hiff'

theorem countRelClasses_eq_of_iff_mem (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    (l1 l2 : List D) (hiff : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    countRelClasses R l1 = countRelClasses R l2 :=
  countRelClasses_eq_of_iff_mem_aux R h_refl h_symm h_trans l1.length l1 l2 (Nat.le_refl _) hiff

theorem countRelClasses_eq_of_rel_iff_on_mem (R1 R2 : D → D → Prop) [DecidableRel R1] [DecidableRel R2] :
    ∀ (n : Nat) (l : List D), l.length ≤ n → (∀ x ∈ l, ∀ y ∈ l, R1 x y ↔ R2 x y) →
      countRelClasses R1 l = countRelClasses R2 l
  | 0, l, h, _ => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    subst hnil; simp [countRelClasses_nil]
  | _ + 1, [], _, _ => by simp [countRelClasses_nil]
  | n + 1, d :: ds, h, h_iff => by
    rw [countRelClasses_cons, countRelClasses_cons]
    have h_flt : ds.filter (fun x => !decide (R1 d x)) = ds.filter (fun x => !decide (R2 d x)) := by
      apply filter_ext_of_mem
      intro x hx
      have h12 := h_iff d List.mem_cons_self x (List.mem_cons_of_mem d hx)
      by_cases h1 : R1 d x
      · have h2 : R2 d x := h12.mp h1; simp [h1, h2]
      · have h2 : ¬R2 d x := fun h2 => h1 (h12.mpr h2); simp [h1, h2]
    rw [h_flt]
    congr 1
    exact countRelClasses_eq_of_rel_iff_on_mem R1 R2 n _
      (Nat.le_trans (List.length_filter_le _ ds) (by dsimp at h; omega))
      (fun x hx y hy =>
        h_iff x (List.mem_cons_of_mem d (List.mem_filter.mp hx).1)
              y (List.mem_cons_of_mem d (List.mem_filter.mp hy).1))

theorem countRelClasses_eq_of_rel_iff (R1 R2 : D → D → Prop) [DecidableRel R1] [DecidableRel R2]
    (h_iff : ∀ x y : D, R1 x y ↔ R2 x y) :
    ∀ (n : Nat) (l : List D), l.length ≤ n → countRelClasses R1 l = countRelClasses R2 l :=
  fun n l hlen => countRelClasses_eq_of_rel_iff_on_mem R1 R2 n l hlen (fun x _ y _ => h_iff x y)

theorem countRelClasses_eq_two_of_two_classes (R : D → D → Prop) [DecidableRel R]
    (h_refl : ∀ x, R x x) (h_symm : ∀ {x y}, R x y → R y x) (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    (a b : D) (hab : ¬R a b) (l : List D) (ha : a ∈ l) (hb : b ∈ l)
    (h_sub : ∀ x ∈ l, R a x ∨ R b x) :
    countRelClasses R l = 2 := by
  rw [countRelClasses_eq_one_add_filter_of_mem R h_refl h_symm h_trans l a ha]
  let l' := l.filter (fun x => !decide (R a x))
  have hb' : b ∈ l' := List.mem_filter.mpr ⟨hb, by simp [hab]⟩
  have hne' : l' ≠ [] := fun hnil => by rw [hnil] at hb'; cases hb'
  have h_one := countRelClasses_eq_one_of_forall R b
    (fun x hx => by
      have hm := List.mem_filter.mp hx
      rcases h_sub x hm.1 with hax | hbx
      · simp [hax] at hm
      · exact hbx)
    hne' h_symm h_trans
  dsimp [l'] at h_one
  rw [h_one]

/-- Equivalence relation generated by `WalkEN e n`. -/
def ReachEN {D : Type} (e n : Perm D) (x y : D) : Prop :=
  Nonempty (WalkEN e n x y)

noncomputable instance instDecidableRelReachEN {D : Type} (e n : Perm D) : DecidableRel (ReachEN e n) :=
  fun _ _ => Classical.propDecidable _

theorem reachEN_refl {D : Type} (e n : Perm D) (x : D) : ReachEN e n x x :=
  ⟨WalkEN.refl x⟩

theorem reachEN_symm {D : Type} (e n : Perm D) {x y : D} (h : ReachEN e n x y) : ReachEN e n y x := by
  obtain ⟨w⟩ := h
  exact ⟨WalkEN.symm e n w⟩

theorem reachEN_trans {D : Type} (e n : Perm D) {x y z : D}
    (h1 : ReachEN e n x y) (h2 : ReachEN e n y z) : ReachEN e n x z := by
  obtain ⟨w1⟩ := h1
  obtain ⟨w2⟩ := h2
  exact ⟨WalkEN.trans e n w1 w2⟩

/-- Walk along `WalkEN e n` matching any permutation iteration whose 1-step action lies in `WalkEN`. -/
def walkEN_of_permIter {D : Type} (e n p : Perm D) (h_step : ∀ u : D, WalkEN e n u (p.f u)) :
    ∀ (k : Nat) (d : D), WalkEN e n d (Perm.iter p k d)
  | 0, d => WalkEN.refl d
  | k + 1, d => WalkEN.trans e n (h_step d) (by
      have h_eq : Perm.iter p (k + 1) d = Perm.iter p k (p.f d) := by
        have := Perm.iter_add p k 1 d
        simpa [Perm.iter] using this
      rw [h_eq]
      exact walkEN_of_permIter e n p h_step k (p.f d))

theorem reachEN_rot {D : Type} (T : PermTriple D) (x y : D) :
    ReachEN T.e T.n x y ↔ ReachEN T.n T.f x y := by
  have h_en_nf : ∀ {u v : D}, StepEN T.e T.n u v → WalkEN T.n T.f u v := by
    intro u v s
    cases s with
    | e_fwd =>
      have h_inv : T.e.f u = T.f.inv (T.n.inv u) := by
        have h := T.enf_id (T.f.inv (T.n.inv u))
        rw [T.f.right_inv, T.n.right_inv] at h
        exact h
      rw [h_inv]
      exact WalkEN.step (StepEN.e_bwd u) (WalkEN.step (StepEN.n_bwd (T.n.inv u)) (WalkEN.refl _))
    | e_bwd =>
      have h_inv : T.e.inv u = T.n.f (T.f.f u) := by
        have h := T.enf_id u
        have h1 := congrArg T.e.inv h
        rw [T.e.left_inv] at h1
        exact h1.symm
      rw [h_inv]
      exact WalkEN.step (StepEN.n_fwd u) (WalkEN.step (StepEN.e_fwd (T.f.f u)) (WalkEN.refl _))
    | n_fwd => exact WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)
    | n_bwd => exact WalkEN.step (StepEN.e_bwd u) (WalkEN.refl _)
  have h_nf_en : ∀ {u v : D}, StepEN T.n T.f u v → WalkEN T.e T.n u v := by
    intro u v s
    cases s with
    | e_fwd => exact WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)
    | e_bwd => exact WalkEN.step (StepEN.n_bwd u) (WalkEN.refl _)
    | n_fwd =>
      rw [T.f_eq_n_inv_e_inv u]
      exact WalkEN.step (StepEN.e_bwd u) (WalkEN.step (StepEN.n_bwd (T.e.inv u)) (WalkEN.refl _))
    | n_bwd =>
      rw [T.f_inv_eq_e_n u]
      exact WalkEN.step (StepEN.n_fwd u) (WalkEN.step (StepEN.e_fwd (T.n.f u)) (WalkEN.refl _))
  have walk_en_nf : ∀ {u v : D}, WalkEN T.e T.n u v → WalkEN T.n T.f u v := by
    intro u v w
    induction w with
    | refl z => exact WalkEN.refl z
    | step s _ ih => exact WalkEN.trans T.n T.f (h_en_nf s) ih
  have walk_nf_en : ∀ {u v : D}, WalkEN T.n T.f u v → WalkEN T.e T.n u v := by
    intro u v w
    induction w with
    | refl z => exact WalkEN.refl z
    | step s _ ih => exact WalkEN.trans T.e T.n (h_nf_en s) ih
  constructor
  · rintro ⟨w⟩; exact ⟨walk_en_nf w⟩
  · rintro ⟨w⟩; exact ⟨walk_nf_en w⟩

theorem reachEN_hypermap_iff_walk (H : Hypermap) (x y : H.Dart) :
    ReachEN H.edge H.node x y ↔ Nonempty (Walk H x y) := by
  have step_en_h : ∀ {u v : H.Dart}, StepEN H.edge H.node u v → Walk H u v := by
    intro u v s
    cases s with
    | e_fwd => exact Walk.step (Step.edge rfl) (Walk.refl _)
    | e_bwd =>
      rw [H.edge_inv_eq_edge]
      exact Walk.step (Step.edge rfl) (Walk.refl _)
    | n_fwd => exact Walk.step (Step.node rfl) (Walk.refl _)
    | n_bwd => exact Walk.step (Step.nodeInv rfl) (Walk.refl _)
  have step_h_en : ∀ {u v : H.Dart}, Step H u v → ReachEN H.edge H.node u v := by
    intro u v s
    cases s with
    | node h => subst h; exact ⟨WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)⟩
    | nodeInv h => subst h; exact ⟨WalkEN.step (StepEN.n_bwd u) (WalkEN.refl _)⟩
    | edge h => subst h; exact ⟨WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)⟩
    | face h =>
      subst h
      have hf := (hypermapToTriple H).f_eq_n_inv_e_inv u
      dsimp [hypermapToTriple] at hf
      rw [hf]
      exact ⟨WalkEN.step (StepEN.e_bwd u) (WalkEN.step (StepEN.n_bwd (H.edge.inv u)) (WalkEN.refl _))⟩
    | faceInv h =>
      subst h
      have hf := (hypermapToTriple H).f_inv_eq_e_n u
      dsimp [hypermapToTriple] at hf
      rw [hf]
      exact ⟨WalkEN.step (StepEN.n_fwd u) (WalkEN.step (StepEN.e_fwd (H.node.f u)) (WalkEN.refl _))⟩
  constructor
  · rintro ⟨w⟩
    induction w with
    | refl z => exact ⟨Walk.refl z⟩
    | step s _ ih =>
      obtain ⟨wi⟩ := ih
      exact ⟨Walk.trans H (step_en_h s) wi⟩
  · rintro ⟨w⟩
    induction w with
    | refl z => exact reachEN_refl _ _ z
    | step s _ ih => exact reachEN_trans _ _ (step_h_en s) ih

theorem countRelClasses_reachEN_eq_countComponents_aux (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    ∀ (n : Nat) (l : List H.Dart), l.length ≤ n →
      countRelClasses (ReachEN H.edge H.node) l = H.countComponents fuel l
  | 0, l, h => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    subst hnil; simp [countRelClasses_nil, countComponents, countComponentsAux]
  | _ + 1, [], _ => by simp [countRelClasses_nil, countComponents, countComponentsAux]
  | n + 1, d :: ds, h => by
    rw [countRelClasses_cons, countComponents_cons]
    have h_flt : ds.filter (fun x => !decide (ReachEN H.edge H.node d x)) =
        ds.filter (fun x => !((H.getComponent fuel d).contains x)) := by
      apply filter_ext_of_mem
      intro x _
      have h_iff : ReachEN H.edge H.node d x ↔ (H.getComponent fuel d).contains x = true := by
        rw [reachEN_hypermap_iff_walk, List.contains_iff_mem, mem_getComponent_iff_walk H darts h_all h_le]
      cases hc : (H.getComponent fuel d).contains x with
      | true => have hR := h_iff.mpr hc; simp [hR]
      | false =>
        have hR : ¬ReachEN H.edge H.node d x := fun h => by rw [h_iff.mp h] at hc; cases hc
        simp [hR]
    rw [h_flt]
    congr 1
    exact countRelClasses_reachEN_eq_countComponents_aux H darts h_all h_le n _
      (Nat.le_trans (filter_length_le _ ds) (by dsimp at h; omega))

theorem countRelClasses_reachEN_eq_countComponents (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (l : List H.Dart) :
    countRelClasses (ReachEN H.edge H.node) l = H.countComponents fuel l :=
  countRelClasses_reachEN_eq_countComponents_aux H darts h_all h_le l.length l (Nat.le_refl _)

private theorem walkEN_imp_permIter_of_edge_id {D : Type} [DecidableEq D]
    (e n : Perm D) (he : ∀ x : D, e.f x = x)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    ∀ {u v : D}, WalkEN e n u v → ∃ m : Nat, v = Perm.iter n m u
  | u, _, WalkEN.refl _ => ⟨0, rfl⟩
  | u, _, WalkEN.step s w => by
    obtain ⟨m, hm⟩ := walkEN_imp_permIter_of_edge_id e n he darts h_all h_le w
    cases s with
    | e_fwd => rw [he u] at hm; exact ⟨m, hm⟩
    | e_bwd =>
      have hinv : e.inv u = u := (by have := he (e.inv u); rwa [e.right_inv] at this : u = e.inv u).symm
      rw [hinv] at hm; exact ⟨m, hm⟩
    | n_fwd =>
      refine ⟨m + 1, ?_⟩
      rw [hm, Perm.iter_add]
      rfl
    | n_bwd =>
      have hcu : orbitClosesWithin n u u fuel :=
        orbitClosesWithin_mono n u u (orbitClosesWithin_of_complete n darts h_all u) h_le
      let L := (getOrbit n fuel u).length
      have h_fuel : 1 ≤ fuel := by
        cases darts with
        | nil => have := h_all u; cases this
        | cons _ _ => dsimp at h_le; omega
      have hL_pos : 1 ≤ L := getOrbit_length_pos n h_fuel u
      have hL_per : Perm.iter n L u = u := perm_iter_length_getOrbit_eq_self n fuel u hcu
      have h_inv_iter : n.inv u = Perm.iter n (L - 1) u := by
        have h1 : L = (L - 1) + 1 := by omega
        have hpf : n.f (Perm.iter n (L - 1) u) = u := by
          have : n.f (Perm.iter n (L - 1) u) = Perm.iter n L u := by rw [← Perm.iter_succ, ← h1]
          rw [this, hL_per]
        have := congrArg n.inv hpf
        rw [n.left_inv] at this
        exact this.symm
      rw [hm, h_inv_iter, ← Perm.iter_add]
      exact ⟨m + (L - 1), rfl⟩

theorem countRelClasses_reachEN_eq_countOrbits_of_edge_id_aux {D : Type} [DecidableEq D]
    (e n : Perm D) (he : ∀ x : D, e.f x = x)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    ∀ (k : Nat) (l : List D), l.length ≤ k →
      countRelClasses (ReachEN e n) l = countOrbits n fuel l
  | 0, l, h => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    subst hnil; simp [countRelClasses_nil, countOrbits, countOrbitsAux]
  | _ + 1, [], _ => by simp [countRelClasses_nil, countOrbits, countOrbitsAux]
  | k + 1, d :: ds, h => by
    rw [countRelClasses_cons, countOrbits_cons]
    have h_closes : orbitClosesWithin n d d fuel :=
      orbitClosesWithin_mono n d d (orbitClosesWithin_of_complete n darts h_all d) h_le
    have h_iff : ∀ x, ReachEN e n d x ↔ (getOrbit n fuel d).contains x = true := by
      intro x
      rw [List.contains_iff_mem, mem_getOrbit_iff_exists_iter n fuel d x h_closes]
      constructor
      · rintro ⟨w⟩; exact walkEN_imp_permIter_of_edge_id e n he darts h_all h_le w
      · rintro ⟨m, rfl⟩
        exact ⟨walkEN_of_permIter e n n (fun u => WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)) m d⟩
    have h_flt : ds.filter (fun x => !decide (ReachEN e n d x)) =
        ds.filter (fun x => !((getOrbit n fuel d).contains x)) := by
      apply filter_ext_of_mem
      intro x _
      cases hc : (getOrbit n fuel d).contains x with
      | true => have hR := (h_iff x).mpr hc; simp [hR]
      | false =>
        have hR : ¬ReachEN e n d x := fun h => by rw [(h_iff x).mp h] at hc; cases hc
        simp [hR]
    rw [h_flt]
    congr 1
    exact countRelClasses_reachEN_eq_countOrbits_of_edge_id_aux e n he darts h_all h_le k _
      (Nat.le_trans (filter_length_le _ ds) (by dsimp at h; omega))

theorem countRelClasses_reachEN_eq_countOrbits_of_edge_id {D : Type} [DecidableEq D]
    (e n : Perm D) (he : ∀ x : D, e.f x = x)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel)
    (l : List D) :
    countRelClasses (ReachEN e n) l = countOrbits n fuel l :=
  countRelClasses_reachEN_eq_countOrbits_of_edge_id_aux e n he darts h_all h_le l.length l (Nat.le_refl _)

end RelClassesAndEquiv

section GenusDeficitAndEulerInequality

/-- Combinatorial genus deficit `|D| + 2C - (V + E + F)` of a permutation triple. -/
noncomputable def genusDeficit {D : Type} [DecidableEq D] (T : PermTriple D) (fuel : Nat) (darts : List D) : Int :=
  (darts.length : Int) + 2 * (countRelClasses (ReachEN T.e T.n) darts : Int) -
    ((countOrbits T.n fuel darts : Int) + (countOrbits T.e fuel darts : Int) + (countOrbits T.f fuel darts : Int))

theorem genusDeficit_fuel_eq {D : Type} [DecidableEq D] (T : PermTriple D) (darts : List D)
    (h_all : ∀ x : D, x ∈ darts) {fuel1 fuel2 : Nat}
    (h1 : darts.length ≤ fuel1) (h2 : darts.length ≤ fuel2) :
    genusDeficit T fuel1 darts = genusDeficit T fuel2 darts := by
  dsimp [genusDeficit]
  rw [countOrbits_fuel_eq_of_complete T.n darts darts h_all h1,
      ← countOrbits_fuel_eq_of_complete T.n darts darts h_all h2,
      countOrbits_fuel_eq_of_complete T.e darts darts h_all h1,
      ← countOrbits_fuel_eq_of_complete T.e darts darts h_all h2,
      countOrbits_fuel_eq_of_complete T.f darts darts h_all h1,
      ← countOrbits_fuel_eq_of_complete T.f darts darts h_all h2]

theorem countOrbits_le_length {D : Type} [DecidableEq D] (p : Perm D) (fuel : Nat) :
    ∀ (n : Nat) (l : List D), l.length ≤ n → countOrbits p fuel l ≤ l.length
  | 0, l, h => by
    have hnil : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp h)
    subst hnil; simp [countOrbits, countOrbitsAux]
  | _ + 1, [], _ => by simp [countOrbits, countOrbitsAux]
  | n + 1, d :: ds, h => by
    rw [countOrbits_cons]
    have h_flt := filter_length_le (fun x => !((getOrbit p fuel d).contains x)) ds
    have h_ih := countOrbits_le_length p fuel n (ds.filter (fun x => !((getOrbit p fuel d).contains x)))
      (by dsimp at h; omega)
    dsimp at *
    omega

theorem countOrbits_eq_length_of_id {D : Type} [DecidableEq D] (p : Perm D)
    (hp : ∀ x : D, p.f x = x) {fuel : Nat} (h_fuel : 1 ≤ fuel) :
    ∀ (l : List D), l.Nodup → countOrbits p fuel l = l.length
  | [], _ => rfl
  | d :: ds, hnodup => by
    cases fuel with
    | zero => omega
    | succ f' =>
      rw [countOrbits_cons]
      have h_orb : getOrbit p (f' + 1) d = [d] := getOrbit_fixed_point p d f' (hp d)
      rw [h_orb]
      have hd_not : d ∉ ds := (List.nodup_cons.mp hnodup).1
      have h_flt : ds.filter (fun x => !([d].contains x)) = ds := by
        rw [List.filter_eq_self]
        intro x hx
        have hxd : x ≠ d := fun h => hd_not (h ▸ hx)
        cases hc : [d].contains x with
        | false => rfl
        | true =>
          have hm := List.contains_iff_mem.mp hc
          simp at hm
          exact False.elim (hxd hm)
      rw [h_flt, countOrbits_eq_length_of_id p hp h_fuel ds (List.nodup_cons.mp hnodup).2]
      simp only [List.length_cons]
      omega

theorem genusDeficit_rot {D : Type} [DecidableEq D] (T : PermTriple D) (fuel : Nat) (darts : List D) :
    genusDeficit T.rot fuel darts = genusDeficit T fuel darts := by
  dsimp [genusDeficit, PermTriple.rot]
  have hC : countRelClasses (ReachEN T.n T.f) darts = countRelClasses (ReachEN T.e T.n) darts :=
    countRelClasses_eq_of_rel_iff (ReachEN T.n T.f) (ReachEN T.e T.n)
      (fun x y => (reachEN_rot T x y).symm) darts.length darts (Nat.le_refl _)
  rw [hC]
  omega

/-- Uncouple an edge transition `(a, b)` in a permutation triple:
    `e₁ = swapCompLeft T.e a b`, `n₁ = T.n`, `f₁ = swapCompRight T.f a b`. -/
def uncoupleEdge {D : Type} [DecidableEq D] (T : PermTriple D) (a b : D) : PermTriple D where
  e := swapCompLeft T.e a b
  n := T.n
  f := swapCompRight T.f a b
  enf_id := fun x => by
    dsimp [swapCompLeft, swapCompRight]
    rw [T.enf_id (swapFun a b x), swapFun_invol]

/-- Disjunction describing reachability under `(e₁ = swapCompLeft e a b, n)` for any `(e, n)`-walk
    when `b = e.f a`. -/
def ReachOrBridge {D : Type} (e1 n : Perm D) (a b x y : D) : Prop :=
  ReachEN e1 n x y ∨ ((ReachEN e1 n x a ∧ ReachEN e1 n b y) ∨ (ReachEN e1 n x b ∧ ReachEN e1 n a y))

theorem reachOrBridge_trans {D : Type} (e1 n : Perm D) (a b : D) {x y z : D}
    (h1 : ReachOrBridge e1 n a b x y) (h2 : ReachOrBridge e1 n a b y z) :
    ReachOrBridge e1 n a b x z := by
  rcases h1 with hxy | ⟨⟨hxa, hby⟩ | ⟨hxb, hay⟩⟩
  · rcases h2 with hyz | ⟨⟨hya, hbz⟩ | ⟨hyb, haz⟩⟩
    · exact Or.inl (reachEN_trans e1 n hxy hyz)
    · exact Or.inr (Or.inl ⟨reachEN_trans e1 n hxy hya, hbz⟩)
    · exact Or.inr (Or.inr ⟨reachEN_trans e1 n hxy hyb, haz⟩)
  · rcases h2 with hyz | ⟨⟨hya, hbz⟩ | ⟨hyb, haz⟩⟩
    · exact Or.inr (Or.inl ⟨hxa, reachEN_trans e1 n hby hyz⟩)
    · have hba := reachEN_trans e1 n hby hya
      exact Or.inl (reachEN_trans e1 n hxa (reachEN_trans e1 n (reachEN_symm e1 n hba) hbz))
    · exact Or.inl (reachEN_trans e1 n hxa haz)
  · rcases h2 with hyz | ⟨⟨hya, hbz⟩ | ⟨hyb, haz⟩⟩
    · exact Or.inr (Or.inr ⟨hxb, reachEN_trans e1 n hay hyz⟩)
    · exact Or.inl (reachEN_trans e1 n hxb hbz)
    · have hab := reachEN_trans e1 n hay hyb
      exact Or.inl (reachEN_trans e1 n hxb (reachEN_trans e1 n (reachEN_symm e1 n hab) haz))

theorem stepEN_uncouple_split {D : Type} [DecidableEq D] (e n : Perm D) {a b u v : D}
    (hb : b = e.f a) (s : StepEN e n u v) :
    ReachOrBridge (swapCompLeft e a b) n a b u v := by
  let e1 := swapCompLeft e a b
  cases s with
  | n_fwd => exact Or.inl ⟨WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)⟩
  | n_bwd => exact Or.inl ⟨WalkEN.step (StepEN.n_bwd u) (WalkEN.refl _)⟩
  | e_fwd =>
    by_cases hua : u = a
    · have hvb : e.f u = b := by rw [hua, ← hb]
      rw [hvb, hua]
      exact Or.inr (Or.inl ⟨reachEN_refl _ _ _, reachEN_refl _ _ _⟩)
    · by_cases huinv : u = e.inv a
      · have hstep : e1.f u = b := by
          dsimp [e1, swapCompLeft]
          rw [huinv, e.right_inv, swapFun_left]
        have hv : e.f u = a := by rw [huinv, e.right_inv]
        have hw : WalkEN e1 n u (e1.f u) := WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)
        rw [hstep] at hw
        rw [hv]
        exact Or.inr (Or.inr ⟨⟨hw⟩, reachEN_refl _ _ _⟩)
      · have hne_b : e.f u ≠ b := fun h => by
          rw [hb] at h
          have hi := congrArg e.inv h
          rw [e.left_inv, e.left_inv] at hi
          exact hua hi
        have hne_a : e.f u ≠ a := fun h => by
          have hi := congrArg e.inv h
          rw [e.left_inv] at hi
          exact huinv hi
        have he1 : e1.f u = e.f u := by dsimp [e1, swapCompLeft]; exact swapFun_of_ne hne_a hne_b
        have hw : WalkEN e1 n u (e1.f u) := WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)
        rw [he1] at hw
        exact Or.inl ⟨hw⟩
  | e_bwd =>
    by_cases hub : u = b
    · have hv : e.inv u = a := by rw [hub, hb, e.left_inv]
      rw [hv, hub]
      exact Or.inr (Or.inr ⟨reachEN_refl _ _ _, reachEN_refl _ _ _⟩)
    · by_cases hua : u = a
      · have hstep : e1.inv b = e.inv a := by
          dsimp [e1, swapCompLeft]
          rw [swapFun_right]
        have hw : WalkEN e1 n b (e1.inv b) := WalkEN.step (StepEN.e_bwd b) (WalkEN.refl _)
        rw [hstep] at hw
        rw [hua]
        exact Or.inr (Or.inl ⟨reachEN_refl _ _ _, ⟨hw⟩⟩)
      · have he1 : e1.inv u = e.inv u := by dsimp [e1, swapCompLeft]; rw [swapFun_of_ne hua hub]
        have hw : WalkEN e1 n u (e1.inv u) := WalkEN.step (StepEN.e_bwd u) (WalkEN.refl _)
        rw [he1] at hw
        exact Or.inl ⟨hw⟩

theorem reachEN_uncouple_split {D : Type} [DecidableEq D] (e n : Perm D) {a b x y : D}
    (hb : b = e.f a) (h : ReachEN e n x y) :
    ReachOrBridge (swapCompLeft e a b) n a b x y := by
  have h_walk : ∀ {u v : D}, WalkEN e n u v → ReachOrBridge (swapCompLeft e a b) n a b u v := by
    intro u v w
    induction w with
    | refl z => exact Or.inl (reachEN_refl _ _ _)
    | step s _ ih => exact reachOrBridge_trans (swapCompLeft e a b) n a b (stepEN_uncouple_split e n hb s) ih
  obtain ⟨w⟩ := h
  exact h_walk w

theorem reachEN_uncouple_mono {D : Type} [DecidableEq D] (e n : Perm D) {a b x y : D}
    (hb : b = e.f a) (h : ReachEN (swapCompLeft e a b) n x y) :
    ReachEN e n x y := by
  have h_swap_walk : ∀ z : D, WalkEN e n z (swapFun a b z) := fun z => by
    by_cases hza : z = a
    · rw [hza, swapFun_left, hb]; exact WalkEN.step (StepEN.e_fwd a) (WalkEN.refl _)
    · by_cases hzb : z = b
      · have hw : WalkEN e n (e.f a) (e.inv (e.f a)) := WalkEN.step (StepEN.e_bwd (e.f a)) (WalkEN.refl _)
        rw [e.left_inv, ← hb] at hw
        rw [hzb, swapFun_right]
        exact hw
      · rw [swapFun_of_ne hza hzb]; exact WalkEN.refl z
  have h_step : ∀ {u v : D}, StepEN (swapCompLeft e a b) n u v → WalkEN e n u v := by
    intro u v s
    cases s with
    | n_fwd => exact WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)
    | n_bwd => exact WalkEN.step (StepEN.n_bwd u) (WalkEN.refl _)
    | e_fwd =>
      dsimp [swapCompLeft]
      exact WalkEN.step (StepEN.e_fwd u) (h_swap_walk (e.f u))
    | e_bwd =>
      dsimp [swapCompLeft]
      exact WalkEN.trans e n (h_swap_walk u) (WalkEN.step (StepEN.e_bwd (swapFun a b u)) (WalkEN.refl _))
  obtain ⟨w⟩ := h
  induction w with
  | refl z => exact reachEN_refl _ _ _
  | step s _ ih => exact reachEN_trans e n ⟨h_step s⟩ ih

/-- Uncoupling an edge weakly decreases genus deficit:
    `genusDeficit (uncoupleEdge T a (T.e.f a)) fuel darts ≤ genusDeficit T fuel darts`. -/
theorem genusDeficit_uncoupleEdge_le {D : Type} [DecidableEq D] (T : PermTriple D)
    (darts : List D) (h_all : ∀ x : D, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {a : D} (h_ne : T.e.f a ≠ a) :
    genusDeficit (uncoupleEdge T a (T.e.f a)) fuel darts ≤ genusDeficit T fuel darts := by
  let b := T.e.f a
  let T1 := uncoupleEdge T a b
  have hab : a ≠ b := fun h => h_ne h.symm
  have hb_orb : b ∈ getOrbit T.e fuel a := by
    have hca := orbitClosesWithin_mono T.e a a (orbitClosesWithin_of_complete T.e darts h_all a) h_le
    have h1 : b = Perm.iter T.e 1 a := rfl
    rw [h1]
    exact iter_mem_getOrbit_of_closes T.e fuel a hca 1
  have hE1 : countOrbits T1.e fuel darts = countOrbits T.e fuel darts + 1 :=
    countOrbits_swapCompLeft_same T.e darts h_all h_le hab hb_orb
  have hN1 : countOrbits T1.n fuel darts = countOrbits T.n fuel darts := rfl
  let S : D → Bool := fun x => decide (ReachEN T1.e T.n a x ∨ ReachEN T1.e T.n b x)
  have hS_iff : ∀ x, S x = true ↔ ReachEN T1.e T.n a x ∨ ReachEN T1.e T.n b x := by
    intro x; simp [S]
  have hS_T1 : ∀ {x y : D}, ReachEN T1.e T.n x y → S x = S y := by
    intro x y hxy
    by_cases hx : S x = true
    · have hy : ReachEN T1.e T.n a y ∨ ReachEN T1.e T.n b y :=
        ((hS_iff x).mp hx).elim (fun h => Or.inl (reachEN_trans _ _ h hxy))
                                (fun h => Or.inr (reachEN_trans _ _ h hxy))
      rw [hx, (hS_iff y).mpr hy]
    · have hfx : S x = false := by cases h : S x <;> simp_all
      have hfy : S y = false := by
        cases hy : S y
        · rfl
        · have hx' : ReachEN T1.e T.n a x ∨ ReachEN T1.e T.n b x :=
            ((hS_iff y).mp hy).elim (fun h => Or.inl (reachEN_trans _ _ h (reachEN_symm _ _ hxy)))
                                    (fun h => Or.inr (reachEN_trans _ _ h (reachEN_symm _ _ hxy)))
          rw [(hS_iff x).mpr hx'] at hfx; cases hfx
      rw [hfx, hfy]
  have hS_T : ∀ {x y : D}, ReachEN T.e T.n x y → S x = S y := by
    intro x y hxy
    have hsplit := reachEN_uncouple_split T.e T.n (rfl : b = T.e.f a) hxy
    by_cases hx : S x = true
    · rcases hsplit with h_direct | ⟨⟨_, hby⟩ | ⟨_, hay⟩⟩
      · exact hS_T1 h_direct
      · rw [hx, (hS_iff y).mpr (Or.inr hby)]
      · rw [hx, (hS_iff y).mpr (Or.inl hay)]
    · have hfx : S x = false := by cases h : S x <;> simp_all
      have hsplit_rev := reachEN_uncouple_split T.e T.n (rfl : b = T.e.f a) (reachEN_symm T.e T.n hxy)
      have hfy : S y = false := by
        cases hy : S y
        · rfl
        · rcases hsplit_rev with h_direct | ⟨⟨_, hbx⟩ | ⟨_, hax⟩⟩
          · have heq := hS_T1 h_direct; rw [hy] at heq; rw [← heq] at hfx; cases hfx
          · rw [(hS_iff x).mpr (Or.inr hbx)] at hfx; cases hfx
          · rw [(hS_iff x).mpr (Or.inl hax)] at hfx; cases hfx
      rw [hfx, hfy]
  change genusDeficit T1 fuel darts ≤ genusDeficit T fuel darts
  dsimp [genusDeficit]
  change (darts.length : Int) + 2 * (countRelClasses (ReachEN T1.e T.n) darts : Int) -
      ((countOrbits T1.n fuel darts : Int) + (countOrbits T1.e fuel darts : Int) + (countOrbits T1.f fuel darts : Int)) ≤
    (darts.length : Int) + 2 * (countRelClasses (ReachEN T.e T.n) darts : Int) -
      ((countOrbits T.n fuel darts : Int) + (countOrbits T.e fuel darts : Int) + (countOrbits T.f fuel darts : Int))
  rw [countRelClasses_partition_of_closed (ReachEN T1.e T.n) (reachEN_refl _ _)
        (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS_T1 darts,
      countRelClasses_partition_of_closed (ReachEN T.e T.n) (reachEN_refl _ _)
        (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS_T darts]
  have h_out_eq : countRelClasses (ReachEN T1.e T.n) (darts.filter (fun x => !S x)) =
      countRelClasses (ReachEN T.e T.n) (darts.filter (fun x => !S x)) := by
    apply countRelClasses_eq_of_rel_iff_on_mem (ReachEN T1.e T.n) (ReachEN T.e T.n) _ _ (Nat.le_refl _)
    intro x hx y _
    have hSx : S x = false := by have := (List.mem_filter.mp hx).2; cases h : S x <;> simp_all
    have hx_not_a : ¬ReachEN T1.e T.n a x := fun hm => by
      rw [(hS_iff x).mpr (Or.inl hm)] at hSx; cases hSx
    have hx_not_b : ¬ReachEN T1.e T.n b x := fun hm => by
      rw [(hS_iff x).mpr (Or.inr hm)] at hSx; cases hSx
    constructor
    · exact reachEN_uncouple_mono T.e T.n (rfl : b = T.e.f a)
    · intro hxy
      rcases reachEN_uncouple_split T.e T.n (rfl : b = T.e.f a) hxy with hd | ⟨⟨hxa, _⟩ | ⟨hxb, _⟩⟩
      · exact hd
      · exact False.elim (hx_not_a (reachEN_symm _ _ hxa))
      · exact False.elim (hx_not_b (reachEN_symm _ _ hxb))
  have h_in_T : countRelClasses (ReachEN T.e T.n) (darts.filter S) = 1 := by
    apply countRelClasses_eq_one_of_forall (ReachEN T.e T.n) a
    · intro x hx
      rcases (hS_iff x).mp (List.mem_filter.mp hx).2 with hax | hbx
      · exact reachEN_uncouple_mono T.e T.n (rfl : b = T.e.f a) hax
      · exact reachEN_trans T.e T.n ⟨WalkEN.step (StepEN.e_fwd a) (WalkEN.refl _)⟩
          (reachEN_uncouple_mono T.e T.n (rfl : b = T.e.f a) hbx)
    · intro hnil
      have ha_in : a ∈ darts.filter S := List.mem_filter.mpr ⟨h_all a, (hS_iff a).mpr (Or.inl (reachEN_refl _ _ _))⟩
      rw [hnil] at ha_in; cases ha_in
    · exact fun h => reachEN_symm _ _ h
    · exact fun h1 h2 => reachEN_trans _ _ h1 h2
  by_cases h_ab_T1 : ReachEN T1.e T.n a b
  · have h_in_T1 : countRelClasses (ReachEN T1.e T.n) (darts.filter S) = 1 := by
      apply countRelClasses_eq_one_of_forall (ReachEN T1.e T.n) a
      · intro x hx
        rcases (hS_iff x).mp (List.mem_filter.mp hx).2 with hax | hbx
        · exact hax
        · exact reachEN_trans _ _ h_ab_T1 hbx
      · intro hnil
        have ha_in : a ∈ darts.filter S := List.mem_filter.mpr ⟨h_all a, (hS_iff a).mpr (Or.inl (reachEN_refl _ _ _))⟩
        rw [hnil] at ha_in; cases ha_in
      · exact fun h => reachEN_symm _ _ h
      · exact fun h1 h2 => reachEN_trans _ _ h1 h2
    by_cases h_ab_f : b ∈ getOrbit T.f fuel a
    · have hF1 : countOrbits T1.f fuel darts = countOrbits T.f fuel darts + 1 :=
        countOrbits_swapCompRight_same T.f darts h_all h_le hab h_ab_f
      rw [h_out_eq, h_in_T, h_in_T1, hE1, hN1, hF1]
      omega
    · have hF1 : countOrbits T1.f fuel darts + 1 = countOrbits T.f fuel darts :=
        countOrbits_swapCompRight_diff T.f darts h_all h_le h_ab_f
      rw [h_out_eq, h_in_T, h_in_T1, hE1, hN1]
      omega
  · have h_in_T1 : countRelClasses (ReachEN T1.e T.n) (darts.filter S) = 2 := by
      apply countRelClasses_eq_two_of_two_classes (ReachEN T1.e T.n) (reachEN_refl _ _)
        (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) a b h_ab_T1
      · exact List.mem_filter.mpr ⟨h_all a, (hS_iff a).mpr (Or.inl (reachEN_refl _ _ _))⟩
      · exact List.mem_filter.mpr ⟨h_all b, (hS_iff b).mpr (Or.inr (reachEN_refl _ _ _))⟩
      · intro x hx; exact (hS_iff x).mp (List.mem_filter.mp hx).2
    have h_ab_f : b ∈ getOrbit T.f fuel a := by
      by_cases hf : b ∈ getOrbit T.f fuel a
      · exact hf
      · exfalso
        have h_b_f1 : b ∈ getOrbit T1.f fuel a := mem_getOrbit_swapCompRight_diff T.f darts h_all h_le hf
        have h_ab_reach : ReachEN T1.e T1.n a b := by
          obtain ⟨k, _, hk⟩ := mem_getOrbit_imp_exists_iter T1.f fuel a b h_b_f1
          rw [hk]
          exact ⟨walkEN_of_permIter T1.e T1.n T1.f (fun u => by
            rw [T1.f_eq_n_inv_e_inv u]
            exact WalkEN.step (StepEN.e_bwd u) (WalkEN.step (StepEN.n_bwd (T1.e.inv u)) (WalkEN.refl _))) k a⟩
        exact h_ab_T1 h_ab_reach
    have hF1 : countOrbits T1.f fuel darts = countOrbits T.f fuel darts + 1 :=
      countOrbits_swapCompRight_same T.f darts h_all h_le hab h_ab_f
    rw [h_out_eq, h_in_T, h_in_T1, hE1, hN1, hF1]
    omega

theorem genusDeficit_eq_zero_of_edge_id {D : Type} [DecidableEq D] (T : PermTriple D)
    (he : ∀ x : D, T.e.f x = x) (darts : List D) (h_nodup : darts.Nodup) (h_all : ∀ x : D, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    genusDeficit T fuel darts = 0 := by
  dsimp [genusDeficit]
  cases h_d : darts with
  | nil => simp [countRelClasses_nil, countOrbits, countOrbitsAux]
  | cons d0 ds =>
    have h_fuel : 1 ≤ fuel := by rw [h_d] at h_le; dsimp at h_le; omega
    have h_all' : ∀ x : D, x ∈ d0 :: ds := h_d ▸ h_all
    have h_le' : (d0 :: ds).length ≤ fuel := h_d ▸ h_le
    have h_nodup' : (d0 :: ds).Nodup := h_d ▸ h_nodup
    have hE : countOrbits T.e fuel (d0 :: ds) = (d0 :: ds).length :=
      countOrbits_eq_length_of_id T.e he h_fuel (d0 :: ds) h_nodup'
    have hF : countOrbits T.f fuel (d0 :: ds) = countOrbits T.n fuel (d0 :: ds) := by
      have hf_symm : T.f = T.n.symm := by
        apply perm_ext
        · funext x
          have h := T.enf_id x
          rw [he] at h
          have hi := congrArg T.n.inv h
          rwa [T.n.left_inv] at hi
        · funext x
          have h := T.f_inv_eq_e_n x
          rw [h, he]
          rfl
      rw [hf_symm]
      exact countOrbits_symm_of_complete T.n (d0 :: ds) (d0 :: ds) h_all' h_le'
    have hC : countRelClasses (ReachEN T.e T.n) (d0 :: ds) = countOrbits T.n fuel (d0 :: ds) :=
      countRelClasses_reachEN_eq_countOrbits_of_edge_id T.e T.n he (d0 :: ds) h_all' h_le' (d0 :: ds)
    rw [hE, hF, hC]
    omega

private theorem genusDeficit_nonneg_aux {D : Type} [DecidableEq D]
    (darts : List D) (h_nodup : darts.Nodup) (h_all : ∀ x : D, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    ∀ (m : Nat) (T : PermTriple D),
      darts.length - countOrbits T.e fuel darts ≤ m → 0 ≤ genusDeficit T fuel darts
  | 0, T, hm => by
    have h_len_le := countOrbits_le_length T.e fuel darts.length darts (Nat.le_refl _)
    have h_eq : countOrbits T.e fuel darts = darts.length := by omega
    have he_id : ∀ x : D, T.e.f x = x := by
      cases h_all_b : darts.all (fun x => decide (T.e.f x = x)) with
      | true =>
        intro x
        have := List.all_eq_true.mp h_all_b x (h_all x)
        simpa using this
      | false =>
        exfalso
        obtain ⟨a, _, ha_f⟩ := List.all_eq_false.mp h_all_b
        have ha_ne : T.e.f a ≠ a := by simpa using ha_f
        let T1 := uncoupleEdge T a (T.e.f a)
        have hb_orb : T.e.f a ∈ getOrbit T.e fuel a := by
          have hca := orbitClosesWithin_mono T.e a a (orbitClosesWithin_of_complete T.e darts h_all a) h_le
          exact iter_mem_getOrbit_of_closes T.e fuel a hca 1
        have hE1 : countOrbits T1.e fuel darts = countOrbits T.e fuel darts + 1 :=
          countOrbits_swapCompLeft_same T.e darts h_all h_le (fun h => ha_ne h.symm) hb_orb
        have h1_le := countOrbits_le_length T1.e fuel darts.length darts (Nat.le_refl _)
        omega
    rw [genusDeficit_eq_zero_of_edge_id T he_id darts h_nodup h_all h_le]
    omega
  | m + 1, T, hm => by
    by_cases h_all_b : darts.all (fun x => decide (T.e.f x = x)) = true
    · have he_id : ∀ x : D, T.e.f x = x := fun x => by
        have := List.all_eq_true.mp h_all_b x (h_all x); simpa using this
      rw [genusDeficit_eq_zero_of_edge_id T he_id darts h_nodup h_all h_le]
      omega
    · have h_all_f : darts.all (fun x => decide (T.e.f x = x)) = false := by
        cases h : darts.all (fun x => decide (T.e.f x = x)) <;> simp_all
      obtain ⟨a, _, ha_f⟩ := List.all_eq_false.mp h_all_f
      have ha_ne : T.e.f a ≠ a := by simpa using ha_f
      let T1 := uncoupleEdge T a (T.e.f a)
      have hb_orb : T.e.f a ∈ getOrbit T.e fuel a := by
        have hca := orbitClosesWithin_mono T.e a a (orbitClosesWithin_of_complete T.e darts h_all a) h_le
        exact iter_mem_getOrbit_of_closes T.e fuel a hca 1
      have hE1 : countOrbits T1.e fuel darts = countOrbits T.e fuel darts + 1 :=
        countOrbits_swapCompLeft_same T.e darts h_all h_le (fun h => ha_ne h.symm) hb_orb
      have h_ih := genusDeficit_nonneg_aux darts h_nodup h_all h_le m T1 (by omega)
      have h_mono := genusDeficit_uncoupleEdge_le T darts h_all h_le ha_ne
      dsimp [T1] at h_ih
      omega

/-- **Universal Non-Negativity of Genus Deficit (`genusDeficit ≥ 0`)** for EVERY permutation triple. -/
theorem genusDeficit_nonneg {D : Type} [DecidableEq D] (T : PermTriple D)
    (darts : List D) (h_nodup : darts.Nodup) (h_all : ∀ x : D, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    0 ≤ genusDeficit T fuel darts :=
  genusDeficit_nonneg_aux darts h_nodup h_all h_le darts.length T (Nat.sub_le _ _)

/-- For ANY involution `e` (`∀ x, e.f (e.f x) = x`) on complete `Nodup` `darts`,
    `darts.length ≤ 2 * countOrbits e fuel darts`, with equality iff `e` is fixed-point-free. -/
theorem length_le_two_mul_countOrbits_of_involution {D : Type} [DecidableEq D] (e : Perm D)
    (he : ∀ x : D, e.f (e.f x) = x) (darts : List D) (h_nodup : darts.Nodup)
    (h_all : ∀ x : D, x ∈ darts) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    darts.length ≤ 2 * countOrbits e fuel darts ∧
      (darts.length = 2 * countOrbits e fuel darts ↔ ∀ d : D, e.f d ≠ d) := by
  cases h_d : darts with
  | nil =>
    have h_empty : ∀ d : D, False := fun d => by have := h_all d; rw [h_d] at this; cases this
    simp [countOrbits, countOrbitsAux]
    intro d; exact False.elim (h_empty d)
  | cons d0 ds =>
    have h_fuel : 1 ≤ fuel := by rw [h_d] at h_le; dsimp at h_le; omega
    have h_all' : ∀ x : D, x ∈ d0 :: ds := h_d ▸ h_all
    have h_le' : (d0 :: ds).length ≤ fuel := h_d ▸ h_le
    have h_nodup' : (d0 :: ds).Nodup := h_d ▸ h_nodup
    let S : D → Bool := fun x => decide (e.f x = x)
    have hS : ∀ x, S (e.f x) = S x := fun x => by
      dsimp [S]
      by_cases h : e.f x = x
      · simp [h]
      · have h2 : e.f (e.f x) ≠ e.f x := by rw [he x]; exact fun h' => h h'.symm
        simp [h, h2]
    have h_part_orb := countOrbits_partition_of_closed e fuel (d0 :: ds) S hS
    have h_part_len := length_eq_filter_add_filter_not S (d0 :: ds)
    have h_len1 : ((d0 :: ds).filter S).length = 1 * countOrbits e fuel ((d0 :: ds).filter S) := by
      apply length_eq_mul_countOrbits_of_uniform e fuel 1 ((d0 :: ds).filter S) (nodup_filter S h_nodup')
      · intro x _; exact orbitClosesWithin_mono e x x (orbitClosesWithin_of_complete e (d0 :: ds) h_all' x) h_le'
      · intro x hx y hy
        have hSx : S x = true := (List.mem_filter.mp hx).2
        have hfx : e.f x = x := by simpa [S] using hSx
        cases fuel with
        | zero => omega
        | succ f' =>
          rw [getOrbit_fixed_point e x f' hfx] at hy
          simp at hy
          subst hy
          exact hx
      · intro x hx
        have hfx : e.f x = x := by simpa [S] using (List.mem_filter.mp hx).2
        cases fuel with
        | zero => omega
        | succ f' => rw [getOrbit_fixed_point e x f' hfx]; rfl
    have h_len2 : ((d0 :: ds).filter (fun x => !S x)).length =
        2 * countOrbits e fuel ((d0 :: ds).filter (fun x => !S x)) := by
      apply length_eq_mul_countOrbits_of_uniform e fuel 2 ((d0 :: ds).filter (fun x => !S x))
        (nodup_filter _ h_nodup')
      · intro x _; exact orbitClosesWithin_mono e x x (orbitClosesWithin_of_complete e (d0 :: ds) h_all' x) h_le'
      · intro x hx y hy
        have hfx : e.f x ≠ x := by simpa [S] using (List.mem_filter.mp hx).2
        rw [getOrbit_involution_of_ne e he x hfx h_fuel] at hy
        simp at hy
        rcases hy with rfl | rfl
        · exact List.mem_filter.mpr ⟨h_all' _, by
            have hne : e.f (e.f x) ≠ e.f x := by rw [he x]; exact fun h => hfx h.symm
            simpa [S] using hne⟩
        · exact hx
      · intro x hx
        have hfx : e.f x ≠ x := by simpa [S] using (List.mem_filter.mp hx).2
        exact getOrbit_involution_length_two e he x hfx h_fuel
    have h_tot_len : (d0 :: ds).length = countOrbits e fuel ((d0 :: ds).filter S) +
        2 * countOrbits e fuel ((d0 :: ds).filter (fun x => !S x)) := by omega
    have h_le_res : (d0 :: ds).length ≤ 2 * countOrbits e fuel (d0 :: ds) := by omega
    refine ⟨h_le_res, ?_⟩
    constructor
    · intro h_eq d
      have h_zero : countOrbits e fuel ((d0 :: ds).filter S) = 0 := by omega
      intro hfd
      have hd_mem : d ∈ (d0 :: ds).filter S := List.mem_filter.mpr ⟨h_all' d, by simpa [S] using hfd⟩
      cases hflt : (d0 :: ds).filter S with
      | nil => rw [hflt] at hd_mem; cases hd_mem
      | cons x xs =>
        rw [hflt, countOrbits_cons] at h_zero
        omega
    · intro h_free
      have h_flt_nil : (d0 :: ds).filter S = [] := by
        rw [List.filter_eq_nil_iff]
        intro x _
        simpa [S] using h_free x
      have h_z : countOrbits e fuel ((d0 :: ds).filter S) = 0 := by rw [h_flt_nil]; rfl
      omega

/-- **Universal Euler Inequality (`EulerChar ≤ 2 * numComponents`)** on every finite complete hypermap,
    along with the exact planar characterization `isPlanar = true ↔ genusDeficit = 0 ∧ edge fixed-point-free`. -/
theorem eulerChar_le_two_mul_numComponents (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    (H.EulerChar fuel darts : Int) ≤ 2 * (H.numComponents fuel darts : Int) ∧
      (H.isPlanar fuel darts = true ↔
        genusDeficit (hypermapToTriple H) fuel darts = 0 ∧ (∀ d : H.Dart, H.edge.f d ≠ d)) := by
  have hg := genusDeficit_nonneg (hypermapToTriple H) darts h_nodup h_all h_le
  have ⟨hl_le, hl_iff⟩ := length_le_two_mul_countOrbits_of_involution H.edge H.edge_edge darts h_nodup h_all h_le
  have hC : countRelClasses (ReachEN H.edge H.node) darts = H.countComponents fuel darts :=
    countRelClasses_reachEN_eq_countComponents H darts h_all h_le darts
  dsimp [genusDeficit, hypermapToTriple] at hg
  rw [hC] at hg
  dsimp [Hypermap.EulerChar, Hypermap.numNodes, Hypermap.numEdges, Hypermap.numFaces, Hypermap.numComponents, Hypermap.isPlanar]
  constructor
  · omega
  · constructor
    · intro hp
      have heq : (↑(countOrbits H.node fuel darts) - ↑(countOrbits H.edge fuel darts) +
          ↑(countOrbits H.face fuel darts) : Int) = 2 * ↑(H.countComponents fuel darts) := by
        simpa using hp
      refine ⟨?_, hl_iff.mp (by omega)⟩
      dsimp [genusDeficit, hypermapToTriple]
      rw [hC]
      omega
    · rintro ⟨hg0, hfree⟩
      dsimp [genusDeficit, hypermapToTriple] at hg0
      rw [hC] at hg0
      have hl_eq := hl_iff.mpr hfree
      have heq : (↑(countOrbits H.node fuel darts) - ↑(countOrbits H.edge fuel darts) +
          ↑(countOrbits H.face fuel darts) : Int) = 2 * ↑(H.countComponents fuel darts) := by
        omega
      simpa using heq

/-- Isolate a fixed edge dart `d` (`T.e.f d = d`) by bypassing `d` in `T.n` and `T.f`. -/
def isolateFixed {D : Type} [DecidableEq D] (T : PermTriple D) (d : D) (hd : T.e.f d = d) : PermTriple D where
  e := T.e
  n := bypass T.n d
  f := bypass T.f d
  enf_id := fun x => by
    by_cases hxd : x = d
    · subst hxd
      dsimp [bypass]
      rw [if_pos rfl, if_pos rfl, hd]
    · have hfn : ∀ y : D, T.n.f (T.f.f y) = T.e.inv y := fun y => by
        have h := T.enf_id y
        have hi := congrArg T.e.inv h
        rwa [T.e.left_inv] at hi
      by_cases hfx : T.f.f x = d
      · have hfd_ne : T.f.f d ≠ d := fun hfd => hxd (by
          have h1 := hfx.trans hfd.symm
          have hi := congrArg T.f.inv h1
          rwa [T.f.left_inv, T.f.left_inv] at hi)
        have hn_fd : T.n.f (T.f.f d) = d := by
          rw [hfn d]
          have := congrArg T.e.inv hd
          rw [T.e.left_inv] at this
          exact this.symm
        have hbfx : (bypass T.f d).f x = T.f.f d := by
          dsimp [bypass]; rw [if_neg hxd, if_pos hfx]
        have hbn : (bypass T.n d).f (T.f.f d) = T.n.f d := by
          dsimp [bypass]; rw [if_neg hfd_ne, if_pos hn_fd]
        rw [hbfx, hbn, ← hfx, hfn x, T.e.right_inv]
      · have hne_n : T.n.f (T.f.f x) ≠ d := fun hn => hxd (by
          rw [hfn x] at hn
          have := congrArg T.e.f hn
          rwa [T.e.right_inv, hd] at this)
        have hbfx : (bypass T.f d).f x = T.f.f x := by
          dsimp [bypass]; rw [if_neg hxd, if_neg hfx]
        have hbn : (bypass T.n d).f (T.f.f x) = T.n.f (T.f.f x) := by
          dsimp [bypass]; rw [if_neg hfx, if_neg hne_n]
        rw [hbfx, hbn, T.enf_id x]

private theorem bypass_of_fixed {D : Type} [DecidableEq D] (p : Perm D) (d : D) (hp : p.f d = d) :
    bypass p d = p := by
  rw [bypass_eq_swapCompLeft, hp, swapCompLeft_same]

private theorem bypass_inv_self {D : Type} [DecidableEq D] (p : Perm D) (d : D) :
    (bypass p d).inv d = d := by
  have h : (bypass p d).f d = d := by dsimp [bypass]; simp
  have hi := congrArg (bypass p d).inv h
  rw [(bypass p d).left_inv] at hi
  exact hi.symm

private theorem filter_true_eq {α : Type} : ∀ l : List α, l.filter (fun _ => true) = l
  | [] => rfl
  | x :: xs => by dsimp [List.filter]; congr 1; exact filter_true_eq xs

/-- Isolating a fixed edge dart preserves `genusDeficit` identically. -/
theorem genusDeficit_isolateFixed_eq {D : Type} [DecidableEq D] (T : PermTriple D) (d : D)
    (hd : T.e.f d = d) (darts : List D) (h_all : ∀ x : D, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    genusDeficit (isolateFixed T d hd) fuel darts = genusDeficit T fuel darts := by
  let T1 := isolateFixed T d hd
  have hd_einv : T.e.inv d = d := by
    have := congrArg T.e.inv hd
    rw [T.e.left_inv] at this
    exact this.symm
  by_cases hn_fix : T.n.f d = d
  · have hf_fix : T.f.f d = d := by
      have h1 := T.enf_id d
      have h2 := congrArg T.e.inv h1
      rw [T.e.left_inv, hd_einv] at h2
      have h3 := h2.trans hn_fix.symm
      have hi := congrArg T.n.inv h3
      rwa [T.n.left_inv, T.n.left_inv] at hi
    have hT1 : T1 = T := by
      dsimp [T1, isolateFixed]
      have hn_eq : bypass T.n d = T.n := bypass_of_fixed T.n d hn_fix
      have hf_eq : bypass T.f d = T.f := bypass_of_fixed T.f d hf_fix
      have h_mk : ∀ (e1 n1 f1 : Perm D) h1 (n2 f2 : Perm D) h2,
          n1 = n2 → f1 = f2 → (PermTriple.mk e1 n1 f1 h1 = PermTriple.mk e1 n2 f2 h2) := by
        rintro _ _ _ _ _ _ _ rfl rfl; rfl
      cases T
      exact h_mk _ _ _ _ _ _ _ hn_eq hf_eq
    change genusDeficit T1 fuel darts = genusDeficit T fuel darts
    rw [hT1]
  · have hf_ne : T.f.f d ≠ d := fun hf_fix => hn_fix (by
      have h := T.enf_id d
      rw [hf_fix] at h
      have h2 := congrArg T.e.inv h
      rw [T.e.left_inv, hd_einv] at h2
      exact h2)
    have hV1 : countOrbits T1.n fuel darts = countOrbits T.n fuel darts + 1 := by
      dsimp [T1, isolateFixed]
      rw [bypass_eq_swapCompLeft]
      have hcn := orbitClosesWithin_mono T.n d d (orbitClosesWithin_of_complete T.n darts h_all d) h_le
      exact countOrbits_swapCompLeft_same T.n darts h_all h_le (fun h => hn_fix h.symm)
        (iter_mem_getOrbit_of_closes T.n fuel d hcn 1)
    have hE1 : countOrbits T1.e fuel darts = countOrbits T.e fuel darts := rfl
    have hF1 : countOrbits T1.f fuel darts = countOrbits T.f fuel darts + 1 := by
      dsimp [T1, isolateFixed]
      rw [bypass_eq_swapCompLeft]
      have hcf := orbitClosesWithin_mono T.f d d (orbitClosesWithin_of_complete T.f darts h_all d) h_le
      exact countOrbits_swapCompLeft_same T.f darts h_all h_le (fun h => hf_ne h.symm)
        (iter_mem_getOrbit_of_closes T.f fuel d hcf 1)
    have hd_n1 : T1.n.f d = d := by dsimp [T1, isolateFixed, bypass]; simp
    have hd_n1_inv : T1.n.inv d = d := bypass_inv_self T.n d
    have h_self_T1 : ∀ {x y : D}, WalkEN T1.e T1.n x y → x = d → y = d := by
      intro x y w hx
      induction w with
      | refl => exact hx
      | step s _ ih =>
        apply ih
        cases s with
        | e_fwd => exact hx.symm ▸ hd
        | e_bwd => exact hx.symm ▸ hd_einv
        | n_fwd => exact hx.symm ▸ hd_n1
        | n_bwd => exact hx.symm ▸ hd_n1_inv
    have h_reach_self_T1 : ∀ {y : D}, ReachEN T1.e T1.n d y → y = d := fun ⟨w⟩ => h_self_T1 w rfl
    have h_t1_t : ∀ {x y : D}, ReachEN T1.e T1.n x y → ReachEN T.e T.n x y := by
      have walk_bypass_fwd : ∀ u : D, WalkEN T.e T.n u ((bypass T.n d).f u) := fun u => by
        dsimp [bypass]
        by_cases hud : u = d
        · rw [if_pos hud, hud]; exact WalkEN.refl d
        · rw [if_neg hud]
          by_cases hnu : T.n.f u = d
          · rw [if_pos hnu]
            exact WalkEN.step (StepEN.n_fwd u) (by rw [hnu]; exact WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _))
          · rw [if_neg hnu]
            exact WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)
      have h_step : ∀ {u v : D}, StepEN T1.e T1.n u v → WalkEN T.e T.n u v := by
        intro u v s
        cases s with
        | e_fwd => exact WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)
        | e_bwd => exact WalkEN.step (StepEN.e_bwd u) (WalkEN.refl _)
        | n_fwd => exact walk_bypass_fwd u
        | n_bwd =>
          have hbw := walk_bypass_fwd ((bypass T.n d).inv u)
          have hri : (bypass T.n d).f ((bypass T.n d).inv u) = u := (bypass T.n d).right_inv u
          rw [hri] at hbw
          exact WalkEN.symm T.e T.n hbw
      rintro x y ⟨w⟩
      induction w with
      | refl z => exact reachEN_refl _ _ z
      | step s _ ih => exact reachEN_trans T.e T.n ⟨h_step s⟩ ih
    let b := T.n.f d
    let normD : D → D := fun x => if x = d then b else x
    have h_t_t1 : ∀ {x y : D}, ReachEN T.e T.n x y → ReachEN T1.e T1.n (normD x) (normD y) := by
      have h_step_fwd : ∀ {u v : D}, StepEN T.e T.n u v → ReachEN T1.e T1.n (normD u) (normD v) := by
        have h_nfwd : ∀ u : D, WalkEN T1.e T1.n (normD u) (normD (T.n.f u)) := fun u => by
          by_cases hud : u = d
          · have hnd_ne : T.n.f u ≠ d := by rw [hud]; exact hn_fix
            dsimp [normD]
            rw [if_pos hud, if_neg hnd_ne, hud]
            exact WalkEN.refl b
          · dsimp [normD]
            rw [if_neg hud]
            by_cases hnu : T.n.f u = d
            · rw [if_pos hnu]
              have hstep : T1.n.f u = b := by
                dsimp [T1, isolateFixed, bypass]
                rw [if_neg hud, if_pos hnu]
              rw [← hstep]
              exact WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)
            · rw [if_neg hnu]
              have hstep : T1.n.f u = T.n.f u := by
                dsimp [T1, isolateFixed, bypass]
                rw [if_neg hud, if_neg hnu]
              rw [← hstep]
              exact WalkEN.step (StepEN.n_fwd u) (WalkEN.refl _)
        intro u v s
        cases s with
        | e_fwd =>
          by_cases hud : u = d
          · have heu : T.e.f u = d := hud.symm ▸ hd
            dsimp [normD]; rw [if_pos hud, if_pos heu]; exact reachEN_refl _ _ _
          · have heu : T.e.f u ≠ d := fun h => hud (by
              have hi := congrArg T.e.inv h; rwa [T.e.left_inv, hd_einv] at hi)
            dsimp [normD]; rw [if_neg hud, if_neg heu]
            exact ⟨WalkEN.step (StepEN.e_fwd u) (WalkEN.refl _)⟩
        | e_bwd =>
          by_cases hud : u = d
          · have heu : T.e.inv u = d := hud.symm ▸ hd_einv
            dsimp [normD]; rw [if_pos hud, if_pos heu]; exact reachEN_refl _ _ _
          · have heu : T.e.inv u ≠ d := fun h => hud (by
              have hi := congrArg T.e.f h; rwa [T.e.right_inv, hd] at hi)
            dsimp [normD]; rw [if_neg hud, if_neg heu]
            exact ⟨WalkEN.step (StepEN.e_bwd u) (WalkEN.refl _)⟩
        | n_fwd => exact ⟨h_nfwd u⟩
        | n_bwd =>
          have hw := h_nfwd (T.n.inv u)
          rw [T.n.right_inv u] at hw
          exact ⟨WalkEN.symm T1.e T1.n hw⟩
      rintro x y ⟨w⟩
      induction w with
      | refl z => exact reachEN_refl _ _ _
      | step s _ ih => exact reachEN_trans T1.e T1.n (h_step_fwd s) ih
    have h_iff_ne : ∀ x y : D, x ≠ d → y ≠ d → (ReachEN T1.e T1.n x y ↔ ReachEN T.e T.n x y) := by
      intro x y hxd hyd
      constructor
      · exact h_t1_t
      · intro hxy
        have h1 := h_t_t1 hxy
        dsimp [normD] at h1
        rwa [if_neg hxd, if_neg hyd] at h1
    let xs := darts.filter (fun x => !decide (x = d))
    have h_rel_xs : countRelClasses (ReachEN T1.e T1.n) xs = countRelClasses (ReachEN T.e T.n) xs := by
      apply countRelClasses_eq_of_rel_iff_on_mem (ReachEN T1.e T1.n) (ReachEN T.e T.n) _ _ (Nat.le_refl _)
      intro x hx y hy
      have hxd : x ≠ d := by have := (List.mem_filter.mp hx).2; simpa using this
      have hyd : y ≠ d := by have := (List.mem_filter.mp hy).2; simpa using this
      exact h_iff_ne x y hxd hyd
    have hC_T1 : countRelClasses (ReachEN T1.e T1.n) darts = 1 + countRelClasses (ReachEN T1.e T1.n) xs := by
      have h_dxs : countRelClasses (ReachEN T1.e T1.n) darts = countRelClasses (ReachEN T1.e T1.n) (d :: xs) := by
        apply countRelClasses_eq_of_iff_mem (ReachEN T1.e T1.n) (reachEN_refl _ _)
          (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
        intro x
        constructor
        · intro _
          by_cases hxd : x = d
          · subst hxd; exact List.mem_cons_self
          · exact List.mem_cons_of_mem d (List.mem_filter.mpr ⟨h_all x, by simp [hxd]⟩)
        · intro _; exact h_all x
      rw [h_dxs, countRelClasses_cons]
      have h_flt_xs : xs.filter (fun x => !decide (ReachEN T1.e T1.n d x)) = xs := by
        calc xs.filter (fun x => !decide (ReachEN T1.e T1.n d x))
            = xs.filter (fun _ => true) := by
              apply filter_ext_of_mem
              intro x hx
              have hxd : x ≠ d := by have := (List.mem_filter.mp hx).2; simpa using this
              have hnr : ¬ReachEN T1.e T1.n d x := fun hr => hxd (h_reach_self_T1 hr)
              simp [hnr]
          _ = xs := filter_true_eq xs
      rw [h_flt_xs]
    have hC_T : countRelClasses (ReachEN T.e T.n) xs = countRelClasses (ReachEN T.e T.n) darts := by
      let S : D → Bool := fun x => decide (ReachEN T.e T.n b x)
      have hS : ∀ {x y : D}, ReachEN T.e T.n x y → S x = S y := by
        intro x y hxy
        dsimp [S]
        by_cases hx : ReachEN T.e T.n b x
        · simp [hx, reachEN_trans _ _ hx hxy]
        · have hy : ¬ReachEN T.e T.n b y := fun hy => hx (reachEN_trans _ _ hy (reachEN_symm _ _ hxy))
          simp [hx, hy]
      rw [countRelClasses_partition_of_closed (ReachEN T.e T.n) (reachEN_refl _ _)
            (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS xs,
          countRelClasses_partition_of_closed (ReachEN T.e T.n) (reachEN_refl _ _)
            (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2) S hS darts]
      have hb_xs : b ∈ xs := List.mem_filter.mpr ⟨h_all b, by simp [b, hn_fix]⟩
      have h1_xs : countRelClasses (ReachEN T.e T.n) (xs.filter S) = 1 := by
        apply countRelClasses_eq_one_of_forall (ReachEN T.e T.n) b
        · intro x hx; simpa [S] using (List.mem_filter.mp hx).2
        · intro hnil; have hbm : b ∈ xs.filter S := List.mem_filter.mpr ⟨hb_xs, by simp [S, reachEN_refl]⟩
          rw [hnil] at hbm; cases hbm
        · exact fun h => reachEN_symm _ _ h
        · exact fun h1 h2 => reachEN_trans _ _ h1 h2
      have h1_d : countRelClasses (ReachEN T.e T.n) (darts.filter S) = 1 := by
        apply countRelClasses_eq_one_of_forall (ReachEN T.e T.n) b
        · intro x hx; simpa [S] using (List.mem_filter.mp hx).2
        · intro hnil; have hbm : b ∈ darts.filter S := List.mem_filter.mpr ⟨h_all b, by simp [S, reachEN_refl]⟩
          rw [hnil] at hbm; cases hbm
        · exact fun h => reachEN_symm _ _ h
        · exact fun h1 h2 => reachEN_trans _ _ h1 h2
      have hbd : ReachEN T.e T.n b d := reachEN_symm T.e T.n ⟨WalkEN.step (StepEN.n_fwd d) (WalkEN.refl _)⟩
      have h_out : countRelClasses (ReachEN T.e T.n) (xs.filter (fun x => !S x)) =
          countRelClasses (ReachEN T.e T.n) (darts.filter (fun x => !S x)) := by
        apply countRelClasses_eq_of_iff_mem (ReachEN T.e T.n) (reachEN_refl _ _)
          (fun h => reachEN_symm _ _ h) (fun h1 h2 => reachEN_trans _ _ h1 h2)
        intro x
        simp only [List.mem_filter, Bool.not_eq_true']
        constructor
        · intro ⟨hxm, hns⟩; exact ⟨(List.mem_filter.mp hxm).1, hns⟩
        · intro ⟨hxm, hns⟩
          refine ⟨List.mem_filter.mpr ⟨hxm, ?_⟩, hns⟩
          have hxd : x ≠ d := by
            intro h_eq; subst h_eq
            have hSd : S x = true := by simpa [S] using hbd
            rw [hSd] at hns; cases hns
          simp [hxd]
      rw [h1_xs, h1_d, h_out]
    have hC1 : countRelClasses (ReachEN T1.e T1.n) darts =
        countRelClasses (ReachEN T.e T.n) darts + 1 := by
      rw [hC_T1, h_rel_xs, hC_T]
      omega
    dsimp [genusDeficit]
    rw [hC1, hV1, hE1, hF1]
    omega

end GenusDeficitAndEulerInequality

section PlanarSurgeryPreservation

theorem beq_eq_of_pointwise {α : Type} (b1 b2 : BEq α)
    (h : ∀ x y : α, @BEq.beq α b1 x y = @BEq.beq α b2 x y) : b1 = b2 := by
  cases b1
  cases b2
  congr 1
  funext x y
  exact h x y

private theorem instBEqOfDecidableEq_eq {α : Type} (d1 d2 : DecidableEq α) :
    @instBEqOfDecidableEq α d1 = @instBEqOfDecidableEq α d2 := by
  apply beq_eq_of_pointwise
  intro x y
  change @decide (x = y) (d1 x y) = @decide (x = y) (d2 x y)
  by_cases h : x = y
  · rw [@decide_eq_true (x = y) (d1 x y) h, @decide_eq_true (x = y) (d2 x y) h]
  · rw [@decide_eq_false (x = y) (d1 x y) h, @decide_eq_false (x = y) (d2 x y) h]

theorem subtype_beq_eq_decidableEq {D : Type} [DecidableEq D] (P : D → Prop) :
    (@Subtype.instBEq D P inferInstance) = (@instBEqOfDecidableEq { d : D // P d } inferInstance) := by
  apply beq_eq_of_pointwise
  intro x y
  show decide (x.val = y.val) = decide (x = y)
  by_cases h : x.val = y.val
  · have hxy : x = y := Subtype.ext h
    simp [hxy]
  · have hne : x ≠ y := fun hxy => h (congrArg Subtype.val hxy)
    simp [h, hne]

/-- Restrict a list `l : List D` to the subtype `{ d : D // P d }`. -/
def predDarts {D : Type} (P : D → Prop) [DecidablePred P] : List D → List { d : D // P d }
  | [] => []
  | d :: ds => if h : P d then ⟨d, h⟩ :: predDarts P ds else predDarts P ds

theorem mem_predDarts_iff {D : Type} (P : D → Prop) [DecidablePred P] :
    ∀ (l : List D) (x : { d : D // P d }), x ∈ predDarts P l ↔ x.val ∈ l
  | [], _ => by simp [predDarts]
  | a :: as, x => by
    dsimp [predDarts]
    split
    · rename_i ha
      constructor
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem a ((mem_predDarts_iff P as x).mp hmem)
      · intro hx
        rcases List.mem_cons.mp hx with h_eq | hmem
        · cases x with
          | mk xv xp =>
            dsimp at h_eq
            subst h_eq
            exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((mem_predDarts_iff P as x).mpr hmem)
    · rename_i hna
      constructor
      · intro hx; exact List.mem_cons_of_mem a ((mem_predDarts_iff P as x).mp hx)
      · intro hx
        rcases List.mem_cons.mp hx with h_eq | hmem
        · exact False.elim (hna (h_eq ▸ x.property))
        · exact (mem_predDarts_iff P as x).mpr hmem

theorem nodup_predDarts {D : Type} (P : D → Prop) [DecidablePred P] :
    ∀ {l : List D}, l.Nodup → (predDarts P l).Nodup
  | [], _ => by simp [predDarts]
  | a :: as, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨ha_nmem, has_nd⟩
    dsimp [predDarts]
    split
    · refine List.nodup_cons.mpr ⟨?_, nodup_predDarts P has_nd⟩
      intro hmem
      exact ha_nmem ((mem_predDarts_iff P as _).mp hmem)
    · exact nodup_predDarts P has_nd

theorem map_predDarts {D : Type} (P : D → Prop) [DecidablePred P] :
    ∀ (l : List D), (predDarts P l).map Subtype.val = l.filter (fun d => decide (P d))
  | [] => by simp [predDarts]
  | a :: as => by
    dsimp [predDarts, List.filter]
    by_cases ha : P a
    · simp [ha, map_predDarts P as]
    · simp [ha, map_predDarts P as]

theorem filter_map_subtype {D : Type} (P : D → Prop)
    (q' : { d : D // P d } → Bool) (q : D → Bool)
    (hq : ∀ y : { d : D // P d }, q' y = q y.val) :
    ∀ (l' : List { d : D // P d }),
      (l'.filter q').map Subtype.val = (l'.map Subtype.val).filter q
  | [] => rfl
  | y :: ys => by
    dsimp [List.map, List.filter]
    rw [hq y]
    cases hqy : q y.val
    · simp [filter_map_subtype P q' q hq ys]
    · simp [filter_map_subtype P q' q hq ys]

theorem perm_eq_of_f_eq {D : Type} {p q : Perm D} (h : ∀ x, p.f x = q.f x) : p = q := by
  have hf : p.f = q.f := funext h
  have hinv : p.inv = q.inv := by
    funext x
    calc
      p.inv x = p.inv (q.f (q.inv x)) := by rw [q.right_inv]
      _ = p.inv (p.f (q.inv x)) := by rw [h]
      _ = q.inv x := p.left_inv _
  cases p
  cases q
  cases hf
  cases hinv
  rfl

theorem permTriple_eq_of_f_eq {D : Type} {T1 T2 : PermTriple D}
    (he : ∀ x, T1.e.f x = T2.e.f x)
    (hn : ∀ x, T1.n.f x = T2.n.f x)
    (hf : ∀ x, T1.f.f x = T2.f.f x) : T1 = T2 := by
  have h1 : T1.e = T2.e := perm_eq_of_f_eq he
  have h2 : T1.n = T2.n := perm_eq_of_f_eq hn
  have h3 : T1.f = T2.f := perm_eq_of_f_eq hf
  cases T1
  cases T2
  cases h1
  cases h2
  cases h3
  rfl

/-- Restrict a permutation `p` to an invariant subtype `{ d : D // P d }`. -/
def restrictPermPred {D : Type} (p : Perm D) (P : D → Prop)
    (h_inv : ∀ d, P d ↔ P (p.f d)) : Perm { d : D // P d } where
  f x := ⟨p.f x.val, (h_inv x.val).mp x.property⟩
  inv x := ⟨p.inv x.val, (h_inv (p.inv x.val)).mpr (by rw [p.right_inv]; exact x.property)⟩
  left_inv x := Subtype.ext (p.left_inv x.val)
  right_inv x := Subtype.ext (p.right_inv x.val)

theorem restrictPermPred_iter {D : Type} (p : Perm D) (P : D → Prop)
    (h_inv : ∀ d, P d ↔ P (p.f d)) :
    ∀ (k : Nat) (x : { d : D // P d }),
      (Perm.iter (restrictPermPred p P h_inv) k x).val = Perm.iter p k x.val
  | 0, _ => rfl
  | k + 1, x => by
    rw [Perm.iter_succ, Perm.iter_succ, ← restrictPermPred_iter p P h_inv k x]
    rfl

/-- Restrict a `PermTriple` to an invariant subtype `{ d : D // P d }`. -/
def restrictTriplePred {D : Type} (T : PermTriple D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (T.e.f d))
    (h_n : ∀ d, P d ↔ P (T.n.f d)) : PermTriple { d : D // P d } :=
  let h_f : ∀ d, P d ↔ P (T.f.f d) := fun d => by
    have h1 := h_e (T.n.f (T.f.f d))
    have h2 := h_n (T.f.f d)
    rw [T.enf_id d] at h1
    exact (Iff.trans h2 h1).symm
  { e := restrictPermPred T.e P h_e
    n := restrictPermPred T.n P h_n
    f := restrictPermPred T.f P h_f
    enf_id := fun x => Subtype.ext (T.enf_id x.val) }

private theorem contains_decidableEq_iff_mem {α : Type} [DecidableEq α] (l : List α) (x : α) :
    @List.contains α (@instBEqOfDecidableEq α inferInstance) l x = true ↔ x ∈ l := by
  induction l with
  | nil =>
    constructor
    · intro h; dsimp [List.contains, List.elem] at h; cases h
    · intro h; cases h
  | cons a as ih =>
    dsimp [List.contains, List.elem]
    change (decide (x = a) || @List.elem α (@instBEqOfDecidableEq α inferInstance) x as) = true ↔ x ∈ a :: as
    rw [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    exact or_congr Iff.rfl ih

theorem getOrbit_contains_restrictPermPred_iff {D : Type} [DecidableEq D]
    (p : Perm D) (P : D → Prop) (h_inv : ∀ d, P d ↔ P (p.f d))
    (fuel : Nat) (x y : { d : D // P d })
    (hx_sub : orbitClosesWithin (restrictPermPred p P h_inv) x x fuel)
    (hx_amb : orbitClosesWithin p x.val x.val fuel) :
    (@List.contains { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
      (@getOrbit { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
        (restrictPermPred p P h_inv) fuel x) y) =
      (getOrbit p fuel x.val).contains y.val := by
  have hiff :
      (@List.contains { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
        (@getOrbit { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
          (restrictPermPred p P h_inv) fuel x) y = true) ↔
        ((getOrbit p fuel x.val).contains y.val = true) := by
    rw [contains_decidableEq_iff_mem, List.contains_iff_mem]
    rw [mem_getOrbit_iff_exists_iter (restrictPermPred p P h_inv) fuel x y hx_sub]
    rw [mem_getOrbit_iff_exists_iter p fuel x.val y.val hx_amb]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; exact restrictPermPred_iter p P h_inv k x⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, Subtype.ext ?_⟩
      rw [restrictPermPred_iter p P h_inv k x]
      exact hk
  cases hb1 :
      (@List.contains { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
        (@getOrbit { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
          (restrictPermPred p P h_inv) fuel x) y) <;>
    cases hb2 : (getOrbit p fuel x.val).contains y.val
  · rfl
  · exfalso; exact absurd (hiff.mpr hb2) (by rw [hb1]; decide)
  · exfalso; exact absurd (hiff.mp hb1) (by rw [hb2]; decide)
  · rfl

theorem countOrbits_restrictPermPred_eq {D : Type} [DecidableEq D]
    (p : Perm D) (P : D → Prop) (h_inv : ∀ d, P d ↔ P (p.f d))
    (fuel : Nat)
    (h_close_sub : ∀ x : { d : D // P d }, orbitClosesWithin (restrictPermPred p P h_inv) x x fuel)
    (h_close_amb : ∀ x : { d : D // P d }, orbitClosesWithin p x.val x.val fuel) :
    ∀ (n : Nat) (l' : List { d : D // P d }), l'.length ≤ n →
      @countOrbits { d : D // P d } (@instBEqOfDecidableEq { d : D // P d } inferInstance)
        (restrictPermPred p P h_inv) fuel l' =
        countOrbits p fuel (l'.map Subtype.val)
  | 0, [], _ => by simp [countOrbits, countOrbitsAux]
  | 0, _ :: _, hlen => by simp at hlen
  | n + 1, [], _ => by simp [countOrbits, countOrbitsAux]
  | n + 1, x :: xs, hlen => by
    let orbX := @getOrbit { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
      (restrictPermPred p P h_inv) fuel x
    have h_lhs :
        @countOrbits { d : D // P d } (@instBEqOfDecidableEq { d : D // P d } inferInstance)
          (restrictPermPred p P h_inv) fuel (x :: xs) =
        1 + @countOrbits { d : D // P d } (@instBEqOfDecidableEq { d : D // P d } inferInstance)
          (restrictPermPred p P h_inv) fuel
          (xs.filter (fun y => !(@List.contains _ (@instBEqOfDecidableEq _ inferInstance) orbX y))) :=
      @countOrbits_cons { d : D // P d } inferInstance (restrictPermPred p P h_inv) fuel x xs
    have h_rhs :
        countOrbits p fuel (List.map Subtype.val (x :: xs)) =
        1 + countOrbits p fuel
          ((xs.map Subtype.val).filter (fun z => !(getOrbit p fuel x.val).contains z)) := by
      rw [List.map_cons]
      exact countOrbits_cons p fuel x.val (xs.map Subtype.val)
    have hq : ∀ y : { d : D // P d },
        (!(@List.contains { d : D // P d } (@instBEqOfDecidableEq _ inferInstance) orbX y)) =
        (!(getOrbit p fuel x.val).contains y.val) := fun y => by
      dsimp only [orbX]
      rw [getOrbit_contains_restrictPermPred_iff p P h_inv fuel x y (h_close_sub x) (h_close_amb x)]
    have hfilt := filter_map_subtype P
      (fun y => !(@List.contains { d : D // P d } (@instBEqOfDecidableEq _ inferInstance) orbX y))
      (fun z => !(getOrbit p fuel x.val).contains z) hq xs
    have hlen' :
        (xs.filter (fun y => !(@List.contains _ (@instBEqOfDecidableEq _ inferInstance) orbX y))).length ≤ n := by
      have h1 := List.length_filter_le
        (fun y => !(@List.contains { d : D // P d } (@instBEqOfDecidableEq _ inferInstance) orbX y)) xs
      simp only [List.length_cons] at hlen
      omega
    have hrec := countOrbits_restrictPermPred_eq p P h_inv fuel h_close_sub h_close_amb n
      (xs.filter (fun y => !(@List.contains _ (@instBEqOfDecidableEq _ inferInstance) orbX y))) hlen'
    rw [h_lhs, h_rhs, hrec, hfilt]

private theorem stepEN_preserves_pred {D : Type} (e n : Perm D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (e.f d))
    (h_n : ∀ d, P d ↔ P (n.f d))
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

theorem reachEN_preserves_pred {D : Type} (e n : Perm D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (e.f d))
    (h_n : ∀ d, P d ↔ P (n.f d)) :
    ∀ {u v : D}, ReachEN e n u v → (P u ↔ P v) := by
  intro u v ⟨w⟩
  induction w with
  | refl _ => exact Iff.rfl
  | step s _ ih => exact Iff.trans (stepEN_preserves_pred e n P h_e h_n s) ih

theorem reachEN_restrictTriple_iff {D : Type} (e n : Perm D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (e.f d))
    (h_n : ∀ d, P d ↔ P (n.f d))
    (x y : { d : D // P d }) :
    ReachEN (restrictPermPred e P h_e) (restrictPermPred n P h_n) x y ↔
      ReachEN e n x.val y.val := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | refl _ => exact ⟨.refl _⟩
    | @step a _ _ s _ ih =>
      rcases ih with ⟨w'⟩
      cases s with
      | e_fwd => exact ⟨.step (StepEN.e_fwd a.val) w'⟩
      | e_bwd => exact ⟨.step (StepEN.e_bwd a.val) w'⟩
      | n_fwd => exact ⟨.step (StepEN.n_fwd a.val) w'⟩
      | n_bwd => exact ⟨.step (StepEN.n_bwd a.val) w'⟩
  · rintro ⟨w⟩
    have aux : ∀ {u v : D}, WalkEN e n u v → ∀ (hu : P u) (hv : P v),
        ReachEN (restrictPermPred e P h_e) (restrictPermPred n P h_n) ⟨u, hu⟩ ⟨v, hv⟩ := by
      intro u v hw
      induction hw with
      | refl u =>
        intro hu hv
        have heq : (⟨u, hu⟩ : { d : D // P d }) = ⟨u, hv⟩ := rfl
        rw [heq]
        exact ⟨.refl _⟩
      | @step u w v s hrest ih =>
        intro hu hv
        have hwP : P w := (stepEN_preserves_pred e n P h_e h_n s).mp hu
        rcases ih hwP hv with ⟨w'⟩
        refine ⟨?_⟩
        cases s with
        | e_fwd => exact .step (StepEN.e_fwd (⟨u, hu⟩ : { d : D // P d })) w'
        | e_bwd => exact .step (StepEN.e_bwd (⟨u, hu⟩ : { d : D // P d })) w'
        | n_fwd => exact .step (StepEN.n_fwd (⟨u, hu⟩ : { d : D // P d })) w'
        | n_bwd => exact .step (StepEN.n_bwd (⟨u, hu⟩ : { d : D // P d })) w'
    exact aux w x.property y.property

theorem countRelClassesAux_restrict {D : Type} (P : D → Prop)
    (R_P : { d : D // P d } → { d : D // P d } → Prop) [DecidableRel R_P]
    (R : D → D → Prop) [DecidableRel R]
    (hR : ∀ x y : { d : D // P d }, R_P x y ↔ R x.val y.val) :
    ∀ (fuel : Nat) (l' : List { d : D // P d }),
      countRelClassesAux R_P fuel l' = countRelClassesAux R fuel (l'.map Subtype.val)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    dsimp [countRelClassesAux, List.map]
    have hq : ∀ y : { d : D // P d }, (!decide (R_P x y)) = (!decide (R x.val y.val)) := fun y => by
      have hd : decide (R_P x y) = decide (R x.val y.val) := by
        by_cases h : R_P x y
        · simp [h, (hR x y).mp h]
        · have hn : ¬R x.val y.val := fun h2 => h ((hR x y).mpr h2)
          simp [h, hn]
      rw [hd]
    rw [countRelClassesAux_restrict P R_P R hR k _]
    rw [filter_map_subtype P (fun y => !decide (R_P x y)) (fun z => !decide (R x.val z)) hq xs]

theorem countRelClasses_restrictTriple {D : Type} (e n : Perm D) (P : D → Prop)
    (h_e : ∀ d, P d ↔ P (e.f d))
    (h_n : ∀ d, P d ↔ P (n.f d))
    (l' : List { d : D // P d }) :
    @countRelClasses { d : D // P d }
      (ReachEN (restrictPermPred e P h_e) (restrictPermPred n P h_n))
      (instDecidableRelReachEN (restrictPermPred e P h_e) (restrictPermPred n P h_n))
      l' =
    @countRelClasses D (ReachEN e n) (instDecidableRelReachEN e n) (l'.map Subtype.val) := by
  unfold countRelClasses
  rw [List.length_map]
  exact countRelClassesAux_restrict P
    (ReachEN (restrictPermPred e P h_e) (restrictPermPred n P h_n))
    (ReachEN e n)
    (reachEN_restrictTriple_iff e n P h_e h_n)
    l'.length l'

theorem genusDeficit_pred_split {D : Type} [DecidableEq D]
    (T : PermTriple D) (fuel : Nat) (darts : List D)
    (h_nodup : darts.Nodup) (h_comp : ∀ d, d ∈ darts)
    (h_fuel : darts.length ≤ fuel)
    (P : D → Prop) [DecidablePred P]
    (h_e : ∀ d, P d ↔ P (T.e.f d))
    (h_n : ∀ d, P d ↔ P (T.n.f d)) :
    genusDeficit T fuel darts =
      genusDeficit (restrictTriplePred T P h_e h_n) fuel (predDarts P darts) +
        genusDeficit (restrictTriplePred T (fun d => ¬ P d)
          (fun d => not_congr (h_e d)) (fun d => not_congr (h_n d))) fuel
          (predDarts (fun d => ¬ P d) darts) := by
  let Q : D → Prop := fun d => ¬ P d
  have hQe : ∀ d, Q d ↔ Q (T.e.f d) := fun d => not_congr (h_e d)
  have hQn : ∀ d, Q d ↔ Q (T.n.f d) := fun d => not_congr (h_n d)
  let TP := restrictTriplePred T P h_e h_n
  let TQ := restrictTriplePred T Q hQe hQn
  let dartsP := predDarts P darts
  let dartsQ := predDarts Q darts
  let S : D → Bool := fun d => decide (P d)
  have hS_filt_P : darts.filter S = dartsP.map Subtype.val :=
    (map_predDarts P darts).symm
  have hnot_S : (fun d => !S d) = (fun d => decide (Q d)) := by
    funext d
    dsimp [S, Q]
    by_cases hp : P d <;> simp [hp]
  have hS_filt_notP : darts.filter (fun d => !S d) = dartsQ.map Subtype.val := by
    rw [hnot_S]
    exact (map_predDarts Q darts).symm
  have h_len_split : darts.length = dartsP.length + dartsQ.length := by
    have h1 := length_eq_filter_add_filter_not S darts
    rw [hS_filt_P, hS_filt_notP, List.length_map, List.length_map] at h1
    exact h1
  have h_closed_reach : ∀ {u v : D}, ReachEN T.e T.n u v → S u = S v := by
    intro u v hreach
    have hiff := reachEN_preserves_pred T.e T.n P h_e h_n hreach
    dsimp [S]
    by_cases hu : P u
    · simp [hu, hiff.mp hu]
    · have hv : ¬P v := fun hv' => hu (hiff.mpr hv')
      simp [hu, hv]
  have hC_split :
      @countRelClasses D (ReachEN T.e T.n) (instDecidableRelReachEN T.e T.n) darts =
        @countRelClasses D (ReachEN T.e T.n) (instDecidableRelReachEN T.e T.n) (darts.filter S) +
          @countRelClasses D (ReachEN T.e T.n) (instDecidableRelReachEN T.e T.n) (darts.filter (fun d => !S d)) :=
    countRelClasses_partition_of_closed (ReachEN T.e T.n)
      (reachEN_refl T.e T.n) (fun {x y} h => reachEN_symm T.e T.n h)
      (fun {x y z} h1 h2 => reachEN_trans T.e T.n h1 h2) S h_closed_reach darts
  rw [hS_filt_P, hS_filt_notP] at hC_split
  rw [← countRelClasses_restrictTriple T.e T.n P h_e h_n dartsP] at hC_split
  rw [← countRelClasses_restrictTriple T.e T.n Q hQe hQn dartsQ] at hC_split
  have h_close_amb : ∀ p : Perm D, ∀ d : D, orbitClosesWithin p d d fuel := fun p d =>
    orbitClosesWithin_mono p d d (orbitClosesWithin_of_complete p darts h_comp d) h_fuel
  have h_nodup_P : dartsP.Nodup := nodup_predDarts P h_nodup
  have h_comp_P : ∀ x : { d : D // P d }, x ∈ dartsP := fun x =>
    (mem_predDarts_iff P darts x).mpr (h_comp x.val)
  have h_len_P : dartsP.length ≤ fuel := by omega
  have h_nodup_Q : dartsQ.Nodup := nodup_predDarts Q h_nodup
  have h_comp_Q : ∀ x : { d : D // Q d }, x ∈ dartsQ := fun x =>
    (mem_predDarts_iff Q darts x).mpr (h_comp x.val)
  have h_len_Q : dartsQ.length ≤ fuel := by omega
  have h_orb_split : ∀ (p : Perm D) (hp : ∀ d, P d ↔ P (p.f d)),
      countOrbits p fuel darts =
        @countOrbits { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
          (restrictPermPred p P hp) fuel dartsP +
        @countOrbits { d : D // Q d } (@instBEqOfDecidableEq _ inferInstance)
          (restrictPermPred p Q (fun d => not_congr (hp d))) fuel dartsQ := by
    intro p hp
    have hSp : ∀ d, S (p.f d) = S d := fun d => by
      dsimp [S]
      by_cases hpd : P d
      · simp [hpd, (hp d).mp hpd]
      · have hnp : ¬P (p.f d) := fun h2 => hpd ((hp d).mpr h2)
        simp [hpd, hnp]
    have hpart := countOrbits_partition_of_closed p fuel darts S hSp
    rw [hS_filt_P, hS_filt_notP] at hpart
    have h1 := countOrbits_restrictPermPred_eq p P hp fuel
      (fun x => orbitClosesWithin_mono _ x x
        (orbitClosesWithin_of_complete _ dartsP h_comp_P x) h_len_P)
      (fun x => h_close_amb p x.val)
      dartsP.length dartsP (Nat.le_refl _)
    have h2 := countOrbits_restrictPermPred_eq p Q (fun d => not_congr (hp d)) fuel
      (fun x => orbitClosesWithin_mono _ x x
        (orbitClosesWithin_of_complete _ dartsQ h_comp_Q x) h_len_Q)
      (fun x => h_close_amb p x.val)
      dartsQ.length dartsQ (Nat.le_refl _)
    rw [← h1, ← h2] at hpart
    exact hpart
  have hf_e : ∀ d, P d ↔ P (T.f.f d) := fun d => by
    have h1 := h_e (T.n.f (T.f.f d))
    have h2 := h_n (T.f.f d)
    rw [T.enf_id d] at h1
    exact (Iff.trans h2 h1).symm
  have hV_split := h_orb_split T.n h_n
  have hE_split := h_orb_split T.e h_e
  have hF_split := h_orb_split T.f hf_e
  change
    (darts.length : Int) +
      2 * (@countRelClasses D (ReachEN T.e T.n) (instDecidableRelReachEN T.e T.n) darts : Int) -
      ((countOrbits T.n fuel darts : Int) + (countOrbits T.e fuel darts : Int) +
        (countOrbits T.f fuel darts : Int)) =
    ((dartsP.length : Int) +
      2 * (@countRelClasses { d : D // P d }
        (ReachEN TP.e TP.n) (instDecidableRelReachEN TP.e TP.n) dartsP : Int) -
      ((@countOrbits { d : D // P d } (@instBEqOfDecidableEq _ inferInstance) TP.n fuel dartsP : Int) +
       (@countOrbits { d : D // P d } (@instBEqOfDecidableEq _ inferInstance) TP.e fuel dartsP : Int) +
       (@countOrbits { d : D // P d } (@instBEqOfDecidableEq _ inferInstance) TP.f fuel dartsP : Int))) +
    ((dartsQ.length : Int) +
      2 * (@countRelClasses { d : D // Q d }
        (ReachEN TQ.e TQ.n) (instDecidableRelReachEN TQ.e TQ.n) dartsQ : Int) -
      ((@countOrbits { d : D // Q d } (@instBEqOfDecidableEq _ inferInstance) TQ.n fuel dartsQ : Int) +
       (@countOrbits { d : D // Q d } (@instBEqOfDecidableEq _ inferInstance) TQ.e fuel dartsQ : Int) +
       (@countOrbits { d : D // Q d } (@instBEqOfDecidableEq _ inferInstance) TQ.f fuel dartsQ : Int)))
  dsimp only [TP, TQ, restrictTriplePred]
  have hF_P :
      @countOrbits { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
        (restrictPermPred T.f P (fun d => (Iff.trans (h_n (T.f.f d))
          (by have := h_e (T.n.f (T.f.f d)); rw [T.enf_id d] at this; exact this)).symm))
        fuel dartsP =
      @countOrbits { d : D // P d } (@instBEqOfDecidableEq _ inferInstance)
        (restrictPermPred T.f P hf_e) fuel dartsP := rfl
  have hF_Q :
      @countOrbits { d : D // Q d } (@instBEqOfDecidableEq _ inferInstance)
        (restrictPermPred T.f Q (fun d => not_congr (Iff.trans (h_n (T.f.f d))
          (by have := h_e (T.n.f (T.f.f d)); rw [T.enf_id d] at this; exact this)).symm))
        fuel dartsQ =
      @countOrbits { d : D // Q d } (@instBEqOfDecidableEq _ inferInstance)
        (restrictPermPred T.f Q (fun d => not_congr (hf_e d))) fuel dartsQ := rfl
  rw [h_len_split, hC_split, hV_split, hE_split, hF_split, hF_P, hF_Q]
  omega

theorem genusDeficit_eq_of_complete {D : Type} [DecidableEq D]
    (T : PermTriple D) (l1 l2 : List D)
    (h1_nd : l1.Nodup) (h1_comp : ∀ d, d ∈ l1)
    (h2_nd : l2.Nodup) (h2_comp : ∀ d, d ∈ l2)
    {f1 f2 : Nat} (hf1 : l1.length ≤ f1) (hf2 : l2.length ≤ f2) :
    genusDeficit T f1 l1 = genusDeficit T f2 l2 := by
  let M := Nat.max f1 f2
  have h_f1M : genusDeficit T f1 l1 = genusDeficit T M l1 :=
    genusDeficit_fuel_eq T l1 h1_comp hf1 (Nat.le_trans hf1 (Nat.le_max_left f1 f2))
  have h_f2M : genusDeficit T f2 l2 = genusDeficit T M l2 :=
    genusDeficit_fuel_eq T l2 h2_comp hf2 (Nat.le_trans hf2 (Nat.le_max_right f1 f2))
  rw [h_f1M, h_f2M]
  have hiff : ∀ d, d ∈ l1 ↔ d ∈ l2 := fun d => ⟨fun _ => h2_comp d, fun _ => h1_comp d⟩
  have hlen : l1.length = l2.length := nodup_length_eq_of_iff_mem h1_nd h2_nd hiff
  have hC :
      @countRelClasses D (ReachEN T.e T.n) (instDecidableRelReachEN T.e T.n) l1 =
        @countRelClasses D (ReachEN T.e T.n) (instDecidableRelReachEN T.e T.n) l2 :=
    countRelClasses_eq_of_iff_mem (ReachEN T.e T.n)
      (reachEN_refl T.e T.n) (fun {x y} h => reachEN_symm T.e T.n h)
      (fun {x y z} h1 h2 => reachEN_trans T.e T.n h1 h2) l1 l2 hiff
  have hM : l1.length ≤ M := Nat.le_trans hf1 (Nat.le_max_left f1 f2)
  have hV := countOrbits_eq_of_iff_mem_of_complete T.n l1 l1 l2 h1_comp hM hiff
  have hE := countOrbits_eq_of_iff_mem_of_complete T.e l1 l1 l2 h1_comp hM hiff
  have hF := countOrbits_eq_of_iff_mem_of_complete T.f l1 l1 l2 h1_comp hM hiff
  dsimp [genusDeficit]
  rw [hlen, hC, hV, hE, hF]

theorem genusDeficit_restrictTriple_le {D : Type} [DecidableEq D]
    (T : PermTriple D) (fuel fuel' : Nat)
    (darts : List D) (h_nodup : darts.Nodup) (h_comp : ∀ d, d ∈ darts) (h_fuel : darts.length ≤ fuel)
    (P : D → Prop) [DecidablePred P]
    (h_e : ∀ d, P d ↔ P (T.e.f d))
    (h_n : ∀ d, P d ↔ P (T.n.f d))
    (darts' : List { d : D // P d }) (h_nodup' : darts'.Nodup)
    (h_comp' : ∀ x : { d : D // P d }, x ∈ darts') (h_fuel' : darts'.length ≤ fuel') :
    genusDeficit (restrictTriplePred T P h_e h_n) fuel' darts' ≤ genusDeficit T fuel darts := by
  let Q : D → Prop := fun d => ¬ P d
  have hQe : ∀ d, Q d ↔ Q (T.e.f d) := fun d => not_congr (h_e d)
  have hQn : ∀ d, Q d ↔ Q (T.n.f d) := fun d => not_congr (h_n d)
  let TP := restrictTriplePred T P h_e h_n
  let TQ := restrictTriplePred T Q hQe hQn
  let dartsP := predDarts P darts
  let dartsQ := predDarts Q darts
  have h_nodup_P : dartsP.Nodup := nodup_predDarts P h_nodup
  have h_comp_P : ∀ x : { d : D // P d }, x ∈ dartsP := fun x =>
    (mem_predDarts_iff P darts x).mpr (h_comp x.val)
  have h_len_P : dartsP.length ≤ fuel := by
    have hlen : dartsP.length = (darts.filter (fun d => decide (P d))).length := by
      rw [← List.length_map (f := Subtype.val), map_predDarts P darts]
    rw [hlen]
    exact Nat.le_trans (List.length_filter_le _ _) h_fuel
  have h_nodup_Q : dartsQ.Nodup := nodup_predDarts Q h_nodup
  have h_comp_Q : ∀ x : { d : D // Q d }, x ∈ dartsQ := fun x =>
    (mem_predDarts_iff Q darts x).mpr (h_comp x.val)
  have h_len_Q : dartsQ.length ≤ fuel := by
    have hlen : dartsQ.length = (darts.filter (fun d => decide (Q d))).length := by
      rw [← List.length_map (f := Subtype.val), map_predDarts Q darts]
    rw [hlen]
    exact Nat.le_trans (List.length_filter_le _ _) h_fuel
  have h_nonneg_Q : 0 ≤ genusDeficit TQ fuel dartsQ :=
    genusDeficit_nonneg TQ dartsQ h_nodup_Q h_comp_Q h_len_Q
  have h_split := genusDeficit_pred_split T fuel darts h_nodup h_comp h_fuel P h_e h_n
  have h_eq : genusDeficit TP fuel' darts' = genusDeficit TP fuel dartsP :=
    genusDeficit_eq_of_complete TP darts' dartsP h_nodup' h_comp' h_nodup_P h_comp_P h_fuel' h_len_P
  change genusDeficit TP fuel' darts' ≤ genusDeficit T fuel darts
  rw [h_eq, h_split]
  change genusDeficit TP fuel dartsP ≤ genusDeficit TP fuel dartsP + genusDeficit TQ fuel dartsQ
  omega

instance instDecidableEqExciseDart (H : Hypermap) [DecidableEq H.Dart]
    (removed : List H.Dart) (e' n' f' : Perm H.Dart)
    (h_e_inv : ∀ d, e'.f (e'.f d) = d)
    (h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_edge : ∀ d, d ∈ removed ↔ e'.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ n'.f d ∈ removed) :
    DecidableEq (H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node).Dart :=
  inferInstanceAs (DecidableEq { d : H.Dart // ¬ d ∈ removed })

/-- Monotonicity of `genusDeficit` under general `Hypermap.exciseSubtype`. -/
theorem genusDeficit_exciseSubtype_le (H : Hypermap) [DecidableEq H.Dart]
    (darts removed : List H.Dart)
    (e' n' f' : Perm H.Dart)
    (h_e_inv : ∀ d, e'.f (e'.f d) = d)
    (h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_edge : ∀ d, d ∈ removed ↔ e'.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ n'.f d ∈ removed)
    (h_nodup : darts.Nodup) (h_comp : ∀ d, d ∈ darts)
    {fuel fuel' : Nat} (h_fuel : darts.length ≤ fuel)
    (darts' : List (H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node).Dart)
    (h_nodup' : darts'.Nodup)
    (h_comp' : ∀ x : (H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node).Dart, x ∈ darts')
    (h_fuel' : darts'.length ≤ fuel') :
    genusDeficit (H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node).hypermapToTriple fuel' darts' ≤
      genusDeficit ⟨e', n', f', h_enf⟩ fuel darts := by
  let T' : PermTriple H.Dart := ⟨e', n', f', h_enf⟩
  let P : H.Dart → Prop := fun d => ¬ d ∈ removed
  have hPe : ∀ d, P d ↔ P (T'.e.f d) := fun d => not_congr (h_edge d)
  have hPn : ∀ d, P d ↔ P (T'.n.f d) := fun d => not_congr (h_node d)
  let H' := H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node
  have h_teq : H'.hypermapToTriple = restrictTriplePred T' P hPe hPn := by
    apply permTriple_eq_of_f_eq
    · intro x; rfl
    · intro x; rfl
    · intro x; rfl
  change genusDeficit H'.hypermapToTriple fuel' darts' ≤ genusDeficit T' fuel darts
  rw [h_teq]
  exact genusDeficit_restrictTriple_le T' fuel fuel' darts h_nodup h_comp h_fuel P hPe hPn
    darts' h_nodup' h_comp' h_fuel'

/-- General Planarity Preservation under `exciseSubtype` for any non-increasing triple `(e', n', f')`. -/
theorem exciseSubtype_isPlanar_of_perm (H : Hypermap) [DecidableEq H.Dart]
    (darts removed : List H.Dart)
    (e' n' f' : Perm H.Dart)
    (h_e_inv : ∀ d, e'.f (e'.f d) = d)
    (h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_edge : ∀ d, d ∈ removed ↔ e'.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ n'.f d ∈ removed)
    (h_nodup : darts.Nodup) (h_comp : ∀ d, d ∈ darts)
    {fuel fuel' : Nat} (h_fuel : darts.length ≤ fuel)
    (h_planar : H.isPlanar fuel darts = true)
    (h_gd_le : genusDeficit ⟨e', n', f', h_enf⟩ fuel darts ≤ genusDeficit H.hypermapToTriple fuel darts)
    (h_free : ∀ d : H.Dart, ¬ d ∈ removed → e'.f d ≠ d)
    (darts' : List (H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node).Dart)
    (h_nodup' : darts'.Nodup)
    (h_comp' : ∀ x : (H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node).Dart, x ∈ darts')
    (h_fuel' : darts'.length ≤ fuel') :
    (H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node).isPlanar fuel' darts' = true := by
  let H' := H.exciseSubtype removed e' n' f' h_e_inv h_enf h_edge h_node
  have h_H_gd : genusDeficit H.hypermapToTriple fuel darts = 0 :=
    ((eulerChar_le_two_mul_numComponents H darts h_nodup h_comp h_fuel).2.mp h_planar).1
  have h_le : genusDeficit H'.hypermapToTriple fuel' darts' ≤ genusDeficit ⟨e', n', f', h_enf⟩ fuel darts :=
    genusDeficit_exciseSubtype_le H darts removed e' n' f' h_e_inv h_enf h_edge h_node
      h_nodup h_comp h_fuel darts' h_nodup' h_comp' h_fuel'
  have h_nonneg : 0 ≤ genusDeficit H'.hypermapToTriple fuel' darts' :=
    genusDeficit_nonneg H'.hypermapToTriple darts' h_nodup' h_comp' h_fuel'
  have h_H'_gd : genusDeficit H'.hypermapToTriple fuel' darts' = 0 := by omega
  have h_H'_free : ∀ x : H'.Dart, H'.edge.f x ≠ x := fun x hfx =>
    h_free x.val x.property (congrArg Subtype.val hfx)
  exact (eulerChar_le_two_mul_numComponents H' darts' h_nodup' h_comp' h_fuel').2.mpr
    ⟨h_H'_gd, h_H'_free⟩

/-- Direct Planarity Preservation under `exciseSubtype` using `H`'s original permutations. -/
theorem exciseSubtype_isPlanar (H : Hypermap) [DecidableEq H.Dart]
    (darts removed : List H.Dart)
    (h_edge : ∀ d, d ∈ removed ↔ H.edge.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ H.node.f d ∈ removed)
    (h_nodup : darts.Nodup) (h_comp : ∀ d, d ∈ darts)
    {fuel fuel' : Nat} (h_fuel : darts.length ≤ fuel)
    (h_planar : H.isPlanar fuel darts = true)
    (darts' : List (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).Dart)
    (h_nodup' : darts'.Nodup)
    (h_comp' : ∀ x : (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).Dart, x ∈ darts')
    (h_fuel' : darts'.length ≤ fuel') :
    (H.exciseSubtype removed H.edge H.node H.face H.edge_involution H.edge_node_face_id h_edge h_node).isPlanar fuel' darts' = true := by
  have h_free : ∀ d : H.Dart, H.edge.f d ≠ d :=
    ((eulerChar_le_two_mul_numComponents H darts h_nodup h_comp h_fuel).2.mp h_planar).2
  exact exciseSubtype_isPlanar_of_perm H darts removed H.edge H.node H.face
    H.edge_involution H.edge_node_face_id h_edge h_node
    h_nodup h_comp h_fuel h_planar (Int.le_refl _) (fun d _ => h_free d)
    darts' h_nodup' h_comp' h_fuel'

private theorem swapCompLeft_edge_inv [DecidableEq D] (e : Perm D)
    (h_invol : ∀ x, e.f (e.f x) = x) (d : D) :
    let e1 := swapCompLeft e d (e.f d)
    ∀ x, e1.f (e1.f x) = x := by
  intro e1 x
  let b := e.f d
  have hb : e.f b = d := h_invol d
  by_cases hxd : x = d
  · subst hxd
    dsimp [e1, swapCompLeft, b]
    rw [swapFun_right, swapFun_right]
  · by_cases hxb : x = b
    · subst hxb
      dsimp [e1, swapCompLeft]
      change swapFun d b (e.f (swapFun d b (e.f b))) = b
      rw [hb, swapFun_left, hb, swapFun_left]
    · have hex_ne_d : e.f x ≠ d := fun heq => hxb (by dsimp [b]; rw [← heq, h_invol x])
      have hex_ne_b : e.f x ≠ b := fun heq => hxd (by
        calc x = e.f (e.f x) := (h_invol x).symm
        _ = e.f b := by rw [heq]
        _ = d := hb)
      dsimp [e1, swapCompLeft]
      change swapFun d b (e.f (swapFun d b (e.f x))) = x
      rw [swapFun_of_ne hex_ne_d hex_ne_b, h_invol x, swapFun_of_ne hxd hxb]

private theorem swapCompLeft_edge_mem_pair [DecidableEq D] (e : Perm D)
    (h_invol : ∀ x, e.f (e.f x) = x) (d : D) :
    ∀ x, x ∈ [d, e.f d] ↔ (swapCompLeft e d (e.f d)).f x ∈ [d, e.f d] := by
  intro x
  let b := e.f d
  have hb : e.f b = d := h_invol d
  by_cases hxd : x = d
  · subst hxd
    dsimp [swapCompLeft]
    rw [swapFun_right]
  · by_cases hxb : x = b
    · subst hxb
      dsimp [swapCompLeft]
      rw [hb, swapFun_left]
    · have hex_ne_d : e.f x ≠ d := fun heq => hxb (by dsimp [b]; rw [← heq, h_invol x])
      have hex_ne_b : e.f x ≠ b := fun heq => hxd (by
        calc x = e.f (e.f x) := (h_invol x).symm
        _ = e.f b := by rw [heq]
        _ = d := hb)
      dsimp [swapCompLeft]
      change (x ∈ [d, b]) ↔ swapFun d b (e.f x) ∈ [d, b]
      rw [swapFun_of_ne hex_ne_d hex_ne_b]
      simp [hxd, hxb, hex_ne_d, hex_ne_b]

private theorem bypass_fixes_self [DecidableEq D] (p : Perm D) (a : D) :
    (bypass p a).f a = a := by
  rw [bypass_eq_swapCompLeft]
  dsimp [swapCompLeft]
  exact swapFun_right a (p.f a)

private theorem perm_f_inj {D : Type} (p : Perm D) {x y : D} (h : p.f x = p.f y) : x = y := by
  calc
    x = p.inv (p.f x) := (p.left_inv x).symm
    _ = p.inv (p.f y) := by rw [h]
    _ = y := p.left_inv y

private theorem bypass_two_mem_pair [DecidableEq D] (p : Perm D) (a b : D) :
    ∀ x, x ∈ [a, b] ↔ (bypass (bypass p a) b).f x ∈ [a, b] := by
  let p1 := bypass p a
  let p2 := bypass p1 b
  have hp1a : p1.f a = a := bypass_fixes_self p a
  have hp2b : p2.f b = b := bypass_fixes_self p1 b
  have hp2a : p2.f a = a := by
    by_cases hab : a = b
    · subst hab; exact hp2b
    · rw [show p2 = bypass p1 b from rfl, bypass_eq_swapCompLeft]
      dsimp [swapCompLeft]
      rw [hp1a]
      have hne : p1.f b ≠ a := fun heq => hab (perm_f_inj p1 (by rw [heq, hp1a])).symm
      exact swapFun_of_ne hab hne.symm
  intro x
  constructor
  · intro hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [hp2a]; exact List.mem_cons_self
    · have hxb : x = b := by simpa using hx'
      subst hxb
      rw [hp2b]
      simp
  · intro hx
    by_cases hxa : x = a
    · subst hxa; exact List.mem_cons_self
    · by_cases hxb : x = b
      · subst hxb; simp
      · exfalso
        rcases List.mem_cons.mp hx with ha_eq | hb_eq
        · exact hxa (perm_f_inj p2 (by rw [ha_eq, hp2a]))
        · have hb_eq' : p2.f x = b := by simpa using hb_eq
          exact hxb (perm_f_inj p2 (by rw [hb_eq', hp2b]))

private def deleteEdgeTriple (H : Hypermap) [DecidableEq H.Dart] (d : H.Dart) : PermTriple H.Dart :=
  let b := H.edge.f d
  let T1 := uncoupleEdge H.hypermapToTriple d b
  have h1d : T1.e.f d = d := by
    dsimp [T1, uncoupleEdge, hypermapToTriple, swapCompLeft]
    exact swapFun_right d b
  let T2 := isolateFixed T1 d h1d
  have h2b : T2.e.f b = b := by
    dsimp [T2, isolateFixed, T1, uncoupleEdge, hypermapToTriple, swapCompLeft]
    rw [H.edge_involution d]
    exact swapFun_left d b
  isolateFixed T2 b h2b

/-- Construct the edge-deleted planar-ready subtype hypermap removing `{d, H.edge.f d}`. -/
def deleteEdgeSubtype (H : Hypermap) [DecidableEq H.Dart] (d : H.Dart) : Hypermap :=
  let T3 := deleteEdgeTriple H d
  have h_inv : ∀ x, T3.e.f (T3.e.f x) = x :=
    swapCompLeft_edge_inv H.edge H.edge_involution d
  have h_edge : ∀ x, x ∈ [d, H.edge.f d] ↔ T3.e.f x ∈ [d, H.edge.f d] :=
    swapCompLeft_edge_mem_pair H.edge H.edge_involution d
  have h_node : ∀ x, x ∈ [d, H.edge.f d] ↔ T3.n.f x ∈ [d, H.edge.f d] :=
    bypass_two_mem_pair H.node d (H.edge.f d)
  H.exciseSubtype [d, H.edge.f d] T3.e T3.n T3.f h_inv T3.enf_id h_edge h_node

instance instDecidableEqDeleteEdgeDart (H : Hypermap) [DecidableEq H.Dart] (d : H.Dart) :
    DecidableEq (H.deleteEdgeSubtype d).Dart :=
  instDecidableEqExciseDart H [d, H.edge.f d]
    (deleteEdgeTriple H d).e (deleteEdgeTriple H d).n (deleteEdgeTriple H d).f
    (swapCompLeft_edge_inv H.edge H.edge_involution d)
    (deleteEdgeTriple H d).enf_id
    (swapCompLeft_edge_mem_pair H.edge H.edge_involution d)
    (bypass_two_mem_pair H.node d (H.edge.f d))

theorem deleteEdgeSubtype_isPlanar (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_comp : ∀ z, z ∈ darts)
    {fuel fuel' : Nat} (h_fuel : darts.length ≤ fuel)
    (h_planar : H.isPlanar fuel darts = true)
    (d : H.Dart) (hd_ne : H.edge.f d ≠ d)
    (darts' : List (H.deleteEdgeSubtype d).Dart)
    (h_nodup' : darts'.Nodup)
    (h_comp' : ∀ x : (H.deleteEdgeSubtype d).Dart, x ∈ darts')
    (h_fuel' : darts'.length ≤ fuel') :
    (H.deleteEdgeSubtype d).isPlanar fuel' darts' = true := by
  let T0 := H.hypermapToTriple
  let b := H.edge.f d
  let T1 := uncoupleEdge T0 d b
  have h1d : T1.e.f d = d := by
    dsimp [T1, uncoupleEdge, T0, hypermapToTriple, swapCompLeft]
    exact swapFun_right d b
  let T2 := isolateFixed T1 d h1d
  have h2b : T2.e.f b = b := by
    dsimp [T2, isolateFixed, T1, uncoupleEdge, T0, hypermapToTriple, swapCompLeft]
    rw [H.edge_involution d]
    exact swapFun_left d b
  let T3 := isolateFixed T2 b h2b
  have h_gd1 : genusDeficit T1 fuel darts ≤ genusDeficit T0 fuel darts :=
    genusDeficit_uncoupleEdge_le T0 darts h_comp h_fuel hd_ne
  have h_gd2 : genusDeficit T2 fuel darts = genusDeficit T1 fuel darts :=
    genusDeficit_isolateFixed_eq T1 d h1d darts h_comp h_fuel
  have h_gd3 : genusDeficit T3 fuel darts = genusDeficit T2 fuel darts :=
    genusDeficit_isolateFixed_eq T2 b h2b darts h_comp h_fuel
  have h_gd_le : genusDeficit (deleteEdgeTriple H d) fuel darts ≤
      genusDeficit H.hypermapToTriple fuel darts := by
    change genusDeficit T3 fuel darts ≤ genusDeficit T0 fuel darts
    omega
  have h_H_free : ∀ z : H.Dart, H.edge.f z ≠ z :=
    ((eulerChar_le_two_mul_numComponents H darts h_nodup h_comp h_fuel).2.mp h_planar).2
  have h_free' : ∀ z : H.Dart, ¬ z ∈ [d, H.edge.f d] → (deleteEdgeTriple H d).e.f z ≠ z := by
    intro z hz_nmem
    have hzd : z ≠ d := fun heq => hz_nmem (heq ▸ List.mem_cons_self)
    have hzb : z ≠ H.edge.f d := fun heq => hz_nmem (by simp [heq])
    have hez_d : H.edge.f z ≠ d := fun heq => hzb (by rw [← heq, H.edge_involution])
    have hez_b : H.edge.f z ≠ H.edge.f d := fun heq => hzd (perm_f_inj H.edge heq)
    change swapFun d (H.edge.f d) (H.edge.f z) ≠ z
    rw [swapFun_of_ne hez_d hez_b]
    exact h_H_free z
  have h_res := exciseSubtype_isPlanar_of_perm H darts [d, H.edge.f d]
    (deleteEdgeTriple H d).e (deleteEdgeTriple H d).n (deleteEdgeTriple H d).f
    (swapCompLeft_edge_inv H.edge H.edge_involution d)
    (deleteEdgeTriple H d).enf_id
    (swapCompLeft_edge_mem_pair H.edge H.edge_involution d)
    (bypass_two_mem_pair H.node d (H.edge.f d))
    h_nodup h_comp h_fuel h_planar h_gd_le h_free'
    darts' h_nodup' h_comp' h_fuel'
  dsimp only [deleteEdgeSubtype]
  rw [instBEqOfDecidableEq_eq (H.instDecidableEqDeleteEdgeDart d)
    (fun a b => H.instDecidableEqExciseDart [d, H.edge.f d]
      (deleteEdgeTriple H d).e (deleteEdgeTriple H d).n (deleteEdgeTriple H d).f
      (swapCompLeft_edge_inv H.edge H.edge_involution d)
      (deleteEdgeTriple H d).enf_id
      (swapCompLeft_edge_mem_pair H.edge H.edge_involution d)
      (bypass_two_mem_pair H.node d (H.edge.f d)) a b)]
  exact h_res

private def smoothDeg2Triple (H : Hypermap) [DecidableEq H.Dart] (x : H.Dart) : PermTriple H.Dart :=
  let y := H.node.f x
  let ex := H.edge.f x
  let ey := H.edge.f y
  let T1 := uncoupleEdge H.hypermapToTriple.rot x y
  let T2 := T1.rot.rot
  let T3 := uncoupleEdge T2 x ey
  uncoupleEdge T3 y ex

private theorem smoothDeg2_four_distinct (H : Hypermap) (x : H.Dart)
    (hx_ne : H.node.f x ≠ x)
    (hx_efree : H.edge.f x ≠ x)
    (hy_efree : H.edge.f (H.node.f x) ≠ H.node.f x)
    (h_noloop : H.edge.f x ≠ H.node.f x) :
    let y := H.node.f x
    let ex := H.edge.f x
    let ey := H.edge.f y
    y ≠ x ∧ ex ≠ x ∧ ey ≠ y ∧ ex ≠ y ∧ ey ≠ x ∧ ex ≠ ey := by
  intro y ex ey
  refine ⟨hx_ne, hx_efree, hy_efree, h_noloop, ?_, ?_⟩
  · intro hey_x
    apply h_noloop
    calc
      H.edge.f x = H.edge.f (H.edge.f y) := congrArg H.edge.f hey_x.symm
      _ = H.node.f x := H.edge_involution y
  · intro hex_ey
    exact hx_ne (perm_f_inj H.edge hex_ey).symm

private theorem smoothDeg2Triple_e_eval (H : Hypermap) [DecidableEq H.Dart] (x : H.Dart)
    (hx_ne : H.node.f x ≠ x)
    (hx_efree : H.edge.f x ≠ x)
    (hy_efree : H.edge.f (H.node.f x) ≠ H.node.f x)
    (h_noloop : H.edge.f x ≠ H.node.f x) :
    let y := H.node.f x
    let ex := H.edge.f x
    let ey := H.edge.f y
    let e4 := (smoothDeg2Triple H x).e
    e4.f x = x ∧ e4.f y = y ∧ e4.f ex = ey ∧ e4.f ey = ex ∧
      ∀ z, z ≠ x → z ≠ y → z ≠ ex → z ≠ ey → e4.f z = H.edge.f z := by
  intro y ex ey e4
  rcases smoothDeg2_four_distinct H x hx_ne hx_efree hy_efree h_noloop with
    ⟨hyx, hexx, heyy, hexy, heyx, hexey⟩
  have hdef : ∀ z, e4.f z = swapFun y ex (swapFun x ey (H.edge.f (swapFun x y z))) := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hdef x, swapFun_left, show H.edge.f y = ey from rfl, swapFun_right,
      swapFun_of_ne hyx.symm hexx.symm]
  · rw [hdef y, swapFun_right, show H.edge.f x = ex from rfl,
      swapFun_of_ne hexx hexey, swapFun_right]
  · rw [hdef ex, swapFun_of_ne hexx hexy, show H.edge.f ex = x from H.edge_involution x,
      swapFun_left, swapFun_of_ne heyy hexey.symm]
  · rw [hdef ey, swapFun_of_ne heyx heyy, show H.edge.f ey = y from H.edge_involution y,
      swapFun_of_ne hyx heyy.symm, swapFun_left]
  · intro z hzx hzy hzex hzey
    have hez_x : H.edge.f z ≠ x := fun heq => hzex (by
      calc z = H.edge.f (H.edge.f z) := (H.edge_involution z).symm
      _ = ex := by rw [heq])
    have hez_y : H.edge.f z ≠ y := fun heq => hzey (by
      calc z = H.edge.f (H.edge.f z) := (H.edge_involution z).symm
      _ = ey := by rw [heq])
    have hez_ex : H.edge.f z ≠ ex := fun heq => hzx (perm_f_inj H.edge heq)
    have hez_ey : H.edge.f z ≠ ey := fun heq => hzy (perm_f_inj H.edge heq)
    rw [hdef z, swapFun_of_ne hzx hzy, swapFun_of_ne hez_x hez_ey, swapFun_of_ne hez_y hez_ex]

private theorem smoothDeg2Triple_e_inv (H : Hypermap) [DecidableEq H.Dart] (x : H.Dart)
    (hx_ne : H.node.f x ≠ x)
    (hx_efree : H.edge.f x ≠ x)
    (hy_efree : H.edge.f (H.node.f x) ≠ H.node.f x)
    (h_noloop : H.edge.f x ≠ H.node.f x) :
    ∀ z, (smoothDeg2Triple H x).e.f ((smoothDeg2Triple H x).e.f z) = z := by
  rcases smoothDeg2Triple_e_eval H x hx_ne hx_efree hy_efree h_noloop with
    ⟨hfx, hfy, hfex, hfey, hfo⟩
  let y := H.node.f x
  let ex := H.edge.f x
  let ey := H.edge.f y
  intro z
  by_cases hzx : z = x
  · subst hzx; rw [hfx, hfx]
  · by_cases hzy : z = y
    · subst hzy; rw [hfy, hfy]
    · by_cases hzex : z = ex
      · subst hzex; rw [hfex, hfey]
      · by_cases hzey : z = ey
        · subst hzey; rw [hfey, hfex]
        · have hez_x : H.edge.f z ≠ x := fun heq => hzex (by
            calc z = H.edge.f (H.edge.f z) := (H.edge_involution z).symm
            _ = ex := by rw [heq])
          have hez_y : H.edge.f z ≠ y := fun heq => hzey (by
            calc z = H.edge.f (H.edge.f z) := (H.edge_involution z).symm
            _ = ey := by rw [heq])
          have hez_ex : H.edge.f z ≠ ex := fun heq => hzx (perm_f_inj H.edge heq)
          have hez_ey : H.edge.f z ≠ ey := fun heq => hzy (perm_f_inj H.edge heq)
          rw [hfo z hzx hzy hzex hzey, hfo (H.edge.f z) hez_x hez_y hez_ex hez_ey,
            H.edge_involution z]

private theorem smoothDeg2Triple_e_mem_pair (H : Hypermap) [DecidableEq H.Dart] (x : H.Dart)
    (hx_ne : H.node.f x ≠ x)
    (hx_efree : H.edge.f x ≠ x)
    (hy_efree : H.edge.f (H.node.f x) ≠ H.node.f x)
    (h_noloop : H.edge.f x ≠ H.node.f x) :
    ∀ z, z ∈ [x, H.node.f x] ↔ (smoothDeg2Triple H x).e.f z ∈ [x, H.node.f x] := by
  rcases smoothDeg2_four_distinct H x hx_ne hx_efree hy_efree h_noloop with
    ⟨hyx, hexx, heyy, hexy, heyx, hexey⟩
  rcases smoothDeg2Triple_e_eval H x hx_ne hx_efree hy_efree h_noloop with
    ⟨hfx, hfy, hfex, hfey, hfo⟩
  let y := H.node.f x
  let ex := H.edge.f x
  let ey := H.edge.f y
  intro z
  by_cases hzx : z = x
  · subst hzx; rw [hfx]
  · by_cases hzy : z = y
    · subst hzy; rw [hfy]
    · by_cases hzex : z = ex
      · rw [hzex, hfex]
        constructor
        · intro h; rcases List.mem_cons.mp h with h1 | h2
          · exact False.elim (hexx h1)
          · exact False.elim (hexy (by simpa using h2))
        · intro h; rcases List.mem_cons.mp h with h1 | h2
          · exact False.elim (heyx h1)
          · exact False.elim (heyy (by simpa using h2))
      · by_cases hzey : z = ey
        · rw [hzey, hfey]
          constructor
          · intro h; rcases List.mem_cons.mp h with h1 | h2
            · exact False.elim (heyx h1)
            · exact False.elim (heyy (by simpa using h2))
          · intro h; rcases List.mem_cons.mp h with h1 | h2
            · exact False.elim (hexx h1)
            · exact False.elim (hexy (by simpa using h2))
        · have hez_x : H.edge.f z ≠ x := fun heq => hzex (by
            calc z = H.edge.f (H.edge.f z) := (H.edge_involution z).symm
            _ = ex := by rw [heq])
          have hez_y : H.edge.f z ≠ y := fun heq => hzey (by
            calc z = H.edge.f (H.edge.f z) := (H.edge_involution z).symm
            _ = ey := by rw [heq])
          rw [hfo z hzx hzy hzex hzey]
          constructor
          · intro h; rcases List.mem_cons.mp h with h1 | h2
            · exact False.elim (hzx h1)
            · exact False.elim (hzy (by simpa using h2))
          · intro h; rcases List.mem_cons.mp h with h1 | h2
            · exact False.elim (hez_x h1)
            · exact False.elim (hez_y (by simpa using h2))

private theorem smoothDeg2Triple_n_mem_pair (H : Hypermap) [DecidableEq H.Dart] (x : H.Dart)
    (hy_back : H.node.f (H.node.f x) = x) :
    ∀ z, z ∈ [x, H.node.f x] ↔ (smoothDeg2Triple H x).n.f z ∈ [x, H.node.f x] := by
  let y := H.node.f x
  intro z
  have hnd : (smoothDeg2Triple H x).n.f z = swapFun x y (H.node.f z) := rfl
  rw [hnd]
  by_cases hzx : z = x
  · rw [hzx, show H.node.f x = y from rfl, swapFun_right]
  · by_cases hzy : z = y
    · rw [hzy, hy_back, swapFun_left]
    · have hnz_x : H.node.f z ≠ x := fun heq => hzy (perm_f_inj H.node (heq.trans hy_back.symm))
      have hnz_y : H.node.f z ≠ y := fun heq => hzx (perm_f_inj H.node heq)
      rw [swapFun_of_ne hnz_x hnz_y]
      constructor
      · intro h; rcases List.mem_cons.mp h with h1 | h2
        · exact False.elim (hzx h1)
        · exact False.elim (hzy (by simpa using h2))
      · intro h; rcases List.mem_cons.mp h with h1 | h2
        · exact False.elim (hnz_x h1)
        · exact False.elim (hnz_y (by simpa using h2))

/-- Smooth a degree-2 vertex `{x, H.node.f x}` out of a planar hypermap into a subtype. -/
def smoothDeg2Subtype (H : Hypermap) [DecidableEq H.Dart]
    (x : H.Dart)
    (hx_ne : H.node.f x ≠ x)
    (hy_back : H.node.f (H.node.f x) = x)
    (hx_efree : H.edge.f x ≠ x)
    (hy_efree : H.edge.f (H.node.f x) ≠ H.node.f x)
    (h_noloop : H.edge.f x ≠ H.node.f x) : Hypermap :=
  let T4 := smoothDeg2Triple H x
  H.exciseSubtype [x, H.node.f x] T4.e T4.n T4.f
    (smoothDeg2Triple_e_inv H x hx_ne hx_efree hy_efree h_noloop)
    T4.enf_id
    (smoothDeg2Triple_e_mem_pair H x hx_ne hx_efree hy_efree h_noloop)
    (smoothDeg2Triple_n_mem_pair H x hy_back)

instance instDecidableEqSmoothDeg2Dart (H : Hypermap) [DecidableEq H.Dart] (x : H.Dart)
    (hx_ne : H.node.f x ≠ x)
    (hy_back : H.node.f (H.node.f x) = x)
    (hx_efree : H.edge.f x ≠ x)
    (hy_efree : H.edge.f (H.node.f x) ≠ H.node.f x)
    (h_noloop : H.edge.f x ≠ H.node.f x) :
    DecidableEq (H.smoothDeg2Subtype x hx_ne hy_back hx_efree hy_efree h_noloop).Dart :=
  instDecidableEqExciseDart H [x, H.node.f x]
    (smoothDeg2Triple H x).e (smoothDeg2Triple H x).n (smoothDeg2Triple H x).f
    (smoothDeg2Triple_e_inv H x hx_ne hx_efree hy_efree h_noloop)
    (smoothDeg2Triple H x).enf_id
    (smoothDeg2Triple_e_mem_pair H x hx_ne hx_efree hy_efree h_noloop)
    (smoothDeg2Triple_n_mem_pair H x hy_back)

theorem smoothDeg2Subtype_isPlanar (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_comp : ∀ z, z ∈ darts)
    {fuel fuel' : Nat} (h_fuel : darts.length ≤ fuel)
    (h_planar : H.isPlanar fuel darts = true)
    (x : H.Dart)
    (hx_ne : H.node.f x ≠ x)
    (hy_back : H.node.f (H.node.f x) = x)
    (hx_efree : H.edge.f x ≠ x)
    (hy_efree : H.edge.f (H.node.f x) ≠ H.node.f x)
    (h_noloop : H.edge.f x ≠ H.node.f x)
    (darts' : List (H.smoothDeg2Subtype x hx_ne hy_back hx_efree hy_efree h_noloop).Dart)
    (h_nodup' : darts'.Nodup)
    (h_comp' : ∀ z : (H.smoothDeg2Subtype x hx_ne hy_back hx_efree hy_efree h_noloop).Dart, z ∈ darts')
    (h_fuel' : darts'.length ≤ fuel') :
    (H.smoothDeg2Subtype x hx_ne hy_back hx_efree hy_efree h_noloop).isPlanar fuel' darts' = true := by
  let y := H.node.f x
  let ex := H.edge.f x
  let ey := H.edge.f y
  rcases smoothDeg2_four_distinct H x hx_ne hx_efree hy_efree h_noloop with
    ⟨_, hexx, heyy, hexy, heyx, hexey⟩
  let T0 := H.hypermapToTriple
  let T1 := uncoupleEdge T0.rot x y
  let T2 := T1.rot.rot
  let T3 := uncoupleEdge T2 x ey
  let T4 := uncoupleEdge T3 y ex
  have h_gd1 : genusDeficit T1 fuel darts ≤ genusDeficit T0 fuel darts := by
    have h1 := genusDeficit_uncoupleEdge_le T0.rot darts h_comp h_fuel hx_ne
    rw [genusDeficit_rot T0 fuel darts] at h1
    exact h1
  have h_gd2 : genusDeficit T2 fuel darts = genusDeficit T1 fuel darts := by
    dsimp [T2]
    rw [genusDeficit_rot T1.rot fuel darts, genusDeficit_rot T1 fuel darts]
  have hT2_ex : T2.e.f x = ey := by
    dsimp [T2, T1, PermTriple.rot, uncoupleEdge, T0, hypermapToTriple, swapCompRight]
    rw [swapFun_left]
  have h_gd3 : genusDeficit T3 fuel darts ≤ genusDeficit T2 fuel darts := by
    have h_ne2 : T2.e.f x ≠ x := by rw [hT2_ex]; exact heyx
    have h3 := genusDeficit_uncoupleEdge_le T2 darts h_comp h_fuel h_ne2
    change genusDeficit (uncoupleEdge T2 x (T2.e.f x)) fuel darts ≤ genusDeficit T2 fuel darts at h3
    rwa [hT2_ex] at h3
  have hT3_ey : T3.e.f y = ex := by
    dsimp [T3, uncoupleEdge, swapCompLeft]
    dsimp [T2, T1, PermTriple.rot, uncoupleEdge, swapCompRight, T0, hypermapToTriple]
    rw [swapFun_right, swapFun_of_ne hexx hexey]
  have h_gd4 : genusDeficit T4 fuel darts ≤ genusDeficit T3 fuel darts := by
    have h_ne3 : T3.e.f y ≠ y := by rw [hT3_ey]; exact hexy
    have h4 := genusDeficit_uncoupleEdge_le T3 darts h_comp h_fuel h_ne3
    change genusDeficit (uncoupleEdge T3 y (T3.e.f y)) fuel darts ≤ genusDeficit T3 fuel darts at h4
    rwa [hT3_ey] at h4
  have h_gd_le : genusDeficit (smoothDeg2Triple H x) fuel darts ≤
      genusDeficit H.hypermapToTriple fuel darts := by
    change genusDeficit T4 fuel darts ≤ genusDeficit T0 fuel darts
    omega
  have h_H_free : ∀ z : H.Dart, H.edge.f z ≠ z :=
    ((eulerChar_le_two_mul_numComponents H darts h_nodup h_comp h_fuel).2.mp h_planar).2
  have h_free' : ∀ z : H.Dart, ¬ z ∈ [x, y] → (smoothDeg2Triple H x).e.f z ≠ z := by
    rcases smoothDeg2Triple_e_eval H x hx_ne hx_efree hy_efree h_noloop with
      ⟨_, _, hfex, hfey, hfo⟩
    intro z hz_nmem
    have hzx : z ≠ x := fun heq => hz_nmem (heq ▸ List.mem_cons_self)
    have hzy : z ≠ y := fun heq => hz_nmem (by simp [heq])
    by_cases hzex : z = ex
    · subst hzex; rw [hfex]; exact hexey.symm
    · by_cases hzey : z = ey
      · subst hzey; rw [hfey]; exact hexey
      · rw [hfo z hzx hzy hzex hzey]
        exact h_H_free z
  have h_res := exciseSubtype_isPlanar_of_perm H darts [x, y]
    (smoothDeg2Triple H x).e (smoothDeg2Triple H x).n (smoothDeg2Triple H x).f
    (smoothDeg2Triple_e_inv H x hx_ne hx_efree hy_efree h_noloop)
    (smoothDeg2Triple H x).enf_id
    (smoothDeg2Triple_e_mem_pair H x hx_ne hx_efree hy_efree h_noloop)
    (smoothDeg2Triple_n_mem_pair H x hy_back)
    h_nodup h_comp h_fuel h_planar h_gd_le h_free'
    darts' h_nodup' h_comp' h_fuel'
  dsimp only [smoothDeg2Subtype]
  rw [instBEqOfDecidableEq_eq
    (H.instDecidableEqSmoothDeg2Dart x hx_ne hy_back hx_efree hy_efree h_noloop)
    (fun a b => H.instDecidableEqExciseDart [x, y]
      (smoothDeg2Triple H x).e (smoothDeg2Triple H x).n (smoothDeg2Triple H x).f
      (smoothDeg2Triple_e_inv H x hx_ne hx_efree hy_efree h_noloop)
      (smoothDeg2Triple H x).enf_id
      (smoothDeg2Triple_e_mem_pair H x hx_ne hx_efree hy_efree h_noloop)
      (smoothDeg2Triple_n_mem_pair H x hy_back) a b)]
  exact h_res

end PlanarSurgeryPreservation

end Hypermap
