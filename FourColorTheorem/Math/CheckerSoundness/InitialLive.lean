import FourColorTheorem.Math.CheckerSoundness.LoopInvariants

namespace Math
namespace CheckerSoundness

open FastReducer
open Batch
open Soundness

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

/-!
# Stage D2 & D4.1: Initial Live Set, Base-3 Digit Extraction, `S₃` Group Closure, and `extend` Invariance

This module establishes the algebraic and base-3 representation theorems connecting
boundary colorings `b : BoundaryColoring c`, `permDigit`, `permTraceAux`, `orbit6OfColoring`,
`FastReducer.extend`, and the initial state of `runReducerLoop`:

1. **`extend_relabelBoundary_eq`:** Under `IsSoundEarlier`, `IsWellFormedEarlier`, and
   `IsIrreflexiveAdj`, `FastReducer.extend` is invariant under `relabelBoundary θ` for
   every `θ : ColorPairing`.
2. **Exact `S₃` Coset Transitivity & Group Closure (`s3_coset_transitivity`, `permDigit_comp`, `permDigit_inv`):**
   The 6 digit permutations in `permDigit` form the full symmetric group $S_3$ on $\{0, 1, 2\}$
   and partition into 3 pairs under `swap12Digit`:
   - Pair 0: `p_0 = [0, 1, 2]` (`orb.j0`) and `p_1 = [0, 2, 1]` (`orb.j1`)
   - Pair 2: `p_2 = [1, 0, 2]` (`orb.j2`) and `p_4 = [2, 0, 1]` (`orb.j4`)
   - Pair 5: `p_5 = [2, 1, 0]` (`orb.j5`) and `p_3 = [1, 2, 0]` (`orb.j3`)
3. **Base-3 Trace Digit Extraction (`permTraceVal`, `permTraceAux_eq_iff`, `permTraceAux_lt_pow3`):**
   Exact injectivity and `< 3^r` boundedness of `permTraceAux` on base-3 edge digits.
4. **Ring-Cycle `S₄` Invariance of `extend` (`extend_eq_of_edge_digits`):**
   Any two valid boundary colorings on a ring cycle `IsRingCycle c` whose edge digits differ by
   `permDigit k` differ by a global $S_4$ color permutation and therefore have identical
   `FastReducer.extend` outcomes.
5. **`InitialLiveSpec`:** Clean structural specification of `initialLiveTotal`.
-/

/-- Under `IsSoundEarlier`, `IsWellFormedEarlier`, and `IsIrreflexiveAdj`,
    `FastReducer.extend` is invariant under `relabelBoundary θ` for any `θ : ColorPairing`. -/
theorem extend_relabelBoundary_eq (c : Configuration) (earlier : Array (Array Nat))
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (θ : ColorPairing) :
    (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c (relabelBoundary θ b))).1 =
      (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 :=
  extend_involution_eq c earlier h_earlier h_wf h_irrefl b hb (relabelColor θ) (relabelColor_inv θ)

/-- The `(12)` digit transposition swapping `1 ↔ 2` and fixing `0`. -/
def swap12Digit : Nat → Nat
  | 0 => 0
  | 1 => 2
  | 2 => 1
  | d => d

/-- `inOrbit6 (orbit6OfColoring r b0 pow3) j` holds iff `j` equals `permTraceAux (permDigit k)`
    for some `k : Fin 6`. -/
theorem inOrbit6_orbit6OfColoring_iff (r : Nat) (b0 : Nat → Color) (pow3 : Array Nat) (j : Nat) :
    inOrbit6 (orbit6OfColoring r b0 pow3) j ↔
      ∃ k : Fin 6, j = permTraceAux (permDigit k) r b0 pow3 r 0 0 := by
  dsimp [inOrbit6, orbit6OfColoring]
  constructor
  · rintro (h0 | h1 | h2 | h3 | h4 | h5)
    · exact ⟨⟨0, by decide⟩, h0⟩
    · exact ⟨⟨1, by decide⟩, h1⟩
    · exact ⟨⟨2, by decide⟩, h2⟩
    · exact ⟨⟨3, by decide⟩, h3⟩
    · exact ⟨⟨4, by decide⟩, h4⟩
    · exact ⟨⟨5, by decide⟩, h5⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    rcases k with _ | _ | _ | _ | _ | _ | k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · omega

theorem permDigit_zero_eq (d : Nat) (hd : d < 3) :
    permDigit ⟨0, by decide⟩ d = d := by
  revert d hd; decide

theorem permDigit_lt_three (k : Fin 6) (d : Nat) (hd : d < 3) :
    permDigit k d < 3 := by
  revert k d hd; decide

theorem permDigit_comp (k1 k2 : Fin 6) :
    ∃ k3 : Fin 6, ∀ d < 3, permDigit k1 (permDigit k2 d) = permDigit k3 d := by
  revert k1 k2; decide

theorem permDigit_inv (k : Fin 6) :
    ∃ k_inv : Fin 6, ∀ d < 3,
      permDigit k_inv (permDigit k d) = d ∧ permDigit k (permDigit k_inv d) = d := by
  revert k; decide

theorem relabelDigit_inv (θ : ColorPairing) (d : Nat) (hd : d < 3) :
    relabelDigit θ (relabelDigit θ d) = d := by
  rcases θ with ⟨a, b, c, d_col, h⟩
  revert d hd
  cases a <;> cases b <;> cases c <;> cases d_col <;> revert h <;> decide

theorem swap12Digit_permDigit_0 (d : Nat) (hd : d < 3) :
    swap12Digit (permDigit ⟨0, by decide⟩ d) = permDigit ⟨1, by decide⟩ d := by
  revert d hd; decide

theorem swap12Digit_permDigit_2 (d : Nat) (hd : d < 3) :
    swap12Digit (permDigit ⟨2, by decide⟩ d) = permDigit ⟨4, by decide⟩ d := by
  revert d hd; decide

theorem swap12Digit_permDigit_5 (d : Nat) (hd : d < 3) :
    swap12Digit (permDigit ⟨5, by decide⟩ d) = permDigit ⟨3, by decide⟩ d := by
  revert d hd; decide

/-- Composing `relabelDigit θ` with `permDigit k` yields another `permDigit k'` on `{0, 1, 2}`:
    for every `θ : ColorPairing` and `k : Fin 6`, there exists `k' : Fin 6` such that
    `∀ d < 3, relabelDigit θ (permDigit k d) = permDigit k' d`. -/
theorem relabelDigit_comp_permDigit (θ : ColorPairing) (k : Fin 6) :
    ∃ k' : Fin 6, ∀ d < 3, relabelDigit θ (permDigit k d) = permDigit k' d := by
  rcases θ with ⟨a, b, c, d, h⟩
  revert k
  cases a <;> cases b <;> cases c <;> cases d <;> revert h <;> decide

/-- **Exact `S₃` Coset Transitivity Theorem:**
    For every `k : Fin 6` and every canonical pairing index `m ∈ {0, 2, 5}` (corresponding to
    `orb.j0`, `orb.j2`, `orb.j5`), there exists `θ ∈ [theta1, theta2, theta3]` such that on all
    digits `d < 3`, `relabelDigit θ (permDigit k d)` equals either `permDigit m d` or
    `swap12Digit (permDigit m d)`. -/
theorem s3_coset_transitivity (k m : Fin 6)
    (hm : m = ⟨0, by decide⟩ ∨ m = ⟨2, by decide⟩ ∨ m = ⟨5, by decide⟩) :
    ∃ θ ∈ [theta1, theta2, theta3],
      (∀ d < 3, relabelDigit θ (permDigit k d) = permDigit m d) ∨
      (∀ d < 3, relabelDigit θ (permDigit k d) = swap12Digit (permDigit m d)) := by
  revert k m hm
  decide

/-- If two digit permutations `p1, p2` agree on all digits `< 3`, then `permTraceAux p1` and
    `permTraceAux p2` are equal everywhere. -/
theorem permTraceAux_congr (p1 p2 : Nat → Nat) (r : Nat) (b0 : Nat → Color) (pow3 : Array Nat)
    (h_eq : ∀ d < 3, p1 d = p2 d) (rem i acc : Nat) :
    permTraceAux p1 r b0 pow3 rem i acc = permTraceAux p2 r b0 pow3 rem i acc := by
  induction rem generalizing i acc with
  | zero => rfl
  | succ rem ih =>
    dsimp [permTraceAux]
    have hd_lt : (let diff := (b0 i).toNat ^^^ (b0 ((i + 1) % r)).toNat; if diff > 0 then diff - 1 else 0) < 3 := by
      cases b0 i <;> cases b0 ((i + 1) % r) <;> decide
    rw [h_eq _ hd_lt]
    exact ih (i + 1) _

/-- Edge digit `d_i ∈ {0, 1, 2}` of boundary coloring `b` at ring index `i`. -/
def edgeDigitAt (r : Nat) (b : Nat → Color) (i : Nat) : Nat :=
  let diff := (b i).toNat ^^^ (b ((i + 1) % r)).toNat
  if diff > 0 then diff - 1 else 0

theorem edgeDigitAt_lt_three (r : Nat) (b : Nat → Color) (i : Nat) :
    edgeDigitAt r b i < 3 := by
  dsimp [edgeDigitAt]
  cases b i <;> cases b ((i + 1) % r) <;> decide

/-- `boundaryTrace c b pow3` equals `permTraceAux (permDigit 0) c.ringSize b pow3 c.ringSize 0 0`. -/
theorem boundaryTrace_eq_permTraceAux_zero (c : Configuration) (b : BoundaryColoring c) (pow3 : Array Nat) :
    boundaryTrace c b pow3 =
      permTraceAux (permDigit ⟨0, by decide⟩) c.ringSize b pow3 c.ringSize 0 0 := by
  unfold boundaryTrace
  rw [← permTraceAux_id c.ringSize b pow3 c.ringSize 0 0]
  exact permTraceAux_congr (fun d => d) (permDigit ⟨0, by decide⟩) c.ringSize b pow3
    (fun d hd => (permDigit_zero_eq d hd).symm) c.ringSize 0 0

/-!
### Base-3 Digit Extraction and Injectivity of `permTraceAux` (`permTraceVal`)
-/

/-- Shifted base-3 value of `permTraceAux`: accumulates `p (edgeDigitAt r b0 i) + 3 * rest`. -/
def permTraceVal (p : Nat → Nat) (r : Nat) (b0 : Nat → Color) : Nat → Nat → Nat
  | 0, _ => 0
  | rem + 1, i => p (edgeDigitAt r b0 i) + 3 * permTraceVal p r b0 rem (i + 1)

/-- When `∀ idx < r, pow3.getD idx 0 = 3 ^ idx`, `permTraceAux` equals `acc + permTraceVal * 3 ^ i`. -/
theorem permTraceAux_eq_permTraceVal (p : Nat → Nat) (r : Nat) (b0 : Nat → Color)
    (pow3 : Array Nat) (h_pow : ∀ idx < r, pow3.getD idx 0 = 3 ^ idx)
    (rem i acc : Nat) (h_le : i + rem ≤ r) :
    permTraceAux p r b0 pow3 rem i acc = acc + permTraceVal p r b0 rem i * 3 ^ i := by
  induction rem generalizing i acc with
  | zero =>
    dsimp [permTraceAux, permTraceVal]
    omega
  | succ rem ih =>
    have hi : i < r := by omega
    dsimp [permTraceAux, permTraceVal]
    change permTraceAux p r b0 pow3 rem (i + 1) (acc + p (edgeDigitAt r b0 i) * pow3.getD i 0) =
      acc + (p (edgeDigitAt r b0 i) + 3 * permTraceVal p r b0 rem (i + 1)) * 3 ^ i
    rw [h_pow i hi, ih (i + 1) _ (by omega), Nat.pow_succ]
    rw [Nat.add_mul, Nat.mul_comm 3 (permTraceVal p r b0 rem (i + 1)), Nat.mul_assoc,
        Nat.mul_comm (3 ^ i) 3, ← Nat.add_assoc]

/-- At `i = 0, acc = 0, rem = r`, `permTraceAux` equals `permTraceVal p r b0 r 0`. -/
theorem permTraceAux_zero_eq_permTraceVal (p : Nat → Nat) (r : Nat) (b0 : Nat → Color)
    (pow3 : Array Nat) (h_pow : ∀ idx < r, pow3.getD idx 0 = 3 ^ idx) :
    permTraceAux p r b0 pow3 r 0 0 = permTraceVal p r b0 r 0 := by
  rw [permTraceAux_eq_permTraceVal p r b0 pow3 h_pow r 0 0 (by omega)]
  simp

/-- When `p` maps `{0, 1, 2}` into `{0, 1, 2}`, `permTraceVal p r b0 rem i < 3 ^ rem`. -/
theorem permTraceVal_lt_pow3 (p : Nat → Nat) (hp : ∀ d < 3, p d < 3)
    (r : Nat) (b0 : Nat → Color) (rem i : Nat) :
    permTraceVal p r b0 rem i < 3 ^ rem := by
  induction rem generalizing i with
  | zero =>
    dsimp [permTraceVal]
    decide
  | succ rem ih =>
    dsimp [permTraceVal]
    have hd : p (edgeDigitAt r b0 i) < 3 := hp _ (edgeDigitAt_lt_three r b0 i)
    have h_ih := ih (i + 1)
    rw [Nat.pow_succ]
    omega

/-- When `∀ idx < r, pow3.getD idx 0 = 3 ^ idx`, `permTraceAux (permDigit k) r b0 pow3 r 0 0 < 3 ^ r`. -/
theorem permTraceAux_permDigit_lt_pow3 (k : Fin 6) (r : Nat) (b0 : Nat → Color)
    (pow3 : Array Nat) (h_pow : ∀ idx < r, pow3.getD idx 0 = 3 ^ idx) :
    permTraceAux (permDigit k) r b0 pow3 r 0 0 < 3 ^ r := by
  rw [permTraceAux_zero_eq_permTraceVal (permDigit k) r b0 pow3 h_pow]
  exact permTraceVal_lt_pow3 (permDigit k) (permDigit_lt_three k) r b0 r 0

/-- Base-3 digit injectivity of `permTraceVal`: two `permTraceVal` sums over `rem` digits are equal
    if and only if all `rem` base-3 digits are equal. -/
theorem permTraceVal_eq_iff (p1 p2 : Nat → Nat)
    (hp1 : ∀ d < 3, p1 d < 3) (hp2 : ∀ d < 3, p2 d < 3)
    (r : Nat) (b1 b2 : Nat → Color) (rem i : Nat) :
    permTraceVal p1 r b1 rem i = permTraceVal p2 r b2 rem i ↔
      ∀ idx < rem, p1 (edgeDigitAt r b1 (i + idx)) = p2 (edgeDigitAt r b2 (i + idx)) := by
  induction rem generalizing i with
  | zero =>
    dsimp [permTraceVal]
    constructor
    · intro _ idx h_lt; omega
    · intro _; rfl
  | succ rem ih =>
    dsimp [permTraceVal]
    have hd1 : p1 (edgeDigitAt r b1 i) < 3 := hp1 _ (edgeDigitAt_lt_three r b1 i)
    have hd2 : p2 (edgeDigitAt r b2 i) < 3 := hp2 _ (edgeDigitAt_lt_three r b2 i)
    constructor
    · intro h_eq idx h_lt
      have h_d_eq : p1 (edgeDigitAt r b1 i) = p2 (edgeDigitAt r b2 i) := by omega
      have h_v_eq : permTraceVal p1 r b1 rem (i + 1) = permTraceVal p2 r b2 rem (i + 1) := by omega
      cases idx with
      | zero =>
        rw [Nat.add_zero]
        exact h_d_eq
      | succ idx' =>
        have h_step := (ih (i + 1)).mp h_v_eq idx' (by omega)
        have h_add : i + 1 + idx' = i + (idx' + 1) := by omega
        rwa [h_add] at h_step
    · intro h_all
      have h0 := h_all 0 (by omega)
      rw [Nat.add_zero] at h0
      have h_rest : ∀ idx' < rem,
          p1 (edgeDigitAt r b1 (i + 1 + idx')) = p2 (edgeDigitAt r b2 (i + 1 + idx')) := by
        intro idx' h_lt'
        have h_add : i + 1 + idx' = i + (idx' + 1) := by omega
        rw [h_add]
        exact h_all (idx' + 1) (by omega)
      have h_v_eq := (ih (i + 1)).mpr h_rest
      omega

/-- Exact base-3 injectivity of `permTraceAux`: when `∀ idx < r, pow3.getD idx 0 = 3 ^ idx`,
    two `permTraceAux` values agree iff their permuted edge digits agree at every index `< r`. -/
theorem permTraceAux_eq_iff (p1 p2 : Nat → Nat)
    (hp1 : ∀ d < 3, p1 d < 3) (hp2 : ∀ d < 3, p2 d < 3)
    (r : Nat) (b1 b2 : Nat → Color) (pow3 : Array Nat)
    (h_pow : ∀ idx < r, pow3.getD idx 0 = 3 ^ idx) :
    permTraceAux p1 r b1 pow3 r 0 0 = permTraceAux p2 r b2 pow3 r 0 0 ↔
      ∀ idx < r, p1 (edgeDigitAt r b1 idx) = p2 (edgeDigitAt r b2 idx) := by
  rw [permTraceAux_zero_eq_permTraceVal p1 r b1 pow3 h_pow,
      permTraceAux_zero_eq_permTraceVal p2 r b2 pow3 h_pow,
      permTraceVal_eq_iff p1 p2 hp1 hp2 r b1 b2 r 0]
  simp

/-- **Theorem D4.1a (`inOrbit6_orbit6OfColoring_digits_iff`):**
    When `∀ idx < r, pow3.getD idx 0 = 3 ^ idx`, `boundaryTrace c b pow3` belongs to
    `orbit6OfColoring c.ringSize b0 pow3` iff there exists `k : Fin 6` such that
    `∀ idx < c.ringSize, edgeDigitAt c.ringSize b idx = permDigit k (edgeDigitAt c.ringSize b0 idx)`. -/
theorem inOrbit6_orbit6OfColoring_digits_iff (c : Configuration)
    (b b0 : BoundaryColoring c) (pow3 : Array Nat)
    (h_pow : ∀ idx < c.ringSize, pow3.getD idx 0 = 3 ^ idx) :
    inOrbit6 (orbit6OfColoring c.ringSize b0 pow3) (boundaryTrace c b pow3) ↔
      ∃ k : Fin 6, ∀ idx < c.ringSize,
        edgeDigitAt c.ringSize b idx = permDigit k (edgeDigitAt c.ringSize b0 idx) := by
  rw [boundaryTrace_eq_permTraceAux_zero c b pow3,
      inOrbit6_orbit6OfColoring_iff c.ringSize b0 pow3]
  constructor
  · rintro ⟨k, h_eq⟩
    refine ⟨k, ?_⟩
    have h_digits := (permTraceAux_eq_iff (permDigit ⟨0, by decide⟩) (permDigit k)
      (permDigit_lt_three ⟨0, by decide⟩) (permDigit_lt_three k) c.ringSize b b0 pow3 h_pow).mp h_eq
    intro idx h_lt
    have h_step := h_digits idx h_lt
    rwa [permDigit_zero_eq _ (edgeDigitAt_lt_three c.ringSize b idx)] at h_step
  · rintro ⟨k, h_digits⟩
    refine ⟨k, ?_⟩
    apply (permTraceAux_eq_iff (permDigit ⟨0, by decide⟩) (permDigit k)
      (permDigit_lt_three ⟨0, by decide⟩) (permDigit_lt_three k) c.ringSize b b0 pow3 h_pow).mpr
    intro idx h_lt
    rw [permDigit_zero_eq _ (edgeDigitAt_lt_three c.ringSize b idx)]
    exact h_digits idx h_lt

/-- **Theorem D4.1b (`inOrbit6_orbit6OfColoring_trans`):**
    Since `S₃` acts as a group via `permDigit`, if `orbit6OfColoring r b1 pow3` and
    `orbit6OfColoring r b2 pow3` share any trace index `j`, then every trace index `x` in
    `orbit6OfColoring r b1 pow3` also belongs to `orbit6OfColoring r b2 pow3`. -/
theorem inOrbit6_orbit6OfColoring_trans (r : Nat) (b1 b2 : Nat → Color) (pow3 : Array Nat)
    (h_pow : ∀ idx < r, pow3.getD idx 0 = 3 ^ idx)
    (j x : Nat)
    (hj1 : inOrbit6 (orbit6OfColoring r b1 pow3) j)
    (hj2 : inOrbit6 (orbit6OfColoring r b2 pow3) j)
    (hx1 : inOrbit6 (orbit6OfColoring r b1 pow3) x) :
    inOrbit6 (orbit6OfColoring r b2 pow3) x := by
  rcases (inOrbit6_orbit6OfColoring_iff r b1 pow3 j).mp hj1 with ⟨k1, hk1⟩
  rcases (inOrbit6_orbit6OfColoring_iff r b2 pow3 j).mp hj2 with ⟨k2, hk2⟩
  rcases (inOrbit6_orbit6OfColoring_iff r b1 pow3 x).mp hx1 with ⟨kx, hkx⟩
  have h_eq : permTraceAux (permDigit k1) r b1 pow3 r 0 0 = permTraceAux (permDigit k2) r b2 pow3 r 0 0 :=
    hk1.symm.trans hk2
  have h_dig := (permTraceAux_eq_iff (permDigit k1) (permDigit k2)
    (permDigit_lt_three k1) (permDigit_lt_three k2) r b1 b2 pow3 h_pow).mp h_eq
  rcases permDigit_inv k1 with ⟨k1_inv, hk1_inv⟩
  rcases permDigit_comp kx k1_inv with ⟨k_mid, hk_mid⟩
  rcases permDigit_comp k_mid k2 with ⟨ky, hky⟩
  rw [inOrbit6_orbit6OfColoring_iff r b2 pow3 x]
  refine ⟨ky, ?_⟩
  rw [hkx]
  apply (permTraceAux_eq_iff (permDigit kx) (permDigit ky)
    (permDigit_lt_three kx) (permDigit_lt_three ky) r b1 b2 pow3 h_pow).mpr
  intro idx h_lt
  have hd1 := edgeDigitAt_lt_three r b1 idx
  have hd2 := edgeDigitAt_lt_three r b2 idx
  have h_inv_d1 := (hk1_inv (edgeDigitAt r b1 idx) hd1).1
  rw [← h_inv_d1, h_dig idx h_lt]
  have hd2_k2 : permDigit k2 (edgeDigitAt r b2 idx) < 3 := permDigit_lt_three k2 _ hd2
  rw [hk_mid _ hd2_k2, hky _ hd2]

/-- If `b` has edge digits `p (edgeDigitAt r b0 i)` for all `i < r`, then applying `q` via
    `permTraceAux q r b` equals `permTraceAux (fun d => q (p d)) r b0`. -/
theorem permTraceAux_comp_of_edge_digits (p q : Nat → Nat) (r : Nat) (b b0 : Nat → Color)
    (pow3 : Array Nat) (rem i acc : Nat) (h_le : i + rem ≤ r)
    (h_digits : ∀ idx < r, edgeDigitAt r b idx = p (edgeDigitAt r b0 idx)) :
    permTraceAux q r b pow3 rem i acc =
      permTraceAux (fun d => q (p d)) r b0 pow3 rem i acc := by
  induction rem generalizing i acc with
  | zero => rfl
  | succ rem ih =>
    have hi : i < r := by omega
    have hd := h_digits i hi
    dsimp [permTraceAux]
    change permTraceAux q r b pow3 rem (i + 1) (acc + q (edgeDigitAt r b i) * pow3.getD i 0) =
      permTraceAux (fun d => q (p d)) r b0 pow3 rem (i + 1) (acc + q (p (edgeDigitAt r b0 i)) * pow3.getD i 0)
    rw [hd]
    exact ih (i + 1) _ (by omega)

/-- On a ring cycle `IsRingCycle c`, if valid boundary coloring `b` has edge digits
    `permDigit k (edgeDigitAt c.ringSize b0 i)`, then for every `θ : ColorPairing`,
    `boundaryTraceTheta c b θ pow3` belongs to `orbit6OfColoring c.ringSize b0 pow3`. -/
theorem relabel_inOrbit6_of_edge_digits (c : Configuration) (h_ring : IsRingCycle c)
    (b b0 : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (pow3 : Array Nat) (k : Fin 6)
    (h_digits : ∀ idx < c.ringSize, edgeDigitAt c.ringSize b idx = permDigit k (edgeDigitAt c.ringSize b0 idx))
    (θ : ColorPairing) :
    inOrbit6 (orbit6OfColoring c.ringSize b0 pow3) (boundaryTraceTheta c b θ pow3) := by
  rw [boundaryTrace_relabel c h_ring b hb θ pow3,
      permTraceAux_comp_of_edge_digits (permDigit k) (relabelDigit θ) c.ringSize b b0 pow3
        c.ringSize 0 0 (by omega) h_digits]
  rcases relabelDigit_comp_permDigit θ k with ⟨k', hk'⟩
  rw [permTraceAux_congr (fun d => relabelDigit θ (permDigit k d)) (permDigit k')
        c.ringSize b0 pow3 hk' c.ringSize 0 0]
  exact (inOrbit6_orbit6OfColoring_iff c.ringSize b0 pow3 _).mpr ⟨k', rfl⟩

/-- **Theorem D4.1c (`relabel_same_orbit_of_orbit6OfColoring`):**
    On a ring cycle `IsRingCycle c` with `∀ idx < c.ringSize, pow3.getD idx 0 = 3 ^ idx`,
    for any valid boundary coloring `b`, `inOrbit6 (orbit6OfColoring c.ringSize b0 pow3)`
    is invariant under `boundaryTraceTheta c b θ pow3`. -/
theorem relabel_same_orbit_of_orbit6OfColoring (c : Configuration) (h_ring : IsRingCycle c)
    (b b0 : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (pow3 : Array Nat) (h_pow : ∀ idx < c.ringSize, pow3.getD idx 0 = 3 ^ idx)
    (θ : ColorPairing) :
    inOrbit6 (orbit6OfColoring c.ringSize b0 pow3) (boundaryTrace c b pow3) ↔
      inOrbit6 (orbit6OfColoring c.ringSize b0 pow3) (boundaryTraceTheta c b θ pow3) := by
  constructor
  · intro h_in
    rcases (inOrbit6_orbit6OfColoring_digits_iff c b b0 pow3 h_pow).mp h_in with ⟨k, hk⟩
    exact relabel_inOrbit6_of_edge_digits c h_ring b b0 hb pow3 k hk θ
  · intro h_in_theta
    have hb_theta : IsValidBoundaryColoring c (relabelBoundary θ b) :=
      relabelBoundary_valid c b θ hb
    have h_in' : inOrbit6 (orbit6OfColoring c.ringSize b0 pow3) (boundaryTrace c (relabelBoundary θ b) pow3) :=
      h_in_theta
    rcases (inOrbit6_orbit6OfColoring_digits_iff c (relabelBoundary θ b) b0 pow3 h_pow).mp h_in' with ⟨k, hk⟩
    have h_step := relabel_inOrbit6_of_edge_digits c h_ring (relabelBoundary θ b) b0 hb_theta pow3 k hk θ
    have h_inv_b : relabelBoundary θ (relabelBoundary θ b) = b := by
      funext i
      exact relabelColor_inv θ (b i)
    unfold boundaryTraceTheta at h_step
    rwa [h_inv_b] at h_step

/-- On a ring cycle `IsRingCycle c`, if valid boundary coloring `b` has edge digits
    `permDigit k (edgeDigitAt c.ringSize b0 i)`, then for each canonical pairing index
    `m ∈ {0, 2, 5}` of `orb = orbit6OfColoring c.ringSize b0 pow3`, there exists
    `θ ∈ [theta1, theta2, theta3]` such that `boundaryTraceTheta c b θ pow3` equals either
    the `m`-th trace or its `(12)`-conjugate `swap12Digit ∘ permDigit m`. -/
theorem pairing_cover_trace_of_edge_digits (c : Configuration) (h_ring : IsRingCycle c)
    (b b0 : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (pow3 : Array Nat) (k m : Fin 6)
    (hm : m = ⟨0, by decide⟩ ∨ m = ⟨2, by decide⟩ ∨ m = ⟨5, by decide⟩)
    (h_digits : ∀ idx < c.ringSize, edgeDigitAt c.ringSize b idx = permDigit k (edgeDigitAt c.ringSize b0 idx)) :
    ∃ θ ∈ [theta1, theta2, theta3],
      boundaryTraceTheta c b θ pow3 = permTraceAux (permDigit m) c.ringSize b0 pow3 c.ringSize 0 0 ∨
      boundaryTraceTheta c b θ pow3 =
        permTraceAux (fun d => swap12Digit (permDigit m d)) c.ringSize b0 pow3 c.ringSize 0 0 := by
  rcases s3_coset_transitivity k m hm with ⟨θ, hθ_mem, h_id | h_swap⟩
  · refine ⟨θ, hθ_mem, Or.inl ?_⟩
    rw [boundaryTrace_relabel c h_ring b hb θ pow3,
        permTraceAux_comp_of_edge_digits (permDigit k) (relabelDigit θ) c.ringSize b b0 pow3
          c.ringSize 0 0 (by omega) h_digits]
    exact permTraceAux_congr (fun d => relabelDigit θ (permDigit k d)) (permDigit m)
      c.ringSize b0 pow3 h_id c.ringSize 0 0
  · refine ⟨θ, hθ_mem, Or.inr ?_⟩
    rw [boundaryTrace_relabel c h_ring b hb θ pow3,
        permTraceAux_comp_of_edge_digits (permDigit k) (relabelDigit θ) c.ringSize b b0 pow3
          c.ringSize 0 0 (by omega) h_digits]
    exact permTraceAux_congr (fun d => relabelDigit θ (permDigit k d)) (fun d => swap12Digit (permDigit m d))
      c.ringSize b0 pow3 h_swap c.ringSize 0 0

/-- **Theorem D4.1d (`pairing_cover_orbit_of_orbit6OfColoring`):**
    For `orb = orbit6OfColoring c.ringSize b0 pow3`, if `inOrbit6 orb (boundaryTrace c b pow3)`,
    then for each of the 3 `(12)`-symmetric trace pairs `(orb.j0, orb.j1)`, `(orb.j2, orb.j4)`,
    `(orb.j5, orb.j3)`, there exists `θ : ColorPairing` such that `boundaryTraceTheta c b θ pow3`
    equals one of the two traces in that pair. -/
theorem pairing_cover_orbit_of_orbit6OfColoring (c : Configuration) (h_ring : IsRingCycle c)
    (b b0 : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (pow3 : Array Nat) (h_pow : ∀ idx < c.ringSize, pow3.getD idx 0 = 3 ^ idx)
    (h_in : inOrbit6 (orbit6OfColoring c.ringSize b0 pow3) (boundaryTrace c b pow3))
    (j_a j_b : Nat)
    (h_pair :
      (j_a = (orbit6OfColoring c.ringSize b0 pow3).j0 ∧ j_b = (orbit6OfColoring c.ringSize b0 pow3).j1) ∨
      (j_a = (orbit6OfColoring c.ringSize b0 pow3).j2 ∧ j_b = (orbit6OfColoring c.ringSize b0 pow3).j4) ∨
      (j_a = (orbit6OfColoring c.ringSize b0 pow3).j5 ∧ j_b = (orbit6OfColoring c.ringSize b0 pow3).j3)) :
    ∃ θ : ColorPairing,
      boundaryTraceTheta c b θ pow3 = j_a ∨ boundaryTraceTheta c b θ pow3 = j_b := by
  rcases (inOrbit6_orbit6OfColoring_digits_iff c b b0 pow3 h_pow).mp h_in with ⟨k, hk⟩
  rcases h_pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases pairing_cover_trace_of_edge_digits c h_ring b b0 hb pow3 k ⟨0, by decide⟩ (Or.inl rfl) hk with
      ⟨θ, _, h_l | h_r⟩
    · exact ⟨θ, Or.inl h_l⟩
    · refine ⟨θ, Or.inr ?_⟩
      rw [h_r]
      exact permTraceAux_congr _ _ c.ringSize b0 pow3 swap12Digit_permDigit_0 c.ringSize 0 0
  · rcases pairing_cover_trace_of_edge_digits c h_ring b b0 hb pow3 k ⟨2, by decide⟩ (Or.inr (Or.inl rfl)) hk with
      ⟨θ, _, h_l | h_r⟩
    · exact ⟨θ, Or.inl h_l⟩
    · refine ⟨θ, Or.inr ?_⟩
      rw [h_r]
      exact permTraceAux_congr _ _ c.ringSize b0 pow3 swap12Digit_permDigit_2 c.ringSize 0 0
  · rcases pairing_cover_trace_of_edge_digits c h_ring b b0 hb pow3 k ⟨5, by decide⟩ (Or.inr (Or.inr rfl)) hk with
      ⟨θ, _, h_l | h_r⟩
    · exact ⟨θ, Or.inl h_l⟩
    · refine ⟨θ, Or.inr ?_⟩
      rw [h_r]
      exact permTraceAux_congr _ _ c.ringSize b0 pow3 swap12Digit_permDigit_5 c.ringSize 0 0

/-!
### Ring-Cycle `S₄` Invariance of `FastReducer.extend` (`extend_eq_of_edge_digits`)
-/

/-- The 6 color permutations fixing `Color.c0` and permuting `{c1, c2, c3}` according to `permDigit k`. -/
def permColor (k : Fin 6) : Color → Color
  | Color.c0 => Color.c0
  | col => colorOfNat (permDigit k (col.toNat - 1) + 1)

/-- Klein four-group addition (`^^^`) on `Color`. -/
def xorColorCol (col dCol : Color) : Color :=
  colorOfNat (col.toNat ^^^ dCol.toNat)

/-- Affine $V_4$ transformation `col ↦ xorColorCol (permColor k col) dCol`. -/
def affineColor (k : Fin 6) (dCol : Color) (col : Color) : Color :=
  xorColorCol (permColor k col) dCol

theorem affineColor_inj (k : Fin 6) (dCol col1 col2 : Color)
    (h : affineColor k dCol col1 = affineColor k dCol col2) :
    col1 = col2 := by
  revert k h
  cases dCol <;> cases col1 <;> cases col2 <;> decide

theorem affineColor_zero (k : Fin 6) (c1 c0 : Color) :
    c1 = affineColor k (xorColorCol c1 (permColor k c0)) c0 := by
  revert k
  cases c1 <;> cases c0 <;> decide

/-- Single-edge propagation along the ring cycle: if `col1' = affineColor k dCol col1`,
    `col1 ≠ col2`, `col1' ≠ col2'`, and the edge digit of `(col1', col2')` equals `permDigit k`
    of the edge digit of `(col1, col2)`, then `col2' = affineColor k dCol col2`. -/
theorem step_color_of_edgeDigit_eq (k : Fin 6) (col1 col2 col1' col2' dCol : Color)
    (h_ne : col1 ≠ col2) (h_ne' : col1' ≠ col2')
    (h_col1 : col1' = affineColor k dCol col1)
    (h_dig : (let diff := col1'.toNat ^^^ col2'.toNat; if diff > 0 then diff - 1 else 0) =
             permDigit k (let diff := col1.toNat ^^^ col2.toNat; if diff > 0 then diff - 1 else 0)) :
    col2' = affineColor k dCol col2 := by
  revert k h_ne h_ne' h_col1 h_dig
  cases col1 <;> cases col2 <;> cases col1' <;> cases col2' <;> cases dCol <;> decide

/-- On a ring cycle `IsRingCycle c`, if two valid boundary colorings `b` and `b0` have edge digits
    related by `permDigit k` across `< c.ringSize`, then `b i = affineColor k dCol (b0 i)`
    for all `i < c.ringSize`, where `dCol = xorColorCol (b 0) (permColor k (b0 0))`. -/
theorem boundary_eq_affineColor_of_edge_digits (c : Configuration) (h_ring : IsRingCycle c)
    (b b0 : BoundaryColoring c)
    (hb : IsValidBoundaryColoring c b) (hb0 : IsValidBoundaryColoring c b0)
    (k : Fin 6)
    (h_digits : ∀ idx < c.ringSize, edgeDigitAt c.ringSize b idx = permDigit k (edgeDigitAt c.ringSize b0 idx)) :
    ∀ i < c.ringSize, b i = affineColor k (xorColorCol (b 0) (permColor k (b0 0))) (b0 i) := by
  intro i hi
  induction i with
  | zero =>
    exact affineColor_zero k (b 0) (b0 0)
  | succ i ih =>
    have hi_lt : i < c.ringSize := by omega
    have h_prev := ih hi_lt
    have h_mod : (i + 1) % c.ringSize = i + 1 := Nat.mod_eq_of_lt hi
    have h_adj : c.adj i (i + 1) = true := by
      have := h_ring.2 i hi_lt
      rwa [h_mod] at this
    have h_ne0 : b0 i ≠ b0 (i + 1) := hb0 i (i + 1) hi_lt hi h_adj
    have h_ne : b i ≠ b (i + 1) := hb i (i + 1) hi_lt hi h_adj
    have h_dig := h_digits i hi_lt
    dsimp [edgeDigitAt] at h_dig
    rw [h_mod] at h_dig
    exact step_color_of_edgeDigit_eq k (b0 i) (b0 (i + 1)) (b i) (b (i + 1))
      (xorColorCol (b 0) (permColor k (b0 0))) h_ne0 h_ne h_prev h_dig

/-- If two boundary colorings agree on all `< c.ringSize`, their `extendsToInterior` propositions are equivalent. -/
theorem extendsToInterior_congr_ring (c : Configuration) (b1 b2 : BoundaryColoring c)
    (h_agree : ∀ i < c.ringSize, b1 i = b2 i) :
    extendsToInterior c b1 ↔ extendsToInterior c b2 := by
  constructor
  · rintro ⟨full, h_ring, h_valid⟩
    refine ⟨full, ?_, h_valid⟩
    intro i hi
    rw [h_ring i hi, h_agree i hi]
  · rintro ⟨full, h_ring, h_valid⟩
    refine ⟨full, ?_, h_valid⟩
    intro i hi
    rw [h_ring i hi, ← h_agree i hi]

/-- **Theorem D4.1e (`extend_eq_of_edge_digits`):**
    On a ring cycle `IsRingCycle c`, under `IsSoundEarlier`, `IsWellFormedEarlier`, and `IsIrreflexiveAdj`,
    if two valid boundary colorings `b` and `b0` have edge digits related by `permDigit k`,
    then `(extend earlier c.totalNodes c.ringSize (initCol c b)).1 = (extend earlier c.totalNodes c.ringSize (initCol c b0)).1`. -/
theorem extend_eq_of_edge_digits (c : Configuration) (earlier : Array (Array Nat))
    (h_ring : IsRingCycle c)
    (h_earlier : IsSoundEarlier c earlier)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (b b0 : BoundaryColoring c)
    (hb : IsValidBoundaryColoring c b) (hb0 : IsValidBoundaryColoring c b0)
    (k : Fin 6)
    (h_digits : ∀ idx < c.ringSize, edgeDigitAt c.ringSize b idx = permDigit k (edgeDigitAt c.ringSize b0 idx)) :
    (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 =
      (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b0)).1 := by
  have h_iff1 := extend_iff_extendsToInterior c earlier h_earlier h_wf h_irrefl b hb
  have h_iff2 := extend_iff_extendsToInterior c earlier h_earlier h_wf h_irrefl b0 hb0
  apply Bool.eq_iff_iff.mpr
  rw [h_iff1, h_iff2]
  constructor
  · intro h_ext_b
    rcases permDigit_inv k with ⟨k_inv, hk_inv⟩
    have h_digits_symm : ∀ idx < c.ringSize,
        edgeDigitAt c.ringSize b0 idx = permDigit k_inv (edgeDigitAt c.ringSize b idx) := by
      intro idx h_lt
      rw [h_digits idx h_lt]
      exact ((hk_inv (edgeDigitAt c.ringSize b0 idx) (edgeDigitAt_lt_three c.ringSize b0 idx)).1).symm
    have h_aff0 := boundary_eq_affineColor_of_edge_digits c h_ring b0 b hb0 hb k_inv h_digits_symm
    let dCol0 := xorColorCol (b0 0) (permColor k_inv (b 0))
    have h_ext_perm := extendsToInterior_perm c b (affineColor k_inv dCol0) (affineColor_inj k_inv dCol0) h_ext_b
    exact (extendsToInterior_congr_ring c (fun i => affineColor k_inv dCol0 (b i)) b0
      (fun i hi => (h_aff0 i hi).symm)).mp h_ext_perm
  · intro h_ext_b0
    have h_aff := boundary_eq_affineColor_of_edge_digits c h_ring b b0 hb hb0 k h_digits
    let dCol := xorColorCol (b 0) (permColor k (b0 0))
    have h_ext_perm := extendsToInterior_perm c b0 (affineColor k dCol) (affineColor_inj k dCol) h_ext_b0
    exact (extendsToInterior_congr_ring c (fun i => affineColor k dCol (b0 i)) b
      (fun i hi => (h_aff i hi).symm)).mp h_ext_perm

/-- Every entry of `Array.replicate N 0` has `getD j 0 = 0`. -/
@[simp] theorem array_replicate_zero_getD (N j : Nat) :
    (Array.replicate N 0).getD j 0 = 0 := by
  unfold Array.getD
  split
  · simp
  · rfl

/-- Helper to construct `ReducerInv N` for the initial state of `checkFastTotal` / `computeEliminationRanks`. -/
theorem reducerInv_of_init_props (N : Nat) (live0 : ByteArray) (orbits0 : Array Orbit6) (sms : Array SMData)
    (h_nodup : orbits0.toList.Nodup)
    (h_disj : ∀ o₁ ∈ orbits0.toList, ∀ o₂ ∈ orbits0.toList, o₁ ≠ o₂ → ∀ j, inOrbit6 o₁ j → ¬ inOrbit6 o₂ j)
    (h_live : ∀ o ∈ orbits0.toList, orbitAllLive live0 o)
    (h_bnd : ∀ o ∈ orbits0.toList, orbitBounded N o)
    (h_sz : live0.size = N) :
    ReducerInv N {
      live := live0
      orbits := orbits0
      activeSM := sms
      ranks := Array.replicate N 0
      iter := 0
      changed := true
    } where
  nodup := h_nodup
  disjoint := h_disj
  allLive := h_live
  bounded := by
    intro o ho
    simp only [h_sz, Array.size_replicate]
    exact ⟨h_bnd o ho, h_bnd o ho⟩
  rankLe := by
    intro j
    dsimp
    rw [array_replicate_zero_getD]
    omega
  liveSize := h_sz
  ranksSize := Array.size_replicate

/-- Every entry of `a` is `0` or `1`. -/
def ByteArrayBinary (a : ByteArray) : Prop :=
  ∀ j, a.get! j = 0 ∨ a.get! j = 1

/-- Complete structural specification of `initialLiveTotal (rconfOfConfig c earlier) pow3`. -/
structure InitialLiveSpec (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) : Prop where
  init_inv :
    let rc := rconfOfConfig c earlier
    let N := pow3.getD rc.r 1
    let (live0, orbits0) := initialLiveTotal rc pow3
    ∀ sms : Array SMData,
      ReducerInv N {
        live := live0, orbits := orbits0, activeSM := sms,
        ranks := Array.replicate N 0, iter := 0, changed := true
      }
  live_binary :
    ByteArrayBinary (initialLiveTotal (rconfOfConfig c earlier) pow3).1
  ext_live_zero :
    let rc := rconfOfConfig c earlier
    let (live0, orbits0) := initialLiveTotal rc pow3
    ∀ b : BoundaryColoring c, IsValidBoundaryColoring c b →
      (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = true →
      live0.get! (boundaryTrace c b pow3) = 0 ∧
      ∀ orb ∈ orbits0.toList, ¬ inOrbit6 orb (boundaryTrace c b pow3)
  nonext_in_orbit :
    let rc := rconfOfConfig c earlier
    let (_, orbits0) := initialLiveTotal rc pow3
    ∀ b : BoundaryColoring c, IsValidBoundaryColoring c b →
      (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = false →
      ∃ orb ∈ orbits0.toList, inOrbit6 orb (boundaryTrace c b pow3)
  relabel_same_orbit :
    let rc := rconfOfConfig c earlier
    let (_, orbits0) := initialLiveTotal rc pow3
    ∀ (b : BoundaryColoring c) (θ : ColorPairing) (orb : Orbit6),
      IsValidBoundaryColoring c b →
      orb ∈ orbits0.toList →
      (inOrbit6 orb (boundaryTrace c b pow3) ↔ inOrbit6 orb (boundaryTraceTheta c b θ pow3))
  pairing_cover_orbit :
    let rc := rconfOfConfig c earlier
    let (_, orbits0) := initialLiveTotal rc pow3
    ∀ (b : BoundaryColoring c) (orb : Orbit6),
      IsValidBoundaryColoring c b →
      orb ∈ orbits0.toList →
      inOrbit6 orb (boundaryTrace c b pow3) →
      ∀ (j_a j_b : Nat),
        ((j_a = orb.j0 ∧ j_b = orb.j1) ∨ (j_a = orb.j2 ∧ j_b = orb.j4) ∨ (j_a = orb.j5 ∧ j_b = orb.j3)) →
        ∃ θ : ColorPairing,
          boundaryTraceTheta c b θ pow3 = j_a ∨ boundaryTraceTheta c b θ pow3 = j_b

end CheckerSoundness
end Math
