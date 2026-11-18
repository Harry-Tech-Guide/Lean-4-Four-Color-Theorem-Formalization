module

public import FourColorTheorem.Math.DischargingBase

@[expose] public section

attribute [-simp] Nat.lor_eq Nat.land_eq Nat.xor_eq Nat.shiftLeft_eq' Nat.shiftRight_eq'

namespace Math

namespace Discharging

variable (H : Hypermap) [DecidableEq H.Dart]

local macro "rvd_simp" : tactic =>
  `(tactic| try simp only [ruleVertexDart_0, ruleVertexDart_1, ruleVertexDart_2, ruleVertexDart_3,
    ruleVertexDart_4, ruleVertexDart_5, ruleVertexDart_6, ruleVertexDart_7, ruleVertexDart_8,
    ruleVertexDart_9, ruleVertexDart_10, ruleVertexDart_11, ruleVertexDart_12, ruleVertexDart_13,
    ruleVertexDart_14, ruleVertexDart_15, ruleVertexDart_16])

/-!
### Stage K.2: `symForcedRec`, `extractCondsRec`, and Full Semantic Soundness of `verifyTree`
-/

/-- Rotational shift of a cartwheel position `p0` by `x_shift` (`0 ≤ x_shift < deg`) within its `deg`-ring. -/
def shiftCartPos (deg x_shift p0 : Nat) : Nat :=
  if !Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg)) then
    Nat.add p0 x_shift
  else
    Nat.sub (Nat.add p0 x_shift) deg

/-- Reflection of a cartwheel position `1 ≤ p ≤ 2 * deg` across spoke 1. -/
def reflCartPos (deg p : Nat) : Nat :=
  if Nat.ble p deg then
    Nat.add (Nat.sub deg p) 1
  else if !Nat.ble (Nat.mul 2 deg) p then
    Nat.sub (Nat.mul 3 deg) p
  else
    Nat.mul 2 deg

/-- Combined rotational/reflectional image of cartwheel position `p0`. -/
def symCartPos (deg x_shift : Nat) (refl : Bool) (p0 : Nat) : Nat :=
  if refl then reflCartPos deg (shiftCartPos deg x_shift p0)
  else shiftCartPos deg x_shift p0

/-- Rotated/reflected cartwheel degree assignment induced by `(x_shift, refl)`. -/
def symCartDeg (deg x_shift : Nat) (refl : Bool) (cartDeg : Nat → Nat) : Nat → Nat :=
  fun p0 => cartDeg (symCartPos deg x_shift refl p0)

theorem shiftCartPos_bounds {deg x_shift p0 : Nat} (h_deg : 1 ≤ deg) (h_shift : x_shift < deg)
    (hp1 : 1 ≤ p0) (hp2 : p0 ≤ 2 * deg) :
    1 ≤ shiftCartPos deg x_shift p0 ∧ shiftCartPos deg x_shift p0 ≤ 2 * deg := by
  unfold shiftCartPos
  have h_div_mod := Nat.div_add_mod (p0 - 1) deg
  have h_mod_lt : (p0 - 1) % deg < deg := Nat.mod_lt (p0 - 1) (by omega)
  have h_div_le : (p0 - 1) / deg ≤ 1 := by
    have h_lt : p0 - 1 < 2 * deg := by omega
    have h_div_lt : (p0 - 1) / deg < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr h_lt
    omega
  have h_prod_le : deg * ((p0 - 1) / deg) ≤ deg := by
    have := Nat.mul_le_mul_left deg h_div_le
    omega
  cases h_cond : Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg)) with
  | false =>
    have h_lt_deg : x_shift + (p0 - 1) % deg < deg :=
      Classical.byContradiction fun h_ge => by
        have h_le : deg ≤ Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg) := by
          change deg ≤ x_shift + (p0 - 1) % deg
          omega
        rw [Nat.ble_eq_true_of_le h_le] at h_cond
        contradiction
    simp only [Bool.not_false, ite_true]
    change 1 ≤ p0 + x_shift ∧ p0 + x_shift ≤ 2 * deg
    omega
  | true =>
    have h_ge_deg : deg ≤ x_shift + (p0 - 1) % deg := Nat.le_of_ble_eq_true h_cond
    simp only [Bool.not_true]
    change 1 ≤ p0 + x_shift - deg ∧ p0 + x_shift - deg ≤ 2 * deg
    omega

theorem reflCartPos_bounds {deg p : Nat} (h_deg : 1 ≤ deg) (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * deg) :
    1 ≤ reflCartPos deg p ∧ reflCartPos deg p ≤ 2 * deg := by
  unfold reflCartPos
  cases h1 : Nat.ble p deg with
  | true =>
    have hp_le : p ≤ deg := Nat.le_of_ble_eq_true h1
    simp only [ite_true]
    change 1 ≤ deg - p + 1 ∧ deg - p + 1 ≤ 2 * deg
    omega
  | false =>
    have hp_gt : deg < p :=
      Classical.byContradiction fun h_le => by
        rw [Nat.ble_eq_true_of_le (by omega)] at h1; contradiction
    cases h2 : Nat.ble (Nat.mul 2 deg) p with
    | false =>
      have hp_lt : p < 2 * deg :=
        Classical.byContradiction fun h_ge => by
          have h_le : Nat.mul 2 deg ≤ p := by change 2 * deg ≤ p; omega
          rw [Nat.ble_eq_true_of_le h_le] at h2; contradiction
      simp only [Bool.not_false, ite_true]
      change 1 ≤ 3 * deg - p ∧ 3 * deg - p ≤ 2 * deg
      omega
    | true =>
      simp only [Bool.not_true]
      change 1 ≤ 2 * deg ∧ 2 * deg ≤ 2 * deg
      omega

theorem symCartPos_bounds {deg x_shift p0 : Nat} (refl : Bool)
    (h_deg : 1 ≤ deg) (h_shift : x_shift < deg) (hp1 : 1 ≤ p0) (hp2 : p0 ≤ 2 * deg) :
    1 ≤ symCartPos deg x_shift refl p0 ∧ symCartPos deg x_shift refl p0 ≤ 2 * deg := by
  unfold symCartPos
  have ⟨hs1, hs2⟩ := shiftCartPos_bounds h_deg h_shift hp1 hp2
  cases refl with
  | false => exact ⟨hs1, hs2⟩
  | true => exact reflCartPos_bounds h_deg hs1 hs2

/-- Inner loop helper for `symForcedRec` to prove condition forcing by structural induction on `conds`. -/
noncomputable def symForcedLoop (st x_shift deg : Nat) (refl : Bool) (conds : List (Nat × Nat)) : Bool :=
  List.rec
    (motive := fun _ => Bool)
    true
    (fun c _ ih =>
      let (p0, bm) := c
      strictNat
        (Bool.rec
          (Nat.sub (Nat.add p0 x_shift) deg)
          (Nat.add p0 x_shift)
          (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))))
        fun p =>
      Bool.rec
        (Bool.rec
          ih
          false
          (!Nat.beq (Nat.land (getLaneNat st p) (Nat.xor 31 bm)) 0))
        (Bool.rec
          false
          (let q :=
             Bool.rec
               (Bool.rec
                 (Nat.mul 2 deg)
                 (Nat.sub (Nat.mul 3 deg) p)
                 (!Nat.ble (Nat.mul 2 deg) p))
               (Nat.add (Nat.sub deg p) 1)
               (Nat.ble p deg)
           Bool.rec
             ih
             false
             (!Nat.beq (Nat.land (getLaneNat st q) (Nat.xor 31 bm)) 0))
          (Nat.ble 1 p && Nat.ble p (Nat.mul 2 deg)))
        refl)
    conds

theorem symForcedRec_eq_loop (st x deg : Nat) (refl : Bool) (conds : List (Nat × Nat)) :
    symForcedRec st x deg refl conds = symForcedLoop st (Nat.sub x 1) deg refl conds := by
  unfold symForcedRec
  rw [strictNat_eq]
  rfl

theorem symForcedLoop_cons_eq (st x_shift deg : Nat) (refl : Bool) (c : Nat × Nat) (conds : List (Nat × Nat)) :
    symForcedLoop st x_shift deg refl (c :: conds) =
      (let p := shiftCartPos deg x_shift c.1
       if refl then
         if Nat.ble 1 p && Nat.ble p (Nat.mul 2 deg) then
           let q := reflCartPos deg p
           if !Nat.beq (Nat.land (getLaneNat st q) (Nat.xor 31 c.2)) 0 then
             false
           else
             symForcedLoop st x_shift deg refl conds
         else
           false
       else
         if !Nat.beq (Nat.land (getLaneNat st p) (Nat.xor 31 c.2)) 0 then
           false
         else
           symForcedLoop st x_shift deg refl conds) := by
  rcases c with ⟨p0, bm⟩
  unfold symForcedLoop shiftCartPos reflCartPos
  dsimp only
  have h_p :
      (@Bool.rec (fun _ => Nat) (Nat.sub (Nat.add p0 x_shift) deg) (Nat.add p0 x_shift)
        (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg)))) =
      (if (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))) = true then
        Nat.add p0 x_shift else Nat.sub (Nat.add p0 x_shift) deg) := by
    cases (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))) <;> rfl
  rw [strictNat_eq, h_p]
  let p := if (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))) = true then
    Nat.add p0 x_shift else Nat.sub (Nat.add p0 x_shift) deg
  cases refl with
  | false =>
    dsimp only
    cases (!Nat.beq (Nat.land (getLaneNat st p) (Nat.xor 31 bm)) 0) <;> rfl
  | true =>
    dsimp only
    cases (Nat.ble 1 p && Nat.ble p (Nat.mul 2 deg)) with
    | false => rfl
    | true =>
      dsimp only
      have h_q :
          (@Bool.rec (fun _ => Nat)
            (@Bool.rec (fun _ => Nat) (Nat.mul 2 deg) (Nat.sub (Nat.mul 3 deg) p) (!Nat.ble (Nat.mul 2 deg) p))
            (Nat.add (Nat.sub deg p) 1) (Nat.ble p deg)) =
          (if Nat.ble p deg = true then Nat.add (Nat.sub deg p) 1
           else if (!Nat.ble (Nat.mul 2 deg) p) = true then Nat.sub (Nat.mul 3 deg) p
           else Nat.mul 2 deg) := by
        cases Nat.ble p deg <;> cases (!Nat.ble (Nat.mul 2 deg) p) <;> rfl
      rw [h_q]
      let q := if Nat.ble p deg = true then Nat.add (Nat.sub deg p) 1
               else if (!Nat.ble (Nat.mul 2 deg) p) = true then Nat.sub (Nat.mul 3 deg) p
               else Nat.mul 2 deg
      cases (!Nat.beq (Nat.land (getLaneNat st q) (Nat.xor 31 bm)) 0) <;> rfl

theorem testBit_of_land_xor_31_eq_zero {lane bm d : Nat}
    (h_tb : lane.testBit (degBitIdx d) = true)
    (h_zero : (!Nat.beq (Nat.land lane (Nat.xor 31 bm)) 0) = false) :
    bm.testBit (degBitIdx d) = true := by
  have h_eq : lane &&& (31 ^^^ bm) = 0 := by
    cases h_b : Nat.beq (Nat.land lane (Nat.xor 31 bm)) 0 with
    | true => exact Nat.beq_eq.mp h_b
    | false => rw [h_b] at h_zero; contradiction
  have h_bit : (lane &&& (31 ^^^ bm)).testBit (degBitIdx d) = false := by
    rw [h_eq, Nat.zero_testBit]
  rw [Nat.testBit_and, Nat.testBit_xor, h_tb, testBit_31_degBitIdx d, Bool.true_and] at h_bit
  cases h_bm : bm.testBit (degBitIdx d) with
  | true => rfl
  | false => rw [h_bm] at h_bit; contradiction

/-- Soundness of `symForcedRec`:
    if `MatchesCartState deg cartDeg st`, every `(p0, bm) ∈ conds` has `1 ≤ p0 ≤ 2 * deg`,
    and `symForcedRec st x deg refl conds = true` (with `1 ≤ deg` and `x - 1 < deg`),
    then for every `(p0, bm) ∈ conds`, the rotated/reflected degree assignment
    `symCartDeg deg (x - 1) refl cartDeg` satisfies `bm.testBit (degBitIdx (symCartDeg deg (x - 1) refl cartDeg p0)) = true`. -/
theorem symForcedRec_sound (deg : Nat) (cartDeg : Nat → Nat) (st x : Nat) (refl : Bool)
    (conds : List (Nat × Nat)) (h_deg : 1 ≤ deg) (h_shift : x - 1 < deg)
    (h_match : MatchesCartState deg cartDeg st)
    (h_conds : ∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg)
    (h_ok : symForcedRec st x deg refl conds = true) :
    ∀ c ∈ conds, c.2.testBit (degBitIdx (symCartDeg deg (x - 1) refl cartDeg c.1)) = true := by
  rw [symForcedRec_eq_loop] at h_ok
  have h_loop :
      ∀ (cs : List (Nat × Nat)),
        (∀ c ∈ cs, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) →
        symForcedLoop st (x - 1) deg refl cs = true →
        ∀ c ∈ cs, c.2.testBit (degBitIdx (symCartDeg deg (x - 1) refl cartDeg c.1)) = true := by
    intro cs
    induction cs with
    | nil =>
      intro _ _ c hc
      cases hc
    | cons c cs ih =>
      intro h_cs h_cs_ok c' hc'
      rw [symForcedLoop_cons_eq] at h_cs_ok
      dsimp only at h_cs_ok
      have ⟨hp0_1, hp0_2⟩ := h_cs c List.mem_cons_self
      have h_tail : ∀ c'' ∈ cs, 1 ≤ c''.1 ∧ c''.1 ≤ 2 * deg :=
        fun c'' hm => h_cs c'' (List.mem_cons_of_mem _ hm)
      have ⟨hp1, hp2⟩ := shiftCartPos_bounds h_deg h_shift hp0_1 hp0_2
      cases refl with
      | false =>
        cases h_z : (!Nat.beq (Nat.land (getLaneNat st (shiftCartPos deg (x - 1) c.1)) (Nat.xor 31 c.2)) 0) with
        | true =>
          rw [h_z] at h_cs_ok; contradiction
        | false =>
          rw [h_z] at h_cs_ok
          rcases List.mem_cons.mp hc' with rfl | hc_tail
          · unfold symCartDeg symCartPos
            have h_tb : (getLaneNat st (shiftCartPos deg (x - 1) c'.1)).testBit (degBitIdx (cartDeg (shiftCartPos deg (x - 1) c'.1))) = true :=
              h_match (shiftCartPos deg (x - 1) c'.1) hp1 (by omega)
            exact testBit_of_land_xor_31_eq_zero h_tb h_z
          · exact ih h_tail h_cs_ok c' hc_tail
      | true =>
        cases h_p_b : (Nat.ble 1 (shiftCartPos deg (x - 1) c.1) && Nat.ble (shiftCartPos deg (x - 1) c.1) (Nat.mul 2 deg)) with
        | false =>
          rw [h_p_b] at h_cs_ok; contradiction
        | true =>
          rw [h_p_b] at h_cs_ok
          have ⟨hq1, hq2⟩ := reflCartPos_bounds h_deg hp1 hp2
          cases h_z : (!Nat.beq (Nat.land (getLaneNat st (reflCartPos deg (shiftCartPos deg (x - 1) c.1))) (Nat.xor 31 c.2)) 0) with
          | true =>
            rw [h_z] at h_cs_ok; contradiction
          | false =>
            rw [h_z] at h_cs_ok
            simp only [ite_true] at h_cs_ok
            rcases List.mem_cons.mp hc' with rfl | hc_tail
            · unfold symCartDeg symCartPos
              simp only [ite_true]
              have h_tb : (getLaneNat st (reflCartPos deg (shiftCartPos deg (x - 1) c'.1))).testBit
                  (degBitIdx (cartDeg (reflCartPos deg (shiftCartPos deg (x - 1) c'.1)))) = true :=
                h_match (reflCartPos deg (shiftCartPos deg (x - 1) c'.1)) hq1 (by omega)
              exact testBit_of_land_xor_31_eq_zero h_tb h_z
            · exact ih h_tail h_cs_ok c' hc_tail
  exact h_loop conds h_conds h_ok

/-- Inner loop helper for `extractCondsRec` to prove `1 ≤ c.1 ≤ 2 * deg` for all extracted conditions. -/
noncomputable def extractCondsLoop (deg condV condM lev : Nat) (acc0 : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
  Nat.rec
    (motive := fun _ => List (Nat × Nat) → Option (List (Nat × Nat)))
    (fun acc =>
      strictNat (getLaneNat condV 0) fun n =>
      Bool.rec
        none
        (some ((n, getLaneNat condM 0) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)))
    (fun i ih acc =>
      strictNat (Nat.add i 1) fun idx =>
      strictNat (getLaneNat condV idx) fun n =>
      Bool.rec
        none
        (ih ((n, getLaneNat condM idx) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)))
    lev acc0

theorem extractCondsRec_eq_loop (deg condV condM lev : Nat) :
    extractCondsRec deg condV condM lev = extractCondsLoop deg condV condM lev [] := rfl

theorem extractCondsLoop_sound (deg condV condM : Nat) :
    ∀ (lev : Nat) (acc res : List (Nat × Nat)),
      (∀ c ∈ acc, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) →
      extractCondsLoop deg condV condM lev acc = some res →
      ∀ c ∈ res, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg := by
  intro lev
  induction lev with
  | zero =>
    intro acc res h_acc h_some c hc
    change (strictNat (getLaneNat condV 0) fun n =>
      @Bool.rec (fun _ => Option (List (Nat × Nat))) none
        (some ((n, getLaneNat condM 0) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = some res at h_some
    rw [strictNat_eq] at h_some
    let n := getLaneNat condV 0
    cases h_b : (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)) with
    | false =>
      rw [h_b] at h_some; contradiction
    | true =>
      rw [h_b] at h_some
      dsimp only at h_some
      injection h_some with h_eq
      subst h_eq
      rcases List.mem_cons.mp hc with rfl | hc_acc
      · rcases Bool.and_eq_true_iff.mp h_b with ⟨hb1, hb2⟩
        exact ⟨Nat.le_of_ble_eq_true hb1, Nat.le_of_ble_eq_true hb2⟩
      · exact h_acc c hc_acc
  | succ i ih =>
    intro acc res h_acc h_some
    unfold extractCondsLoop at h_some
    dsimp only at h_some
    rw [strictNat_eq, strictNat_eq] at h_some
    let idx := Nat.add i 1
    let n := getLaneNat condV idx
    change (@Bool.rec (fun _ => Option (List (Nat × Nat))) none
      (extractCondsLoop deg condV condM i ((n, getLaneNat condM idx) :: acc))
      (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = some res at h_some
    cases h_b : (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)) with
    | false =>
      rw [h_b] at h_some; contradiction
    | true =>
      rw [h_b] at h_some
      dsimp only at h_some
      apply ih ((n, getLaneNat condM idx) :: acc) res _ h_some
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc_acc
      · rcases Bool.and_eq_true_iff.mp h_b with ⟨hb1, hb2⟩
        exact ⟨Nat.le_of_ble_eq_true hb1, Nat.le_of_ble_eq_true hb2⟩
      · exact h_acc c hc_acc

theorem extractCondsRec_sound (deg condV condM lev : Nat) {conds : List (Nat × Nat)}
    (h_some : extractCondsRec deg condV condM lev = some conds) :
    ∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg := by
  rw [extractCondsRec_eq_loop] at h_some
  exact extractCondsLoop_sound deg condV condM lev [] conds (fun _ h => by cases h) h_some

theorem findSymOutletRec_mem (line : Nat) (syms : List SymOutlet) {found : SymOutlet}
    (h_find : findSymOutletRec line syms = some found) :
    found ∈ syms := by
  induction syms with
  | nil =>
    unfold findSymOutletRec at h_find
    contradiction
  | cons o syms ih =>
    unfold findSymOutletRec at h_find
    dsimp only at h_find
    change (@Bool.rec (fun _ => Option SymOutlet) (findSymOutletRec line syms) (some o) (Nat.beq o.number line)) = some found at h_find
    cases h_eq : Nat.beq o.number line with
    | true =>
      rw [h_eq] at h_find
      dsimp only at h_find
      injection h_find with h_o
      subst h_o
      exact List.mem_cons_self
    | false =>
      rw [h_eq] at h_find
      dsimp only at h_find
      exact List.mem_cons_of_mem _ (ih h_find)

/-!
### Stage L.1: Real Hypermap Cartwheel Instantiation (`spokeDart`, `cartDart`, `cartDegOfDart`, `dischargingTreesVerified_hypermap_soundness`)
-/

/-- The `i`-th outgoing spoke dart (`1 ≤ i ≤ deg`) around hub dart `d0` in hypermap `H`,
    obtained by iterating `H.node.f` `(i - 1)` times starting from `d0`. -/
def spokeDart (H : Hypermap) (d0 : H.Dart) (i : Nat) : H.Dart :=
  Hypermap.Perm.iter H.node (i - 1) d0

@[simp] theorem spokeDart_one (H : Hypermap) (d0 : H.Dart) :
    spokeDart H d0 1 = d0 := rfl

theorem spokeDart_succ (H : Hypermap) (d0 : H.Dart) {i : Nat} (hi : 1 ≤ i) :
    spokeDart H d0 (i + 1) = H.node.f (spokeDart H d0 i) := by
  cases i with
  | zero => omega
  | succ k => rfl

theorem perm_iter_mem_getOrbit_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d0 : H.Dart) (n : Nat) :
    Hypermap.Perm.iter H.node n d0 ∈ getOrbit H.node fuel d0 := by
  induction n with
  | zero =>
    exact List.contains_iff_mem.mp (Hypermap.getOrbit_contains_self H.node fuel d0)
  | succ n ih =>
    rw [Hypermap.Perm.iter_succ]
    exact Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le ih

/-- Every `spokeDart H d0 i` belongs to the node orbit `getOrbit H.node fuel d0` on a complete dart list. -/
theorem spokeDart_mem_getOrbit_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d0 : H.Dart) (i : Nat) :
    spokeDart H d0 i ∈ getOrbit H.node fuel d0 :=
  perm_iter_mem_getOrbit_of_complete H darts h_all h_le d0 (i - 1)

/-- Maps each RSST cartwheel position `0 ≤ p ≤ 5 * deg` around hub dart `d0` in hypermap `H`
    to its representative vertex dart, matching the 5 concentric cartwheel rings of `getAdjMat` / `doFan` / `doOutlet`:
    - `p = 0`: hub dart `d0`
    - `1 ≤ p ≤ deg` (`ringIdx = 0`, spoke `i`): `ruleVertexDart H true (H.edge.f s_i) 0` (`= H.edge.f s_i`)
    - `deg + 1 ≤ p ≤ 2 * deg` (`ringIdx = 1`, hat `deg + i`): `ruleVertexDart H true (H.edge.f s_i) 5`
    - `2 * deg + 1 ≤ p ≤ 3 * deg` (`ringIdx = 2`, 1st fan `2 * deg + i`): `ruleVertexDart H true (H.edge.f s_i) 12`
    - `3 * deg + 1 ≤ p ≤ 4 * deg` (`ringIdx = 3`, 2nd fan `3 * deg + i`): `ruleVertexDart H true (H.edge.f s_i) 13`
    - `4 * deg + 1 ≤ p ≤ 5 * deg` (`ringIdx ≥ 4`, 3rd fan `4 * deg + i`): `H.edge.f (H.node.f^5 (H.edge.f s_i))`. -/
def cartDart (H : Hypermap) (deg : Nat) (d0 : H.Dart) (p : Nat) : H.Dart :=
  if p == 0 then d0
  else
    let ringIdx := (p - 1) / deg
    let s := spokeDart H d0 ((p - 1) % deg + 1)
    if ringIdx == 0 then ruleVertexDart H true (H.edge.f s) 0
    else if ringIdx == 1 then ruleVertexDart H true (H.edge.f s) 5
    else if ringIdx == 2 then ruleVertexDart H true (H.edge.f s) 12
    else if ringIdx == 3 then ruleVertexDart H true (H.edge.f s) 13
    else H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f (H.edge.f s))))))

/-- Concrete cartwheel degree assignment `Nat → Nat` around hub dart `d0` in hypermap `H`. -/
def cartDegOfDart (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (d0 : H.Dart) (p : Nat) : Nat :=
  Hypermap.nodeDegree H (cartDart H deg d0 p) fuel

@[simp] theorem cartDart_zero (H : Hypermap) (deg : Nat) (d0 : H.Dart) :
    cartDart H deg d0 0 = d0 := rfl

@[simp] theorem cartDegOfDart_zero (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (d0 : H.Dart) :
    cartDegOfDart H fuel deg d0 0 = Hypermap.nodeDegree H d0 fuel := rfl

theorem ringIdx_of_mul_add {deg k i : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    ((k * deg + i) - 1) / deg = k := by
  have h_deg_pos : 0 < deg := by omega
  have h_eq : (k * deg + i) - 1 = (i - 1) + deg * k := by
    rw [Nat.mul_comm deg k]
    omega
  rw [h_eq, Nat.add_mul_div_left (i - 1) k h_deg_pos, Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem spokeIdx_of_mul_add {deg k i : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    ((k * deg + i) - 1) % deg + 1 = i := by
  have h_eq : (k * deg + i) - 1 = (i - 1) + deg * k := by
    rw [Nat.mul_comm deg k]
    omega
  rw [h_eq, Nat.add_mul_mod_self_left (i - 1) deg k, Nat.mod_eq_of_lt (by omega)]
  omega

/-- For `1 ≤ i ≤ deg`, cartwheel spoke position `i` maps to `H.edge.f (spokeDart H d0 i)`. -/
theorem cartDart_spoke (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 i = H.edge.f (spokeDart H d0 i) := by
  dsimp [cartDart]
  have h_ne0 : (i == 0) = false := beq_false_of_ne (by omega)
  have h_div : (i - 1) / deg = 0 := by
    simpa using ringIdx_of_mul_add (k := 0) hi1 hi2
  have h_mod : (i - 1) % deg + 1 = i := by
    simpa using spokeIdx_of_mul_add (k := 0) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-- For `1 ≤ i ≤ deg`, cartwheel hat position `deg + i` maps to `ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 5`. -/
theorem cartDart_hat (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 (deg + i) = ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 5 := by
  dsimp [cartDart]
  have h_ne0 : (deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((deg + i) - 1) / deg = 1 := by
    simpa using ringIdx_of_mul_add (k := 1) hi1 hi2
  have h_mod : ((deg + i) - 1) % deg + 1 = i := by
    simpa using spokeIdx_of_mul_add (k := 1) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-- For `1 ≤ i ≤ deg`, 1st fan position `2 * deg + i` maps to `ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 12`. -/
theorem cartDart_fan1 (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 (2 * deg + i) = ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 12 := by
  dsimp [cartDart]
  have h_ne0 : (2 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((2 * deg + i) - 1) / deg = 2 := ringIdx_of_mul_add (k := 2) hi1 hi2
  have h_mod : ((2 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 2) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-- For `1 ≤ i ≤ deg`, 2nd fan position `3 * deg + i` maps to `ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 13`. -/
theorem cartDart_fan2 (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 (3 * deg + i) = ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 13 := by
  dsimp [cartDart]
  have h_ne0 : (3 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((3 * deg + i) - 1) / deg = 3 := ringIdx_of_mul_add (k := 3) hi1 hi2
  have h_mod : ((3 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 3) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-- For `1 ≤ i ≤ deg`, 3rd fan position `4 * deg + i` maps to `H.edge.f (H.node.f^5 (H.edge.f (spokeDart H d0 i)))`. -/
theorem cartDart_fan3 (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 (4 * deg + i) =
      H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f (H.edge.f (spokeDart H d0 i))))))) := by
  dsimp [cartDart]
  have h_ne0 : (4 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((4 * deg + i) - 1) / deg = 4 := ringIdx_of_mul_add (k := 4) hi1 hi2
  have h_mod : ((4 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 4) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-!
### Stage L.2: Degree-6 Discharging with Degree-5 and Degree-6 Neighbors (Primal & Dual)
-/

/-- If `r.b1.1 > degs 1` (`0 < r.b1.1`), then `matchesRawRuleDegs degs r = false`. -/
theorem not_matchesRawRuleDegs_of_b1_lt (degs : Nat → Nat) (r : RawRule)
    (h_pos : 0 < r.b1.1) (h_lt : degs 1 < r.b1.1) :
    matchesRawRuleDegs degs r = false := by
  dsimp [matchesRawRuleDegs]
  rw [@degMatchesBound_eq_false_of_lt (degs 1) r.b1 h_pos h_lt]
  simp

private def r1  : RawRule := { num := 1,  b0 := (5, 5), b1 := (5, 12), triples := [], invert := true }
private def r3  : RawRule := { num := 3,  b0 := (5, 6), b1 := (7, 12), triples := [(3, (5, 5))], invert := true }
private def r5  : RawRule := { num := 5,  b0 := (5, 6), b1 := (6, 12), triples := [(3, (5, 6)), (5, (5, 5))], invert := true }
private def r7  : RawRule := { num := 7,  b0 := (6, 6), b1 := (6, 12), triples := [(3, (5, 5)), (5, (5, 6)), (9, (5, 5))], invert := true }
private def r9  : RawRule := { num := 9,  b0 := (6, 6), b1 := (6, 12), triples := [(3, (6, 6)), (5, (5, 6)), (9, (5, 5))], invert := true }
private def r11 : RawRule := { num := 11, b0 := (6, 6), b1 := (6, 12), triples := [(3, (6, 6)), (5, (6, 6)), (9, (5, 6)), (11, (5, 5))], invert := true }
private def r13 : RawRule := { num := 13, b0 := (6, 6), b1 := (7, 12), triples := [(3, (5, 5)), (5, (6, 6)), (7, (5, 5)), (9, (5, 6))], invert := true }
private def r15 : RawRule := { num := 15, b0 := (6, 6), b1 := (7, 12), triples := [(3, (6, 6)), (5, (6, 6)), (7, (5, 5)), (9, (6, 6)), (11, (5, 6))], invert := true }

private theorem if_false_eq_true_zero : (if false = true then (1 : Int) else 0) = 0 := rfl

/-- When `degs 0 = 5` and `degs 1 ≤ 6`, rule `r3` (`b1 = (7, 12)`) vanishes,
    so at most `r1` and `r5` can match (`orientOutflowDegs inv degs ≤ 2`). -/
theorem orientOutflowDegs_le_2_of_deg_5_of_target_deg_le_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (hb1 : degs 1 ≤ 6) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r3 (by decide) (by dsimp [r3]; omega)
  have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h5 : (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  rw [h3]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- When `degs 0 = 5` and `7 ≤ degs 3`, both `r3` (`degs 3 = 5`) and `r5` (`degs 3 ≤ 6`) vanish,
    leaving only `r1` (`orientOutflowDegs inv degs ≤ 1`). -/
theorem orientOutflowDegs_le_1_of_deg_5_of_deg3_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (hb3 : 7 ≤ degs 3) :
    orientOutflowDegs inv degs ≤ 1 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
  have h5 : matchesRawRuleDegs degs r5 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r5 3 5 6 (by decide) (by decide) (by omega)
  have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  rw [h3, h5]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- When `degs 0 = 6` and `degs 1 ≤ 6`, rules `r3, r13, r15` (`b1 = (7, 12)`) vanish
    and `{r5, r11}` / `{r7, r9}` conflict, so `orientOutflowDegs inv degs ≤ 2`. -/
theorem orientOutflowDegs_le_2_of_deg_6_of_target_deg_le_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb1 : degs 1 ≤ 6) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r3 (by decide) (by dsimp [r3]; omega)
  have h13 : matchesRawRuleDegs degs r13 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r13 (by decide) (by dsimp [r13]; omega)
  have h15 : matchesRawRuleDegs degs r15 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r15 (by decide) (by dsimp [r15]; omega)
  have hc5_11 := conflict_pair_at inv degs r5 r11 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  have hc7_9 := conflict_pair_at inv degs r7 r9 3 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  rw [h3, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- When `degs 0 = 6` and `7 ≤ degs 3`, all 7 rules `r3..r15` vanish (`orientOutflowDegs inv degs = 0`). -/
theorem orientOutflowDegs_eq_zero_of_deg_6_of_deg3_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb3 : 7 ≤ degs 3) :
    orientOutflowDegs inv degs = 0 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
  have h5 : matchesRawRuleDegs degs r5 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r5 3 5 6 (by decide) (by decide) (by omega)
  have h7 : matchesRawRuleDegs degs r7 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r7 3 5 5 (by decide) (by decide) (by omega)
  have h9 : matchesRawRuleDegs degs r9 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r9 3 6 6 (by decide) (by decide) (by omega)
  have h11 : matchesRawRuleDegs degs r11 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r11 3 6 6 (by decide) (by decide) (by omega)
  have h13 : matchesRawRuleDegs degs r13 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r13 3 5 5 (by decide) (by decide) (by omega)
  have h15 : matchesRawRuleDegs degs r15 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r15 3 6 6 (by decide) (by decide) (by omega)
  rw [h3, h5, h7, h9, h11, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- When `degs 0 = 6`, `degs 1 ≤ 6`, `6 ≤ degs 5`, `6 ≤ degs 9`, and `6 ≤ degs 11`,
    every rule in `theRules` vanishes (`orientOutflowDegs inv degs = 0`). -/
theorem orientOutflowDegs_eq_zero_of_deg_6_of_target_deg_le_6_of_no_deg5_second_ring
    (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb1 : degs 1 ≤ 6)
    (hb5 : 6 ≤ degs 5) (hb9 : 6 ≤ degs 9) (hb11 : 6 ≤ degs 11) :
    orientOutflowDegs inv degs = 0 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r3 (by decide) (by dsimp [r3]; omega)
  have h5 : matchesRawRuleDegs degs r5 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r5 5 5 5 (by decide) (by decide) (by omega)
  have h7 : matchesRawRuleDegs degs r7 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r7 9 5 5 (by decide) (by decide) (by omega)
  have h9 : matchesRawRuleDegs degs r9 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r9 9 5 5 (by decide) (by decide) (by omega)
  have h11 : matchesRawRuleDegs degs r11 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r11 11 5 5 (by decide) (by decide) (by omega)
  have h13 : matchesRawRuleDegs degs r13 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r13 (by decide) (by dsimp [r13]; omega)
  have h15 : matchesRawRuleDegs degs r15 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r15 (by decide) (by dsimp [r15]; omega)
  rw [h3, h5, h7, h9, h11, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Compensating Outflow Lemma for Degree-6 Vertices (`r3` activation):
    when `degs 0 = 6`, `7 ≤ degs 1`, and `degs 3 = 5`, rule `r3` fires in orientation `inv`,
    so `1 ≤ orientOutflowDegs inv degs`. -/
theorem one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb1 : 7 ≤ degs 1) (hb3 : degs 3 = 5) :
    1 ≤ orientOutflowDegs inv degs := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hr3 : matchesRawRuleDegs degs r3 = true := by
    dsimp [matchesRawRuleDegs, r3, List.all, degMatchesBound]
    rw [hb0, hb3, decide_eq_true hb1]
    rfl
  have h_inv3 : (if inv then r3.invert else true) = true := by cases inv <;> rfl
  have h5 : 0 ≤ (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) := by split <;> omega
  have h7 : 0 ≤ (if (if inv then r7.invert else true) && matchesRawRuleDegs degs r7 then (1 : Int) else 0) := by split <;> omega
  have h9 : 0 ≤ (if (if inv then r9.invert else true) && matchesRawRuleDegs degs r9 then (1 : Int) else 0) := by split <;> omega
  have h11 : 0 ≤ (if (if inv then r11.invert else true) && matchesRawRuleDegs degs r11 then (1 : Int) else 0) := by split <;> omega
  have h13 : 0 ≤ (if (if inv then r13.invert else true) && matchesRawRuleDegs degs r13 then (1 : Int) else 0) := by split <;> omega
  have h15 : 0 ≤ (if (if inv then r15.invert else true) && matchesRawRuleDegs degs r15 then (1 : Int) else 0) := by split <;> omega
  rw [hr3, h_inv3]; dsimp; omega

/-- Double Compensating Outflow Lemma for Degree-6 Vertices (`r3 + r5` activation):
    when `degs 0 = 6`, `7 ≤ degs 1`, `degs 3 = 5`, and `degs 5 = 5`, both `r3` and `r5` fire
    in orientation `inv`, so `2 ≤ orientOutflowDegs inv degs`. -/
theorem two_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5_of_deg5_5 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb1 : 7 ≤ degs 1) (hb3 : degs 3 = 5) (hb5 : degs 5 = 5) :
    2 ≤ orientOutflowDegs inv degs := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hr3 : matchesRawRuleDegs degs r3 = true := by
    dsimp [matchesRawRuleDegs, r3, List.all, degMatchesBound]
    rw [hb0, hb3, decide_eq_true hb1]
    rfl
  have hr5 : matchesRawRuleDegs degs r5 = true := by
    dsimp [matchesRawRuleDegs, r5, List.all, degMatchesBound]
    rw [hb0, hb3, hb5, decide_eq_true (by omega : 6 ≤ degs 1)]
    rfl
  have h_inv3 : (if inv then r3.invert else true) = true := by cases inv <;> rfl
  have h_inv5 : (if inv then r5.invert else true) = true := by cases inv <;> rfl
  have h7 : 0 ≤ (if (if inv then r7.invert else true) && matchesRawRuleDegs degs r7 then (1 : Int) else 0) := by split <;> omega
  have h9 : 0 ≤ (if (if inv then r9.invert else true) && matchesRawRuleDegs degs r9 then (1 : Int) else 0) := by split <;> omega
  have h11 : 0 ≤ (if (if inv then r11.invert else true) && matchesRawRuleDegs degs r11 then (1 : Int) else 0) := by split <;> omega
  have h13 : 0 ≤ (if (if inv then r13.invert else true) && matchesRawRuleDegs degs r13 then (1 : Int) else 0) := by split <;> omega
  have h15 : 0 ≤ (if (if inv then r15.invert else true) && matchesRawRuleDegs degs r15 then (1 : Int) else 0) := by split <;> omega
  rw [hr3, hr5, h_inv3, h_inv5]; dsimp; omega

/-- When a spoke `d` at a degree-6 vertex points to a neighbor `H.edge.f d` of degree `≥ 7`
    and at least one flanking spoke around `H.edge.f d` (`H.node.f (H.edge.f d)` or `H.node.inv (H.edge.f d)`)
    has a degree-5 neighbor, rule `r3` fires from `d` (`1 ≤ dartRuleOutflow H fuel d`). -/
theorem one_le_dartRuleOutflow_of_deg_6_of_target_deg_ge_7_of_flanking_spoke_deg_5
    (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart)
    (h_d6 : Hypermap.nodeDegree H d fuel = 6)
    (h_ed7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_flank5 : Hypermap.nodeDegree H (H.edge.f (H.node.f (H.edge.f d))) fuel = 5 ∨
                Hypermap.nodeDegree H (H.edge.f (H.node.inv (H.edge.f d))) fuel = 5) :
    1 ≤ dartRuleOutflow H fuel d := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  rcases h_flank5 with h_next5 | h_prev5
  · have hf : 0 ≤ orientOutflowDegs false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) :=
      foldl_add_nonneg _ _ (fun _ _ => by split <;> omega)
    have ht : 1 ≤ orientOutflowDegs true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) :=
      one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 true
        (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel)
        (by simpa [ruleVertexDart] using h_d6)
        (by simpa [ruleVertexDart] using h_ed7)
        (by simpa [ruleVertexDart, ruleRotInv] using h_next5)
    omega
  · have hf : 1 ≤ orientOutflowDegs false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) :=
      one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 false
        (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel)
        (by simpa [ruleVertexDart] using h_d6)
        (by simpa [ruleVertexDart] using h_ed7)
        (by simpa [ruleVertexDart, ruleRotInv] using h_prev5)
    have ht : 0 ≤ orientOutflowDegs true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) :=
      foldl_add_nonneg _ _ (fun _ _ => by split <;> omega)
    omega

/-- When a spoke `d` at a degree-6 vertex points to a neighbor `H.edge.f d` of degree `≥ 7`
    and BOTH flanking spokes `H.node.f (H.edge.f d)` and `H.node.inv (H.edge.f d)` have degree-5 neighbors,
    rule `r3` fires in both orientations (`2 ≤ dartRuleOutflow H fuel d`). -/
theorem two_le_dartRuleOutflow_of_deg_6_of_target_deg_ge_7_of_both_flanking_spokes_deg_5
    (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart)
    (h_d6 : Hypermap.nodeDegree H d fuel = 6)
    (h_ed7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next5 : Hypermap.nodeDegree H (H.edge.f (H.node.f (H.edge.f d))) fuel = 5)
    (h_prev5 : Hypermap.nodeDegree H (H.edge.f (H.node.inv (H.edge.f d))) fuel = 5) :
    2 ≤ dartRuleOutflow H fuel d := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf : 1 ≤ orientOutflowDegs false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) :=
    one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel)
      (by simpa [ruleVertexDart] using h_d6)
      (by simpa [ruleVertexDart] using h_ed7)
      (by simpa [ruleVertexDart, ruleRotInv] using h_prev5)
  have ht : 1 ≤ orientOutflowDegs true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) :=
    one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel)
      (by simpa [ruleVertexDart] using h_d6)
      (by simpa [ruleVertexDart] using h_ed7)
      (by simpa [ruleVertexDart, ruleRotInv] using h_next5)
  omega

/-- Global Degree-6 Discharging Theorem with Degree-`≥ 6` Neighbors:
    if `nodeDegree H u fuel = 6` and every spoke `d ∈ getOrbit H.node fuel u` has
    either `7 ≤ nodeDegree H (H.edge.f d) fuel` or flanking spokes of degree `≥ 7`
    (`7 ≤ nodeDegree H (H.edge.f (H.node.f d)) fuel ∧ 7 ≤ nodeDegree H (H.edge.f (H.node.inv d)) fuel`,
    with `6 ≤ nodeDegree H (H.edge.f d) fuel`),
    then `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_6_of_neighbors_deg_ge_6_of_flanking_spokes_ge_7
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : Hypermap.nodeDegree H u fuel = 6)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_flank7 : ∀ d ∈ getOrbit H.node fuel u,
      7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel ∨
      (7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∧
       7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  apply finalCharge_le_zero_of_deg_6_of_orbitNetShift_nonpos H darts h_all h_le u h_loopless h_deg6
  dsimp [orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 0 (by
    intro d hd
    have hd_deg : Hypermap.nodeDegree H d fuel ≤ 6 := by
      have := nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
      omega
    have h_out_nonneg : 0 ≤ dartRuleOutflow H fuel d := dartRuleOutflow_nonneg H fuel d
    rcases h_flank7 d hd with h_ed7 | ⟨h_next7, h_prev7⟩
    · rw [netDartShift_eq_neg_outflow_of_deg_le_6_of_target_deg_ge_7 H fuel d (H.edge_involution d) hd_deg h_ed7]
      omega
    · dsimp [netDartShift]
      have h_in0 : dartRuleOutflow H fuel (H.edge.f d) = 0 :=
        dartRuleOutflow_eq_zero_of_deg_ge_6_of_flanking_spokes_ge_7 H fuel d (h_nb6 d hd) h_next7 h_prev7
      omega)
  omega

/-- Primal–Dual Degree-6 Discharging Theorem on `H.dual` with Degree-`≥ 6` Neighbors. -/
theorem dual_finalCharge_le_zero_of_deg_6_of_isBridgeless_of_neighbors_deg_ge_6_of_flanking_spokes_ge_7
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg6 : Hypermap.nodeDegree H.dual u fuel = 6)
    (h_nb6 : ∀ d ∈ getOrbit H.dual.node fuel u, 6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel)
    (h_flank7 : ∀ d ∈ getOrbit H.dual.node fuel u,
      7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel ∨
      (7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∧
       7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel)) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_6_of_neighbors_deg_ge_6_of_flanking_spokes_ge_7
    H.dual darts h_all h_le u h_loopless h_deg6 h_nb6 h_flank7

/-!
### Stage L.3: Hub-Cap Discharging Bounds for Degrees 12–19 with Degree-5 Neighbors & Master Phase 5 Synthesis
-/

/-- When `degs 0 = 5` and either `6 ≤ degs 3` or `6 ≤ degs 5`,
    at most 2 of the 3 rules `[r1, r3, r5]` can match (`orientOutflowDegs inv degs ≤ 2`). -/
theorem orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (h_3_or_5 : 6 ≤ degs 3 ∨ 6 ≤ degs 5) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h3_le : (if (if inv then r3.invert else true) && matchesRawRuleDegs degs r3 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h5_le : (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  rcases h_3_or_5 with hb3 | hb5
  · have h3_zero : matchesRawRuleDegs degs r3 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
    rw [h3_zero]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  · have h5_zero : matchesRawRuleDegs degs r5 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r5 5 5 5 (by decide) (by decide) (by omega)
    rw [h5_zero]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Sharp Incoming Outflow Bound (`≤ 5`) from a Degree-5 Neighbor Flanked on One Side by Degree `≥ 6`:
    if `nodeDegree H (H.edge.f d) fuel = 5` and at least one flanking spoke (`H.node.f d` or `H.node.inv d`)
    has neighbor degree `≥ 6`, then `dartRuleOutflow H fuel (H.edge.f d) ≤ 5`. -/
theorem dartRuleOutflow_le_5_of_deg_5_of_flanking_spoke_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr5 : Hypermap.nodeDegree H (H.edge.f d) fuel = 5)
    (h_flank6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
                6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 5 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  rcases h_flank6 with h_next6 | h_prev6
  · have hf := orientOutflowDegs_le_3_of_deg_5 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr5)
    have ht := orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr5)
      (Or.inl (by simpa [ruleVertexDart_true_edge_three] using h_next6))
    omega
  · have hf := orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr5)
      (Or.inl (by simpa [ruleVertexDart_false_edge_three] using h_prev6))
    have ht := orientOutflowDegs_le_3_of_deg_5 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr5)
    omega

/-- Sharp Incoming Outflow Bound (`≤ 4`) from an Isolated Degree-5 Neighbor
    (flanked on both sides by degree-`≥ 6` spoke neighbors):
    if `nodeDegree H (H.edge.f d) fuel = 5`, `6 ≤ nodeDegree H (H.edge.f (H.node.f d)) fuel`,
    and `6 ≤ nodeDegree H (H.edge.f (H.node.inv d)) fuel`, then `dartRuleOutflow H fuel (H.edge.f d) ≤ 4`. -/
theorem dartRuleOutflow_le_4_of_deg_5_of_flanking_spokes_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr5 : Hypermap.nodeDegree H (H.edge.f d) fuel = 5)
    (h_next6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 4 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_curr5)
    (Or.inl (by simpa [ruleVertexDart_false_edge_three] using h_prev6))
  have ht := orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_curr5)
    (Or.inl (by simpa [ruleVertexDart_true_edge_three] using h_next6))
  omega

/-- Sharp Incoming Outflow Bound (`≤ 2`) from a Degree-5 Neighbor Flanked on Both Sides by Degree `≥ 7`:
    if `nodeDegree H (H.edge.f d) fuel = 5`, `7 ≤ nodeDegree H (H.edge.f (H.node.f d)) fuel`,
    and `7 ≤ nodeDegree H (H.edge.f (H.node.inv d)) fuel`, then `dartRuleOutflow H fuel (H.edge.f d) ≤ 2`. -/
theorem dartRuleOutflow_le_2_of_deg_5_of_flanking_spokes_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr5 : Hypermap.nodeDegree H (H.edge.f d) fuel = 5)
    (h_next7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 2 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_1_of_deg_5_of_deg3_ge_7 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_curr5)
    (by simpa [ruleVertexDart_false_edge_three] using h_prev7)
  have ht := orientOutflowDegs_le_1_of_deg_5_of_deg3_ge_7 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_curr5)
    (by simpa [ruleVertexDart_true_edge_three] using h_next7)
  omega

/-- Sharp Incoming Outflow Bound (`≤ 3`) from a Degree-6 Neighbor Flanked on One Side by Degree `≥ 7`. -/
theorem dartRuleOutflow_le_3_of_deg_6_of_flanking_spoke_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr6 : Hypermap.nodeDegree H (H.edge.f d) fuel = 6)
    (h_flank7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
                7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 3 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  rcases h_flank7 with h_next7 | h_prev7
  · have hf := orientOutflowDegs_le_3_of_deg_6 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr6)
    have ht := orientOutflowDegs_eq_zero_of_deg_6_of_deg3_ge_7 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr6)
      (by simpa [ruleVertexDart_true_edge_three] using h_next7)
    omega
  · have hf := orientOutflowDegs_eq_zero_of_deg_6_of_deg3_ge_7 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr6)
      (by simpa [ruleVertexDart_false_edge_three] using h_prev7)
    have ht := orientOutflowDegs_le_3_of_deg_6 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr6)
    omega

/-- Global Hub-Cap Discharging Theorem for Degrees `12–19` (and all `deg ≥ 12`) with Degree-5 Neighbors:
    for any loopless hub vertex `u` of degree `k ≥ 12` where every spoke `d ∈ getOrbit H.node fuel u`
    either:
    1. points to a degree-5 neighbor with at least one flanking spoke of degree `≥ 6`
       (no 3 consecutive degree-5 neighbors), or
    2. points to a neighbor of degree `≥ 6` flanked by degree-`≥ 6` spokes, or
    3. points to a degree-6 neighbor with at least one flanking spoke of degree `≥ 7`, or
    4. points to a neighbor of degree `≥ 8` (or `< 5`),
    every spoke has `netDartShift H fuel d ≤ 5` and `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`
    (`60 - 10k + 5k = 60 - 5k ≤ 0` for all `k ≥ 12`). -/
theorem finalCharge_le_zero_of_deg_ge_12_of_deg5_or_deg_ge_6_neighbors
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H u fuel)
    (h_spokes : ∀ d ∈ getOrbit H.node fuel u,
      (Hypermap.nodeDegree H (H.edge.f d) fuel = 5 ∧
        (6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
         6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)) ∨
      (6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∧
       6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) ∨
      (Hypermap.nodeDegree H (H.edge.f d) fuel = 6 ∧
        (7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
         7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)) ∨
      8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 5 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have h_in5 : dartRuleOutflow H fuel (H.edge.f d) ≤ 5 := by
      rcases h_spokes d hd with ⟨h5, h_fl6⟩ | ⟨h_next6, h_prev6⟩ | ⟨h6, h_fl7⟩ | h_ge8
      · exact dartRuleOutflow_le_5_of_deg_5_of_flanking_spoke_ge_6 H fuel d h5 h_fl6
      · exact dartRuleOutflow_le_5_of_target_deg_ge_8_of_flanking_spokes_ge_6 H fuel d (by omega) h_next6 h_prev6
      · have := dartRuleOutflow_le_3_of_deg_6_of_flanking_spoke_ge_7 H fuel d h6 h_fl7; omega
      · rcases Nat.lt_or_ge 8 (Hypermap.nodeDegree H (H.edge.f d) fuel) with h_ge9 | h_le8
        · have := dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel (H.edge.f d) h_ge9; omega
        · have h_eq8 : Hypermap.nodeDegree H (H.edge.f d) fuel = 8 := by omega
          have := dartRuleOutflow_le_4_of_deg_8 H fuel (H.edge.f d) h_eq8; omega
    omega)
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Primal–Dual Hub-Cap Discharging Theorem on `H.dual` for Degrees `12–19` (and `deg ≥ 12`) with Degree-5 Neighbors. -/
theorem dual_finalCharge_le_zero_of_deg_ge_12_of_isBridgeless_of_deg5_or_deg_ge_6_neighbors
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_spokes : ∀ d ∈ getOrbit H.dual.node fuel u,
      (Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel = 5 ∧
        (6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∨
         6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel)) ∨
      (6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∧
       6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel) ∨
      (Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel = 6 ∧
        (7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∨
         7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel)) ∨
      8 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_12_of_deg5_or_deg_ge_6_neighbors
    H.dual darts h_all h_le u h_loopless h_deg12 h_spokes

/-- Global Hub-Cap Discharging Theorem for Degrees `10–19` (and all `deg ≥ 10`) with Isolated Degree-5 Neighbors:
    for any loopless hub vertex `u` of degree `k ≥ 10` where every spoke `d ∈ getOrbit H.node fuel u`
    either:
    1. points to an isolated degree-5 neighbor (`deg = 5` flanked on both sides by degree-`≥ 6` spokes), or
    2. points to a degree-6 neighbor with at least one flanking spoke of degree `≥ 7`, or
    3. points to a neighbor of degree `≥ 8`,
    every spoke has `netDartShift H fuel d ≤ 4` and `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`
    (`60 - 10k + 4k = 60 - 6k ≤ 0` for all `k ≥ 10`). -/
theorem finalCharge_le_zero_of_deg_ge_10_of_isolated_deg5_neighbors
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg10 : 10 ≤ Hypermap.nodeDegree H u fuel)
    (h_spokes : ∀ d ∈ getOrbit H.node fuel u,
      (Hypermap.nodeDegree H (H.edge.f d) fuel = 5 ∧
       6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∧
       6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) ∨
      (Hypermap.nodeDegree H (H.edge.f d) fuel = 6 ∧
        (7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
         7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)) ∨
      8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 4 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have h_in4 : dartRuleOutflow H fuel (H.edge.f d) ≤ 4 := by
      rcases h_spokes d hd with ⟨h5, h_next6, h_prev6⟩ | ⟨h6, h_fl7⟩ | h_ge8
      · exact dartRuleOutflow_le_4_of_deg_5_of_flanking_spokes_ge_6 H fuel d h5 h_next6 h_prev6
      · have := dartRuleOutflow_le_3_of_deg_6_of_flanking_spoke_ge_7 H fuel d h6 h_fl7; omega
      · rcases Nat.lt_or_ge 8 (Hypermap.nodeDegree H (H.edge.f d) fuel) with h_ge9 | h_le8
        · have := dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel (H.edge.f d) h_ge9; omega
        · have h_eq8 : Hypermap.nodeDegree H (H.edge.f d) fuel = 8 := by omega
          exact dartRuleOutflow_le_4_of_deg_8 H fuel (H.edge.f d) h_eq8
    omega)
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Primal–Dual Hub-Cap Discharging Theorem on `H.dual` for Degrees `10–19` (and `deg ≥ 10`) with Isolated Degree-5 Neighbors. -/
theorem dual_finalCharge_le_zero_of_deg_ge_10_of_isBridgeless_of_isolated_deg5_neighbors
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg10 : 10 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_spokes : ∀ d ∈ getOrbit H.dual.node fuel u,
      (Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel = 5 ∧
       6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∧
       6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel) ∨
      (Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel = 6 ∧
        (7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∨
         7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel)) ∨
      8 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_10_of_isolated_deg5_neighbors
    H.dual darts h_all h_le u h_loopless h_deg10 h_spokes

/-- Incoming outflow into a degree-`≤ 6` vertex `d` from a degree-`≥ 6` neighbor `H.edge.f d`
    vanishes (`dartRuleOutflow H fuel (H.edge.f d) = 0`) whenever coordinates `5, 9, 11` around `H.edge.f d`
    have degree `≥ 6` in both orientations. -/
theorem dartRuleOutflow_eq_zero_of_deg_ge_6_of_target_deg_le_6_of_no_deg5_second_ring
    (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart)
    (h_d_le6 : Hypermap.nodeDegree H d fuel ≤ 6)
    (h_ed_ge6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_sec : ∀ inv : Bool,
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 5) fuel ∧
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 9) fuel ∧
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 11) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) = 0 := by
  rcases Nat.lt_or_ge 6 (Hypermap.nodeDegree H (H.edge.f d) fuel) with h_ge7 | h_le6
  · apply dartRuleOutflow_eq_zero_of_deg_ge_7_of_target_deg_le_6 H fuel (H.edge.f d) h_ge7
    rw [H.edge_involution d]
    exact h_d_le6
  · have h_eq6 : Hypermap.nodeDegree H (H.edge.f d) fuel = 6 := by omega
    rw [dartRuleOutflow_eq_orientOutflowDegs_add]
    rcases h_sec false with ⟨hf5, hf9, hf11⟩
    rcases h_sec true with ⟨ht5, ht9, ht11⟩
    have hf := orientOutflowDegs_eq_zero_of_deg_6_of_target_deg_le_6_of_no_deg5_second_ring false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_eq6)
      (by simpa [ruleVertexDart, H.edge_involution] using h_d_le6)
      hf5 hf9 hf11
    have ht := orientOutflowDegs_eq_zero_of_deg_6_of_target_deg_le_6_of_no_deg5_second_ring true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_eq6)
      (by simpa [ruleVertexDart, H.edge_involution] using h_d_le6)
      ht5 ht9 ht11
    omega

/-- Global Degree-6 Discharging Theorem when all neighbors have degree `≥ 6` and no degree-6 neighbor
    has degree-5 vertices at coordinates `5, 9, 11`. -/
theorem finalCharge_le_zero_of_deg_6_of_neighbors_deg_ge_6_of_no_deg5_second_ring
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : Hypermap.nodeDegree H u fuel = 6)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_sec : ∀ d ∈ getOrbit H.node fuel u, ∀ inv : Bool,
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 5) fuel ∧
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 9) fuel ∧
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 11) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  apply finalCharge_le_zero_of_deg_6_of_orbitNetShift_nonpos H darts h_all h_le u h_loopless h_deg6
  dsimp [orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 0 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel ≤ 6 := by
      have := nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
      omega
    have h_out_nonneg : 0 ≤ dartRuleOutflow H fuel d := dartRuleOutflow_nonneg H fuel d
    have h_in0 : dartRuleOutflow H fuel (H.edge.f d) = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_6_of_target_deg_le_6_of_no_deg5_second_ring
        H fuel d hd_deg (h_nb6 d hd) (h_sec d hd)
    omega)
  omega

/-- Primal–Dual Degree-6 Discharging Theorem on `H.dual` when `orbitNetShift H.dual fuel u ≤ 0`
    (covering all degree-6 hubs whose inflow from degree-5/6 neighbors is compensated by outflow to degree-`≥ 7` neighbors). -/
theorem dual_finalCharge_le_zero_of_deg_6_of_isBridgeless_of_orbitNetShift_nonpos
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg6 : Hypermap.nodeDegree H.dual u fuel = 6)
    (h_net : orbitNetShift H.dual fuel u ≤ 0) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_6_of_orbitNetShift_nonpos H.dual darts h_all h_le u h_loopless h_deg6 h_net

/-!
### Stage M.1: `MatchesCartState31` Lifting through `narrowSWAR`, `checkBoundRec`, and `verifyHubcapMembersRec`
-/

/-- Narrowing a 6-bit lane by bitwise AND (`narrowSWAR st po = st &&& po.keep`) preserves `≤ 31`. -/
theorem getLaneNat_narrowSWAR_le_31 {st : Nat} (po : FastPosOut) {p : Nat}
    (h_le : getLaneNat st p ≤ 31) :
    getLaneNat (narrowSWAR st po) p ≤ 31 := by
  change getLaneNat (st &&& po.keep) p ≤ 31
  rw [getLaneNat_and]
  exact Nat.le_trans Nat.and_le_left h_le

/-- Any active well-formed SWAR outlet preserves `MatchesCartState31` under `narrowSWAR`. -/
theorem matchesCartState31_narrowSWAR_of_outletActive (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) (po : FastPosOut)
    (h_deg : deg ≤ 11)
    (h_valid : validFastPosOut deg po = true)
    (h_match31 : MatchesCartState31 deg cartDeg st)
    (h_active : OutletActive deg cartDeg po = true) :
    MatchesCartState31 deg cartDeg (narrowSWAR st po) :=
  ⟨matchesCartState_narrowSWAR_of_outletActive deg cartDeg st po h_deg h_valid h_match31.1 h_active,
   fun p hp1 hp2 => getLaneNat_narrowSWAR_le_31 po (h_match31.2 p hp1 hp2)⟩

/-- `MatchesCartState31` lifting of `checkBoundLoopRec_sound`, collapsing any `reduceAxleRec` call
    directly into `HasExactReducedAxle deg cartDeg`. -/
theorem checkBoundLoopRec_sound31 (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11)
    (cb : Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (h_cb : ∀ (st' forcedIn' : Nat) (negBefore' rem' excluded' : List FastPosOut) (maxch' : Nat) (hs' : HintStream),
      MatchesCartState31 deg cartDeg st' →
      (∀ po ∈ negBefore', validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem', validFastPosOut deg po = true) →
      (∀ ex ∈ excluded', OutletActive deg cartDeg ex = false) →
      validHintStream hs' = true →
      (cb st' forcedIn' negBefore' rem' excluded' maxch' hs').1 = true →
      HasExactReducedAxle deg cartDeg ∨
      (forcedIn' : Int) + activeOutletSum deg cartDeg negBefore' + activeOutletSum deg cartDeg rem' ≤ (maxch' : Int))
    (h_cb_hs : ∀ (st' forcedIn' : Nat) (negBefore' rem' excluded' : List FastPosOut) (maxch' : Nat) (hs' : HintStream),
      validHintStream hs' = true →
      validHintStream (cb st' forcedIn' negBefore' rem' excluded' maxch' hs').2 = true)
    (st forcedch maxch : Nat) (h_match31 : MatchesCartState31 deg cartDeg st)
    (rem : List FastPosOut) :
    ∀ (allowedch : Nat) (negBefore curExcluded : List FastPosOut) (hs : HintStream),
      allowedch = countPos rem →
      (∀ po ∈ negBefore, validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem, validFastPosOut deg po = true) →
      (∀ ex ∈ curExcluded, OutletActive deg cartDeg ex = false) →
      validHintStream hs = true →
      (checkBoundLoopRec cb st forcedch maxch rem allowedch negBefore curExcluded hs).1 = true →
      HasExactReducedAxle deg cartDeg ∨
      (forcedch : Int) + activeOutletSum deg cartDeg negBefore + activeOutletSum deg cartDeg rem ≤ (maxch : Int) := by
  induction rem with
  | nil =>
    intro allowedch negBefore curExcluded hs _ _ _ _ _ h_ok
    rw [checkBoundLoopRec_nil] at h_ok
    contradiction
  | cons po subRem ih =>
    intro allowedch negBefore curExcluded hs h_all h_neg h_rem h_excl h_hs h_ok
    have h_po := h_rem po List.mem_cons_self
    have h_sub : ∀ q ∈ subRem, validFastPosOut deg q = true :=
      fun q hq => h_rem q (List.mem_cons_of_mem po hq)
    rw [checkBoundLoopRec_cons_eq] at h_ok
    simp only [strictNat_eq] at h_ok
    cases h_pos : po.isPos with
    | false =>
      rw [h_pos] at h_ok
      dsimp only at h_ok
      have h_all' : allowedch = countPos subRem := by
        simpa [countPos, h_pos] using h_all
      have h_neg' : ∀ q ∈ po :: negBefore, validFastPosOut deg q = true ∧ q.isPos = false := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq_mem
        · exact ⟨h_po, h_pos⟩
        · exact h_neg q hq_mem
      rcases ih allowedch (po :: negBefore) curExcluded hs h_all' h_neg' h_sub h_excl h_hs h_ok with h_red | h_bound
      · exact Or.inl h_red
      · right
        simp only [activeOutletSum] at h_bound ⊢
        omega
    | true =>
      rw [h_pos] at h_ok
      dsimp only at h_ok
      cases h_act : OutletActive deg cartDeg po with
      | true =>
        have h_match_next := matchesCartState31_narrowSWAR_of_outletActive deg cartDeg st po h_deg h_po h_match31 h_act
        have h_no_excl := noExcludedForcedRec_eq_true deg cartDeg (narrowSWAR st po) h_match_next.1 curExcluded h_excl
        rw [h_no_excl] at h_ok
        dsimp only at h_ok
        cases h_cb_ok : (cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs).fst with
        | false =>
          rw [h_cb_ok] at h_ok; dsimp only at h_ok; contradiction
        | true =>
          rcases h_cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs
            h_match_next h_neg h_sub h_excl h_hs h_cb_ok with h_red | h_bound
          · exact Or.inl h_red
          · right
            simp only [Nat.add_eq, activeOutletSum, outletVal, h_act, h_pos, ↓reduceIte] at h_bound ⊢
            omega
      | false =>
        let resSub :=
          @Bool.rec (fun _ => Bool × HintStream)
            (true, hs)
            (cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs)
            (noExcludedForcedRec (narrowSWAR st po) curExcluded)
        have h_resSub_hs : validHintStream resSub.2 = true := by
          dsimp [resSub]
          cases noExcludedForcedRec (narrowSWAR st po) curExcluded with
          | false => exact h_hs
          | true => exact h_cb_hs _ _ _ _ _ _ hs h_hs
        change (@Bool.rec (fun _ => Bool × HintStream)
          (false, resSub.2)
          (@Bool.rec (fun _ => Bool × HintStream)
            (checkBoundLoopRec cb st forcedch maxch subRem (Nat.sub allowedch 1) negBefore (po :: curExcluded) resSub.2)
            (true, resSub.2)
            (Nat.ble (Nat.add (Nat.sub allowedch 1) forcedch) maxch))
          resSub.1).1 = true at h_ok
        cases h_okSub : resSub.1 with
        | false =>
          rw [h_okSub] at h_ok; dsimp only at h_ok; contradiction
        | true =>
          rw [h_okSub] at h_ok; dsimp only at h_ok
          have h_all' : Nat.sub allowedch 1 = countPos subRem := by
            have : allowedch = 1 + countPos subRem := by simpa [countPos, h_pos] using h_all
            simp only [Nat.sub_eq]
            omega
          cases h_ble : Nat.ble (Nat.add (Nat.sub allowedch 1) forcedch) maxch with
          | true =>
            right
            have h_le : (Nat.sub allowedch 1) + forcedch ≤ maxch := Nat.le_of_ble_eq_true h_ble
            have h_neg_le : activeOutletSum deg cartDeg negBefore ≤ 0 :=
              activeOutletSum_le_zero_of_all_neg deg cartDeg negBefore (fun q hq => (h_neg q hq).2)
            have h_sub_le : activeOutletSum deg cartDeg subRem ≤ (countPos subRem : Int) :=
              activeOutletSum_le_countPos deg cartDeg subRem
            simp only [activeOutletSum, h_act, Bool.false_eq_true, ↓reduceIte]
            omega
          | false =>
            rw [h_ble] at h_ok; dsimp only at h_ok
            have h_excl' : ∀ ex ∈ po :: curExcluded, OutletActive deg cartDeg ex = false := by
              intro ex hex
              rcases List.mem_cons.mp hex with rfl | hex_mem
              · exact h_act
              · exact h_excl ex hex_mem
            rcases ih (Nat.sub allowedch 1) negBefore (po :: curExcluded) resSub.2 h_all' h_neg h_sub h_excl' h_resSub_hs h_ok with h_red | h_bound
            · exact Or.inl h_red
            · right
              simp only [activeOutletSum, h_act, Bool.false_eq_true, ↓reduceIte]
              omega

/-- `MatchesCartState31` lifting of `checkBoundRec_sound`:
    whenever `(checkBoundRec deg fuel st forcedIn negBefore rem excluded maxch hs).1 = true`
    on `st` satisfying `MatchesCartState31 deg cartDeg st`, either `HasExactReducedAxle deg cartDeg`
    holds directly (via `reduceAxleRec_sound`), or the active outlet sum plus `forcedIn` is at most `maxch`. -/
theorem checkBoundRec_sound31 (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11) (fuel : Nat) :
    ∀ (st forcedIn : Nat) (negBefore rem excluded : List FastPosOut) (maxch : Nat) (hs : HintStream),
      MatchesCartState31 deg cartDeg st →
      (∀ po ∈ negBefore, validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem, validFastPosOut deg po = true) →
      (∀ ex ∈ excluded, OutletActive deg cartDeg ex = false) →
      validHintStream hs = true →
      (checkBoundRec deg fuel st forcedIn negBefore rem excluded maxch hs).1 = true →
      HasExactReducedAxle deg cartDeg ∨
      (forcedIn : Int) + activeOutletSum deg cartDeg negBefore + activeOutletSum deg cartDeg rem ≤ (maxch : Int) := by
  induction fuel with
  | zero =>
    intro st forcedIn negBefore rem excluded maxch hs _ _ _ _ _ h_ok
    rw [checkBoundRec_zero] at h_ok
    contradiction
  | succ fuel ih =>
    intro st forcedIn negBefore rem excluded maxch hs h_match31 h_neg h_rem h_excl h_hs h_ok
    rw [checkBoundRec_succ_eq] at h_ok
    have h_fneg := filterNegAPS_sound deg cartDeg st h_deg h_match31.1 negBefore forcedIn h_neg
    let forced1 := (filterNegAPS st negBefore forcedIn).1
    let nextNegBefore := (filterNegAPS st negBefore forcedIn).2
    have h_frem := filterRemAPS_sound deg cartDeg st h_deg h_match31.1 rem forced1 h_rem
    let forcedch := (filterRemAPS st rem forced1).1
    let allowedch := (filterRemAPS st rem forced1).2.1
    let nextRem := (filterRemAPS st rem forced1).2.2
    change (@Bool.rec (fun _ => Bool × HintStream)
      (@Bool.rec (fun _ => Bool × HintStream)
        (checkBoundLoopRec (checkBoundRec deg fuel) st forcedch maxch nextRem allowedch nextNegBefore excluded hs)
        (reduceAxleRec deg 64 [st] hs)
        (Nat.ble (Nat.add maxch 1) forcedch))
      (true, hs)
      (Nat.ble (Nat.add forcedch allowedch) maxch)).1 = true at h_ok
    cases h_ble1 : Nat.ble (Nat.add forcedch allowedch) maxch with
    | true =>
      right
      have h_le : forcedch + allowedch ≤ maxch := Nat.le_of_ble_eq_true h_ble1
      have h_neg_le : activeOutletSum deg cartDeg nextNegBefore ≤ 0 :=
        activeOutletSum_le_zero_of_all_neg deg cartDeg nextNegBefore (fun q hq => (h_fneg.1 q hq).2)
      have h_rem_le : activeOutletSum deg cartDeg nextRem ≤ (countPos nextRem : Int) :=
        activeOutletSum_le_countPos deg cartDeg nextRem
      have h_all_eq : allowedch = countPos nextRem := h_frem.2.1
      have h1 : (forcedIn : Int) + activeOutletSum deg cartDeg negBefore ≤
          (forced1 : Int) + activeOutletSum deg cartDeg nextNegBefore := h_fneg.2
      have h2 : (forced1 : Int) + activeOutletSum deg cartDeg rem ≤
          (forcedch : Int) + activeOutletSum deg cartDeg nextRem := h_frem.2.2
      omega
    | false =>
      rw [h_ble1] at h_ok; dsimp only at h_ok
      cases h_ble2 : Nat.ble (Nat.add maxch 1) forcedch with
      | true =>
        rw [h_ble2] at h_ok; dsimp only at h_ok
        exact Or.inl (reduceAxleRec_sound deg cartDeg h_deg 64 [st] hs ⟨st, List.mem_cons_self, h_match31⟩ h_hs h_ok)
      | false =>
        rw [h_ble2] at h_ok; dsimp only at h_ok
        rcases checkBoundLoopRec_sound31 deg cartDeg h_deg (checkBoundRec deg fuel) ih
          (fun st' forcedIn' negBefore' rem' excluded' maxch' hs' =>
            checkBoundRec_validHintStream deg fuel st' forcedIn' negBefore' rem' excluded' maxch' hs')
          st forcedch maxch h_match31 nextRem allowedch nextNegBefore excluded hs
          h_frem.2.1 h_fneg.1 h_frem.1 h_excl h_hs h_ok with h_red | h_bound
        · exact Or.inl h_red
        · right
          have h1 : (forcedIn : Int) + activeOutletSum deg cartDeg negBefore ≤
              (forced1 : Int) + activeOutletSum deg cartDeg nextNegBefore := h_fneg.2
          have h2 : (forced1 : Int) + activeOutletSum deg cartDeg rem ≤
              (forcedch : Int) + activeOutletSum deg cartDeg nextRem := h_frem.2.2
          omega

/-- `MatchesCartState31` lifting of `verifyHubcapMembersRec_sound`:
    whenever `(verifyHubcapMembersRec deg st shiftedTable members hs).1 = true` on `st`
    satisfying `MatchesCartState31 deg cartDeg st`, either `HasExactReducedAxle deg cartDeg` holds,
    or EVERY hubcap member `(x, y, v) ∈ members` satisfies the LP bound. -/
theorem verifyHubcapMembersRec_sound31 (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11)
    (st : Nat) (h_match31 : MatchesCartState31 deg cartDeg st)
    (shiftedTable : List (List FastPosOut))
    (h_table : ∀ row ∈ shiftedTable, ∀ po ∈ row, validFastPosOut deg po = true)
    (members : List (Nat × Nat × Int)) :
    ∀ (hs : HintStream),
      validHintStream hs = true →
      (verifyHubcapMembersRec deg st shiftedTable members hs).1 = true →
      HasExactReducedAxle deg cartDeg ∨
      ∀ m ∈ members,
        500 + activeOutletSum deg cartDeg
          (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
           else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
          ((m.2.2 + 500).toNat : Int) := by
  induction members with
  | nil =>
    intro _ _ _
    exact Or.inr (fun _ hm => by contradiction)
  | cons m rest ih =>
    intro hs h_hs h_ok
    rw [verifyHubcapMembersRec_cons] at h_ok
    rcases m with ⟨x, y, v⟩
    dsimp only at h_ok
    simp only [strictNat_eq] at h_ok
    let outsX := lookupListRec [] shiftedTable x
    let outsY := lookupListRec [] shiftedTable y
    let initRem :=
      @Bool.rec (fun _ => List FastPosOut)
        outsX
        (appendFastPosOut outsX outsY)
        (!Nat.beq x y)
    let resCB := checkBoundRec deg 20 st 500 [] initRem [] (v + 500).toNat hs
    change (@Bool.rec (fun _ => Bool × HintStream) (false, resCB.2)
      (verifyHubcapMembersRec deg st shiftedTable rest resCB.2) resCB.1).1 = true at h_ok
    cases h_cb : resCB.1 with
    | false =>
      rw [h_cb] at h_ok; dsimp only at h_ok; contradiction
    | true =>
      rw [h_cb] at h_ok; dsimp only at h_ok
      have h_init_valid : ∀ po ∈ initRem, validFastPosOut deg po = true := by
        dsimp [initRem]
        cases (!Nat.beq x y) with
        | false =>
          exact validFastPosOut_lookupListRec deg shiftedTable h_table x
        | true =>
          dsimp only
          rw [appendFastPosOut_eq_append]
          intro po hpo
          rcases List.mem_append.mp hpo with hX | hY
          · exact validFastPosOut_lookupListRec deg shiftedTable h_table x po hX
          · exact validFastPosOut_lookupListRec deg shiftedTable h_table y po hY
      rcases checkBoundRec_sound31 deg cartDeg h_deg 20 st 500 [] initRem [] (v + 500).toNat hs
        h_match31 (by intro _ h; contradiction) h_init_valid (by intro _ h; contradiction) h_hs h_cb with h_red | h_bound
      · exact Or.inl h_red
      · rcases ih resCB.2 (checkBoundRec_validHintStream deg 20 st 500 [] initRem [] (v + 500).toNat hs h_hs) h_ok with h_red | h_rest
        · exact Or.inl h_red
        · right
          intro m' hm'
          rcases List.mem_cons.mp hm' with rfl | hm_rest
          · dsimp only
            have h_init_eq : initRem = (if Nat.beq x y then outsX else outsX ++ outsY) := by
              dsimp [initRem]
              cases Nat.beq x y with
              | true => rfl
              | false => exact appendFastPosOut_eq_append outsX outsY
            rw [← h_init_eq]
            simpa [activeOutletSum] using h_bound
          · exact h_rest m' hm_rest

/-!
### Stage M.2: Computable RSST Hubcap Cover Validity & Hub Charge Arithmetic Bridge
-/

/-- Number of hubcap members `(x, y, v) ∈ members` incident to spoke `i` (`x == i || y == i`). -/
def hubcapSpokeOcc : List (Nat × Nat × Int) → Nat → Nat
  | [], _ => 0
  | m :: rest, i => (if Nat.beq m.1 i || Nat.beq m.2.1 i then 1 else 0) + hubcapSpokeOcc rest i

/-- RSST weight `w(m) ∈ {1, 2}` of a hubcap member `m = (x, y, v)` in `members`. -/
def hubcapMemberWeight (members : List (Nat × Nat × Int)) (m : Nat × Nat × Int) : Nat :=
  if Nat.beq (hubcapSpokeOcc members m.1) 1 then 2 else 1

/-- Total weight of members in `l` incident to spoke `i` using weight function `w`. -/
def hubcapSpokeWeightSum (w : Nat × Nat × Int → Nat) (i : Nat) : List (Nat × Nat × Int) → Nat
  | [] => 0
  | m :: rest =>
    (if Nat.beq m.1 i || Nat.beq m.2.1 i then w m else 0) + hubcapSpokeWeightSum w i rest

/-- Weighted sum of upper bounds `w(m) * v` over `m = (x, y, v) ∈ l`. -/
def hubcapWeightedBoundSum (w : Nat × Nat × Int → Nat) : List (Nat × Nat × Int) → Int
  | [] => 0
  | m :: rest => (w m : Int) * m.2.2 + hubcapWeightedBoundSum w rest

/-- Computable RSST Hubcap Cover Validity Predicate for hub degree `deg`:
    1. Every member `(x, y, v) ∈ members` has `1 ≤ x, y ≤ deg` and `-500 ≤ v`.
    2. Every spoke `i ∈ [1..deg]` is covered with total weight `2`.
    3. The weighted sum of bounds is at most `20 * (deg - 6) + 1`. -/
def validHubcapCover (deg : Nat) (members : List (Nat × Nat × Int)) : Bool :=
  let w := hubcapMemberWeight members
  members.all (fun m =>
    Nat.ble 1 m.1 && Nat.ble m.1 deg &&
    Nat.ble 1 m.2.1 && Nat.ble m.2.1 deg &&
    decide (-500 ≤ m.2.2)) &&
  (List.range' 1 deg).all (fun i =>
    Nat.beq (hubcapSpokeWeightSum w i members) 2) &&
  decide (hubcapWeightedBoundSum w members ≤ 20 * ((deg : Int) - 6) + 1)

/-- Explicit non-vacuity lemma: the empty hubcap `[]` is never a valid cover for any `deg ≥ 1`. -/
theorem not_validHubcapCover_nil (deg : Nat) (h_deg : 1 ≤ deg) :
    validHubcapCover deg [] = false := by
  rcases Nat.exists_eq_add_of_le h_deg with ⟨k, rfl⟩
  have h_r : List.range' 1 (1 + k) = 1 :: List.range' 2 k := by
    rw [Nat.add_comm 1 k]
    rfl
  simp [validHubcapCover, h_r, hubcapSpokeWeightSum]

/-- Sum of an integer-valued function `f : Nat → Int` over a list of indices `idxs : List Nat`. -/
def sumNatList (f : Nat → Int) : List Nat → Int
  | [] => 0
  | i :: rest => f i + sumNatList f rest

theorem foldl_add_eq_add_sumNatList (f : Nat → Int) (l : List Nat) (init : Int) :
    l.foldl (fun acc i => acc + f i) init = init + sumNatList f l := by
  induction l generalizing init with
  | nil => simp [sumNatList]
  | cons i rest ih =>
    simp only [List.foldl_cons, sumNatList]
    rw [ih (init + f i)]
    omega

theorem sumNatList_add (f g : Nat → Int) (l : List Nat) :
    sumNatList (fun i => f i + g i) l = sumNatList f l + sumNatList g l := by
  induction l with
  | nil => simp [sumNatList]
  | cons i rest ih =>
    simp only [sumNatList, ih]
    omega

theorem sumNatList_const_mul (c : Int) (f : Nat → Int) (l : List Nat) :
    sumNatList (fun i => c * f i) l = c * sumNatList f l := by
  induction l with
  | nil => simp [sumNatList]
  | cons i rest ih =>
    simp only [sumNatList, ih, Int.mul_add]

theorem sumNatList_congr {f g : Nat → Int} {l : List Nat} (h : ∀ i ∈ l, f i = g i) :
    sumNatList f l = sumNatList g l := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
    simp only [sumNatList]
    rw [h i List.mem_cons_self, ih (fun j hj => h j (List.mem_cons_of_mem i hj))]

theorem sumNatList_ite_beq_range' (f : Nat → Int) (x : Nat) :
    ∀ (s n : Nat),
      sumNatList (fun i => if Nat.beq x i then f i else 0) (List.range' s n) =
        if s ≤ x ∧ x < s + n then f x else 0 := by
  intro s n
  induction n generalizing s with
  | zero =>
    simp only [List.range', sumNatList]
    split
    · omega
    · rfl
  | succ n ih =>
    simp only [List.range'_succ, sumNatList, ih (s + 1)]
    cases h_beq : Nat.beq x s with
    | true =>
      have hxs : x = s := Nat.beq_eq.mp h_beq
      subst hxs
      simp only [↓reduceIte]
      have h_not : ¬(x + 1 ≤ x ∧ x < x + 1 + n) := by omega
      have h_yes : x ≤ x ∧ x < x + (n + 1) := by omega
      rw [if_neg h_not, if_pos h_yes]
      omega
    | false =>
      have hxs : x ≠ s := fun h => by subst h; rw [Nat.beq_refl] at h_beq; contradiction
      simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_add]
      by_cases h_in : s + 1 ≤ x ∧ x < s + 1 + n
      · have h_in' : s ≤ x ∧ x < s + (n + 1) := by omega
        rw [if_pos h_in, if_pos h_in']
      · have h_in' : ¬(s ≤ x ∧ x < s + (n + 1)) := by omega
        rw [if_neg h_in, if_neg h_in']

theorem activeOutletSum_member_eq_sumNatList (deg : Nat) (cartDeg : Nat → Nat)
    (shiftedTable : List (List FastPosOut)) {x y : Nat}
    (hx1 : 1 ≤ x) (hx2 : x ≤ deg) (hy1 : 1 ≤ y) (hy2 : y ≤ deg) :
    activeOutletSum deg cartDeg
      (if Nat.beq x y then lookupListRec [] shiftedTable x
       else lookupListRec [] shiftedTable x ++ lookupListRec [] shiftedTable y) =
    sumNatList
      (fun i => if Nat.beq x i || Nat.beq y i then
        activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i) else 0)
      (List.range' 1 deg) := by
  let S := fun i => activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)
  cases hxy : Nat.beq x y with
  | true =>
    have h_eq : x = y := Nat.beq_eq.mp hxy
    subst h_eq
    simp only [Bool.or_self, ↓reduceIte]
    rw [sumNatList_ite_beq_range' S x 1 deg, if_pos ⟨hx1, by omega⟩]
  | false =>
    have h_ne : x ≠ y := fun h => by subst h; rw [Nat.beq_refl] at hxy; contradiction
    simp only [Bool.false_eq_true, ↓reduceIte, activeOutletSum_append]
    have h_split :
        sumNatList (fun i => if Nat.beq x i || Nat.beq y i then S i else 0) (List.range' 1 deg) =
        sumNatList (fun i => (if Nat.beq x i then S i else 0) + (if Nat.beq y i then S i else 0)) (List.range' 1 deg) := by
      apply sumNatList_congr
      intro i _
      cases hxi : Nat.beq x i with
      | false => simp
      | true =>
        have h_xi : x = i := Nat.beq_eq.mp hxi
        have hyi : Nat.beq y i = false := by
          cases h_yi : Nat.beq y i with
          | false => rfl
          | true =>
            have h_yi_eq : y = i := Nat.beq_eq.mp h_yi
            omega
        simp [hyi]
    rw [h_split, sumNatList_add, sumNatList_ite_beq_range' S x 1 deg, sumNatList_ite_beq_range' S y 1 deg,
        if_pos ⟨hx1, by omega⟩, if_pos ⟨hy1, by omega⟩]

theorem sumNatList_hubcapSpokeWeightSum_le_weightedBoundSum
    (deg : Nat) (cartDeg : Nat → Nat) (shiftedTable : List (List FastPosOut))
    (w : Nat × Nat × Int → Nat) (l : List (Nat × Nat × Int))
    (h_valid : ∀ m ∈ l, 1 ≤ m.1 ∧ m.1 ≤ deg ∧ 1 ≤ m.2.1 ∧ m.2.1 ≤ deg ∧ -500 ≤ m.2.2)
    (h_bounds : ∀ m ∈ l,
      500 + activeOutletSum deg cartDeg
        (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
         else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
        ((m.2.2 + 500).toNat : Int)) :
    sumNatList
      (fun i => (hubcapSpokeWeightSum w i l : Int) *
        activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i))
      (List.range' 1 deg) ≤
    hubcapWeightedBoundSum w l := by
  let S := fun i => activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)
  induction l with
  | nil =>
    have h_zero :
        sumNatList (fun i => (hubcapSpokeWeightSum w i [] : Int) * S i) (List.range' 1 deg) =
        sumNatList (fun _ => 0) (List.range' 1 deg) := by
      apply sumNatList_congr
      intro i _
      simp [hubcapSpokeWeightSum]
    rw [h_zero]
    have h_z2 : ∀ l' : List Nat, sumNatList (fun _ => 0) l' = 0 := by
      intro l'; induction l' with
      | nil => rfl
      | cons _ _ ih => simp [sumNatList, ih]
    rw [h_z2]
    exact Int.le_refl 0
  | cons m rest ih =>
    have hm_val := h_valid m List.mem_cons_self
    rcases hm_val with ⟨hx1, hx2, hy1, hy2, hv500⟩
    have hm_b := h_bounds m List.mem_cons_self
    have hm_le :
        activeOutletSum deg cartDeg
          (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
           else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤ m.2.2 := by
      omega
    rw [activeOutletSum_member_eq_sumNatList deg cartDeg shiftedTable hx1 hx2 hy1 hy2] at hm_le
    have h_w_le := Int.mul_le_mul_of_nonneg_left hm_le (Int.natCast_nonneg (w m))
    rw [← sumNatList_const_mul] at h_w_le
    have h_ih := ih
      (fun m' hm' => h_valid m' (List.mem_cons_of_mem m hm'))
      (fun m' hm' => h_bounds m' (List.mem_cons_of_mem m hm'))
    have h_step :
        sumNatList (fun i => (hubcapSpokeWeightSum w i (m :: rest) : Int) * S i) (List.range' 1 deg) =
        sumNatList (fun i => (w m : Int) * (if Nat.beq m.1 i || Nat.beq m.2.1 i then S i else 0)) (List.range' 1 deg) +
        sumNatList (fun i => (hubcapSpokeWeightSum w i rest : Int) * S i) (List.range' 1 deg) := by
      rw [← sumNatList_add]
      apply sumNatList_congr
      intro i _
      dsimp only [hubcapSpokeWeightSum]
      cases Nat.beq m.1 i || Nat.beq m.2.1 i <;> simp [Int.natCast_add, Int.add_mul]
    rw [h_step]
    dsimp [hubcapWeightedBoundSum]
    dsimp [S] at h_w_le h_ih ⊢
    omega

/-- Fundamental RSST Hubcap Arithmetic Soundness Theorem:
    whenever `validHubcapCover deg members = true` and every member `m ∈ members` satisfies
    the verified `checkBoundRec` inequality, the hub's initial charge `10 * (6 - deg)` plus
    the total active outlet sum across all spokes `1 .. deg` is at most `0`. -/
theorem activeOutletSum_hub_le_of_validHubcapCover
    (deg : Nat) (cartDeg : Nat → Nat) (shiftedTable : List (List FastPosOut))
    (members : List (Nat × Nat × Int))
    (h_cover : validHubcapCover deg members = true)
    (h_bounds : ∀ m ∈ members,
      500 + activeOutletSum deg cartDeg
        (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
         else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
        ((m.2.2 + 500).toNat : Int)) :
    10 * (6 - (deg : Int)) +
      (List.range' 1 deg).foldl
        (fun acc i => acc + activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)) 0 ≤ 0 := by
  rw [foldl_add_eq_add_sumNatList, Int.zero_add]
  let w := hubcapMemberWeight members
  let S := fun i => activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)
  dsimp [validHubcapCover] at h_cover
  rcases Bool.and_eq_true_iff.mp h_cover with ⟨h_cov12, h_sum_le_b⟩
  rcases Bool.and_eq_true_iff.mp h_cov12 with ⟨h_all_mem, h_all_spokes⟩
  have h_sum_le : hubcapWeightedBoundSum w members ≤ 20 * ((deg : Int) - 6) + 1 :=
    of_decide_eq_true h_sum_le_b
  have h_valid : ∀ m ∈ members, 1 ≤ m.1 ∧ m.1 ≤ deg ∧ 1 ≤ m.2.1 ∧ m.2.1 ≤ deg ∧ -500 ≤ m.2.2 := by
    intro m hm
    have hm_b := List.all_eq_true.mp h_all_mem m hm
    rcases Bool.and_eq_true_iff.mp hm_b with ⟨hb1234, hb5⟩
    rcases Bool.and_eq_true_iff.mp hb1234 with ⟨hb123, hb4⟩
    rcases Bool.and_eq_true_iff.mp hb123 with ⟨hb12, hb3⟩
    rcases Bool.and_eq_true_iff.mp hb12 with ⟨hb1, hb2⟩
    exact ⟨Nat.le_of_ble_eq_true hb1, Nat.le_of_ble_eq_true hb2,
           Nat.le_of_ble_eq_true hb3, Nat.le_of_ble_eq_true hb4,
           of_decide_eq_true hb5⟩
  have h_le_wb := sumNatList_hubcapSpokeWeightSum_le_weightedBoundSum deg cartDeg shiftedTable w members h_valid h_bounds
  have h_eq_two :
      sumNatList (fun i => (hubcapSpokeWeightSum w i members : Int) * S i) (List.range' 1 deg) =
      2 * sumNatList S (List.range' 1 deg) := by
    rw [← sumNatList_const_mul]
    apply sumNatList_congr
    intro i hi
    have hi_eq : hubcapSpokeWeightSum w i members = 2 :=
      Nat.beq_eq.mp (List.all_eq_true.mp h_all_spokes i hi)
    rw [hi_eq]
    rfl
  dsimp [S] at h_eq_two
  omega

/-- Computable structural validity check on `t : ProofTree` at hub degree `deg` with remaining depth budget `maxLev`:
    - Every `ProofTree.cond v m tTrue tFalse` has `maxLev ≥ 1` and `1 ≤ v ≤ 5 * deg`.
    - Every `ProofTree.hubcap members` satisfies `validHubcapCover deg members = true`. -/
def validProofTree (deg : Nat) : Nat → ProofTree → Bool
  | _, ProofTree.reduce => true
  | _, ProofTree.sym _ _ _ _ => true
  | _, ProofTree.hubcap members => validHubcapCover deg members
  | 0, ProofTree.cond _ _ _ _ => false
  | maxLev + 1, ProofTree.cond v _ tTrue tFalse =>
    Nat.ble 1 v && Nat.ble v (Nat.mul 5 deg) &&
    validProofTree deg maxLev tTrue &&
    validProofTree deg maxLev tFalse

set_option maxRecDepth 2000000 in
theorem validProofTree_present7 : validProofTree 7 58 (present7 ()) = true := by decide

set_option maxRecDepth 2000000 in
theorem validProofTree_present8 : validProofTree 8 58 (present8 ()) = true := by decide

set_option maxRecDepth 2000000 in
theorem validProofTree_present9 : validProofTree 9 58 (present9 ()) = true := by decide

set_option maxRecDepth 2000000 in
theorem validProofTree_present10 : validProofTree 10 58 (present10 ()) = true := by decide

set_option maxRecDepth 2000000 in
theorem validProofTree_present11 : validProofTree 11 58 (present11 ()) = true := by decide

/-!
### Stage M.3: Non-Vacuous 2-Way `CoreCartLeaf` & Elimination of `ProofTree.sym`
-/

/-- Non-vacuous 2-way core leaf certificate for a cartwheel degree assignment `cartDeg`:
    either (1) `cartDeg` has an exact reduced axle configuration (`HasExactReducedAxle`),
    or (2) `cartDeg` satisfies all LP bounds of a structurally valid RSST hubcap cover
       (`validHubcapCover deg members = true`). -/
def CoreCartLeaf (deg : Nat) (shiftedTable : List (List FastPosOut)) (cartDeg : Nat → Nat) : Prop :=
  HasExactReducedAxle deg cartDeg ∨
  (∃ members : List (Nat × Nat × Int),
    validHubcapCover deg members = true ∧
    ∀ m ∈ members,
      500 + activeOutletSum deg cartDeg
        (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
         else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
        ((m.2.2 + 500).toNat : Int))

/-- Every `CoreCartLeaf` either has an exact reduced axle configuration (`HasExactReducedAxle`)
    or satisfies the non-positive hub charge inequality
    `10 * (6 - deg) + ∑_{i=1..deg} activeOutletSum(i) ≤ 0`. -/
theorem coreCartLeaf_reducible_or_hub_sum_le_zero
    (deg : Nat) (shiftedTable : List (List FastPosOut)) (cartDeg : Nat → Nat)
    (h_core : CoreCartLeaf deg shiftedTable cartDeg) :
    HasExactReducedAxle deg cartDeg ∨
    10 * (6 - (deg : Int)) +
      (List.range' 1 deg).foldl
        (fun acc i => acc + activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)) 0 ≤ 0 := by
  rcases h_core with h_red | ⟨members, h_cover, h_bounds⟩
  · exact Or.inl h_red
  · exact Or.inr (activeOutletSum_hub_le_of_validHubcapCover deg cartDeg shiftedTable members h_cover h_bounds)

/-- A cartwheel degree assignment `cd` satisfies the condition prefix stored in lanes `0 .. lev - 1`
    of `(condV, condM)` if for every `i < lev`, the bitmask in lane `i` of `condM` has the bit
    for `cd (getLaneNat condV i)` set. -/
def SatisfiesPrefix (cd : Nat → Nat) (condV condM lev : Nat) : Prop :=
  ∀ i < lev, (getLaneNat condM i).testBit (degBitIdx (cd (getLaneNat condV i))) = true

theorem extractCondsRec_eq_none_of_getLaneNat_zero (deg condV condM lev : Nat)
    (h_zero : getLaneNat condV lev = 0) :
    extractCondsRec deg condV condM lev = none := by
  rw [extractCondsRec_eq_loop]
  cases lev with
  | zero =>
    change (strictNat (getLaneNat condV 0) fun n =>
      @Bool.rec (fun _ => Option (List (Nat × Nat))) none
        (some ((n, getLaneNat condM 0) :: []))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = none
    rw [strictNat_eq, h_zero]
    rfl
  | succ i =>
    change (strictNat (Nat.add i 1) fun idx =>
      strictNat (getLaneNat condV idx) fun n =>
      @Bool.rec (fun _ => Option (List (Nat × Nat))) none
        (extractCondsLoop deg condV condM i ((n, getLaneNat condM idx) :: []))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = none
    rw [strictNat_eq, strictNat_eq]
    have h_idx : Nat.add i 1 = i + 1 := rfl
    rw [h_idx, h_zero]
    rfl

theorem extractCondsLoop_sublist (deg condV condM : Nat) :
    ∀ (k : Nat) (acc res : List (Nat × Nat)),
      extractCondsLoop deg condV condM k acc = some res →
      (∀ c ∈ acc, c ∈ res) ∧
      (∀ j ≤ k, (getLaneNat condV j, getLaneNat condM j) ∈ res) := by
  intro k
  induction k with
  | zero =>
    intro acc res h_some
    change (strictNat (getLaneNat condV 0) fun n =>
      @Bool.rec (fun _ => Option (List (Nat × Nat))) none
        (some ((n, getLaneNat condM 0) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = some res at h_some
    rw [strictNat_eq] at h_some
    let n := getLaneNat condV 0
    cases h_b : (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)) with
    | false => rw [h_b] at h_some; contradiction
    | true =>
      rw [h_b] at h_some
      dsimp only at h_some
      injection h_some with h_eq
      subst h_eq
      refine ⟨fun c hc => List.mem_cons_of_mem _ hc, ?_⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact List.mem_cons_self
  | succ i ih =>
    intro acc res h_some
    unfold extractCondsLoop at h_some
    dsimp only at h_some
    rw [strictNat_eq, strictNat_eq] at h_some
    let idx := Nat.add i 1
    let n := getLaneNat condV idx
    change (@Bool.rec (fun _ => Option (List (Nat × Nat))) none
      (extractCondsLoop deg condV condM i ((n, getLaneNat condM idx) :: acc))
      (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = some res at h_some
    cases h_b : (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)) with
    | false => rw [h_b] at h_some; contradiction
    | true =>
      rw [h_b] at h_some
      dsimp only at h_some
      have ⟨h_acc, h_le⟩ := ih ((n, getLaneNat condM idx) :: acc) res h_some
      refine ⟨fun c hc => h_acc c (List.mem_cons_of_mem _ hc), ?_⟩
      intro j hj
      by_cases hji : j ≤ i
      · exact h_le j hji
      · have hj_eq : j = idx := by change j = i + 1; omega
        subst hj_eq
        exact h_acc _ List.mem_cons_self

theorem satisfiesPrefix_of_extractCondsRec (deg condV condM lev : Nat)
    {conds : List (Nat × Nat)} (h_some : extractCondsRec deg condV condM lev = some conds)
    (cd : Nat → Nat)
    (h_sat : ∀ c ∈ conds, c.2.testBit (degBitIdx (cd c.1)) = true) :
    SatisfiesPrefix cd condV condM (lev + 1) := by
  rw [extractCondsRec_eq_loop] at h_some
  have ⟨_, h_mem⟩ := extractCondsLoop_sublist deg condV condM lev [] conds h_some
  intro j hj
  exact h_sat (getLaneNat condV j, getLaneNat condM j) (h_mem j (by omega))

theorem satisfiesPrefix_cond_iff (cd : Nat → Nat) (condV condM lev v maskTrue : Nat)
    (h_lev : lev + 1 < 60) :
    SatisfiesPrefix cd
      (setLaneNat (setLaneNat condV lev v) (Nat.add lev 1) 0)
      (setLaneNat (setLaneNat condM lev maskTrue) (Nat.add lev 1) 0)
      lev ↔
    SatisfiesPrefix cd condV condM lev := by
  constructor <;> intro h i hi
  · have hi60 : i < 60 := by omega
    have hi_ne1 : i ≠ Nat.add lev 1 := by change i ≠ lev + 1; omega
    have hi_ne0 : i ≠ lev := by omega
    have h_i := h i hi
    rw [getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 i hi60 hi_ne1,
        getLaneNat_setLaneNat_ne _ lev maskTrue i hi60 hi_ne0,
        getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 i hi60 hi_ne1,
        getLaneNat_setLaneNat_ne _ lev v i hi60 hi_ne0] at h_i
    exact h_i
  · have hi60 : i < 60 := by omega
    have hi_ne1 : i ≠ Nat.add lev 1 := by change i ≠ lev + 1; omega
    have hi_ne0 : i ≠ lev := by omega
    rw [getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 i hi60 hi_ne1,
        getLaneNat_setLaneNat_ne _ lev maskTrue i hi60 hi_ne0,
        getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 i hi60 hi_ne1,
        getLaneNat_setLaneNat_ne _ lev v i hi60 hi_ne0]
    exact h i hi

theorem satisfiesPrefix_cond_succ_iff (cd : Nat → Nat) (condV condM lev v maskTrue : Nat)
    (h_lev : lev + 1 < 60) (hv64 : v < 64) :
    SatisfiesPrefix cd
      (setLaneNat (setLaneNat condV lev v) (Nat.add lev 1) 0)
      (setLaneNat (setLaneNat condM lev maskTrue) (Nat.add lev 1) 0)
      (Nat.add lev 1) ↔
    (SatisfiesPrefix cd condV condM lev ∧
     maskTrue.testBit (degBitIdx (cd v)) = true) := by
  let condV' := setLaneNat (setLaneNat condV lev v) (Nat.add lev 1) 0
  let condM' := setLaneNat (setLaneNat condM lev maskTrue) (Nat.add lev 1) 0
  have h_lev60 : lev < 60 := by omega
  have h_ne1 : lev ≠ Nat.add lev 1 := by change lev ≠ lev + 1; omega
  have h_v_eq : getLaneNat condV' lev = v := by
    dsimp [condV']
    rw [getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 lev h_lev60 h_ne1,
        getLaneNat_setLaneNat_self condV lev v h_lev60 hv64]
  have h_m_tb : (getLaneNat condM' lev).testBit (degBitIdx (cd v)) = maskTrue.testBit (degBitIdx (cd v)) := by
    dsimp [condM']
    rw [getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 lev h_lev60 h_ne1,
        testBit_getLaneNat_setLaneNat_self condM lev maskTrue h_lev60 (degBitIdx_lt_6 _)]
  constructor
  · intro h
    refine ⟨(satisfiesPrefix_cond_iff cd condV condM lev v maskTrue h_lev).mp (fun i hi => h i (by change i < lev + 1; omega)), ?_⟩
    have h_at := h lev (by change lev < lev + 1; omega)
    rw [h_v_eq, h_m_tb] at h_at
    exact h_at
  · rintro ⟨h_pre, h_tb⟩ i hi
    have hi_le : i ≤ lev := by change i < lev + 1 at hi; omega
    by_cases hi_lt : i < lev
    · exact (satisfiesPrefix_cond_iff cd condV condM lev v maskTrue h_lev).mpr h_pre i hi_lt
    · have hi_eq : i = lev := by omega
      subst hi_eq
      rw [h_v_eq, h_m_tb]
      exact h_tb

theorem matchesCartState31_cond_true (deg : Nat) (cartDeg : Nat → Nat) (st v : Nat) (m : Int)
    (h_deg : deg ≤ 11) (h_match31 : MatchesCartState31 deg cartDeg st)
    (h_true : (condMaskNat m).testBit (degBitIdx (cartDeg v)) = true) :
    MatchesCartState31 deg cartDeg (setLaneNat st v (Nat.land (getLaneNat st v) (condMaskNat m))) := by
  refine ⟨?_, ?_⟩
  · intro p hp1 hp2
    have hp60 : p < 60 := by omega
    by_cases hpv : p = v
    · subst hpv
      rw [testBit_getLaneNat_setLaneNat_self _ _ _ hp60 (degBitIdx_lt_6 _)]
      change ((getLaneNat st p) &&& (condMaskNat m)).testBit (degBitIdx (cartDeg p)) = true
      rw [Nat.testBit_and, h_match31.1 p hp1 hp2, h_true]
      rfl
    · rw [testBit_getLaneNat_setLaneNat_ne _ _ _ p hp60 hpv (degBitIdx_lt_6 _)]
      exact h_match31.1 p hp1 hp2
  · intro p hp1 hp2
    have hp60 : p < 60 := by omega
    change getLaneNat (setLaneNat st v (getLaneNat st v &&& condMaskNat m)) p ≤ 31
    by_cases hpv : p = v
    · subst hpv
      have h_le : getLaneNat st p &&& condMaskNat m ≤ 31 :=
        Nat.le_trans Nat.and_le_left (h_match31.2 p hp1 hp2)
      rw [getLaneNat_setLaneNat_self st p (getLaneNat st p &&& condMaskNat m) hp60 (by omega)]
      exact h_le
    · rw [getLaneNat_setLaneNat_ne st v (getLaneNat st v &&& condMaskNat m) p hp60 hpv]
      exact h_match31.2 p hp1 hp2

theorem matchesCartState31_cond_false (deg : Nat) (cartDeg : Nat → Nat) (st v : Nat) (m : Int)
    (h_deg : deg ≤ 11) (h_match31 : MatchesCartState31 deg cartDeg st)
    (h_false : (condMaskNat m).testBit (degBitIdx (cartDeg v)) = false) :
    MatchesCartState31 deg cartDeg (setLaneNat st v (Nat.land (getLaneNat st v) (Nat.xor 31 (condMaskNat m)))) := by
  refine ⟨?_, ?_⟩
  · intro p hp1 hp2
    have hp60 : p < 60 := by omega
    by_cases hpv : p = v
    · subst hpv
      rw [testBit_getLaneNat_setLaneNat_self _ _ _ hp60 (degBitIdx_lt_6 _)]
      change ((getLaneNat st p) &&& (31 ^^^ condMaskNat m)).testBit (degBitIdx (cartDeg p)) = true
      rw [Nat.testBit_and, Nat.testBit_xor, h_match31.1 p hp1 hp2, testBit_31_degBitIdx, h_false]
      rfl
    · rw [testBit_getLaneNat_setLaneNat_ne _ _ _ p hp60 hpv (degBitIdx_lt_6 _)]
      exact h_match31.1 p hp1 hp2
  · intro p hp1 hp2
    have hp60 : p < 60 := by omega
    change getLaneNat (setLaneNat st v (getLaneNat st v &&& Nat.xor 31 (condMaskNat m))) p ≤ 31
    by_cases hpv : p = v
    · subst hpv
      have h_le : getLaneNat st p &&& Nat.xor 31 (condMaskNat m) ≤ 31 :=
        Nat.le_trans Nat.and_le_left (h_match31.2 p hp1 hp2)
      rw [getLaneNat_setLaneNat_self st p (getLaneNat st p &&& Nat.xor 31 (condMaskNat m)) hp60 (by omega)]
      exact h_le
    · rw [getLaneNat_setLaneNat_ne st v (getLaneNat st v &&& Nat.xor 31 (condMaskNat m)) p hp60 hpv]
      exact h_match31.2 p hp1 hp2

/-- Master Top-Down Traversal Soundness of `verifyTreePureRec` (Eliminating `ProofTree.sym`):
    Tracks the three invariants (`SymTableSound`, `SiblingSound`, `PrefixSound`) across
    both branches of every `ProofTree.cond` node, proving that every `ProofTree.sym` leaf
    reduces to a previously verified `CoreCartLeaf` subtree via dihedral symmetry. -/
theorem verifyTreePureRec_sound_of_pred (deg : Nat) (shiftedTable : List (List FastPosOut))
    (P : (Nat → Nat) → Prop)
    (h_deg1 : 1 ≤ deg) (h_deg : deg ≤ 11)
    (h_table : ∀ row ∈ shiftedTable, ∀ po ∈ row, validFastPosOut deg po = true)
    (h_leaf : ∀ cd, CoreCartLeaf deg shiftedTable cd → P cd)
    (h_sym : ∀ (cd : Nat → Nat) (k : Nat) (refl : Bool) (conds : List (Nat × Nat)),
      k < deg →
      (∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) →
      (∀ c ∈ conds, c.2.testBit (degBitIdx (symCartDeg deg k refl cd c.1)) = true) →
      (∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') →
      P cd)
    (t : ProofTree) :
    ∀ (maxLev st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream),
      validProofTree deg maxLev t = true →
      lev + maxLev < 60 →
      (∀ o ∈ syms, (∀ c ∈ o.conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) ∧
        (∀ cd', (∀ c ∈ o.conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd')) →
      (∀ conds, extractCondsRec deg condV condM lev = some conds →
        ∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') →
      (∀ cd', SatisfiesPrefix cd' condV condM lev → P cd' ∨ MatchesCartState31 deg cd' st) →
      validHintStream hs = true →
      (verifyTreePureRec deg shiftedTable t st lineno lev condV condM syms hs).1 = true →
      ∀ cd, SatisfiesPrefix cd condV condM lev → P cd := by
  induction t with
  | reduce =>
    intro maxLev st lineno lev condV condM syms hs _ _ _ _ h_pref h_hs h_ok cd h_cd
    rcases h_pref cd h_cd with hP | h_match31
    · exact hP
    · change (let (ok, hs') := reduceAxleRec deg 64 [st] hs
              strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs')).1 = true at h_ok
      simp only [strictNat_eq] at h_ok
      exact h_leaf cd (Or.inl (reduceAxleRec_sound deg cd h_deg 64 [st] hs ⟨st, List.mem_cons_self, h_match31⟩ h_hs h_ok))
  | hubcap members =>
    intro maxLev st lineno lev condV condM syms hs h_valid _ _ _ h_pref h_hs h_ok cd h_cd
    have h_cover : validHubcapCover deg members = true := by
      cases maxLev <;> exact h_valid
    rcases h_pref cd h_cd with hP | h_match31
    · exact hP
    · change (let (ok, hs') := verifyHubcapMembersRec deg st shiftedTable members hs
              strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs')).1 = true at h_ok
      simp only [strictNat_eq] at h_ok
      rcases verifyHubcapMembersRec_sound31 deg cd h_deg st h_match31 shiftedTable h_table members hs h_hs h_ok with h_red | h_bounds
      · exact h_leaf cd (Or.inl h_red)
      · exact h_leaf cd (Or.inr ⟨members, h_cover, h_bounds⟩)
  | sym k eps lev_in line =>
    intro maxLev st lineno lev condV condM syms hs _ _ h_syms _ h_pref _ h_ok cd h_cd
    rcases h_pref cd h_cd with hP | h_match31
    · exact hP
    · change (let ok :=
                Bool.rec false
                  (match findSymOutletRec line syms with
                   | none => false
                   | some found =>
                     Bool.rec false
                       (symForcedRec st (Nat.add k 1) deg (!Nat.beq eps 0) found.conds)
                       (Nat.beq found.nolines (Nat.add lev_in 1)))
                  (!Nat.ble deg k && Nat.ble eps 1)
              strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs)).1 = true at h_ok
      simp only [strictNat_eq] at h_ok
      cases h_ke : (!Nat.ble deg k && Nat.ble eps 1) with
      | false =>
        rw [h_ke] at h_ok; dsimp at h_ok; contradiction
      | true =>
        rw [h_ke] at h_ok; dsimp at h_ok
        cases h_find : findSymOutletRec line syms with
        | none =>
          rw [h_find] at h_ok; contradiction
        | some found =>
          rw [h_find] at h_ok; dsimp at h_ok
          cases h_nl : Nat.beq found.nolines (Nat.add lev_in 1) with
          | false =>
            rw [h_nl] at h_ok; dsimp at h_ok; contradiction
          | true =>
            rw [h_nl] at h_ok; dsimp at h_ok
            rcases Bool.and_eq_true_iff.mp h_ke with ⟨hk_not, _⟩
            have hk_lt : k < deg :=
              Classical.byContradiction fun h_ge => by
                rw [Nat.ble_eq_true_of_le (by omega)] at hk_not
                contradiction
            have ⟨h_found_conds, h_found_P⟩ := h_syms found (findSymOutletRec_mem line syms h_find)
            have h_shift_lt : Nat.add k 1 - 1 < deg := by
              change (k + 1) - 1 < deg
              omega
            have h_forced := symForcedRec_sound deg cd st (Nat.add k 1) (!Nat.beq eps 0)
              found.conds h_deg1 h_shift_lt h_match31.1 h_found_conds h_ok
            exact h_sym cd k (!Nat.beq eps 0) found.conds hk_lt h_found_conds h_forced h_found_P
  | cond v m tTrue tFalse ihTrue ihFalse =>
    intro maxLev st lineno lev condV condM syms hs h_valid h_lev_max h_syms h_sib h_pref h_hs h_ok
    cases maxLev with
    | zero =>
      dsimp [validProofTree] at h_valid
      contradiction
    | succ maxLev' =>
      dsimp [validProofTree] at h_valid
      rcases Bool.and_eq_true_iff.mp h_valid with ⟨h_v123, h_val_false⟩
      rcases Bool.and_eq_true_iff.mp h_v123 with ⟨h_v12, h_val_true⟩
      rcases Bool.and_eq_true_iff.mp h_v12 with ⟨hv1_b, hv2_b⟩
      have hv1 : 1 ≤ v := Nat.le_of_ble_eq_true hv1_b
      have hv2 : v ≤ 5 * deg := Nat.le_of_ble_eq_true hv2_b
      have hv64 : v < 64 := by omega
      have h_lev1 : lev + 1 < 60 := by omega
      rw [verifyTreePureRec_cond_eq] at h_ok
      simp only [strictNat_eq] at h_ok
      let maskTrue := condMaskNat m
      let maskFalse := Nat.xor 31 maskTrue
      let curLane := getLaneNat st v
      let stTrue := setLaneNat st v (Nat.land curLane maskTrue)
      let stFalse := setLaneNat st v (Nat.land curLane maskFalse)
      let lev1 := Nat.add lev 1
      let lineno1 := Nat.add lineno 1
      let syms' :=
        match extractCondsRec deg condV condM lev with
        | none => syms
        | some conds => { number := lineno, nolines := lev1, conds := conds } :: syms
      have h_syms' : ∀ o ∈ syms', (∀ c ∈ o.conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) ∧
          (∀ cd', (∀ c ∈ o.conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') := by
        dsimp [syms']
        cases h_ext : extractCondsRec deg condV condM lev with
        | none => exact h_syms
        | some conds =>
          intro o ho
          rcases List.mem_cons.mp ho with rfl | ho_tail
          · exact ⟨extractCondsRec_sound deg condV condM lev h_ext, h_sib conds h_ext⟩
          · exact h_syms o ho_tail
      let condV' := setLaneNat (setLaneNat condV lev v) lev1 0
      let condM' := setLaneNat (setLaneNat condM lev maskTrue) lev1 0
      let resTrue := verifyTreePureRec deg shiftedTable tTrue stTrue lineno1 lev1 condV' condM' syms' hs
      change (@Bool.rec (fun _ => Bool × Nat × HintStream) (false, resTrue.2.fst, resTrue.2.snd)
        (verifyTreePureRec deg shiftedTable tFalse stFalse resTrue.2.fst lev condV' condM' syms' resTrue.2.snd)
        resTrue.fst).fst = true at h_ok
      cases h_b : resTrue.fst with
      | false =>
        rw [h_b] at h_ok; dsimp at h_ok; contradiction
      | true =>
        rw [h_b] at h_ok; dsimp at h_ok
        have h_sib_true : ∀ conds, extractCondsRec deg condV' condM' lev1 = some conds →
            ∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd' := by
          intro conds h_some
          have h_z : getLaneNat condV' lev1 = 0 :=
            getLaneNat_setLaneNat_self _ lev1 0 h_lev1 (by omega)
          rw [extractCondsRec_eq_none_of_getLaneNat_zero deg condV' condM' lev1 h_z] at h_some
          contradiction
        have h_pref_true : ∀ cd', SatisfiesPrefix cd' condV' condM' lev1 → P cd' ∨ MatchesCartState31 deg cd' stTrue := by
          intro cd' h_sat1
          rcases (satisfiesPrefix_cond_succ_iff cd' condV condM lev v maskTrue h_lev1 hv64).mp h_sat1 with ⟨h_sat0, h_tb⟩
          rcases h_pref cd' h_sat0 with hP | h_match31
          · exact Or.inl hP
          · exact Or.inr (matchesCartState31_cond_true deg cd' st v m h_deg h_match31 h_tb)
        have h_true_all : ∀ cd', SatisfiesPrefix cd' condV' condM' lev1 → P cd' :=
          ihTrue maxLev' stTrue lineno1 lev1 condV' condM' syms' hs
            h_val_true (by change (lev + 1) + maxLev' < 60; omega) h_syms' h_sib_true h_pref_true h_hs h_b
        have h_sib_false : ∀ conds, extractCondsRec deg condV' condM' lev = some conds →
            ∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd' := by
          intro conds h_some cd' h_sat
          exact h_true_all cd' (satisfiesPrefix_of_extractCondsRec deg condV' condM' lev h_some cd' h_sat)
        have h_pref_false : ∀ cd', SatisfiesPrefix cd' condV' condM' lev → P cd' ∨ MatchesCartState31 deg cd' stFalse := by
          intro cd' h_sat0'
          have h_sat0 : SatisfiesPrefix cd' condV condM lev :=
            (satisfiesPrefix_cond_iff cd' condV condM lev v maskTrue h_lev1).mp h_sat0'
          rcases h_pref cd' h_sat0 with hP | h_match31
          · exact Or.inl hP
          · cases h_bit : maskTrue.testBit (degBitIdx (cd' v)) with
            | true =>
              have h_sat1 : SatisfiesPrefix cd' condV' condM' lev1 :=
                (satisfiesPrefix_cond_succ_iff cd' condV condM lev v maskTrue h_lev1 hv64).mpr ⟨h_sat0, h_bit⟩
              exact Or.inl (h_true_all cd' h_sat1)
            | false =>
              exact Or.inr (matchesCartState31_cond_false deg cd' st v m h_deg h_match31 h_bit)
        have h_hs1 : validHintStream resTrue.2.snd = true :=
          verifyTreePureRec_validHintStream deg shiftedTable tTrue stTrue lineno1 lev1 condV' condM' syms' hs h_hs
        have h_false_all : ∀ cd', SatisfiesPrefix cd' condV' condM' lev → P cd' :=
          ihFalse maxLev' stFalse resTrue.2.fst lev condV' condM' syms' resTrue.2.snd
            h_val_false (by omega) h_syms' h_sib_false h_pref_false h_hs1 h_ok
        intro cd h_cd
        exact h_false_all cd ((satisfiesPrefix_cond_iff cd condV condM lev v maskTrue h_lev1).mpr h_cd)

/-- A family `ℱ : (Nat → Nat) → Prop` of cartwheel degree assignments at hub degree `deg`
    is closed under dihedral symmetries (`k < deg` rotations and `refl : Bool` reflections)
    on the first two rings (`1 ≤ p ≤ 2 * deg`). -/
def DihedralClosedFamily (deg : Nat) (ℱ : (Nat → Nat) → Prop) : Prop :=
  ∀ (cd : Nat → Nat) (k : Nat) (refl : Bool),
    k < deg → ℱ cd → ∃ cd', ℱ cd' ∧ ∀ p, 1 ≤ p → p ≤ 2 * deg → cd' p = symCartDeg deg k refl cd p

/-- Inductive dihedral orbit of a cartwheel degree assignment `cartDeg` at hub degree `deg`
    under rotational shifts (`k < deg`) and reflections (`refl : Bool`). -/
inductive InDihedralOrbit (deg : Nat) (cartDeg : Nat → Nat) : (Nat → Nat) → Prop
  | base : InDihedralOrbit deg cartDeg cartDeg
  | step {cd : Nat → Nat} (k : Nat) (refl : Bool) :
      k < deg → InDihedralOrbit deg cartDeg cd →
      InDihedralOrbit deg cartDeg (symCartDeg deg k refl cd)

theorem dihedralClosedFamily_inDihedralOrbit (deg : Nat) (cartDeg : Nat → Nat) :
    DihedralClosedFamily deg (InDihedralOrbit deg cartDeg) :=
  fun cd k refl hk h_in => ⟨symCartDeg deg k refl cd, .step k refl hk h_in, fun _ _ _ => rfl⟩

/-- Top-level `verifyTree` Core Soundness (with `ProofTree.sym` eliminated):
    for any dihedral-closed family `ℱ` of cartwheel degree assignments (`DihedralClosedFamily deg ℱ`)
    that is non-empty (`∃ cd₀, ℱ cd₀`), if `validProofTree deg 58 t = true` and
    `verifyTree configs deg A_low A_upp t outs = true` for `deg ∈ {7, 8, 9, 10, 11}`,
    then there exists a member `cd ∈ ℱ` satisfying the 2-way `CoreCartLeaf` certificate
    (`HasExactReducedAxle` or `validHubcapCover` LP bound). -/
theorem verifyTree_core_soundness (configs : List Configuration) (deg : Nat)
    (A_low A_upp : Array Nat) (t : ProofTree) (outs : Array Outlet)
    (ℱ : (Nat → Nat) → Prop) (h_closed : DihedralClosedFamily deg ℱ)
    {cd0 : Nat → Nat} (h_cd0 : ℱ cd0)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11)
    (h_valid : validProofTree deg 58 t = true)
    (h_ver : verifyTree configs deg A_low A_upp t outs = true) :
    ∃ cd, ℱ cd ∧ CoreCartLeaf deg (getShiftedTableForDeg deg) cd := by
  have h_deg1 : 1 ≤ deg := by rcases h_deg with rfl | rfl | rfl | rfl | rfl <;> omega
  have h_le11 : deg ≤ 11 := by rcases h_deg with rfl | rfl | rfl | rfl | rfl <;> omega
  let shiftedTable := getShiftedTableForDeg deg
  let P : (Nat → Nat) → Prop := fun cd => ℱ cd → ∃ cd', ℱ cd' ∧ CoreCartLeaf deg shiftedTable cd'
  have h_leaf : ∀ cd, CoreCartLeaf deg shiftedTable cd → P cd :=
    fun cd h_core h_F => ⟨cd, h_F, h_core⟩
  have h_sym : ∀ (cd : Nat → Nat) (k : Nat) (refl : Bool) (conds : List (Nat × Nat)),
      k < deg →
      (∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) →
      (∀ c ∈ conds, c.2.testBit (degBitIdx (symCartDeg deg k refl cd c.1)) = true) →
      (∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') →
      P cd := by
    intro cd k refl conds hk h_conds h_forced h_all_P h_F
    rcases h_closed cd k refl hk h_F with ⟨cd', h_F', h_eq⟩
    have h_sat' : ∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true := by
      intro c hc
      rcases h_conds c hc with ⟨hc1, hc2⟩
      rw [h_eq c.1 hc1 hc2]
      exact h_forced c hc
    exact h_all_P cd' h_sat' h_F'
  have h_syms0 : ∀ o ∈ ([] : List SymOutlet), (∀ c ∈ o.conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) ∧
      (∀ cd', (∀ c ∈ o.conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') :=
    fun _ h => by cases h
  have h_sib0 : ∀ conds, extractCondsRec deg 0 0 0 = some conds →
      ∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd' := by
    intro conds h_some
    rw [extractCondsRec_eq_none_of_getLaneNat_zero deg 0 0 0 rfl] at h_some
    contradiction
  have h_pref0 : ∀ cd', SatisfiesPrefix cd' 0 0 0 → P cd' ∨ MatchesCartState31 deg cd' (getInitStateForDeg deg) :=
    fun cd' _ => Or.inr (matchesCartState31_getInitStateForDeg deg cd' h_deg)
  have h_sat0 : SatisfiesPrefix cd0 0 0 0 := fun _ hi => by omega
  exact verifyTreePureRec_sound_of_pred deg shiftedTable P h_deg1 h_le11
    (validFastPosOut_getShiftedTableForDeg deg h_deg) h_leaf h_sym t
    58 (getInitStateForDeg deg) 2 0 0 0 [] ([], getHintsForDeg deg)
    h_valid (by omega) h_syms0 h_sib0 h_pref0 (validHintStream_getHintsForDeg deg h_deg) h_ver cd0 h_sat0 h_cd0

/-- Top-level `DischargingTreesVerified` Core Soundness (with `ProofTree.sym` eliminated):
    for every hub degree `deg ∈ {7, 8, 9, 10, 11}` and any dihedral-closed family `ℱ`
    containing `cd0`, `DischargingTreesVerified configs` guarantees that some `cd ∈ ℱ`
    satisfies the non-vacuous 2-way `CoreCartLeaf deg (getShiftedTableForDeg deg) cd`. -/
theorem dischargingTreesVerified_core_soundness (configs : List Configuration)
    (h_trees : DischargingTreesVerified configs) (deg : Nat)
    (ℱ : (Nat → Nat) → Prop) (h_closed : DihedralClosedFamily deg ℱ)
    {cd0 : Nat → Nat} (h_cd0 : ℱ cd0)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    ∃ cd, ℱ cd ∧ CoreCartLeaf deg (getShiftedTableForDeg deg) cd := by
  rcases h_trees with ⟨h7, h8, h9, h10, h11⟩
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · exact verifyTree_core_soundness configs 7 (trivial_A_low 7) (trivial_A_upp 7) (present7 ()) (readOutlets 7 theRules) ℱ h_closed h_cd0 (Or.inl rfl) validProofTree_present7 h7
  · exact verifyTree_core_soundness configs 8 (trivial_A_low 8) (trivial_A_upp 8) (present8 ()) (readOutlets 8 theRules) ℱ h_closed h_cd0 (Or.inr (Or.inl rfl)) validProofTree_present8 h8
  · exact verifyTree_core_soundness configs 9 (trivial_A_low 9) (trivial_A_upp 9) (present9 ()) (readOutlets 9 theRules) ℱ h_closed h_cd0 (Or.inr (Or.inr (Or.inl rfl))) validProofTree_present9 h9
  · exact verifyTree_core_soundness configs 10 (trivial_A_low 10) (trivial_A_upp 10) (present10 ()) (readOutlets 10 theRules) ℱ h_closed h_cd0 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) validProofTree_present10 h10
  · exact verifyTree_core_soundness configs 11 (trivial_A_low 11) (trivial_A_upp 11) (present11 ()) (readOutlets 11 theRules) ℱ h_closed h_cd0 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) validProofTree_present11 h11

/-- Dihedral Orbit Core Soundness for any cartwheel degree assignment `cartDeg : Nat → Nat`:
    `DischargingTreesVerified configs` guarantees that some member `cd ∈ InDihedralOrbit deg cartDeg`
    satisfies `CoreCartLeaf deg (getShiftedTableForDeg deg) cd` (and hence either `HasExactReducedAxle`
    or `10 * (6 - deg) + ∑_{i=1..deg} activeOutletSum(i) ≤ 0`). -/
theorem dischargingTreesVerified_orbit_core_soundness (configs : List Configuration)
    (h_trees : DischargingTreesVerified configs) (deg : Nat) (cartDeg : Nat → Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    ∃ cd, InDihedralOrbit deg cartDeg cd ∧ CoreCartLeaf deg (getShiftedTableForDeg deg) cd :=
  dischargingTreesVerified_core_soundness configs h_trees deg
    (InDihedralOrbit deg cartDeg) (dihedralClosedFamily_inDihedralOrbit deg cartDeg)
    InDihedralOrbit.base h_deg

/-- Orientation-aware `i`-th spoke dart (`1 ≤ i ≤ deg`) around hub dart `d0` in hypermap `H`:
    iterates `H.node.f` when `refl = false` and `H.node.inv` (`H.node.symm`) when `refl = true`. -/
def spokeDartOriented (H : Hypermap) (refl : Bool) (d0 : H.Dart) (i : Nat) : H.Dart :=
  if refl then Hypermap.Perm.iter H.node.symm (i - 1) d0
  else Hypermap.Perm.iter H.node (i - 1) d0

/-- Orientation-aware cartwheel position map `0 ≤ p ≤ 5 * deg` around hub dart `d0` in hypermap `H`. -/
def cartDartOriented (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) (p : Nat) : H.Dart :=
  if p == 0 then d0
  else
    let ringIdx := (p - 1) / deg
    let s := spokeDartOriented H refl d0 ((p - 1) % deg + 1)
    if ringIdx == 0 then ruleVertexDart H (!refl) (H.edge.f s) 0
    else if ringIdx == 1 then ruleVertexDart H (!refl) (H.edge.f s) 5
    else if ringIdx == 2 then ruleVertexDart H (!refl) (H.edge.f s) 12
    else if ringIdx == 3 then ruleVertexDart H (!refl) (H.edge.f s) 13
    else if refl then H.edge.f (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.edge.f s))))))
    else H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f (H.edge.f s))))))

/-- Orientation-aware cartwheel degree assignment `Nat → Nat` around hub dart `d0` in hypermap `H`. -/
def cartDegOriented (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (refl : Bool) (d0 : H.Dart) (p : Nat) : Nat :=
  Hypermap.nodeDegree H (cartDartOriented H deg refl d0 p) fuel

@[simp] theorem spokeDartOriented_false (H : Hypermap) (d0 : H.Dart) (i : Nat) :
    spokeDartOriented H false d0 i = spokeDart H d0 i := rfl

@[simp] theorem cartDartOriented_false (H : Hypermap) (deg : Nat) (d0 : H.Dart) (p : Nat) :
    cartDartOriented H deg false d0 p = cartDart H deg d0 p := rfl

@[simp] theorem cartDegOriented_false (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (d0 : H.Dart) (p : Nat) :
    cartDegOriented H fuel deg false d0 p = cartDegOfDart H fuel deg d0 p := rfl

@[simp] theorem cartDartOriented_zero (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) :
    cartDartOriented H deg refl d0 0 = d0 := rfl

@[simp] theorem cartDegOriented_zero (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (refl : Bool) (d0 : H.Dart) :
    cartDegOriented H fuel deg refl d0 0 = Hypermap.nodeDegree H d0 fuel := rfl

theorem cartDartOriented_spoke (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 i = H.edge.f (spokeDartOriented H refl d0 i) := by
  dsimp [cartDartOriented]
  have h_ne0 : (i == 0) = false := beq_false_of_ne (by omega)
  have h_div : (i - 1) / deg = 0 := by simpa using ringIdx_of_mul_add (k := 0) hi1 hi2
  have h_mod : (i - 1) % deg + 1 = i := by simpa using spokeIdx_of_mul_add (k := 0) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

theorem cartDartOriented_hat (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 (deg + i) =
      ruleVertexDart H (!refl) (H.edge.f (spokeDartOriented H refl d0 i)) 5 := by
  dsimp [cartDartOriented]
  have h_ne0 : (deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((deg + i) - 1) / deg = 1 := by simpa using ringIdx_of_mul_add (k := 1) hi1 hi2
  have h_mod : ((deg + i) - 1) % deg + 1 = i := by simpa using spokeIdx_of_mul_add (k := 1) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

theorem cartDartOriented_fan1 (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 (2 * deg + i) =
      ruleVertexDart H (!refl) (H.edge.f (spokeDartOriented H refl d0 i)) 12 := by
  dsimp [cartDartOriented]
  have h_ne0 : (2 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((2 * deg + i) - 1) / deg = 2 := ringIdx_of_mul_add (k := 2) hi1 hi2
  have h_mod : ((2 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 2) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

theorem cartDartOriented_fan2 (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 (3 * deg + i) =
      ruleVertexDart H (!refl) (H.edge.f (spokeDartOriented H refl d0 i)) 13 := by
  dsimp [cartDartOriented]
  have h_ne0 : (3 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((3 * deg + i) - 1) / deg = 3 := ringIdx_of_mul_add (k := 3) hi1 hi2
  have h_mod : ((3 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 3) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

theorem cartDartOriented_fan3 (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 (4 * deg + i) =
      if refl then H.edge.f (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.edge.f (spokeDartOriented H refl d0 i)))))))
      else H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f (H.edge.f (spokeDartOriented H refl d0 i))))))) := by
  dsimp [cartDartOriented]
  have h_ne0 : (4 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((4 * deg + i) - 1) / deg = 4 := ringIdx_of_mul_add (k := 4) hi1 hi2
  have h_mod : ((4 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 4) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-!
### Stage N.1: Triangulation Face-Step & Hat-Reflection Identities
-/

/-- `H.face.f d = H.node.inv (H.edge.f d)`. -/
theorem face_f_eq_node_inv_edge_f (H : Hypermap) (d : H.Dart) :
    H.face.f d = H.node.inv (H.edge.f d) := by
  rw [Hypermap.face_eq_node_inv_edge_inv, Hypermap.edge_inv_eq_edge]

/-- On a complete dart list (`darts.length ≤ fuel`), `Hypermap.faceDegree H d fuel = 3`
    implies `H.face.f (H.face.f (H.face.f d)) = d`. -/
theorem face_f_three_of_faceDegree_eq_three (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {d : H.Dart}
    (h_tri : Hypermap.faceDegree H d fuel = 3) :
    H.face.f (H.face.f (H.face.f d)) = d := by
  have h_per := Hypermap.perm_iter_length_getOrbit_eq_self_of_complete H.face darts h_all h_le d
  change Hypermap.Perm.iter H.face (Hypermap.faceDegree H d fuel) d = d at h_per
  rw [h_tri] at h_per
  exact h_per

/-- Fundamental Triangulation Face-Step Identity:
    if `H.face.f^3 = id` at `H.edge.f (H.node.f s)`, then
    `H.edge.f (H.node.inv (H.edge.f s)) = H.node.f (H.edge.f (H.node.f s))`. -/
theorem edge_node_inv_edge_eq_node_f_edge_node_f (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x) (s : H.Dart) :
    H.edge.f (H.node.inv (H.edge.f s)) = H.node.f (H.edge.f (H.node.f s)) := by
  have h_fen := Hypermap.face_edge_node_id H s
  have h_ff : H.face.f (H.face.f s) = H.edge.f (H.node.f s) := by
    have h1 := congrArg (fun x => H.face.f (H.face.f x)) h_fen
    rw [h_tri3 (H.edge.f (H.node.f s))] at h1
    exact h1.symm
  rw [face_f_eq_node_inv_edge_f, face_f_eq_node_inv_edge_f] at h_ff
  have h2 := congrArg H.node.f h_ff
  rw [H.node.right_inv] at h2
  exact h2

/-- Triangulation Hat-Reflection Dart Identity:
    if `H.face.f^3 = id` everywhere on `H`, then for every spoke dart `s : H.Dart`,
    `ruleVertexDart H true (H.edge.f s) 5 = H.node.f (ruleVertexDart H false (H.edge.f (H.node.f s)) 5)`. -/
theorem hat_dart_true_eq_node_f_false (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x) (s : H.Dart) :
    ruleVertexDart H true (H.edge.f s) 5 =
      H.node.f (ruleVertexDart H false (H.edge.f (H.node.f s)) 5) := by
  dsimp [ruleVertexDart, ruleRot]
  let y := H.node.f (H.edge.f (H.node.f s))
  have h1 : H.node.inv (H.edge.f s) = H.edge.f y := by
    have h_step := edge_node_inv_edge_eq_node_f_edge_node_f H h_tri3 s
    have h_e := congrArg H.edge.f h_step
    rw [H.edge_involution] at h_e
    exact h_e
  rw [h1]
  exact edge_node_inv_edge_eq_node_f_edge_node_f H h_tri3 y

/-- Inverse form of the Triangulation Hat-Reflection Dart Identity:
    `H.node.inv (ruleVertexDart H true (H.edge.f s) 5) = ruleVertexDart H false (H.edge.f (H.node.f s)) 5`. -/
theorem node_inv_hat_dart_true_eq_false (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x) (s : H.Dart) :
    H.node.inv (ruleVertexDart H true (H.edge.f s) 5) =
      ruleVertexDart H false (H.edge.f (H.node.f s)) 5 := by
  rw [hat_dart_true_eq_node_f_false H h_tri3 s, H.node.left_inv]

/-- On a complete dart list (`darts.length ≤ fuel`), `H.node.f d` and `d` have the same `nodeDegree`. -/
theorem nodeDegree_node_f_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d : H.Dart) :
    Hypermap.nodeDegree H (H.node.f d) fuel = Hypermap.nodeDegree H d fuel := by
  have hd_mem : d ∈ getOrbit H.node fuel d :=
    List.contains_iff_mem.mp (Hypermap.getOrbit_contains_self H.node fuel d)
  have hfd_mem : H.node.f d ∈ getOrbit H.node fuel d :=
    Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le hd_mem
  exact nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hfd_mem

/-- Unified Triangulation Hat-Reflection Degree Identity:
    for any orientation `r0 : Bool` and spoke dart `s : H.Dart` on a complete triangulated hypermap,
    `nodeDegree` at `ruleVertexDart H (!r0) (H.edge.f s) 5` equals
    `nodeDegree` at `ruleVertexDart H r0 (H.edge.f (ruleRot H r0 s)) 5`. -/
theorem nodeDegree_hat_refl_eq_of_triangulation (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (r0 : Bool) (s : H.Dart) :
    Hypermap.nodeDegree H (ruleVertexDart H (!r0) (H.edge.f s) 5) fuel =
      Hypermap.nodeDegree H (ruleVertexDart H r0 (H.edge.f (ruleRot H r0 s)) 5) fuel := by
  cases r0 with
  | false =>
    change Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f s) 5) fuel =
      Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f (H.node.f s)) 5) fuel
    rw [hat_dart_true_eq_node_f_false H h_tri3 s]
    exact nodeDegree_node_f_eq_of_complete H darts h_all h_le _
  | true =>
    change Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f s) 5) fuel =
      Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f (H.node.inv s)) 5) fuel
    have h_eq := hat_dart_true_eq_node_f_false H h_tri3 (H.node.inv s)
    rw [H.node.right_inv] at h_eq
    rw [h_eq]
    exact (nodeDegree_node_f_eq_of_complete H darts h_all h_le _).symm

/-!
### Stage N.2: Pure `RealHypermapHubFamily` Dihedral Closure & Spoke-Sum Decomposition of `orbitNetShift`
-/

/-- Orientation-selected vertex permutation (`H.node` for `refl = false`, `H.node.symm` for `refl = true`). -/
def nodePermOriented (H : Hypermap) (refl : Bool) : Perm H.Dart :=
  if refl then H.node.symm else H.node

theorem spokeDartOriented_eq_iter (H : Hypermap) (refl : Bool) (d0 : H.Dart) (i : Nat) :
    spokeDartOriented H refl d0 i = Hypermap.Perm.iter (nodePermOriented H refl) (i - 1) d0 := by
  cases refl <;> rfl

theorem ruleRot_eq_nodePermOriented_f (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleRot H refl d = (nodePermOriented H refl).f d := by
  cases refl <;> rfl

theorem perm_iter_nodePermOriented_not (H : Hypermap) (refl : Bool) (m : Nat) (d : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H (!refl)) m d =
      Hypermap.Perm.iter (nodePermOriented H refl).symm m d := by
  cases refl <;> rfl

theorem perm_iter_symm_of_iter {D : Type} (q : Perm D) {m n : Nat} (hm : m ≤ n) (x : D) :
    Hypermap.Perm.iter q.symm m (Hypermap.Perm.iter q n x) =
      Hypermap.Perm.iter q (n - m) x := by
  have h_it := Hypermap.Perm.iter_add q m (n - m) x
  rw [Nat.add_sub_of_le hm] at h_it
  rw [h_it]
  exact Hypermap.Perm.iter_symm_left_inv q m (Hypermap.Perm.iter q (n - m) x)

theorem perm_iter_nodePermOriented_mem_getOrbit_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (n : Nat) :
    Hypermap.Perm.iter (nodePermOriented H refl) n d0 ∈ getOrbit H.node fuel u := by
  induction n with
  | zero => exact hd0
  | succ n ih =>
    rw [Hypermap.Perm.iter_succ]
    cases refl with
    | false =>
      exact Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le ih
    | true =>
      exact Hypermap.getOrbit_closed_under_inv_of_complete H.node darts h_all h_le ih

/-- If `d0 ∈ getOrbit H.node fuel u`, then every oriented spoke `spokeDartOriented H refl d0 i`
    also belongs to `getOrbit H.node fuel u`. -/
theorem spokeDartOriented_mem_getOrbit_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (i : Nat) :
    spokeDartOriented H refl d0 i ∈ getOrbit H.node fuel u := by
  rw [spokeDartOriented_eq_iter]
  exact perm_iter_nodePermOriented_mem_getOrbit_of_complete H darts h_all h_le hd0 refl (i - 1)

/-- Periodicity of `nodePermOriented H refl` on any dart `d0 ∈ getOrbit H.node fuel u`
    of degree `deg = Hypermap.nodeDegree H u fuel`. -/
theorem perm_iter_nodePermOriented_deg_eq_self (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) :
    Hypermap.Perm.iter (nodePermOriented H refl) (Hypermap.nodeDegree H u fuel) d0 = d0 := by
  have h_closes_u := Hypermap.orbitClosesWithin_mono H.node u u
    (Hypermap.orbitClosesWithin_of_complete H.node darts h_all u) h_le
  have h_len : (getOrbit H.node fuel d0).length = Hypermap.nodeDegree H u fuel :=
    Hypermap.getOrbit_length_eq_of_mem H.node fuel h_closes_u hd0
  rw [← h_len]
  cases refl with
  | false =>
    exact Hypermap.perm_iter_length_getOrbit_eq_self_of_complete H.node darts h_all h_le d0
  | true =>
    exact Hypermap.perm_iter_symm_length_getOrbit_eq_self_of_complete H.node darts h_all h_le d0

/-- Rotational shift of `spokeDartOriented`: shifting spoke index `i ∈ 1..deg` by `k < deg`
    around `d0` is identical to taking spoke `i` around `spokeDartOriented H refl d0 (k + 1)`. -/
theorem spokeDartOriented_shiftCartPos_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool)
    (k : Nat) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ Hypermap.nodeDegree H u fuel) :
    let deg := Hypermap.nodeDegree H u fuel
    spokeDartOriented H refl (spokeDartOriented H refl d0 (k + 1)) i =
      spokeDartOriented H refl d0 (shiftCartPos deg k i) := by
  intro deg0
  rw [spokeDartOriented_eq_iter, spokeDartOriented_eq_iter, spokeDartOriented_eq_iter]
  have hk_sub : k + 1 - 1 = k := by omega
  rw [hk_sub, ← Hypermap.Perm.iter_add]
  unfold shiftCartPos
  have h_mod : Nat.mod (Nat.sub i 1) deg0 = i - 1 := by
    change (i - 1) % deg0 = i - 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_mod]
  cases h_ble : Nat.ble deg0 (Nat.add k (i - 1)) with
  | false =>
    dsimp
    have h_eq : i + k - 1 = i - 1 + k := by omega
    rw [h_eq]
  | true =>
    dsimp
    have h_ge : deg0 ≤ k + (i - 1) := Nat.le_of_ble_eq_true h_ble
    have h_per : Hypermap.Perm.iter (nodePermOriented H refl) deg0 d0 = d0 :=
      perm_iter_nodePermOriented_deg_eq_self H darts h_all h_le hd0 refl
    have h_split : i - 1 + k = (i + k - deg0 - 1) + deg0 := by omega
    rw [h_split, Hypermap.Perm.iter_add, h_per]

/-- `shiftCartPos deg k (ringIdx * deg + i)` preserves the ring index `ringIdx` and shifts the spoke `i`. -/
theorem shiftCartPos_mul_add {deg k ringIdx i : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    shiftCartPos deg k (ringIdx * deg + i) = ringIdx * deg + shiftCartPos deg k i := by
  unfold shiftCartPos
  have h_mod1 : Nat.mod (Nat.sub (ringIdx * deg + i) 1) deg = i - 1 := by
    have h := spokeIdx_of_mul_add (deg := deg) (k := ringIdx) (i := i) hi1 hi2
    change (ringIdx * deg + i - 1) % deg = i - 1
    omega
  have h_mod2 : Nat.mod (Nat.sub i 1) deg = i - 1 := by
    change (i - 1) % deg = i - 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_mod1, h_mod2]
  cases h_ble : Nat.ble deg (Nat.add k (i - 1)) with
  | false =>
    dsimp
    change ringIdx * deg + i + k = ringIdx * deg + (i + k)
    omega
  | true =>
    dsimp
    have h_ge : deg ≤ k + (i - 1) := Nat.le_of_ble_eq_true h_ble
    change ringIdx * deg + i + k - deg = ringIdx * deg + (i + k - deg)
    omega

/-- Rotational shift of `cartDartOriented`: for any `1 ≤ p ≤ 5 * deg`, shifting `p` by `k < deg`
    around `d0` gives the exact same dart as `p` around `spokeDartOriented H refl d0 (k + 1)`. -/
theorem cartDartOriented_shiftCartPos_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool)
    {k p : Nat} (hk : k < Hypermap.nodeDegree H u fuel) (hp1 : 1 ≤ p) :
    let deg := Hypermap.nodeDegree H u fuel
    cartDartOriented H deg refl (spokeDartOriented H refl d0 (k + 1)) p =
      cartDartOriented H deg refl d0 (shiftCartPos deg k p) := by
  intro deg0
  have h_deg_pos : 1 ≤ deg0 := by omega
  let ringIdx := (p - 1) / deg0
  let i := (p - 1) % deg0 + 1
  have hi1 : 1 ≤ i := by omega
  have hi2 : i ≤ deg0 := by
    have := Nat.mod_lt (p - 1) (by omega : 0 < deg0)
    omega
  have hp_eq : p = ringIdx * deg0 + i := by
    have h_dm := Nat.div_add_mod (p - 1) deg0
    dsimp [ringIdx, i]
    rw [Nat.mul_comm]
    omega
  have h_sh_eq : shiftCartPos deg0 k p = ringIdx * deg0 + shiftCartPos deg0 k i := by
    conv => lhs; rw [hp_eq]
    exact shiftCartPos_mul_add hi1 hi2
  have h_sh_bnds := shiftCartPos_bounds h_deg_pos hk hi1 (by omega : i ≤ 2 * deg0)
  have h_sh_i_le : shiftCartPos deg0 k i ≤ deg0 := by
    unfold shiftCartPos
    have h_mod : Nat.mod (Nat.sub i 1) deg0 = i - 1 := by
      change (i - 1) % deg0 = i - 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_mod]
    cases h_ble : Nat.ble deg0 (Nat.add k (i - 1)) with
    | false =>
      dsimp
      have h_lt : k + (i - 1) < deg0 := by
        cases Classical.em (deg0 ≤ k + (i - 1)) with
        | inl h_ge =>
          have h_tr : Nat.ble deg0 (Nat.add k (i - 1)) = true := Nat.ble_eq_true_of_le h_ge
          rw [h_ble] at h_tr; contradiction
        | inr h_lt => omega
      change i + k ≤ deg0
      omega
    | true =>
      dsimp
      change i + k - deg0 ≤ deg0
      omega
  have h_sh_pos : 1 ≤ shiftCartPos deg0 k p := by
    rw [h_sh_eq]
    have := h_sh_bnds.1
    omega
  dsimp [cartDartOriented]
  have hp0 : (p == 0) = false := beq_false_of_ne (by omega)
  have hshp0 : (shiftCartPos deg0 k p == 0) = false := beq_false_of_ne (by omega)
  have h_div_sh : (shiftCartPos deg0 k p - 1) / deg0 = ringIdx := by
    rw [h_sh_eq]
    exact ringIdx_of_mul_add h_sh_bnds.1 h_sh_i_le
  have h_mod_sh : (shiftCartPos deg0 k p - 1) % deg0 + 1 = shiftCartPos deg0 k i := by
    rw [h_sh_eq]
    exact spokeIdx_of_mul_add h_sh_bnds.1 h_sh_i_le
  rw [hp0, hshp0, h_div_sh, h_mod_sh]
  dsimp
  have h_spk : spokeDartOriented H refl (spokeDartOriented H refl d0 (k + 1)) i =
      spokeDartOriented H refl d0 (shiftCartPos deg0 k i) :=
    spokeDartOriented_shiftCartPos_eq H darts h_all h_le hd0 refl k hi1 hi2
  rw [show (p - 1) % deg0 + 1 = i from rfl, h_spk]

/-- Reflectional invariance of `cartDegOriented` on `1 ≤ p ≤ 2 * deg` for any triangulated hypermap:
    reflecting `(r0, d1)` via `reflCartPos deg p` agrees with `(!r0, spokeDartOriented H r0 d1 deg)`. -/
theorem cartDegOriented_reflCartPos_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    {u d1 : H.Dart} (hd1 : d1 ∈ getOrbit H.node fuel u) (r0 : Bool)
    {p : Nat} (h_deg : 1 ≤ Hypermap.nodeDegree H u fuel)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * Hypermap.nodeDegree H u fuel) :
    let deg := Hypermap.nodeDegree H u fuel
    cartDegOriented H fuel deg (!r0) (spokeDartOriented H r0 d1 deg) p =
      cartDegOriented H fuel deg r0 d1 (reflCartPos deg p) := by
  intro deg0
  let d2 := spokeDartOriented H r0 d1 deg0
  have h_spk_d2 : ∀ i, 1 ≤ i → i ≤ deg0 →
      spokeDartOriented H (!r0) d2 i =
        Hypermap.Perm.iter (nodePermOriented H r0) (deg0 - i) d1 := by
    intro i hi1 hi2
    dsimp [d2]
    rw [spokeDartOriented_eq_iter, spokeDartOriented_eq_iter, perm_iter_nodePermOriented_not]
    have h_le_deg : i - 1 ≤ deg0 - 1 := by omega
    rw [perm_iter_symm_of_iter (nodePermOriented H r0) h_le_deg d1]
    have h_sub_eq : deg0 - 1 - (i - 1) = deg0 - i := by omega
    rw [h_sub_eq]
  by_cases hp_le : p ≤ deg0
  · -- Case 1: Spokes (`1 ≤ p ≤ deg0`)
    have h_refl_p : reflCartPos deg0 p = deg0 - p + 1 := by
      unfold reflCartPos
      have h_ble : Nat.ble p deg0 = true := Nat.ble_eq_true_of_le hp_le
      rw [h_ble]
      rfl
    rw [h_refl_p]
    dsimp [cartDegOriented]
    rw [cartDartOriented_spoke H deg0 (!r0) d2 hp1 hp_le,
        cartDartOriented_spoke H deg0 r0 d1 (by omega) (by omega),
        h_spk_d2 p hp1 hp_le, spokeDartOriented_eq_iter]
    have h_sub : deg0 - p + 1 - 1 = deg0 - p := by omega
    rw [h_sub]
  · -- Case 2: Hats (`deg0 + 1 ≤ p ≤ 2 * deg0`)
    let i := p - deg0
    have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ deg0 := by omega
    have hp_eq : p = deg0 + i := by omega
    by_cases hp_lt2 : p < 2 * deg0
    · -- Subcase 2a: Interior Hats (`1 ≤ i < deg0`)
      have hi_lt : i < deg0 := by omega
      have h_refl_p : reflCartPos deg0 p = deg0 + (deg0 - i) := by
        unfold reflCartPos
        have h_ble1 : Nat.ble p deg0 = false := by
          cases h : Nat.ble p deg0 with
          | false => rfl
          | true => have := Nat.le_of_ble_eq_true h; omega
        have h_ble2 : Nat.ble (Nat.mul 2 deg0) p = false := by
          cases h : Nat.ble (Nat.mul 2 deg0) p with
          | false => rfl
          | true =>
            have h_le2 : 2 * deg0 ≤ p := Nat.le_of_ble_eq_true h
            omega
        rw [h_ble1, h_ble2]
        dsimp
        change 3 * deg0 - p = deg0 + (deg0 - i)
        omega
      rw [h_refl_p, hp_eq]
      dsimp [cartDegOriented]
      rw [cartDartOriented_hat H deg0 (!r0) d2 hi1 hi2,
          cartDartOriented_hat H deg0 r0 d1 (by omega) (by omega),
          Bool.not_not, h_spk_d2 i hi1 hi2]
      have h_iter_step : Hypermap.Perm.iter (nodePermOriented H r0) (deg0 - i) d1 =
          ruleRot H r0 (spokeDartOriented H r0 d1 (deg0 - i)) := by
        rw [spokeDartOriented_eq_iter, ruleRot_eq_nodePermOriented_f, ← Hypermap.Perm.iter_succ]
        have h_s : deg0 - i - 1 + 1 = deg0 - i := by omega
        rw [h_s]
      rw [h_iter_step]
      exact (nodeDegree_hat_refl_eq_of_triangulation H darts h_all h_le h_tri3 r0 _).symm
    · -- Subcase 2b: Fixed Hat (`p = 2 * deg0`, `i = deg0`)
      have hp_2deg : p = 2 * deg0 := by omega
      have hi_deg : i = deg0 := by omega
      have h_refl_p : reflCartPos deg0 p = deg0 + deg0 := by
        unfold reflCartPos
        have h_ble1 : Nat.ble p deg0 = false := by
          cases h : Nat.ble p deg0 with
          | false => rfl
          | true => have := Nat.le_of_ble_eq_true h; omega
        have h_ble2 : Nat.ble (Nat.mul 2 deg0) p = true := by
          apply Nat.ble_eq_true_of_le
          change 2 * deg0 ≤ p
          omega
        rw [h_ble1, h_ble2]
        dsimp
        change 2 * deg0 = deg0 + deg0
        omega
      rw [h_refl_p, show p = deg0 + deg0 by omega]
      dsimp [cartDegOriented]
      rw [cartDartOriented_hat H deg0 (!r0) d2 h_deg (Nat.le_refl deg0),
          cartDartOriented_hat H deg0 r0 d1 h_deg (Nat.le_refl deg0),
          Bool.not_not, h_spk_d2 deg0 h_deg (Nat.le_refl deg0), Nat.sub_self]
      dsimp [Hypermap.Perm.iter]
      have h_per : Hypermap.Perm.iter (nodePermOriented H r0) deg0 d1 = d1 :=
        perm_iter_nodePermOriented_deg_eq_self H darts h_all h_le hd1 r0
      have h_d1_rot : d1 = ruleRot H r0 (spokeDartOriented H r0 d1 deg0) := by
        rw [spokeDartOriented_eq_iter, ruleRot_eq_nodePermOriented_f, ← Hypermap.Perm.iter_succ]
        have h_s : deg0 - 1 + 1 = deg0 := by omega
        rw [h_s, h_per]
      have h_lhs : Hypermap.nodeDegree H (ruleVertexDart H r0 (H.edge.f d1) 5) fuel =
          Hypermap.nodeDegree H (ruleVertexDart H r0 (H.edge.f (ruleRot H r0 (spokeDartOriented H r0 d1 deg0))) 5) fuel :=
        congrArg (fun x => Hypermap.nodeDegree H (ruleVertexDart H r0 (H.edge.f x) 5) fuel) h_d1_rot
      rw [h_lhs]
      exact (nodeDegree_hat_refl_eq_of_triangulation H darts h_all h_le h_tri3 r0 _).symm

/-- Pure Real-Hypermap Hub Family (`Zero` synthetic `.sym` constructors!):
    contains **only** genuine hypermap cartwheel degree functions `cartDegOriented H fuel deg refl d0`
    for `d0 ∈ getOrbit H.node fuel u` and `refl : Bool`. -/
def RealHypermapHubFamily (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (u : H.Dart)
    (cd : Nat → Nat) : Prop :=
  ∃ d0 ∈ getOrbit H.node fuel u, ∃ refl : Bool,
    cd = cartDegOriented H fuel deg refl d0

/-- On any complete triangulated hypermap (`∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3`),
    `RealHypermapHubFamily H fuel deg u` (`deg = Hypermap.nodeDegree H u fuel`) is unconditionally
    closed under the full dihedral group `DihedralClosedFamily deg`! -/
theorem dihedralClosedFamily_realHypermapHubFamily (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3) (u : H.Dart) :
    let deg := Hypermap.nodeDegree H u fuel
    DihedralClosedFamily deg (RealHypermapHubFamily H fuel deg u) := by
  intro deg0 cd k refl hk h_in
  rcases h_in with ⟨d0, hd0, r0, rfl⟩
  have h_deg_pos : 1 ≤ deg0 := by omega
  have h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x :=
    fun x => face_f_three_of_faceDegree_eq_three H darts h_all h_le (h_tri x (h_all x))
  let d1 := spokeDartOriented H r0 d0 (k + 1)
  have hd1 : d1 ∈ getOrbit H.node fuel u :=
    spokeDartOriented_mem_getOrbit_of_complete H darts h_all h_le hd0 r0 (k + 1)
  cases refl with
  | false =>
    refine ⟨cartDegOriented H fuel deg0 r0 d1, ⟨d1, hd1, r0, rfl⟩, ?_⟩
    intro p hp1 hp2
    dsimp [symCartDeg, symCartPos, cartDegOriented]
    have h_sh : cartDartOriented H deg0 r0 (spokeDartOriented H r0 d0 (k + 1)) p =
        cartDartOriented H deg0 r0 d0 (shiftCartPos deg0 k p) :=
      cartDartOriented_shiftCartPos_eq H darts h_all h_le hd0 r0 hk hp1
    rw [h_sh]
  | true =>
    let d_refl := spokeDartOriented H r0 d0 deg0
    have hd_refl : d_refl ∈ getOrbit H.node fuel u :=
      spokeDartOriented_mem_getOrbit_of_complete H darts h_all h_le hd0 r0 deg0
    let d2 := spokeDartOriented H (!r0) d_refl (k + 1)
    have hd2 : d2 ∈ getOrbit H.node fuel u :=
      spokeDartOriented_mem_getOrbit_of_complete H darts h_all h_le hd_refl (!r0) (k + 1)
    refine ⟨cartDegOriented H fuel deg0 (!r0) d2, ⟨d2, hd2, !r0, rfl⟩, ?_⟩
    intro p hp1 hp2
    dsimp [symCartDeg, symCartPos]
    have h_sh_bnds := shiftCartPos_bounds h_deg_pos hk hp1 hp2
    have h_sh : cartDartOriented H deg0 (!r0) (spokeDartOriented H (!r0) d_refl (k + 1)) p =
        cartDartOriented H deg0 (!r0) d_refl (shiftCartPos deg0 k p) :=
      cartDartOriented_shiftCartPos_eq H darts h_all h_le hd_refl (!r0) hk hp1
    have h_sh_deg : cartDegOriented H fuel deg0 (!r0) d2 p =
        cartDegOriented H fuel deg0 (!r0) d_refl (shiftCartPos deg0 k p) := by
      dsimp [cartDegOriented, d2]
      rw [h_sh]
    rw [h_sh_deg]
    exact cartDegOriented_reflCartPos_eq H darts h_all h_le h_tri3 hd0 r0 h_deg_pos h_sh_bnds.1 h_sh_bnds.2

/-- Real-Hypermap Core Soundness of `DischargingTreesVerified` (Degrees 7–11, `ProofTree.sym` eliminated):
    on any complete triangulated hypermap `H` (`∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3`),
    for any hub dart `u : H.Dart` whose vertex degree `deg = Hypermap.nodeDegree H u fuel` lies in `{7, 8, 9, 10, 11}`,
    `DischargingTreesVerified configs` guarantees that **some actual spoke dart `d0 ∈ getOrbit H.node fuel u`
    and orientation `refl : Bool`** satisfies the non-vacuous 2-way
    `CoreCartLeaf deg (getShiftedTableForDeg deg) (cartDegOriented H fuel deg refl d0)`. -/
theorem dischargingTreesVerified_hypermap_core_soundness (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    (configs : List Configuration) (h_trees : DischargingTreesVerified configs)
    (u : H.Dart)
    (h_deg : Hypermap.nodeDegree H u fuel = 7 ∨
             Hypermap.nodeDegree H u fuel = 8 ∨
             Hypermap.nodeDegree H u fuel = 9 ∨
             Hypermap.nodeDegree H u fuel = 10 ∨
             Hypermap.nodeDegree H u fuel = 11) :
    let deg := Hypermap.nodeDegree H u fuel
    ∃ d0 ∈ getOrbit H.node fuel u, ∃ refl : Bool,
      CoreCartLeaf deg (getShiftedTableForDeg deg) (cartDegOriented H fuel deg refl d0) := by
  let deg := Hypermap.nodeDegree H u fuel
  have h_u_mem : u ∈ getOrbit H.node fuel u :=
    List.contains_iff_mem.mp (Hypermap.getOrbit_contains_self H.node fuel u)
  rcases dischargingTreesVerified_core_soundness configs h_trees deg
    (RealHypermapHubFamily H fuel deg u)
    (dihedralClosedFamily_realHypermapHubFamily H darts h_all h_le h_tri u)
    ⟨u, h_u_mem, false, rfl⟩ h_deg with ⟨cd, ⟨d0, hd0, refl, rfl⟩, h_leaf⟩
  exact ⟨d0, hd0, refl, h_leaf⟩

/-- Primal–Dual Real-Hypermap Core Soundness on `H.dual` (Degrees 7–11, `ProofTree.sym` eliminated):
    on any complete cubic primal hypermap (`∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3`, so `H.dual` is a triangulation),
    for any dual vertex (primal face) `u : H.Dart` of degree `deg ∈ {7, 8, 9, 10, 11}` in `H.dual`,
    `DischargingTreesVerified configs` guarantees that **some actual dual spoke `d0 ∈ getOrbit H.dual.node fuel u`
    and orientation `refl : Bool`** satisfies `CoreCartLeaf deg (getShiftedTableForDeg deg) (cartDegOriented H.dual fuel deg refl d0)`. -/
theorem dual_dischargingTreesVerified_hypermap_core_soundness (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_cubic : ∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3)
    (configs : List Configuration) (h_trees : DischargingTreesVerified configs)
    (u : H.Dart)
    (h_deg : Hypermap.nodeDegree H.dual u fuel = 7 ∨
             Hypermap.nodeDegree H.dual u fuel = 8 ∨
             Hypermap.nodeDegree H.dual u fuel = 9 ∨
             Hypermap.nodeDegree H.dual u fuel = 10 ∨
             Hypermap.nodeDegree H.dual u fuel = 11) :
    let deg := Hypermap.nodeDegree H.dual u fuel
    ∃ d0 ∈ getOrbit H.dual.node fuel u, ∃ refl : Bool,
      CoreCartLeaf deg (getShiftedTableForDeg deg) (cartDegOriented H.dual fuel deg refl d0) := by
  have h_tri_dual : ∀ d ∈ darts, Hypermap.faceDegree H.dual d fuel = 3 := by
    intro d hd
    have h_closes := Hypermap.orbitClosesWithin_mono H.node d d
      (Hypermap.orbitClosesWithin_of_complete H.node darts h_all d) h_le
    dsimp [Hypermap.faceDegree, Hypermap.dual]
    rw [Hypermap.getOrbit_symm_length_eq H.node fuel d h_closes]
    exact h_cubic d hd
  exact dischargingTreesVerified_hypermap_core_soundness H.dual darts h_all h_le h_tri_dual configs h_trees u h_deg

/-- Mapping `fun i => Hypermap.Perm.iter p (i - 1) d0` over `List.range' a n` (`1 ≤ a`)
    equals `Hypermap.iterList p (Hypermap.Perm.iter p (a - 1) d0) n`. -/
theorem map_range'_perm_iter_eq_iterList {D : Type} (p : Perm D) (d0 : D) :
    ∀ (n a : Nat), 1 ≤ a →
      (List.range' a n).map (fun i => Hypermap.Perm.iter p (i - 1) d0) =
        Hypermap.iterList p (Hypermap.Perm.iter p (a - 1) d0) n
  | 0, _, _ => rfl
  | n + 1, a, ha => by
    dsimp [List.range', Hypermap.iterList]
    rw [List.map_cons, map_range'_perm_iter_eq_iterList p d0 n (a + 1) (by omega)]
    have h_step : Hypermap.Perm.iter p (a + 1 - 1) d0 = p.f (Hypermap.Perm.iter p (a - 1) d0) := by
      have h_eq : a + 1 - 1 = (a - 1) + 1 := by omega
      rw [h_eq, Hypermap.Perm.iter_succ]
    rw [h_step]

/-- Mapping `spokeDartOriented H refl d0` over `List.range' 1 deg` equals
    `Hypermap.iterList (nodePermOriented H refl) d0 deg`. -/
theorem map_range'_spokeDartOriented_eq_iterList (H : Hypermap) (refl : Bool) (d0 : H.Dart) (deg : Nat) :
    (List.range' 1 deg).map (spokeDartOriented H refl d0) =
      Hypermap.iterList (nodePermOriented H refl) d0 deg := by
  have h_fn : spokeDartOriented H refl d0 = fun i => Hypermap.Perm.iter (nodePermOriented H refl) (i - 1) d0 := by
    funext i
    exact spokeDartOriented_eq_iter H refl d0 i
  rw [h_fn]
  simpa using map_range'_perm_iter_eq_iterList (nodePermOriented H refl) d0 deg 1 (Nat.le_refl 1)

theorem foldl_add_reverse {α : Type} (l : List α) (f : α → Int) :
    l.reverse.foldl (fun acc x => acc + f x) 0 =
      l.foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
        foldl_add_cons, ih]
    omega

/-- Spoke-Sum Decomposition of `orbitNetShift`:
    for any dart `d0 ∈ getOrbit H.node fuel u` and orientation `refl : Bool` on a complete dart list,
    `orbitNetShift H fuel u` equals the sum of `netDartShift H fuel (spokeDartOriented H refl d0 i)`
    over `i ∈ List.range' 1 (Hypermap.nodeDegree H u fuel)`. -/
theorem orbitNetShift_eq_spokeDartOriented_foldl (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) :
    let deg := Hypermap.nodeDegree H u fuel
    orbitNetShift H fuel u =
      (List.range' 1 deg).foldl (fun acc i => acc + netDartShift H fuel (spokeDartOriented H refl d0 i)) 0 := by
  intro deg0
  dsimp [orbitNetShift]
  rw [← foldl_add_map (List.range' 1 deg0) (spokeDartOriented H refl d0) (netDartShift H fuel),
      map_range'_spokeDartOriented_eq_iterList]
  have h_closes_u := Hypermap.orbitClosesWithin_mono H.node u u
    (Hypermap.orbitClosesWithin_of_complete H.node darts h_all u) h_le
  have h_closes_d0 := Hypermap.orbitClosesWithin_mono H.node d0 d0
    (Hypermap.orbitClosesWithin_of_complete H.node darts h_all d0) h_le
  have h_len_d0 : (getOrbit H.node fuel d0).length = deg0 :=
    Hypermap.getOrbit_length_eq_of_mem H.node fuel h_closes_u hd0
  have h_len_oriented : (getOrbit (nodePermOriented H refl) fuel d0).length = deg0 := by
    cases refl with
    | false => exact h_len_d0
    | true =>
      dsimp [nodePermOriented]
      rw [Hypermap.getOrbit_symm_length_eq H.node fuel d0 h_closes_d0]
      exact h_len_d0
  have h_rev := Hypermap.getOrbit_eq_reverse_iterList_of_complete (nodePermOriented H refl) darts h_all h_le d0
  rw [h_len_oriented] at h_rev
  have h_iter_eq : Hypermap.iterList (nodePermOriented H refl) d0 deg0 =
      (getOrbit (nodePermOriented H refl) fuel d0).reverse := by
    rw [h_rev, List.reverse_reverse]
  rw [h_iter_eq, foldl_add_reverse]
  have h_nodup_u : (getOrbit H.node fuel u).Nodup := Hypermap.getOrbit_nodup H.node fuel u
  have h_nodup_or : (getOrbit (nodePermOriented H refl) fuel d0).Nodup :=
    Hypermap.getOrbit_nodup (nodePermOriented H refl) fuel d0
  apply nodup_foldl_add_eq_of_iff_mem (netDartShift H fuel) h_nodup_u h_nodup_or
  intro x
  have h_iff_d0 : x ∈ getOrbit H.node fuel u ↔ x ∈ getOrbit H.node fuel d0 :=
    (Hypermap.mem_getOrbit_iff_of_mem H.node fuel h_closes_u hd0 x).symm
  rw [h_iff_d0]
  cases refl with
  | false => exact Iff.rfl
  | true =>
    dsimp [nodePermOriented]
    exact (Hypermap.mem_getOrbit_symm_perm_iff H.node fuel d0 x h_closes_d0).symm

/-!
### Stage N.3: Declarative Rule-to-`FastPosOut` Compilation & SWAR Elimination (`compiledOutletsForSpoke`, `activeOutletSum_eq_compiledOutletsSum`)
-/

/-- Computable validity check for an RSST degree bound `bnd = (low, upp)`:
    after normalizing `upp = 9 ↦ 12` and `low = 0 ↦ upp`, `5 ≤ low ≤ 9` and (`upp ≤ 8` or `upp = 12`). -/
def validRSSTBound (bnd : Nat × Nat) : Bool :=
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  decide (5 ≤ low) && decide (low ≤ 9) && (decide (upp ≤ 8) || decide (upp == 12))

/-- 5-bit forbidden degree mask (`0..31`) associated with an RSST bound `bnd = (low, upp)`:
    bit `0..4` is set iff degree `5..9` fails `degMatchesBound`. -/
def forbidMaskOfBound (bnd : Nat × Nat) : Nat :=
  (if degMatchesBound 5 bnd then 0 else 1) |||
  (if degMatchesBound 6 bnd then 0 else 2) |||
  (if degMatchesBound 7 bnd then 0 else 4) |||
  (if degMatchesBound 8 bnd then 0 else 8) |||
  (if degMatchesBound 9 bnd then 0 else 16)

theorem testBit_forbidMaskOfBound_zero (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 0 = !degMatchesBound 5 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_one (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 1 = !degMatchesBound 6 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_two (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 2 = !degMatchesBound 7 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_three (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 3 = !degMatchesBound 8 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_four (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 4 = !degMatchesBound 9 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_of_ge_5 (bnd : Nat × Nat) {i : Nat} (hi : 5 ≤ i) :
    (forbidMaskOfBound bnd).testBit i = false := by
  have h31 : forbidMaskOfBound bnd &&& 31 = forbidMaskOfBound bnd := by
    dsimp [forbidMaskOfBound]
    cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
      cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
      cases degMatchesBound 9 bnd <;> decide
  have h31_tb : (31 : Nat).testBit i = false := by
    have h_eq : (31 : Nat) = 2 ^ 5 - 1 := rfl
    rw [h_eq, Nat.testBit_two_pow_sub_one]
    exact decide_eq_false (by omega)
  rw [← h31, Nat.testBit_and, h31_tb, Bool.and_false]

/-- For any valid RSST bound `bnd` and any degree `d ≥ 9`, `degMatchesBound d bnd = degMatchesBound 9 bnd`. -/
theorem degMatchesBound_eq_degMatchesBound_9_of_ge_9 {bnd : Nat × Nat} {d : Nat}
    (h_val : validRSSTBound bnd = true) (hd : 9 ≤ d) :
    degMatchesBound d bnd = degMatchesBound 9 bnd := by
  dsimp [validRSSTBound, degMatchesBound] at h_val ⊢
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  change (decide (5 ≤ low) && decide (low ≤ 9) && (decide (upp ≤ 8) || decide (upp == 12))) = true at h_val
  rcases Bool.and_eq_true_iff.mp h_val with ⟨h_low, h_upp⟩
  rcases Bool.and_eq_true_iff.mp h_low with ⟨_, h_low9⟩
  have h_le9 : low ≤ 9 := of_decide_eq_true h_low9
  have h_led : low ≤ d := by omega
  change (decide (low ≤ d) && (decide (upp == 12) || decide (d ≤ upp))) =
    (decide (low ≤ 9) && (decide (upp == 12) || decide (9 ≤ upp)))
  rw [decide_eq_true h_led, decide_eq_true h_le9]
  rcases Bool.or_eq_true_iff.mp h_upp with h_u8 | h_u12
  · have hu8 : upp ≤ 8 := of_decide_eq_true h_u8
    have hd_not : ¬ d ≤ upp := by omega
    have h9_not : ¬ 9 ≤ upp := by omega
    rw [decide_eq_false hd_not, decide_eq_false h9_not]
  · have hu12 : (upp == 12) = true := of_decide_eq_true h_u12
    rw [decide_eq_true hu12]
    rfl

/-- Exact equivalence between `!(forbidMaskOfBound bnd).testBit (degBitIdx d)` and `degMatchesBound d bnd`
    for all valid RSST bounds `bnd` and all vertex degrees `d ≥ 5`. -/
theorem not_testBit_forbidMaskOfBound_eq_degMatchesBound {bnd : Nat × Nat} {d : Nat}
    (h_val : validRSSTBound bnd = true) (hd : 5 ≤ d) :
    (!(forbidMaskOfBound bnd).testBit (degBitIdx d)) = degMatchesBound d bnd := by
  by_cases hd5 : d = 5
  · subst hd5
    change (!(forbidMaskOfBound bnd).testBit 0) = degMatchesBound 5 bnd
    rw [testBit_forbidMaskOfBound_zero, Bool.not_not]
  · by_cases hd6 : d = 6
    · subst hd6
      change (!(forbidMaskOfBound bnd).testBit 1) = degMatchesBound 6 bnd
      rw [testBit_forbidMaskOfBound_one, Bool.not_not]
    · by_cases hd7 : d = 7
      · subst hd7
        change (!(forbidMaskOfBound bnd).testBit 2) = degMatchesBound 7 bnd
        rw [testBit_forbidMaskOfBound_two, Bool.not_not]
      · by_cases hd8 : d = 8
        · subst hd8
          change (!(forbidMaskOfBound bnd).testBit 3) = degMatchesBound 8 bnd
          rw [testBit_forbidMaskOfBound_three, Bool.not_not]
        · have hd9 : 9 ≤ d := by omega
          have h_idx : degBitIdx d = 4 := by
            dsimp [degBitIdx]
            have hle5 : ¬ d ≤ 5 := by omega
            have h6 : (d == 6) = false := beq_false_of_ne hd6
            have h7 : (d == 7) = false := beq_false_of_ne hd7
            have h8 : (d == 8) = false := beq_false_of_ne hd8
            rw [if_neg hle5, h6, h7, h8]
            rfl
          rw [h_idx, testBit_forbidMaskOfBound_four, Bool.not_not,
              degMatchesBound_eq_degMatchesBound_9_of_ge_9 h_val hd9]

/-- Declarative 360-bit forbidden mask constructed from a list of `(pos, bnd)` conditions. -/
def forbidOfConds : List (Nat × (Nat × Nat)) → Nat
  | [] => 0
  | (p, bnd) :: rest =>
    Nat.lor (Nat.shiftLeft (forbidMaskOfBound bnd) (Nat.mul p 6)) (forbidOfConds rest)

theorem testBit_shiftLeft_forbidMaskOfBound (bnd : Nat × Nat) (q p : Nat) {i : Nat} (hi : i < 6) :
    (Nat.shiftLeft (forbidMaskOfBound bnd) (Nat.mul q 6)).testBit (p * 6 + i) =
      (if p == q then (forbidMaskOfBound bnd).testBit i else false) := by
  change ((forbidMaskOfBound bnd) <<< (q * 6)).testBit (p * 6 + i) =
    (if p == q then (forbidMaskOfBound bnd).testBit i else false)
  rw [Nat.testBit_shiftLeft]
  by_cases hpq : p = q
  · subst hpq
    have h_ge : decide (p * 6 ≤ p * 6 + i) = true := decide_eq_true (by omega)
    have h_sub : p * 6 + i - p * 6 = i := by omega
    rw [beq_self_eq_true, h_ge, h_sub]
    simp
  · have h_beq : (p == q) = false := beq_false_of_ne hpq
    rw [h_beq]
    by_cases h_ge : q * 6 ≤ p * 6 + i
    · have h_dec : decide (q * 6 ≤ p * 6 + i) = true := decide_eq_true h_ge
      have h_ge5 : 5 ≤ p * 6 + i - q * 6 := by omega
      rw [h_dec, testBit_forbidMaskOfBound_of_ge_5 bnd h_ge5]
      rfl
    · have h_dec : decide (q * 6 ≤ p * 6 + i) = false := decide_eq_false h_ge
      rw [h_dec]
      rfl

theorem list_all_and {α : Type} (l : List α) (f g : α → Bool) :
    l.all (fun x => f x && g x) = (l.all f && l.all g) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    dsimp [List.all]
    rw [ih]
    cases f a <;> cases g a <;> cases rest.all f <;> cases rest.all g <;> rfl

theorem list_all_beq_point {l : List Nat} {q : Nat} (hq : q ∈ l) (f : Nat → Bool) :
    l.all (fun p => if p == q then f p else true) = f q := by
  cases hfq : f q with
  | true =>
    apply List.all_eq_true.mpr
    intro p _
    cases hpq : (p == q) with
    | false => rfl
    | true =>
      have h_eq : p = q := eq_of_beq hpq
      subst h_eq
      exact hfq
  | false =>
    cases h_all : l.all (fun p => if p == q then f p else true) with
    | false => rfl
    | true =>
      have h_q := List.all_eq_true.mp h_all q hq
      rw [beq_self_eq_true, hfq] at h_q
      contradiction

/-- Exact characterization of `OutletActive deg cd po` when `po.forbid = forbidOfConds conds`:
    under `∀ p ∈ 1..5*deg, 5 ≤ cd p`, `OutletActive deg cd po` equals `conds.all (fun c => degMatchesBound (cd c.1) c.2)`. -/
theorem outletActive_of_forbid_eq_forbidOfConds (deg : Nat) (cd : Nat → Nat) (po : FastPosOut)
    (conds : List (Nat × (Nat × Nat)))
    (h_forbid : po.forbid = forbidOfConds conds)
    (h_conds : ∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 5 * deg ∧ validRSSTBound c.2 = true)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cd p) :
    OutletActive deg cd po = conds.all (fun c => degMatchesBound (cd c.1) c.2) := by
  have h_eq_all : OutletActive deg cd po =
      (List.range' 1 (5 * deg)).all (fun p => !(forbidOfConds conds).testBit (p * 6 + degBitIdx (cd p))) := by
    dsimp [OutletActive]
    rw [h_forbid]
    congr 1
    funext p
    rw [testBit_getLaneNat (forbidOfConds conds) p (degBitIdx_lt_6 (cd p))]
  rw [h_eq_all]
  clear h_eq_all h_forbid po
  induction conds with
  | nil =>
    dsimp [forbidOfConds, List.all]
    apply List.all_eq_true.mpr
    intro p _
    rw [Nat.zero_testBit]
    rfl
  | cons c rest ih =>
    rcases c with ⟨q, bnd⟩
    have hc_head := h_conds (q, bnd) List.mem_cons_self
    rcases hc_head with ⟨hq1, hq2, h_val_bnd⟩
    have h_rest_conds : ∀ c' ∈ rest, 1 ≤ c'.1 ∧ c'.1 ≤ 5 * deg ∧ validRSSTBound c'.2 = true :=
      fun c' hc' => h_conds c' (List.mem_cons_of_mem (q, bnd) hc')
    have h_step_fn : (fun p => !(forbidOfConds ((q, bnd) :: rest)).testBit (p * 6 + degBitIdx (cd p))) =
        (fun p => (if p == q then !(forbidMaskOfBound bnd).testBit (degBitIdx (cd p)) else true) &&
          !(forbidOfConds rest).testBit (p * 6 + degBitIdx (cd p))) := by
      funext p
      have h_or : (forbidOfConds ((q, bnd) :: rest)).testBit (p * 6 + degBitIdx (cd p)) =
          ((Nat.shiftLeft (forbidMaskOfBound bnd) (Nat.mul q 6)).testBit (p * 6 + degBitIdx (cd p)) ||
            (forbidOfConds rest).testBit (p * 6 + degBitIdx (cd p))) := by
        dsimp [forbidOfConds]
        exact Nat.testBit_or _ _ _
      rw [h_or, Bool.not_or, testBit_shiftLeft_forbidMaskOfBound bnd q p (degBitIdx_lt_6 (cd p))]
      cases (p == q) <;> rfl
    rw [h_step_fn, list_all_and, ih h_rest_conds]
    have hq_mem : q ∈ List.range' 1 (5 * deg) :=
      List.mem_range'.mpr ⟨q - 1, by omega, by omega⟩
    rw [list_all_beq_point hq_mem]
    have h_m := not_testBit_forbidMaskOfBound_eq_degMatchesBound h_val_bnd (h_min5 q hq1 hq2)
    dsimp [List.all]
    rw [h_m]

/-- Computable counterpart to `lookupListRec`. -/
def lookupListPure {a : Type} (d : a) : List a → Nat → a
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, n + 1 => lookupListPure d xs n

theorem lookupListRec_eq_pure {a : Type} (d : a) (l : List a) (idx : Nat) :
    lookupListRec d l idx = lookupListPure d l idx := by
  induction l generalizing idx with
  | nil => rfl
  | cons x xs ih =>
    cases idx with
    | zero => rfl
    | succ n => exact ih n

/-- Pure pattern-matching lookup for `U[z]` (`z ∈ 0..16`) from `Rules.lean`. -/
def ruleU : Nat → Nat
  | 3 | 7 => 1
  | 5 | 9 | 11 => 3
  | 6 => 2
  | 8 => 4
  | 10 => 8
  | 14 => 5
  | 15 => 6
  | 16 => 15
  | _ => 0

/-- Pure pattern-matching lookup for `V[z]` (`z ∈ 0..16`) from `Rules.lean`. -/
def ruleV : Nat → Nat
  | 2 | 6 | 15 | 16 => 1
  | 4 | 8 | 10 => 2
  | 7 => 3
  | 9 => 5
  | 11 => 9
  | 12 => 4
  | 13 => 12
  | _ => 0

/-- Pure triangle third-vertex lookup (`63` if `(u, v)` is not a directed edge of `(x, y, z)`). -/
def pureTriAdj (x y z u v : Nat) : Nat :=
  if u == x && v == y then z
  else if u == y && v == z then x
  else if u == z && v == x then y
  else 63

/-- Pure spoke-sector triangle lookup around spoke `i ∈ 1..deg` with fan degree `k` (`0` or `5..8`). -/
def pureSpokeAdj (deg i k u v : Nat) : Nat :=
  let h := if i == 1 then deg else i - 1
  let a := deg + h
  let b := deg + i
  let c := 2 * deg + i
  let d := 3 * deg + i
  let e := 4 * deg + i
  let r1 := pureTriAdj 0 h i u v
  if r1 != 63 then r1
  else
    let r2 := pureTriAdj i h a u v
    if r2 != 63 then r2
    else if k == 5 then pureTriAdj i a b u v
    else if k == 6 then
      let r3 := pureTriAdj i a c u v
      if r3 != 63 then r3 else pureTriAdj i c b u v
    else if k == 7 then
      let r3 := pureTriAdj i a c u v
      if r3 != 63 then r3
      else
        let r4 := pureTriAdj i c d u v
        if r4 != 63 then r4 else pureTriAdj i d b u v
    else if k == 8 then
      let r3 := pureTriAdj i a c u v
      if r3 != 63 then r3
      else
        let r4 := pureTriAdj i c d u v
        if r4 != 63 then r4
        else
          let r5 := pureTriAdj i d e u v
          if r5 != 63 then r5 else pureTriAdj i e b u v
    else 63

/-- Look up the exact degree (`0` if not fixed) of spoke `i` in `fanDeg`. -/
def lookupFanDeg (i : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (p, d) :: rest => if p == i then d else lookupFanDeg i rest

/-- Pure cartwheel adjacency lookup across all spokes `i ∈ 1..deg`. -/
def pureCartAdj (deg : Nat) (fanDeg : List (Nat × Nat)) (u v : Nat) : Nat :=
  (List.range' 1 deg).foldl (fun acc i =>
    if acc != 63 then acc
    else pureSpokeAdj deg i (lookupFanDeg i fanDeg) u v) 63

/-- Look up the cartwheel position of rule vertex `z` in `phi`. -/
def lookupPhi (z : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (k, v) :: rest => if k == z then v else lookupPhi z rest

/-- Normalize an RSST bound `(low1, upp1)` by mapping `upp1 = 9 ↦ 12` and `low1 = 0 ↦ upp1`. -/
def normRSSTBound (bnd : Nat × Nat) : Nat × Nat :=
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  (low, upp)

/-- Pure compilation of `r.triples` into shifted cartwheel `(pos, (low, upp))` conditions at spoke `x`. -/
def compileRuleTriples (deg x : Nat) (inv : Bool) :
    List (Nat × (Nat × Nat)) → List (Nat × Nat) → List (Nat × Nat) → List (Nat × (Nat × Nat))
  | [], _, _ => []
  | (z, bnd) :: rest, phi, fanDeg =>
    let nb := normRSSTBound bnd
    let u := lookupPhi (if inv then ruleV z else ruleU z) phi
    let v := lookupPhi (if inv then ruleU z else ruleV z) phi
    let pos_i := pureCartAdj deg fanDeg u v
    let phi' := (z, pos_i) :: phi
    let fanDeg' := if pos_i ≤ deg && nb.1 == nb.2 then (pos_i, nb.1) :: fanDeg else fanDeg
    (shiftCartPos deg (x - 1) pos_i, nb) :: compileRuleTriples deg x inv rest phi' fanDeg'

/-- Pure compilation of a single oriented RSST `RawRule` (`isPos`: inflow `+1` vs outflow `-1`;
    `inv`: unreflected `false` vs reflected `true`) at hub degree `deg` and spoke `x`. -/
def compileRuleOutlet (deg x : Nat) (isPos inv : Bool) (r : RawRule) :
    Option (Bool × List (Nat × (Nat × Nat))) :=
  let bHub := normRSSTBound (if isPos then r.b1 else r.b0)
  let bSpk := normRSSTBound (if isPos then r.b0 else r.b1)
  if decide (bHub.1 ≤ deg) && decide (deg ≤ bHub.2) then
    let phi0 := if isPos then [(0, 1), (1, 0)] else [(0, 0), (1, 1)]
    let fan0 := if bSpk.1 == bSpk.2 then [(1, bSpk.1)] else []
    let headCond := (shiftCartPos deg (x - 1) 1, bSpk)
    some (isPos, headCond :: compileRuleTriples deg x inv r.triples phi0 fan0)
  else
    none

/-- Pure compilation of all outlets generated by a single `r : RawRule` at hub degree `deg` and spoke `x`. -/
def compileRuleAllOutlets (deg x : Nat) (r : RawRule) : List (Bool × List (Nat × (Nat × Nat))) :=
  (match compileRuleOutlet deg x true false r with | some o => [o] | none => []) ++
  (match compileRuleOutlet deg x false false r with | some o => [o] | none => []) ++
  (if r.invert then
    (match compileRuleOutlet deg x true true r with | some o => [o] | none => []) ++
    (match compileRuleOutlet deg x false true r with | some o => [o] | none => [])
   else [])

/-- Declarative list of `(isPos, conds)` pairs compiled directly from `theRules` at spoke `x`. -/
def compiledOutletsForSpoke (deg x : Nat) : List (Bool × List (Nat × (Nat × Nat))) :=
  theRules.foldr (fun r acc => compileRuleAllOutlets deg x r ++ acc) []

/-- Declarative activation predicate for a compiled outlet `co = (isPos, conds)` on `cd`. -/
def compiledOutletActive (cd : Nat → Nat) (co : Bool × List (Nat × (Nat × Nat))) : Bool :=
  co.2.all (fun c => degMatchesBound (cd c.1) c.2)

/-- Declarative sum of signed outlet values (`+1` or `-1`) over a list of compiled outlets. -/
def compiledOutletsSum (cd : Nat → Nat) : List (Bool × List (Nat × (Nat × Nat))) → Int
  | [] => 0
  | co :: rest =>
    (if compiledOutletActive cd co then (if co.1 then 1 else -1) else 0) +
      compiledOutletsSum cd rest

/-- Computable validity check for a condition list `conds` at hub degree `deg`. -/
def validCondList (deg : Nat) (conds : List (Nat × (Nat × Nat))) : Bool :=
  conds.all (fun c => decide (1 ≤ c.1) && decide (c.1 ≤ 5 * deg) && validRSSTBound c.2)

/-- Computable structural equivalence check between a SWAR `List FastPosOut` and a declarative
    `List (Bool × List (Nat × (Nat × Nat)))` at hub degree `deg`. -/
def matchesCompiledOutlets (deg : Nat) : List FastPosOut → List (Bool × List (Nat × (Nat × Nat))) → Bool
  | [], [] => true
  | po :: pos, co :: cos =>
    (po.isPos == co.1) &&
    (po.forbid == forbidOfConds co.2) &&
    validCondList deg co.2 &&
    matchesCompiledOutlets deg pos cos
  | _, _ => false

/-- Computable verification that every spoke `x ∈ 1..deg` in `getShiftedTableForDeg deg`
    matches `compiledOutletsForSpoke deg x`. -/
def validCompiledShiftedTable (deg : Nat) : Bool :=
  (List.range' 1 deg).all (fun x =>
    matchesCompiledOutlets deg
      (lookupListPure [] (getShiftedTableForDeg deg) x)
      (compiledOutletsForSpoke deg x))

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_7 : validCompiledShiftedTable 7 = true := by decide

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_8 : validCompiledShiftedTable 8 = true := by decide

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_9 : validCompiledShiftedTable 9 = true := by decide

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_10 : validCompiledShiftedTable 10 = true := by decide

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_11 : validCompiledShiftedTable 11 = true := by decide

theorem validCompiledShiftedTable_getShiftedTableForDeg (deg : Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    validCompiledShiftedTable deg = true := by
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · exact validCompiledShiftedTable_7
  · exact validCompiledShiftedTable_8
  · exact validCompiledShiftedTable_9
  · exact validCompiledShiftedTable_10
  · exact validCompiledShiftedTable_11

theorem validCondList_sound (deg : Nat) (conds : List (Nat × (Nat × Nat)))
    (h_val : validCondList deg conds = true) :
    ∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 5 * deg ∧ validRSSTBound c.2 = true := by
  intro c hc
  have h_c := List.all_eq_true.mp h_val c hc
  rcases Bool.and_eq_true_iff.mp h_c with ⟨h12, h3⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨h1, h2⟩
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, h3⟩

/-- Inductive soundness of `matchesCompiledOutlets`: when `matchesCompiledOutlets deg pos cos = true`
    and `∀ p ∈ 1..5*deg, 5 ≤ cd p`, `activeOutletSum deg cd pos = compiledOutletsSum cd cos`. -/
theorem activeOutletSum_eq_of_matchesCompiledOutlets (deg : Nat) (cd : Nat → Nat)
    (pos : List FastPosOut) (cos : List (Bool × List (Nat × (Nat × Nat))))
    (h_match : matchesCompiledOutlets deg pos cos = true)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cd p) :
    activeOutletSum deg cd pos = compiledOutletsSum cd cos := by
  induction pos generalizing cos with
  | nil =>
    cases cos with
    | nil => rfl
    | cons _ _ => contradiction
  | cons po pos ih =>
    cases cos with
    | nil => contradiction
    | cons co cos =>
      dsimp [matchesCompiledOutlets] at h_match
      rcases Bool.and_eq_true_iff.mp h_match with ⟨h123, h_rest⟩
      rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, h_val_conds⟩
      rcases Bool.and_eq_true_iff.mp h12 with ⟨h_pos_eq, h_forbid_eq⟩
      have h_isPos : po.isPos = co.1 := eq_of_beq h_pos_eq
      have h_forbid : po.forbid = forbidOfConds co.2 := eq_of_beq h_forbid_eq
      have h_act : OutletActive deg cd po = compiledOutletActive cd co :=
        outletActive_of_forbid_eq_forbidOfConds deg cd po co.2 h_forbid
          (validCondList_sound deg co.2 h_val_conds) h_min5
      dsimp [activeOutletSum, compiledOutletsSum, outletVal]
      rw [h_act, h_isPos, ih cos h_rest]

/-- Exact SWAR-to-Declarative Equivalence for `activeOutletSum` (Degrees 7–11):
    for any hub degree `deg ∈ {7, 8, 9, 10, 11}`, any spoke index `1 ≤ x ≤ deg`,
    and any cartwheel degree assignment `cd` with `∀ p ∈ 1..5*deg, 5 ≤ cd p`,
    the SWAR sum `activeOutletSum deg cd (lookupListRec [] (getShiftedTableForDeg deg) x)`
    equals the declarative rule-bound sum `compiledOutletsSum cd (compiledOutletsForSpoke deg x)`. -/
theorem activeOutletSum_eq_compiledOutletsSum (deg x : Nat) (cd : Nat → Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11)
    (hx1 : 1 ≤ x) (hx2 : x ≤ deg)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cd p) :
    activeOutletSum deg cd (lookupListRec [] (getShiftedTableForDeg deg) x) =
      compiledOutletsSum cd (compiledOutletsForSpoke deg x) := by
  have h_tab := validCompiledShiftedTable_getShiftedTableForDeg deg h_deg
  have hx_mem : x ∈ List.range' 1 deg := List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
  have h_match := List.all_eq_true.mp h_tab x hx_mem
  rw [lookupListRec_eq_pure]
  exact activeOutletSum_eq_of_matchesCompiledOutlets deg cd
    (lookupListPure [] (getShiftedTableForDeg deg) x)
    (compiledOutletsForSpoke deg x) h_match h_min5

-- ============================================================================
-- Stage O.1: Spoke-Shift Reduction & Oriented Rule Outflow Decomposition
-- ============================================================================

/-- Shift every cartwheel coordinate in a list of compiled outlets by `k` spokes. -/
def shiftCompiledOutlets (deg k : Nat) (cos : List (Bool × List (Nat × (Nat × Nat)))) :
    List (Bool × List (Nat × (Nat × Nat))) :=
  cos.map (fun co => (co.1, co.2.map (fun c => (shiftCartPos deg k c.1, c.2))))

/-- Computable check that for every spoke `x ∈ 1..deg`, `compiledOutletsForSpoke deg x`
    equals `shiftCompiledOutlets deg (x - 1) (compiledOutletsForSpoke deg 1)` and all
    spoke-1 conditions lie in `1..5*deg`. -/
def validSpokeShiftTable (deg : Nat) : Bool :=
  (compiledOutletsForSpoke deg 1).all (fun co => validCondList deg co.2) &&
  (List.range' 1 deg).all (fun x =>
    compiledOutletsForSpoke deg x == shiftCompiledOutlets deg (x - 1) (compiledOutletsForSpoke deg 1))

set_option maxRecDepth 200000 in
theorem validSpokeShiftTable_7 : validSpokeShiftTable 7 = true := by decide

set_option maxRecDepth 200000 in
theorem validSpokeShiftTable_8 : validSpokeShiftTable 8 = true := by decide

set_option maxRecDepth 200000 in
theorem validSpokeShiftTable_9 : validSpokeShiftTable 9 = true := by decide

set_option maxRecDepth 200000 in
theorem validSpokeShiftTable_10 : validSpokeShiftTable 10 = true := by decide

set_option maxRecDepth 200000 in
theorem validSpokeShiftTable_11 : validSpokeShiftTable 11 = true := by decide

theorem validSpokeShiftTable_of_deg (deg : Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    validSpokeShiftTable deg = true := by
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · exact validSpokeShiftTable_7
  · exact validSpokeShiftTable_8
  · exact validSpokeShiftTable_9
  · exact validSpokeShiftTable_10
  · exact validSpokeShiftTable_11

theorem compiledOutletActive_shiftCartPos_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (x : Nat)
    (co : Bool × List (Nat × (Nat × Nat)))
    (hx1 : 1 ≤ x) (hx2 : x ≤ Hypermap.nodeDegree H u fuel)
    (h_conds : ∀ c ∈ co.2, 1 ≤ c.1 ∧ c.1 ≤ 5 * Hypermap.nodeDegree H u fuel ∧ validRSSTBound c.2 = true) :
    let deg := Hypermap.nodeDegree H u fuel
    compiledOutletActive (cartDegOriented H fuel deg refl d0)
      (co.1, co.2.map (fun c => (shiftCartPos deg (x - 1) c.1, c.2))) =
    compiledOutletActive (cartDegOriented H fuel deg refl (spokeDartOriented H refl d0 x)) co := by
  intro deg
  rcases co with ⟨isPos, conds⟩
  dsimp [compiledOutletActive]
  induction conds with
  | nil => rfl
  | cons c rest ih =>
    have hc := h_conds c List.mem_cons_self
    have h_rest : ∀ c' ∈ rest, 1 ≤ c'.1 ∧ c'.1 ≤ 5 * deg ∧ validRSSTBound c'.2 = true :=
      fun c' hc' => h_conds c' (List.mem_cons_of_mem c hc')
    dsimp [List.map, List.all]
    have hk_lt : x - 1 < Hypermap.nodeDegree H u fuel := by omega
    have h_shift : cartDegOriented H fuel deg refl d0 (shiftCartPos deg (x - 1) c.1) =
        cartDegOriented H fuel deg refl (spokeDartOriented H refl d0 x) c.1 := by
      dsimp [cartDegOriented]
      have h_cd := cartDartOriented_shiftCartPos_eq H darts h_all h_le hd0 refl hk_lt hc.1
      dsimp at h_cd
      have hx_eq : x - 1 + 1 = x := by omega
      rw [hx_eq] at h_cd
      rw [h_cd]
    rw [h_shift, ih h_rest]

theorem compiledOutletsSum_shiftCompiledOutlets_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (x : Nat)
    (cos : List (Bool × List (Nat × (Nat × Nat))))
    (hx1 : 1 ≤ x) (hx2 : x ≤ Hypermap.nodeDegree H u fuel)
    (h_all_conds : cos.all (fun co => validCondList (Hypermap.nodeDegree H u fuel) co.2) = true) :
    let deg := Hypermap.nodeDegree H u fuel
    compiledOutletsSum (cartDegOriented H fuel deg refl d0) (shiftCompiledOutlets deg (x - 1) cos) =
    compiledOutletsSum (cartDegOriented H fuel deg refl (spokeDartOriented H refl d0 x)) cos := by
  intro deg
  induction cos with
  | nil => rfl
  | cons co rest ih =>
    dsimp [List.all] at h_all_conds
    rcases Bool.and_eq_true_iff.mp h_all_conds with ⟨h_co, h_rest⟩
    have h_act := compiledOutletActive_shiftCartPos_eq H darts h_all h_le hd0 refl x co hx1 hx2
      (validCondList_sound deg co.2 h_co)
    dsimp at h_act
    change (if compiledOutletActive (cartDegOriented H fuel deg refl d0)
              (co.1, co.2.map (fun c => (shiftCartPos deg (x - 1) c.1, c.2))) then
              (if co.1 then 1 else -1) else 0) +
            compiledOutletsSum (cartDegOriented H fuel deg refl d0) (shiftCompiledOutlets deg (x - 1) rest) =
          (if compiledOutletActive (cartDegOriented H fuel deg refl (spokeDartOriented H refl d0 x)) co then
              (if co.1 then 1 else -1) else 0) +
            compiledOutletsSum (cartDegOriented H fuel deg refl (spokeDartOriented H refl d0 x)) rest
    rw [h_act, ih h_rest]

/-- Spoke-Shift Reduction Theorem (Degrees 7–11):
    evaluating `compiledOutletsSum` for `compiledOutletsForSpoke deg x` (`1 ≤ x ≤ deg`)
    around `(d0, refl)` equals evaluating `compiledOutletsForSpoke deg 1` around
    `(spokeDartOriented H refl d0 x, refl)`. -/
theorem compiledOutletsSum_spoke_eq_spoke1 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (x : Nat)
    (h_deg : Hypermap.nodeDegree H u fuel = 7 ∨ Hypermap.nodeDegree H u fuel = 8 ∨
             Hypermap.nodeDegree H u fuel = 9 ∨ Hypermap.nodeDegree H u fuel = 10 ∨
             Hypermap.nodeDegree H u fuel = 11)
    (hx1 : 1 ≤ x) (hx2 : x ≤ Hypermap.nodeDegree H u fuel) :
    let deg := Hypermap.nodeDegree H u fuel
    compiledOutletsSum (cartDegOriented H fuel deg refl d0) (compiledOutletsForSpoke deg x) =
    compiledOutletsSum (cartDegOriented H fuel deg refl (spokeDartOriented H refl d0 x))
      (compiledOutletsForSpoke deg 1) := by
  intro deg
  have h_tab := validSpokeShiftTable_of_deg deg h_deg
  dsimp [validSpokeShiftTable] at h_tab
  rcases Bool.and_eq_true_iff.mp h_tab with ⟨h_conds, h_shifts⟩
  have hx_mem : x ∈ List.range' 1 deg := List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
  have h_shift_x : compiledOutletsForSpoke deg x =
      shiftCompiledOutlets deg (x - 1) (compiledOutletsForSpoke deg 1) :=
    eq_of_beq (List.all_eq_true.mp h_shifts x hx_mem)
  rw [h_shift_x]
  exact compiledOutletsSum_shiftCompiledOutlets_eq H darts h_all h_le hd0 refl x
    (compiledOutletsForSpoke deg 1) hx1 hx2 h_conds

private theorem bool_and_4_swap (a b c d : Bool) :
    (b && (a && (d && (c && true)))) = (a && (b && (c && (d && true)))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private theorem bool_and_6_swap (a b c d e f : Bool) :
    (b && (a && (d && (c && (f && (e && true)))))) =
      (a && (b && (c && (d && (e && (f && true)))))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> rfl

private theorem bool_and_8_swap (a b c d e f g h : Bool) :
    (b && (a && (d && (c && (f && (e && (h && (g && true)))))))) =
      (a && (b && (c && (d && (e && (f && (g && (h && true)))))))) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;> rfl

/-- Helper predicate: every rule in `l` with `invert = false` is orientation-symmetric. -/
def allInvertFalseSymm (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart) :
    List RawRule → Prop
  | [] => True
  | r :: rs =>
    (r.invert = false → matchesRawRule H fuel true d r = matchesRawRule H fuel false d r) ∧
      allInvertFalseSymm H fuel d rs

theorem mem_allInvertFalseSymm (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart)
    {l : List RawRule} {r : RawRule} (h_all : allInvertFalseSymm H fuel d l) (hr : r ∈ l)
    (h_inv : r.invert = false) :
    matchesRawRule H fuel true d r = matchesRawRule H fuel false d r := by
  induction l with
  | nil => contradiction
  | cons a rs ih =>
    rcases h_all with ⟨ha, hrs⟩
    rcases List.mem_cons.mp hr with rfl | h_mem
    · exact ha h_inv
    · exact ih hrs h_mem

/-- Every rule `r ∈ theRules` with `r.invert = false` (`r21`, `r26`, `r63`) has mirror-symmetric
    degree bounds, so `matchesRawRule H fuel true d r = matchesRawRule H fuel false d r`. -/
theorem matchesRawRule_true_eq_false_of_invert_false (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (r : RawRule)
    (hr : r ∈ theRules) (h_inv : r.invert = false) :
    matchesRawRule H fuel true d r = matchesRawRule H fuel false d r := by
  have h_all : allInvertFalseSymm H fuel d theRules := by
    dsimp [theRules, allInvertFalseSymm]
    refine ⟨by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            by intro h; contradiction, ?_, by intro h; contradiction, by intro h; contradiction,
            ?_, by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            by intro h; contradiction, by intro h; contradiction, by intro h; contradiction,
            ?_, by intro h; contradiction, by intro h; contradiction, trivial⟩
    · -- r21
      intro _
      dsimp [matchesRawRule, List.all, ruleVertexDart, ruleRot, ruleRotInv]
      congr 1
      exact bool_and_4_swap _ _ _ _
    · -- r26
      intro _
      dsimp [matchesRawRule, List.all, ruleVertexDart, ruleRot, ruleRotInv]
      congr 1
      exact bool_and_6_swap _ _ _ _ _ _
    · -- r63
      intro _
      dsimp [matchesRawRule, List.all, ruleVertexDart, ruleRot, ruleRotInv]
      congr 1
      exact bool_and_8_swap _ _ _ _ _ _ _ _
  exact mem_allInvertFalseSymm H fuel d h_all hr h_inv

/-- Orientation-invariant decomposition of `rawRuleOutflow` for any `r ∈ theRules` and `refl : Bool`. -/
theorem rawRuleOutflow_eq_oriented (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (refl : Bool) (d : H.Dart) (r : RawRule) (hr : r ∈ theRules) :
    rawRuleOutflow H fuel d r =
      (if matchesRawRule H fuel (!refl) d r then 1 else 0) +
      (if r.invert && matchesRawRule H fuel refl d r then 1 else 0) := by
  dsimp [rawRuleOutflow]
  cases refl with
  | true => rfl
  | false =>
    change (if matchesRawRule H fuel false d r = true then (1 : Int) else 0) +
        (if (r.invert && matchesRawRule H fuel true d r) = true then 1 else 0) =
      (if matchesRawRule H fuel true d r = true then 1 else 0) +
        (if (r.invert && matchesRawRule H fuel false d r) = true then 1 else 0)
    cases h_inv : r.invert with
    | true =>
      simp only [Bool.true_and]
      exact Int.add_comm _ _
    | false =>
      simp only [Bool.false_and]
      rw [matchesRawRule_true_eq_false_of_invert_false H fuel d r hr h_inv]

-- ============================================================================
-- Stage O.2: Spoke-1 Coordinate Identities & `compiledOutletsSum_spoke1_eq_netDartShift`
-- ============================================================================

/-- Check whether cartwheel position `p` at hub degree `deg` (spoke `1`) matches rule coordinate `z`
    under `(isPos, inv)` and previously established exact spoke degrees `fanDeg`. -/
def validCoordMatch (deg : Nat) (isPos inv : Bool) (fanDeg : List (Nat × Nat)) (z p : Nat) : Bool :=
  if !isPos then
    if z == 2 then (if inv then p == deg else p == 2)
    else if z == 3 then (if inv then p == 2 else p == deg)
    else if z == 4 then (if inv then p == deg - 1 else p == 3)
    else if z == 5 then (if inv then p == 3 else p == deg - 1)
    else if z == 6 then (if inv then p == 2 * deg else p == deg + 1)
    else if z == 7 then (if inv then p == deg + 1 else p == 2 * deg)
    else if z == 8 then (if inv then p == 2 * deg - 1 else p == deg + 2)
    else if z == 9 then (if inv then p == deg + 2 else p == 2 * deg - 1)
    else if z == 11 then (if inv then (lookupFanDeg 2 fanDeg == 7) && (p == 3 * deg + 2)
                          else (lookupFanDeg deg fanDeg == 7) && (p == 3 * deg))
    else if z == 12 then (if inv then p == deg - 2 else p == 4)
    else if z == 13 then (if inv then p == deg - 3 else p == 5)
    else if z == 14 then (if inv then p == 4 else p == deg - 2)
    else if z == 15 then (if inv then (lookupFanDeg 1 fanDeg == 7) && (p == 2 * deg + 1)
                          else (lookupFanDeg 1 fanDeg == 7) && (p == 3 * deg + 1))
    else if z == 16 then (if inv then (lookupFanDeg 1 fanDeg == 7) && (p == 3 * deg + 1)
                          else (lookupFanDeg 1 fanDeg == 7) && (p == 2 * deg + 1))
    else false
  else
    if z == 2 then (if inv then p == 2 else p == deg)
    else if z == 3 then (if inv then p == deg else p == 2)
    else if z == 4 then (if inv then p == deg + 1 else p == 2 * deg)
    else if z == 5 then (if inv then p == 2 * deg else p == deg + 1)
    else if z == 6 then (if inv then p == 3 else p == deg - 1)
    else if z == 7 then (if inv then p == deg - 1 else p == 3)
    else if z == 8 then
      (if inv then ((lookupFanDeg 2 fanDeg == 5) && (p == deg + 2)) ||
                   ((lookupFanDeg 2 fanDeg == 6) && (p == 2 * deg + 2))
       else ((lookupFanDeg deg fanDeg == 5) && (p == 2 * deg - 1)) ||
            ((lookupFanDeg deg fanDeg == 6) && (p == 3 * deg)))
    else if z == 9 then
      (if inv then ((lookupFanDeg deg fanDeg == 5) && (p == 2 * deg - 1)) ||
                   ((lookupFanDeg deg fanDeg == 6) && (p == 3 * deg)) ||
                   ((lookupFanDeg deg fanDeg == 7) && (p == 4 * deg))
       else ((lookupFanDeg 2 fanDeg == 5) && (p == deg + 2)) ||
            (((lookupFanDeg 2 fanDeg == 6) || (lookupFanDeg 2 fanDeg == 7)) && (p == 2 * deg + 2)))
    else if z == 11 then
      (if inv then ((lookupFanDeg deg fanDeg == 6) && (p == 2 * deg - 1)) ||
                   ((lookupFanDeg deg fanDeg == 7) && (p == 3 * deg))
       else ((lookupFanDeg 2 fanDeg == 6) && (p == deg + 2)) ||
            ((lookupFanDeg 2 fanDeg == 7) && (p == 3 * deg + 2)))
    else if z == 12 then
      (if inv then ((lookupFanDeg 1 fanDeg == 7) && (p == 3 * deg + 1)) ||
                   ((lookupFanDeg 1 fanDeg == 8) && (p == 4 * deg + 1))
       else p == 2 * deg + 1)
    else if z == 13 then
      (if inv then ((lookupFanDeg 1 fanDeg == 7) && (p == 2 * deg + 1)) ||
                   ((lookupFanDeg 1 fanDeg == 8) && (p == 3 * deg + 1))
       else p == 3 * deg + 1)
    else if z == 14 then
      (if inv then p == 2 * deg + 1
       else ((lookupFanDeg 1 fanDeg == 7) && (p == 3 * deg + 1)) ||
            ((lookupFanDeg 1 fanDeg == 8) && (p == 4 * deg + 1)))
    else if z == 15 then (if inv then p == 4 else p == deg - 2)
    else if z == 16 then (if inv then p == 5 else p == deg - 3)
    else false

/-- Verify that `compileRuleTriples deg 1 inv triples phi fanDeg` matches `triples` step-by-step
    via `validCoordMatch`. -/
def validTriplesCompilation (deg : Nat) (isPos inv : Bool) :
    List (Nat × (Nat × Nat)) → List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], _, _ => true
  | (z, bnd) :: rest, phi, fanDeg =>
    let nb := normRSSTBound bnd
    let u := lookupPhi (if inv then ruleV z else ruleU z) phi
    let v := lookupPhi (if inv then ruleU z else ruleV z) phi
    let pos_i := pureCartAdj deg fanDeg u v
    let p := shiftCartPos deg 0 pos_i
    let phi' := (z, pos_i) :: phi
    let fanDeg' := if pos_i ≤ deg && nb.1 == nb.2 then (pos_i, nb.1) :: fanDeg else fanDeg
    (p == pos_i) &&
      validCoordMatch deg isPos inv fanDeg z p &&
      validRSSTBound bnd &&
      validTriplesCompilation deg isPos inv rest phi' fanDeg'

def validRuleOutletCompilation (deg : Nat) (isPos inv : Bool) (r : RawRule) : Bool :=
  let bHub := normRSSTBound (if isPos then r.b1 else r.b0)
  let bSpk := normRSSTBound (if isPos then r.b0 else r.b1)
  validRSSTBound r.b0 && validRSSTBound r.b1 &&
  if decide (bHub.1 ≤ deg) && decide (deg ≤ bHub.2) then
    let phi0 := if isPos then [(0, 1), (1, 0)] else [(0, 0), (1, 1)]
    let fan0 := if bSpk.1 == bSpk.2 then [(1, bSpk.1)] else []
    (shiftCartPos deg 0 1 == 1) &&
      validTriplesCompilation deg isPos inv r.triples phi0 fan0
  else
    true

def validAllRulesCompilation (deg : Nat) : Bool :=
  theRules.all (fun r =>
    validRuleOutletCompilation deg true false r &&
    validRuleOutletCompilation deg false false r &&
    validRuleOutletCompilation deg true true r &&
    validRuleOutletCompilation deg false true r)

theorem validAllRulesCompilation_7 : validAllRulesCompilation 7 = true := by decide
theorem validAllRulesCompilation_8 : validAllRulesCompilation 8 = true := by decide
theorem validAllRulesCompilation_9 : validAllRulesCompilation 9 = true := by decide
theorem validAllRulesCompilation_10 : validAllRulesCompilation 10 = true := by decide
theorem validAllRulesCompilation_11 : validAllRulesCompilation 11 = true := by decide

theorem validAllRulesCompilation_of_deg (deg : Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    validAllRulesCompilation deg = true := by
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · exact validAllRulesCompilation_7
  · exact validAllRulesCompilation_8
  · exact validAllRulesCompilation_9
  · exact validAllRulesCompilation_10
  · exact validAllRulesCompilation_11

/-- Dual orientation of `edge_node_inv_edge_eq_node_f_edge_node_f` on a triangulated hypermap:
    `H.edge.f (H.node.f (H.edge.f d)) = H.node.inv (H.edge.f (H.node.inv d))`. -/
theorem edge_node_f_edge_eq_node_inv_edge_node_inv (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (d : H.Dart) :
    H.edge.f (H.node.f (H.edge.f d)) = H.node.inv (H.edge.f (H.node.inv d)) := by
  have h1 := edge_node_inv_edge_eq_node_f_edge_node_f H h_tri3 (H.node.inv d)
  have h2 : H.node.f (H.node.inv d) = d := H.node.right_inv d
  rw [h2] at h1
  have h3 := congrArg H.edge.f h1.symm
  rw [H.edge_involution] at h3
  exact h3

/-- Unified triangulation flanking-dart identity for `ruleRot H inv`:
    `H.edge.f (ruleRot H inv (H.edge.f d)) = ruleRotInv H inv (H.edge.f (ruleRotInv H inv d))`. -/
theorem edge_ruleRot_edge_eq (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (inv : Bool) (d : H.Dart) :
    H.edge.f (ruleRot H inv (H.edge.f d)) = ruleRotInv H inv (H.edge.f (ruleRotInv H inv d)) := by
  cases inv with
  | true =>
    dsimp [ruleRot, ruleRotInv]
    exact edge_node_inv_edge_eq_node_f_edge_node_f H h_tri3 d
  | false =>
    dsimp [ruleRot, ruleRotInv]
    exact edge_node_f_edge_eq_node_inv_edge_node_inv H h_tri3 d

/-- Unified triangulation flanking-dart identity for `ruleRotInv H inv`:
    `H.edge.f (ruleRotInv H inv (H.edge.f d)) = ruleRot H inv (H.edge.f (ruleRot H inv d))`. -/
theorem edge_ruleRotInv_edge_eq (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (inv : Bool) (d : H.Dart) :
    H.edge.f (ruleRotInv H inv (H.edge.f d)) = ruleRot H inv (H.edge.f (ruleRot H inv d)) := by
  cases inv with
  | true =>
    dsimp [ruleRot, ruleRotInv]
    exact edge_node_f_edge_eq_node_inv_edge_node_inv H h_tri3 d
  | false =>
    dsimp [ruleRot, ruleRotInv]
    exact edge_node_inv_edge_eq_node_f_edge_node_f H h_tri3 d

/-- Node degree is invariant under `ruleRot H inv`. -/
theorem nodeDegree_ruleRot_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (inv : Bool) (d : H.Dart) :
    Hypermap.nodeDegree H (ruleRot H inv d) fuel = Hypermap.nodeDegree H d fuel := by
  cases inv with
  | false =>
    dsimp [ruleRot]
    exact nodeDegree_node_f_eq_of_complete H darts h_all h_le d
  | true =>
    dsimp [ruleRot]
    have h1 := nodeDegree_node_f_eq_of_complete H darts h_all h_le (H.node.inv d)
    rw [H.node.right_inv] at h1
    exact h1.symm

/-- Node degree is invariant under `ruleRotInv H inv`. -/
theorem nodeDegree_ruleRotInv_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (inv : Bool) (d : H.Dart) :
    Hypermap.nodeDegree H (ruleRotInv H inv d) fuel = Hypermap.nodeDegree H d fuel := by
  cases inv with
  | false => exact nodeDegree_ruleRot_eq H darts h_all h_le true d
  | true => exact nodeDegree_ruleRot_eq H darts h_all h_le false d

/-- Complementary iteration identity on a vertex orbit of degree `k`:
    iterating `nodePermOriented H refl` by `k - m` steps (`m ≤ k`) equals iterating
    the opposite orientation `nodePermOriented H (!refl)` by `m` steps. -/
theorem perm_iter_nodePermOriented_sub_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d0 : H.Dart) (refl : Bool)
    {k m : Nat} (h_deg : Hypermap.nodeDegree H d0 fuel = k) (hm : m ≤ k) :
    Hypermap.Perm.iter (nodePermOriented H refl) (k - m) d0 =
      Hypermap.Perm.iter (nodePermOriented H (!refl)) m d0 := by
  have hd0_mem : d0 ∈ getOrbit H.node fuel d0 :=
    List.contains_iff_mem.mp (Hypermap.getOrbit_contains_self H.node fuel d0)
  have h_per := perm_iter_nodePermOriented_deg_eq_self H darts h_all h_le hd0_mem refl
  rw [h_deg] at h_per
  rw [perm_iter_nodePermOriented_not H refl m d0]
  conv => rhs; rw [← h_per]
  exact (perm_iter_symm_of_iter (nodePermOriented H refl) hm d0).symm

theorem iter_nodePermOriented_1 (H : Hypermap) (refl : Bool) (x : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H refl) 1 x = ruleRotInv H (!refl) x := by
  cases refl <;> rfl

theorem iter_nodePermOriented_2 (H : Hypermap) (refl : Bool) (x : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H refl) 2 x =
      ruleRotInv H (!refl) (ruleRotInv H (!refl) x) := by
  cases refl <;> rfl

theorem iter_nodePermOriented_3 (H : Hypermap) (refl : Bool) (x : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H refl) 3 x =
      ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) x)) := by
  cases refl <;> rfl

theorem iter_nodePermOriented_4 (H : Hypermap) (refl : Bool) (x : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H refl) 4 x =
      ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) x))) := by
  cases refl <;> rfl

theorem iter_nodePermOriented_not_1 (H : Hypermap) (refl : Bool) (x : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H (!refl)) 1 x = ruleRot H (!refl) x := by
  cases refl <;> rfl

theorem iter_nodePermOriented_not_2 (H : Hypermap) (refl : Bool) (x : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H (!refl)) 2 x =
      ruleRot H (!refl) (ruleRot H (!refl) x) := by
  cases refl <;> rfl

theorem iter_nodePermOriented_not_3 (H : Hypermap) (refl : Bool) (x : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H (!refl)) 3 x =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x)) := by
  cases refl <;> rfl

theorem iter_nodePermOriented_not_4 (H : Hypermap) (refl : Bool) (x : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H (!refl)) 4 x =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x))) := by
  cases refl <;> rfl

/-- Spoke evaluation at `1..5` and `deg - 3 .. deg`. -/
theorem spokeDartOriented_1 (H : Hypermap) (refl : Bool) (s : H.Dart) :
    spokeDartOriented H refl s 1 = s := by
  rw [spokeDartOriented_eq_iter]; rfl

theorem spokeDartOriented_2 (H : Hypermap) (refl : Bool) (s : H.Dart) :
    spokeDartOriented H refl s 2 = ruleRotInv H (!refl) s := by
  rw [spokeDartOriented_eq_iter]; exact iter_nodePermOriented_1 H refl s

theorem spokeDartOriented_3 (H : Hypermap) (refl : Bool) (s : H.Dart) :
    spokeDartOriented H refl s 3 = ruleRotInv H (!refl) (ruleRotInv H (!refl) s) := by
  rw [spokeDartOriented_eq_iter]; exact iter_nodePermOriented_2 H refl s

theorem spokeDartOriented_4 (H : Hypermap) (refl : Bool) (s : H.Dart) :
    spokeDartOriented H refl s 4 =
      ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) s)) := by
  rw [spokeDartOriented_eq_iter]; exact iter_nodePermOriented_3 H refl s

theorem spokeDartOriented_5 (H : Hypermap) (refl : Bool) (s : H.Dart) :
    spokeDartOriented H refl s 5 =
      ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) s))) := by
  rw [spokeDartOriented_eq_iter]; exact iter_nodePermOriented_4 H refl s

theorem spokeDartOriented_deg (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (s : H.Dart)
    (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    spokeDartOriented H refl s deg = ruleRot H (!refl) s := by
  rw [spokeDartOriented_eq_iter,
      perm_iter_nodePermOriented_sub_eq H darts h_all h_le s refl h_deg (by omega : 1 ≤ deg),
      iter_nodePermOriented_not_1]

theorem spokeDartOriented_deg_sub_1 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (s : H.Dart)
    (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    spokeDartOriented H refl s (deg - 1) = ruleRot H (!refl) (ruleRot H (!refl) s) := by
  rw [spokeDartOriented_eq_iter]
  have h_sub : deg - 1 - 1 = deg - 2 := by omega
  rw [h_sub,
      perm_iter_nodePermOriented_sub_eq H darts h_all h_le s refl h_deg (by omega : 2 ≤ deg),
      iter_nodePermOriented_not_2]

theorem spokeDartOriented_deg_sub_2 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (s : H.Dart)
    (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    spokeDartOriented H refl s (deg - 2) =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) s)) := by
  rw [spokeDartOriented_eq_iter]
  have h_sub : deg - 2 - 1 = deg - 3 := by omega
  rw [h_sub,
      perm_iter_nodePermOriented_sub_eq H darts h_all h_le s refl h_deg (by omega : 3 ≤ deg),
      iter_nodePermOriented_not_3]

theorem spokeDartOriented_deg_sub_3 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (s : H.Dart)
    (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    spokeDartOriented H refl s (deg - 3) =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) s))) := by
  rw [spokeDartOriented_eq_iter]
  have h_sub : deg - 3 - 1 = deg - 4 := by omega
  rw [h_sub,
      perm_iter_nodePermOriented_sub_eq H darts h_all h_le s refl h_deg (by omega : 4 ≤ deg),
      iter_nodePermOriented_not_4]

/-- Clockwise hat `5` of `H.edge.f (ruleRot H (!refl) t)` has the same `nodeDegree`
    as counter-clockwise hat `4` of `H.edge.f t`. -/
theorem nodeDegree_hat5_rot_eq_hat4 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (t : H.Dart) :
    Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f (ruleRot H (!refl) t)) 5) fuel =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f t) 4) fuel := by
  have h := (nodeDegree_hat_refl_eq_of_triangulation H darts h_all h_le h_tri3 (!refl) t).symm
  have h_eq : ruleVertexDart H (!!refl) (H.edge.f t) 5 = ruleVertexDart H (!refl) (H.edge.f t) 4 := by
    cases refl <;> rfl
  rw [h_eq] at h
  exact h

/-- Fan periodicity identities around a vertex dart `x` of degree `5, 6, 7, 8`. -/
theorem fan_deg5_rot2_eq_rotInv3 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 5) :
    ruleRot H (!refl) (ruleRot H (!refl) x) =
      ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) x)) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 2 ≤ 5)
  rw [iter_nodePermOriented_3, iter_nodePermOriented_not_2] at h
  exact h.symm

theorem fan_deg5_rotInv2_eq_rot3 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 5) :
    ruleRotInv H (!refl) (ruleRotInv H (!refl) x) =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x)) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 3 ≤ 5)
  rw [iter_nodePermOriented_2, iter_nodePermOriented_not_3] at h
  exact h

theorem fan_deg6_rotInv3_eq_rot3 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 6) :
    ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) x)) =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x)) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 3 ≤ 6)
  rw [iter_nodePermOriented_3, iter_nodePermOriented_not_3] at h
  exact h

theorem fan_deg6_rot2_eq_rotInv4 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 6) :
    ruleRot H (!refl) (ruleRot H (!refl) x) =
      ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) x))) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 2 ≤ 6)
  rw [iter_nodePermOriented_4, iter_nodePermOriented_not_2] at h
  exact h.symm

theorem fan_deg6_rotInv2_eq_rot4 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 6) :
    ruleRotInv H (!refl) (ruleRotInv H (!refl) x) =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x))) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 4 ≤ 6)
  rw [iter_nodePermOriented_2, iter_nodePermOriented_not_4] at h
  exact h

theorem fan_deg7_rotInv4_eq_rot3 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 7) :
    ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) x))) =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x)) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 3 ≤ 7)
  rw [iter_nodePermOriented_4, iter_nodePermOriented_not_3] at h
  exact h

theorem fan_deg7_rotInv3_eq_rot4 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 7) :
    ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) x)) =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x))) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 4 ≤ 7)
  rw [iter_nodePermOriented_3, iter_nodePermOriented_not_4] at h
  exact h

theorem fan_deg8_iter5_eq_rot3 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 8) :
    (if refl then H.edge.f (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.node.inv x)))))
     else H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f x)))))) =
      H.edge.f (ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x))) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 3 ≤ 8)
  rw [iter_nodePermOriented_not_3] at h
  have h5 : (if refl then H.edge.f (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.node.inv x)))))
             else H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f x)))))) =
      H.edge.f (Hypermap.Perm.iter (nodePermOriented H refl) 5 x) := by
    cases refl <;> rfl
  rw [h5]
  exact congrArg H.edge.f h

theorem fan_deg8_rotInv4_eq_rot4 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ y : H.Dart, y ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (refl : Bool) (x : H.Dart)
    (h_deg : Hypermap.nodeDegree H x fuel = 8) :
    ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) (ruleRotInv H (!refl) x))) =
      ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) (ruleRot H (!refl) x))) := by
  have h := perm_iter_nodePermOriented_sub_eq H darts h_all h_le x refl h_deg (by omega : 4 ≤ 8)
  rw [iter_nodePermOriented_4, iter_nodePermOriented_not_4] at h
  exact h

/-- Mirror identities for `ruleVertexDart H refl d z` vs `ruleVertexDart H (!refl) d z'`. -/
theorem ruleVertexDart_refl_2 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 2 = ruleVertexDart H (!refl) d 3 := by cases refl <;> rfl
theorem ruleVertexDart_refl_3 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 3 = ruleVertexDart H (!refl) d 2 := by cases refl <;> rfl
theorem ruleVertexDart_refl_4 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 4 = ruleVertexDart H (!refl) d 5 := by cases refl <;> rfl
theorem ruleVertexDart_refl_5 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 5 = ruleVertexDart H (!refl) d 4 := by cases refl <;> rfl
theorem ruleVertexDart_refl_6 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 6 = ruleVertexDart H (!refl) d 7 := by cases refl <;> rfl
theorem ruleVertexDart_refl_7 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 7 = ruleVertexDart H (!refl) d 6 := by cases refl <;> rfl
theorem ruleVertexDart_refl_8 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 8 = ruleVertexDart H (!refl) d 9 := by cases refl <;> rfl
theorem ruleVertexDart_refl_9 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 9 = ruleVertexDart H (!refl) d 8 := by cases refl <;> rfl
theorem ruleVertexDart_refl_10 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 10 = ruleVertexDart H (!refl) d 11 := by cases refl <;> rfl
theorem ruleVertexDart_refl_11 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 11 = ruleVertexDart H (!refl) d 10 := by cases refl <;> rfl
theorem ruleVertexDart_refl_12 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 12 = ruleVertexDart H (!refl) d 14 := by cases refl <;> rfl
theorem ruleVertexDart_refl_14 (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleVertexDart H refl d 14 = ruleVertexDart H (!refl) d 12 := by cases refl <;> rfl

/-- Spoke-1 cartwheel degree identities for Ring 0 (`1..5` and `deg - 3 .. deg`). -/
theorem cartDegOriented_1_eq (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 1 = Hypermap.nodeDegree H (H.edge.f s) fuel := by
  dsimp [cartDegOriented]
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_1]

theorem cartDegOriented_2_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 2 =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 2) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_2,
      edge_ruleRot_edge_eq H h_tri3 (!refl) s]
  exact (nodeDegree_ruleRotInv_eq H darts h_all h_le (!refl) _).symm

theorem cartDegOriented_2_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 2 =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 3) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_2,
      H.edge_involution]

theorem cartDegOriented_deg_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s deg =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 3) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
      spokeDartOriented_deg H darts h_all h_le refl s h_deg h5,
      edge_ruleRotInv_edge_eq H h_tri3 (!refl) s]
  exact (nodeDegree_ruleRot_eq H darts h_all h_le (!refl) _).symm

theorem cartDegOriented_deg_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s deg =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 2) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
      spokeDartOriented_deg H darts h_all h_le refl s h_deg h5,
      H.edge_involution]

theorem cartDegOriented_3_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 3 =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 4) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_3]

theorem cartDegOriented_3_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 3 =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 7) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_3,
      H.edge_involution]

theorem cartDegOriented_deg_sub_1_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg - 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 5) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
      spokeDartOriented_deg_sub_1 H darts h_all h_le refl s h_deg h5]

theorem cartDegOriented_deg_sub_1_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg - 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 6) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
      spokeDartOriented_deg_sub_1 H darts h_all h_le refl s h_deg h5,
      H.edge_involution]

theorem cartDegOriented_4_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 4 =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 12) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_4]

theorem cartDegOriented_4_eq_in_refl (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 4 =
      Hypermap.nodeDegree H (ruleVertexDart H refl (H.edge.f s) 15) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_4,
      H.edge_involution]
  cases refl <;> rfl

theorem cartDegOriented_5_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 5 =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 13) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_5]

theorem cartDegOriented_5_eq_in_refl (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s 5 =
      Hypermap.nodeDegree H (ruleVertexDart H refl (H.edge.f s) 16) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_5,
      H.edge_involution]
  cases refl <;> rfl

theorem cartDegOriented_deg_sub_2_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg - 2) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 14) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
      spokeDartOriented_deg_sub_2 H darts h_all h_le refl s h_deg h5]

theorem cartDegOriented_deg_sub_2_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg - 2) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 15) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
      spokeDartOriented_deg_sub_2 H darts h_all h_le refl s h_deg h5,
      H.edge_involution]

theorem cartDegOriented_deg_sub_3_eq_out_refl (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg - 3) =
      Hypermap.nodeDegree H (ruleVertexDart H refl s 13) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
      spokeDartOriented_deg_sub_3 H darts h_all h_le refl s h_deg h5]
  cases refl <;> rfl

theorem cartDegOriented_deg_sub_3_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg - 3) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 16) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
      spokeDartOriented_deg_sub_3 H darts h_all h_le refl s h_deg h5,
      H.edge_involution]

/-- Spoke-1 cartwheel degree identities for Ring 1 (`deg + 1`, `2 * deg`, `deg + 2`, `2 * deg - 1`). -/
theorem cartDegOriented_deg_add_1_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 6) fuel := by
  dsimp [cartDegOriented]
  rw [cartDartOriented_hat H deg refl s (by omega) (by omega), spokeDartOriented_1]
  rfl

theorem cartDegOriented_deg_add_1_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 5) fuel := by
  dsimp [cartDegOriented]
  rw [cartDartOriented_hat H deg refl s (by omega) (by omega), spokeDartOriented_1]

theorem cartDegOriented_two_mul_deg_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (2 * deg) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 4) fuel := by
  have h_eq : 2 * deg = deg + deg := by omega
  dsimp [cartDegOriented]
  rw [h_eq, cartDartOriented_hat H deg refl s (by omega) (by omega),
      spokeDartOriented_deg H darts h_all h_le refl s h_deg h5]
  exact nodeDegree_hat5_rot_eq_hat4 H darts h_all h_le h_tri3 refl s

theorem cartDegOriented_two_mul_deg_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (2 * deg) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 7) fuel :=
  cartDegOriented_two_mul_deg_eq_in H darts h_all h_le h_tri3 refl s h_deg h5

theorem cartDegOriented_deg_add_2_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (deg + 2) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 8) fuel := by
  dsimp [cartDegOriented]
  rw [cartDartOriented_hat H deg refl s (by omega) (by omega), spokeDartOriented_2]
  rfl

theorem cartDegOriented_two_mul_deg_sub_1_eq_out (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (2 * deg - 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 9) fuel := by
  have h_eq : 2 * deg - 1 = deg + (deg - 1) := by omega
  dsimp [cartDegOriented]
  rw [h_eq, cartDartOriented_hat H deg refl s (by omega) (by omega),
      spokeDartOriented_deg_sub_1 H darts h_all h_le refl s h_deg h5]
  exact nodeDegree_hat5_rot_eq_hat4 H darts h_all h_le h_tri3 refl (ruleRot H (!refl) s)

theorem cartDegOriented_deg_add_2_eq_in_of_deg5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s2 : cartDegOriented H fuel deg refl s 2 = 5) :
    cartDegOriented H fuel deg refl s (deg + 2) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 9) fuel := by
  have hs2_deg : Hypermap.nodeDegree H (H.edge.f (ruleRotInv H (!refl) s)) fuel = 5 := by
    dsimp [cartDegOriented] at h_s2
    rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_2] at h_s2
    exact h_s2
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_hat H deg refl s (by omega) (by omega), spokeDartOriented_2]
  rvd_simp
  rw [edge_ruleRot_edge_eq H h_tri3 (!refl) s,
      fan_deg5_rot2_eq_rotInv3 H darts h_all h_le refl (H.edge.f (ruleRotInv H (!refl) s)) hs2_deg]

theorem cartDegOriented_deg_add_2_eq_in_of_deg6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s2 : cartDegOriented H fuel deg refl s 2 = 6) :
    cartDegOriented H fuel deg refl s (deg + 2) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 11) fuel := by
  have hs2_deg : Hypermap.nodeDegree H (H.edge.f (ruleRotInv H (!refl) s)) fuel = 6 := by
    dsimp [cartDegOriented] at h_s2
    rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_2] at h_s2
    exact h_s2
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_hat H deg refl s (by omega) (by omega), spokeDartOriented_2]
  rvd_simp
  rw [edge_ruleRot_edge_eq H h_tri3 (!refl) s,
      fan_deg6_rot2_eq_rotInv4 H darts h_all h_le refl (H.edge.f (ruleRotInv H (!refl) s)) hs2_deg]

theorem cartDegOriented_two_mul_deg_sub_1_eq_in_of_deg5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg)
    (h_sd : cartDegOriented H fuel deg refl s deg = 5) :
    cartDegOriented H fuel deg refl s (2 * deg - 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 8) fuel := by
  have hsd_deg : Hypermap.nodeDegree H (H.edge.f (ruleRot H (!refl) s)) fuel = 5 := by
    dsimp [cartDegOriented] at h_sd
    rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
        spokeDartOriented_deg H darts h_all h_le refl s h_deg h5] at h_sd
    exact h_sd
  rw [cartDegOriented_two_mul_deg_sub_1_eq_out H darts h_all h_le h_tri3 refl s h_deg h5]
  rvd_simp
  rw [edge_ruleRotInv_edge_eq H h_tri3 (!refl) s,
      fan_deg5_rotInv2_eq_rot3 H darts h_all h_le refl (H.edge.f (ruleRot H (!refl) s)) hsd_deg]

theorem cartDegOriented_two_mul_deg_sub_1_eq_in_of_deg6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg)
    (h_sd : cartDegOriented H fuel deg refl s deg = 6) :
    cartDegOriented H fuel deg refl s (2 * deg - 1) =
      Hypermap.nodeDegree H (ruleVertexDart H refl (H.edge.f s) 11) fuel := by
  have hsd_deg : Hypermap.nodeDegree H (H.edge.f (ruleRot H (!refl) s)) fuel = 6 := by
    dsimp [cartDegOriented] at h_sd
    rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
        spokeDartOriented_deg H darts h_all h_le refl s h_deg h5] at h_sd
    exact h_sd
  rw [cartDegOriented_two_mul_deg_sub_1_eq_out H darts h_all h_le h_tri3 refl s h_deg h5,
      ruleVertexDart_refl_11]
  rvd_simp
  rw [edge_ruleRotInv_edge_eq H h_tri3 (!refl) s,
      fan_deg6_rotInv2_eq_rot4 H darts h_all h_le refl (H.edge.f (ruleRot H (!refl) s)) hsd_deg]

/-- Spoke-1 cartwheel degree identities for Rings 2–4 (`2 * deg + 1`, `3 * deg + 1`, `4 * deg + 1`,
    `2 * deg + 2`, `3 * deg + 2`, `3 * deg`, `4 * deg`). -/
theorem cartDegOriented_fan1_s1_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (2 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 12) fuel := by
  dsimp [cartDegOriented]
  rw [cartDartOriented_fan1 H deg refl s (by omega) (by omega), spokeDartOriented_1]

theorem cartDegOriented_fan1_s1_eq_out_16_of_deg7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s1 : cartDegOriented H fuel deg refl s 1 = 7) :
    cartDegOriented H fuel deg refl s (2 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 16) fuel := by
  have hs1_deg : Hypermap.nodeDegree H (H.edge.f s) fuel = 7 := by
    rw [← cartDegOriented_1_eq H fuel deg refl s h5]; exact h_s1
  rw [cartDegOriented_fan1_s1_eq_in H fuel deg refl s h5]
  rvd_simp
  rw [fan_deg7_rotInv3_eq_rot4 H darts h_all h_le refl (H.edge.f s) hs1_deg]

theorem cartDegOriented_fan1_s1_eq_out_refl_15_of_deg7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (2 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H refl s 15) fuel := by
  rw [cartDegOriented_fan1_s1_eq_in H fuel deg refl s h5]
  rvd_simp
  cases refl <;> rfl

theorem cartDegOriented_fan1_s1_eq_in_refl_13_of_deg7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s1 : cartDegOriented H fuel deg refl s 1 = 7) :
    cartDegOriented H fuel deg refl s (2 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H refl (H.edge.f s) 13) fuel := by
  have h := cartDegOriented_fan1_s1_eq_out_16_of_deg7 H darts h_all h_le refl s h5 h_s1
  have h_eq : ruleVertexDart H (!refl) s 16 = ruleVertexDart H refl (H.edge.f s) 13 := by
    rvd_simp; cases refl <;> rfl
  rw [h_eq] at h
  exact h

theorem cartDegOriented_fan2_s1_eq_in (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (3 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 13) fuel := by
  dsimp [cartDegOriented]
  rw [cartDartOriented_fan2 H deg refl s (by omega) (by omega), spokeDartOriented_1]

theorem cartDegOriented_fan2_s1_eq_in_14_of_deg7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s1 : cartDegOriented H fuel deg refl s 1 = 7) :
    cartDegOriented H fuel deg refl s (3 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 14) fuel := by
  have hs1_deg : Hypermap.nodeDegree H (H.edge.f s) fuel = 7 := by
    rw [← cartDegOriented_1_eq H fuel deg refl s h5]; exact h_s1
  rw [cartDegOriented_fan2_s1_eq_in H fuel deg refl s h5]
  rvd_simp
  rw [fan_deg7_rotInv4_eq_rot3 H darts h_all h_le refl (H.edge.f s) hs1_deg]

theorem cartDegOriented_fan2_s1_eq_out_15_of_deg7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s1 : cartDegOriented H fuel deg refl s 1 = 7) :
    cartDegOriented H fuel deg refl s (3 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 15) fuel :=
  cartDegOriented_fan2_s1_eq_in_14_of_deg7 H darts h_all h_le refl s h5 h_s1

theorem cartDegOriented_fan2_s1_eq_out_refl_16 (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat) (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (3 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H refl s 16) fuel := by
  rw [cartDegOriented_fan2_s1_eq_in H fuel deg refl s h5]
  rvd_simp
  cases refl <;> rfl

theorem cartDegOriented_fan2_s1_eq_in_refl_13_of_deg8 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s1 : cartDegOriented H fuel deg refl s 1 = 8) :
    cartDegOriented H fuel deg refl s (3 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H refl (H.edge.f s) 13) fuel := by
  have hs1_deg : Hypermap.nodeDegree H (H.edge.f s) fuel = 8 := by
    rw [← cartDegOriented_1_eq H fuel deg refl s h5]; exact h_s1
  rw [cartDegOriented_fan2_s1_eq_in H fuel deg refl s h5]
  rvd_simp
  rw [fan_deg8_rotInv4_eq_rot4 H darts h_all h_le refl (H.edge.f s) hs1_deg]
  cases refl <;> rfl

theorem cartDegOriented_fan3_s1_eq_in_14_of_deg8 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s1 : cartDegOriented H fuel deg refl s 1 = 8) :
    cartDegOriented H fuel deg refl s (4 * deg + 1) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 14) fuel := by
  have hs1_deg : Hypermap.nodeDegree H (H.edge.f s) fuel = 8 := by
    rw [← cartDegOriented_1_eq H fuel deg refl s h5]; exact h_s1
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_fan3 H deg refl s (by omega) (by omega), spokeDartOriented_1,
      fan_deg8_iter5_eq_rot3 H darts h_all h_le refl (H.edge.f s) hs1_deg]

theorem cartDegOriented_fan1_s2_eq_in_9 (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (2 * deg + 2) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 9) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_fan1 H deg refl s (by omega) (by omega), spokeDartOriented_2]
  rvd_simp
  rw [edge_ruleRot_edge_eq H h_tri3 (!refl) s]

theorem cartDegOriented_fan2_s2_eq_in_11 (H : Hypermap) [DecidableEq H.Dart]
    (fuel deg : Nat)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (3 * deg + 2) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 11) fuel := by
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_fan2 H deg refl s (by omega) (by omega), spokeDartOriented_2]
  rvd_simp
  rw [edge_ruleRot_edge_eq H h_tri3 (!refl) s]

theorem cartDegOriented_fan2_s2_eq_out_refl_11_of_deg7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s2 : cartDegOriented H fuel deg refl s 2 = 7) :
    cartDegOriented H fuel deg refl s (3 * deg + 2) =
      Hypermap.nodeDegree H (ruleVertexDart H refl s 11) fuel := by
  have hs2_deg : Hypermap.nodeDegree H (H.edge.f (ruleRotInv H (!refl) s)) fuel = 7 := by
    dsimp [cartDegOriented] at h_s2
    rw [cartDartOriented_spoke H deg refl s (by omega) (by omega), spokeDartOriented_2] at h_s2
    exact h_s2
  dsimp [cartDegOriented]; rvd_simp
  rw [cartDartOriented_fan2 H deg refl s (by omega) (by omega), spokeDartOriented_2]
  rvd_simp
  rw [fan_deg7_rotInv4_eq_rot3 H darts h_all h_le refl (H.edge.f (ruleRotInv H (!refl) s)) hs2_deg]
  cases refl <;> rfl

theorem cartDegOriented_fan1_sdeg_eq_out_11 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) :
    cartDegOriented H fuel deg refl s (3 * deg) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 11) fuel := by
  have h_eq : 3 * deg = 2 * deg + deg := by omega
  dsimp [cartDegOriented]; rvd_simp
  rw [h_eq, cartDartOriented_fan1 H deg refl s (by omega) (by omega),
      spokeDartOriented_deg H darts h_all h_le refl s h_deg h5]
  rfl

theorem cartDegOriented_fan1_sdeg_eq_in_8_of_deg6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg)
    (h_sd : cartDegOriented H fuel deg refl s deg = 6) :
    cartDegOriented H fuel deg refl s (3 * deg) =
      Hypermap.nodeDegree H (ruleVertexDart H (!refl) (H.edge.f s) 8) fuel := by
  have hsd_deg : Hypermap.nodeDegree H (H.edge.f (ruleRot H (!refl) s)) fuel = 6 := by
    dsimp [cartDegOriented] at h_sd
    rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
        spokeDartOriented_deg H darts h_all h_le refl s h_deg h5] at h_sd
    exact h_sd
  rw [cartDegOriented_fan1_sdeg_eq_out_11 H darts h_all h_le refl s h_deg h5]
  rvd_simp
  rw [edge_ruleRotInv_edge_eq H h_tri3 (!refl) s,
      fan_deg6_rotInv3_eq_rot3 H darts h_all h_le refl (H.edge.f (ruleRot H (!refl) s)) hsd_deg]

theorem cartDegOriented_fan1_sdeg_eq_in_refl_11_of_deg7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg)
    (h_sd : cartDegOriented H fuel deg refl s deg = 7) :
    cartDegOriented H fuel deg refl s (3 * deg) =
      Hypermap.nodeDegree H (ruleVertexDart H refl (H.edge.f s) 11) fuel := by
  have hsd_deg : Hypermap.nodeDegree H (H.edge.f (ruleRot H (!refl) s)) fuel = 7 := by
    dsimp [cartDegOriented] at h_sd
    rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
        spokeDartOriented_deg H darts h_all h_le refl s h_deg h5] at h_sd
    exact h_sd
  rw [cartDegOriented_fan1_sdeg_eq_out_11 H darts h_all h_le refl s h_deg h5,
      ruleVertexDart_refl_11 H refl (H.edge.f s)]
  rvd_simp
  rw [edge_ruleRotInv_edge_eq H h_tri3 (!refl) s,
      fan_deg7_rotInv3_eq_rot4 H darts h_all h_le refl (H.edge.f (ruleRot H (!refl) s)) hsd_deg]

theorem cartDegOriented_fan2_sdeg_eq_in_refl_9_of_deg7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg)
    (h_sd : cartDegOriented H fuel deg refl s deg = 7) :
    cartDegOriented H fuel deg refl s (4 * deg) =
      Hypermap.nodeDegree H (ruleVertexDart H refl (H.edge.f s) 9) fuel := by
  have hsd_deg : Hypermap.nodeDegree H (H.edge.f (ruleRot H (!refl) s)) fuel = 7 := by
    dsimp [cartDegOriented] at h_sd
    rw [cartDartOriented_spoke H deg refl s (by omega) (by omega),
        spokeDartOriented_deg H darts h_all h_le refl s h_deg h5] at h_sd
    exact h_sd
  have h_eq : 4 * deg = 3 * deg + deg := by omega
  dsimp [cartDegOriented]
  rw [h_eq, cartDartOriented_fan2 H deg refl s (by omega) (by omega),
      spokeDartOriented_deg H darts h_all h_le refl s h_deg h5,
      ruleVertexDart_refl_9 H refl (H.edge.f s)]
  rvd_simp
  rw [edge_ruleRotInv_edge_eq H h_tri3 (!refl) s,
      fan_deg7_rotInv4_eq_rot3 H darts h_all h_le refl (H.edge.f (ruleRot H (!refl) s)) hsd_deg]

/-- Invariant relating `lookupFanDeg` in `compileRuleTriples` to actual cartwheel degrees `cd`. -/
def FanDegInvariant (cd : Nat → Nat) (fanDeg : List (Nat × Nat)) : Prop :=
  ∀ i k, lookupFanDeg i fanDeg = k → k ≠ 0 → cd i = k

/-- Soundness of `validCoordMatch`: any `(z, p)` accepted by `validCoordMatch deg isPos inv fanDeg z p`
    on a complete triangulated hypermap `H` (with `5 ≤ deg`, `Hypermap.nodeDegree H s fuel = deg`,
    and `FanDegInvariant (cartDegOriented H fuel deg refl s) fanDeg`) satisfies
    `cartDegOriented H fuel deg refl s p = Hypermap.nodeDegree H (ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s) z) fuel`. -/
theorem validCoordMatch_sound (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl isPos inv : Bool) (s : H.Dart)
    (fanDeg : List (Nat × Nat)) (z p : Nat)
    (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg)
    (h_fan : FanDegInvariant (cartDegOriented H fuel deg refl s) fanDeg)
    (h_match : validCoordMatch deg isPos inv fanDeg z p = true) :
    cartDegOriented H fuel deg refl s p =
      Hypermap.nodeDegree H
        (ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s) z) fuel := by
  unfold validCoordMatch at h_match
  cases isPos with
  | false =>
    dsimp at h_match ⊢
    by_cases hz2 : z = 2
    · subst hz2; simp only [beq_self_eq_true, ite_true] at h_match
      cases inv with
      | false =>
        have hp := eq_of_beq h_match; subst hp
        exact cartDegOriented_2_eq_out H darts h_all h_le h_tri3 refl s h5
      | true =>
        have hp := eq_of_beq h_match; subst hp
        rw [ruleVertexDart_refl_2]
        exact cartDegOriented_deg_eq_out H darts h_all h_le h_tri3 refl s h_deg h5
    · simp only [beq_false_of_ne hz2, Bool.false_eq_true, ite_false] at h_match
      by_cases hz3 : z = 3
      · subst hz3; simp only [beq_self_eq_true, ite_true] at h_match
        cases inv with
        | false =>
          have hp := eq_of_beq h_match; subst hp
          exact cartDegOriented_deg_eq_out H darts h_all h_le h_tri3 refl s h_deg h5
        | true =>
          have hp := eq_of_beq h_match; subst hp
          rw [ruleVertexDart_refl_3]
          exact cartDegOriented_2_eq_out H darts h_all h_le h_tri3 refl s h5
      · simp only [beq_false_of_ne hz3, Bool.false_eq_true, ite_false] at h_match
        by_cases hz4 : z = 4
        · subst hz4; simp only [beq_self_eq_true, ite_true] at h_match
          cases inv with
          | false =>
            have hp := eq_of_beq h_match; subst hp
            exact cartDegOriented_3_eq_out H fuel deg refl s h5
          | true =>
            have hp := eq_of_beq h_match; subst hp
            rw [ruleVertexDart_refl_4]
            exact cartDegOriented_deg_sub_1_eq_out H darts h_all h_le refl s h_deg h5
        · simp only [beq_false_of_ne hz4, Bool.false_eq_true, ite_false] at h_match
          by_cases hz5 : z = 5
          · subst hz5; simp only [beq_self_eq_true, ite_true] at h_match
            cases inv with
            | false =>
              have hp := eq_of_beq h_match; subst hp
              exact cartDegOriented_deg_sub_1_eq_out H darts h_all h_le refl s h_deg h5
            | true =>
              have hp := eq_of_beq h_match; subst hp
              rw [ruleVertexDart_refl_5]
              exact cartDegOriented_3_eq_out H fuel deg refl s h5
          · simp only [beq_false_of_ne hz5, Bool.false_eq_true, ite_false] at h_match
            by_cases hz6 : z = 6
            · subst hz6; simp only [beq_self_eq_true, ite_true] at h_match
              cases inv with
              | false =>
                have hp := eq_of_beq h_match; subst hp
                exact cartDegOriented_deg_add_1_eq_out H fuel deg refl s h5
              | true =>
                have hp := eq_of_beq h_match; subst hp
                rw [ruleVertexDart_refl_6]
                exact cartDegOriented_two_mul_deg_eq_out H darts h_all h_le h_tri3 refl s h_deg h5
            · simp only [beq_false_of_ne hz6, Bool.false_eq_true, ite_false] at h_match
              by_cases hz7 : z = 7
              · subst hz7; simp only [beq_self_eq_true, ite_true] at h_match
                cases inv with
                | false =>
                  have hp := eq_of_beq h_match; subst hp
                  exact cartDegOriented_two_mul_deg_eq_out H darts h_all h_le h_tri3 refl s h_deg h5
                | true =>
                  have hp := eq_of_beq h_match; subst hp
                  rw [ruleVertexDart_refl_7]
                  exact cartDegOriented_deg_add_1_eq_out H fuel deg refl s h5
              · simp only [beq_false_of_ne hz7, Bool.false_eq_true, ite_false] at h_match
                by_cases hz8 : z = 8
                · subst hz8; simp only [beq_self_eq_true, ite_true] at h_match
                  cases inv with
                  | false =>
                    have hp := eq_of_beq h_match; subst hp
                    exact cartDegOriented_deg_add_2_eq_out H fuel deg refl s h5
                  | true =>
                    have hp := eq_of_beq h_match; subst hp
                    rw [ruleVertexDart_refl_8]
                    exact cartDegOriented_two_mul_deg_sub_1_eq_out H darts h_all h_le h_tri3 refl s h_deg h5
                · simp only [beq_false_of_ne hz8, Bool.false_eq_true, ite_false] at h_match
                  by_cases hz9 : z = 9
                  · subst hz9; simp only [beq_self_eq_true, ite_true] at h_match
                    cases inv with
                    | false =>
                      have hp := eq_of_beq h_match; subst hp
                      exact cartDegOriented_two_mul_deg_sub_1_eq_out H darts h_all h_le h_tri3 refl s h_deg h5
                    | true =>
                      have hp := eq_of_beq h_match; subst hp
                      rw [ruleVertexDart_refl_9]
                      exact cartDegOriented_deg_add_2_eq_out H fuel deg refl s h5
                  · simp only [beq_false_of_ne hz9, Bool.false_eq_true, ite_false] at h_match
                    by_cases hz11 : z = 11
                    · subst hz11; simp only [beq_self_eq_true, ite_true] at h_match
                      cases inv with
                      | false =>
                        rcases Bool.and_eq_true_iff.mp h_match with ⟨_, hp_eq⟩
                        have hp := eq_of_beq hp_eq; subst hp
                        exact cartDegOriented_fan1_sdeg_eq_out_11 H darts h_all h_le refl s h_deg h5
                      | true =>
                        rcases Bool.and_eq_true_iff.mp h_match with ⟨hf, hp_eq⟩
                        have hp := eq_of_beq hp_eq; subst hp
                        have hs2 : cartDegOriented H fuel deg refl s 2 = 7 :=
                          h_fan 2 7 (eq_of_beq hf) (by decide)
                        exact cartDegOriented_fan2_s2_eq_out_refl_11_of_deg7 H darts h_all h_le refl s h5 hs2
                    · simp only [beq_false_of_ne hz11, Bool.false_eq_true, ite_false] at h_match
                      by_cases hz12 : z = 12
                      · subst hz12; simp only [beq_self_eq_true, ite_true] at h_match
                        cases inv with
                        | false =>
                          have hp := eq_of_beq h_match; subst hp
                          exact cartDegOriented_4_eq_out H fuel deg refl s h5
                        | true =>
                          have hp := eq_of_beq h_match; subst hp
                          rw [ruleVertexDart_refl_12]
                          exact cartDegOriented_deg_sub_2_eq_out H darts h_all h_le refl s h_deg h5
                      · simp only [beq_false_of_ne hz12, Bool.false_eq_true, ite_false] at h_match
                        by_cases hz13 : z = 13
                        · subst hz13; simp only [beq_self_eq_true, ite_true] at h_match
                          cases inv with
                          | false =>
                            have hp := eq_of_beq h_match; subst hp
                            exact cartDegOriented_5_eq_out H fuel deg refl s h5
                          | true =>
                            have hp := eq_of_beq h_match; subst hp
                            exact cartDegOriented_deg_sub_3_eq_out_refl H darts h_all h_le refl s h_deg h5
                        · simp only [beq_false_of_ne hz13, Bool.false_eq_true, ite_false] at h_match
                          by_cases hz14 : z = 14
                          · subst hz14; simp only [beq_self_eq_true, ite_true] at h_match
                            cases inv with
                            | false =>
                              have hp := eq_of_beq h_match; subst hp
                              exact cartDegOriented_deg_sub_2_eq_out H darts h_all h_le refl s h_deg h5
                            | true =>
                              have hp := eq_of_beq h_match; subst hp
                              rw [ruleVertexDart_refl_14]
                              exact cartDegOriented_4_eq_out H fuel deg refl s h5
                          · simp only [beq_false_of_ne hz14, Bool.false_eq_true, ite_false] at h_match
                            by_cases hz15 : z = 15
                            · subst hz15; simp only [beq_self_eq_true, ite_true] at h_match
                              cases inv with
                              | false =>
                                rcases Bool.and_eq_true_iff.mp h_match with ⟨hf, hp_eq⟩
                                have hp := eq_of_beq hp_eq; subst hp
                                have hs1 : cartDegOriented H fuel deg refl s 1 = 7 :=
                                  h_fan 1 7 (eq_of_beq hf) (by decide)
                                exact cartDegOriented_fan2_s1_eq_out_15_of_deg7 H darts h_all h_le refl s h5 hs1
                              | true =>
                                rcases Bool.and_eq_true_iff.mp h_match with ⟨_, hp_eq⟩
                                have hp := eq_of_beq hp_eq; subst hp
                                exact cartDegOriented_fan1_s1_eq_out_refl_15_of_deg7 H fuel deg refl s h5
                            · simp only [beq_false_of_ne hz15, Bool.false_eq_true, ite_false] at h_match
                              by_cases hz16 : z = 16
                              · subst hz16; simp only [beq_self_eq_true, ite_true] at h_match
                                cases inv with
                                | false =>
                                  rcases Bool.and_eq_true_iff.mp h_match with ⟨hf, hp_eq⟩
                                  have hp := eq_of_beq hp_eq; subst hp
                                  have hs1 : cartDegOriented H fuel deg refl s 1 = 7 :=
                                    h_fan 1 7 (eq_of_beq hf) (by decide)
                                  exact cartDegOriented_fan1_s1_eq_out_16_of_deg7 H darts h_all h_le refl s h5 hs1
                                | true =>
                                  rcases Bool.and_eq_true_iff.mp h_match with ⟨_, hp_eq⟩
                                  have hp := eq_of_beq hp_eq; subst hp
                                  exact cartDegOriented_fan2_s1_eq_out_refl_16 H fuel deg refl s h5
                              · simp only [beq_false_of_ne hz16, Bool.false_eq_true, ite_false] at h_match
  | true =>
    dsimp at h_match ⊢
    by_cases hz2 : z = 2
    · subst hz2; simp only [beq_self_eq_true, ite_true] at h_match
      cases inv with
      | false =>
        have hp := eq_of_beq h_match; subst hp
        exact cartDegOriented_deg_eq_in H darts h_all h_le refl s h_deg h5
      | true =>
        have hp := eq_of_beq h_match; subst hp
        rw [ruleVertexDart_refl_2]
        exact cartDegOriented_2_eq_in H fuel deg refl s h5
    · simp only [beq_false_of_ne hz2, Bool.false_eq_true, ite_false] at h_match
      by_cases hz3 : z = 3
      · subst hz3; simp only [beq_self_eq_true, ite_true] at h_match
        cases inv with
        | false =>
          have hp := eq_of_beq h_match; subst hp
          exact cartDegOriented_2_eq_in H fuel deg refl s h5
        | true =>
          have hp := eq_of_beq h_match; subst hp
          rw [ruleVertexDart_refl_3]
          exact cartDegOriented_deg_eq_in H darts h_all h_le refl s h_deg h5
      · simp only [beq_false_of_ne hz3, Bool.false_eq_true, ite_false] at h_match
        by_cases hz4 : z = 4
        · subst hz4; simp only [beq_self_eq_true, ite_true] at h_match
          cases inv with
          | false =>
            have hp := eq_of_beq h_match; subst hp
            exact cartDegOriented_two_mul_deg_eq_in H darts h_all h_le h_tri3 refl s h_deg h5
          | true =>
            have hp := eq_of_beq h_match; subst hp
            rw [ruleVertexDart_refl_4]
            exact cartDegOriented_deg_add_1_eq_in H fuel deg refl s h5
        · simp only [beq_false_of_ne hz4, Bool.false_eq_true, ite_false] at h_match
          by_cases hz5 : z = 5
          · subst hz5; simp only [beq_self_eq_true, ite_true] at h_match
            cases inv with
            | false =>
              have hp := eq_of_beq h_match; subst hp
              exact cartDegOriented_deg_add_1_eq_in H fuel deg refl s h5
            | true =>
              have hp := eq_of_beq h_match; subst hp
              rw [ruleVertexDart_refl_5]
              exact cartDegOriented_two_mul_deg_eq_in H darts h_all h_le h_tri3 refl s h_deg h5
          · simp only [beq_false_of_ne hz5, Bool.false_eq_true, ite_false] at h_match
            by_cases hz6 : z = 6
            · subst hz6; simp only [beq_self_eq_true, ite_true] at h_match
              cases inv with
              | false =>
                have hp := eq_of_beq h_match; subst hp
                exact cartDegOriented_deg_sub_1_eq_in H darts h_all h_le refl s h_deg h5
              | true =>
                have hp := eq_of_beq h_match; subst hp
                rw [ruleVertexDart_refl_6]
                exact cartDegOriented_3_eq_in H fuel deg refl s h5
            · simp only [beq_false_of_ne hz6, Bool.false_eq_true, ite_false] at h_match
              by_cases hz7 : z = 7
              · subst hz7; simp only [beq_self_eq_true, ite_true] at h_match
                cases inv with
                | false =>
                  have hp := eq_of_beq h_match; subst hp
                  exact cartDegOriented_3_eq_in H fuel deg refl s h5
                | true =>
                  have hp := eq_of_beq h_match; subst hp
                  rw [ruleVertexDart_refl_7]
                  exact cartDegOriented_deg_sub_1_eq_in H darts h_all h_le refl s h_deg h5
              · simp only [beq_false_of_ne hz7, Bool.false_eq_true, ite_false] at h_match
                by_cases hz8 : z = 8
                · subst hz8; simp only [beq_self_eq_true, ite_true] at h_match
                  cases inv with
                  | false =>
                    rcases Bool.or_eq_true_iff.mp h_match with h_c1 | h_c2
                    · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                      have hp := eq_of_beq hp_eq; subst hp
                      have hsd : cartDegOriented H fuel deg refl s deg = 5 :=
                        h_fan deg 5 (eq_of_beq hf) (by decide)
                      exact cartDegOriented_two_mul_deg_sub_1_eq_in_of_deg5 H darts h_all h_le h_tri3 refl s h_deg h5 hsd
                    · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨hf, hp_eq⟩
                      have hp := eq_of_beq hp_eq; subst hp
                      have hsd : cartDegOriented H fuel deg refl s deg = 6 :=
                        h_fan deg 6 (eq_of_beq hf) (by decide)
                      exact cartDegOriented_fan1_sdeg_eq_in_8_of_deg6 H darts h_all h_le h_tri3 refl s h_deg h5 hsd
                  | true =>
                    rw [ruleVertexDart_refl_8]
                    rcases Bool.or_eq_true_iff.mp h_match with h_c1 | h_c2
                    · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                      have hp := eq_of_beq hp_eq; subst hp
                      have hs2 : cartDegOriented H fuel deg refl s 2 = 5 :=
                        h_fan 2 5 (eq_of_beq hf) (by decide)
                      exact cartDegOriented_deg_add_2_eq_in_of_deg5 H darts h_all h_le h_tri3 refl s h5 hs2
                    · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨_, hp_eq⟩
                      have hp := eq_of_beq hp_eq; subst hp
                      exact cartDegOriented_fan1_s2_eq_in_9 H fuel deg h_tri3 refl s h5
                · simp only [beq_false_of_ne hz8, Bool.false_eq_true, ite_false] at h_match
                  by_cases hz9 : z = 9
                  · subst hz9; simp only [beq_self_eq_true, ite_true] at h_match
                    cases inv with
                    | false =>
                      rcases Bool.or_eq_true_iff.mp h_match with h_c1 | h_c2
                      · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                        have hp := eq_of_beq hp_eq; subst hp
                        have hs2 : cartDegOriented H fuel deg refl s 2 = 5 :=
                          h_fan 2 5 (eq_of_beq hf) (by decide)
                        exact cartDegOriented_deg_add_2_eq_in_of_deg5 H darts h_all h_le h_tri3 refl s h5 hs2
                      · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨_, hp_eq⟩
                        have hp := eq_of_beq hp_eq; subst hp
                        exact cartDegOriented_fan1_s2_eq_in_9 H fuel deg h_tri3 refl s h5
                    | true =>
                      rcases Bool.or_eq_true_iff.mp h_match with h_c12 | h_c3
                      · rcases Bool.or_eq_true_iff.mp h_c12 with h_c1 | h_c2
                        · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                          have hp := eq_of_beq hp_eq; subst hp
                          rw [ruleVertexDart_refl_9]
                          have hsd : cartDegOriented H fuel deg refl s deg = 5 :=
                            h_fan deg 5 (eq_of_beq hf) (by decide)
                          exact cartDegOriented_two_mul_deg_sub_1_eq_in_of_deg5 H darts h_all h_le h_tri3 refl s h_deg h5 hsd
                        · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨hf, hp_eq⟩
                          have hp := eq_of_beq hp_eq; subst hp
                          rw [ruleVertexDart_refl_9]
                          have hsd : cartDegOriented H fuel deg refl s deg = 6 :=
                            h_fan deg 6 (eq_of_beq hf) (by decide)
                          exact cartDegOriented_fan1_sdeg_eq_in_8_of_deg6 H darts h_all h_le h_tri3 refl s h_deg h5 hsd
                      · rcases Bool.and_eq_true_iff.mp h_c3 with ⟨hf, hp_eq⟩
                        have hp := eq_of_beq hp_eq; subst hp
                        have hsd : cartDegOriented H fuel deg refl s deg = 7 :=
                          h_fan deg 7 (eq_of_beq hf) (by decide)
                        exact cartDegOriented_fan2_sdeg_eq_in_refl_9_of_deg7 H darts h_all h_le h_tri3 refl s h_deg h5 hsd
                  · simp only [beq_false_of_ne hz9, Bool.false_eq_true, ite_false] at h_match
                    by_cases hz11 : z = 11
                    · subst hz11; simp only [beq_self_eq_true, ite_true] at h_match
                      cases inv with
                      | false =>
                        rcases Bool.or_eq_true_iff.mp h_match with h_c1 | h_c2
                        · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                          have hp := eq_of_beq hp_eq; subst hp
                          have hs2 : cartDegOriented H fuel deg refl s 2 = 6 :=
                            h_fan 2 6 (eq_of_beq hf) (by decide)
                          exact cartDegOriented_deg_add_2_eq_in_of_deg6 H darts h_all h_le h_tri3 refl s h5 hs2
                        · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨_, hp_eq⟩
                          have hp := eq_of_beq hp_eq; subst hp
                          exact cartDegOriented_fan2_s2_eq_in_11 H fuel deg h_tri3 refl s h5
                      | true =>
                        rcases Bool.or_eq_true_iff.mp h_match with h_c1 | h_c2
                        · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                          have hp := eq_of_beq hp_eq; subst hp
                          have hsd : cartDegOriented H fuel deg refl s deg = 6 :=
                            h_fan deg 6 (eq_of_beq hf) (by decide)
                          exact cartDegOriented_two_mul_deg_sub_1_eq_in_of_deg6 H darts h_all h_le h_tri3 refl s h_deg h5 hsd
                        · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨hf, hp_eq⟩
                          have hp := eq_of_beq hp_eq; subst hp
                          have hsd : cartDegOriented H fuel deg refl s deg = 7 :=
                            h_fan deg 7 (eq_of_beq hf) (by decide)
                          exact cartDegOriented_fan1_sdeg_eq_in_refl_11_of_deg7 H darts h_all h_le h_tri3 refl s h_deg h5 hsd
                    · simp only [beq_false_of_ne hz11, Bool.false_eq_true, ite_false] at h_match
                      by_cases hz12 : z = 12
                      · subst hz12; simp only [beq_self_eq_true, ite_true] at h_match
                        cases inv with
                        | false =>
                          have hp := eq_of_beq h_match; subst hp
                          exact cartDegOriented_fan1_s1_eq_in H fuel deg refl s h5
                        | true =>
                          rw [ruleVertexDart_refl_12]
                          rcases Bool.or_eq_true_iff.mp h_match with h_c1 | h_c2
                          · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                            have hp := eq_of_beq hp_eq; subst hp
                            have hs1 : cartDegOriented H fuel deg refl s 1 = 7 :=
                              h_fan 1 7 (eq_of_beq hf) (by decide)
                            exact cartDegOriented_fan2_s1_eq_in_14_of_deg7 H darts h_all h_le refl s h5 hs1
                          · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨hf, hp_eq⟩
                            have hp := eq_of_beq hp_eq; subst hp
                            have hs1 : cartDegOriented H fuel deg refl s 1 = 8 :=
                              h_fan 1 8 (eq_of_beq hf) (by decide)
                            exact cartDegOriented_fan3_s1_eq_in_14_of_deg8 H darts h_all h_le refl s h5 hs1
                      · simp only [beq_false_of_ne hz12, Bool.false_eq_true, ite_false] at h_match
                        by_cases hz13 : z = 13
                        · subst hz13; simp only [beq_self_eq_true, ite_true] at h_match
                          cases inv with
                          | false =>
                            have hp := eq_of_beq h_match; subst hp
                            exact cartDegOriented_fan2_s1_eq_in H fuel deg refl s h5
                          | true =>
                            rcases Bool.or_eq_true_iff.mp h_match with h_c1 | h_c2
                            · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                              have hp := eq_of_beq hp_eq; subst hp
                              have hs1 : cartDegOriented H fuel deg refl s 1 = 7 :=
                                h_fan 1 7 (eq_of_beq hf) (by decide)
                              exact cartDegOriented_fan1_s1_eq_in_refl_13_of_deg7 H darts h_all h_le refl s h5 hs1
                            · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨hf, hp_eq⟩
                              have hp := eq_of_beq hp_eq; subst hp
                              have hs1 : cartDegOriented H fuel deg refl s 1 = 8 :=
                                h_fan 1 8 (eq_of_beq hf) (by decide)
                              exact cartDegOriented_fan2_s1_eq_in_refl_13_of_deg8 H darts h_all h_le refl s h5 hs1
                        · simp only [beq_false_of_ne hz13, Bool.false_eq_true, ite_false] at h_match
                          by_cases hz14 : z = 14
                          · subst hz14; simp only [beq_self_eq_true, ite_true] at h_match
                            cases inv with
                            | false =>
                              rcases Bool.or_eq_true_iff.mp h_match with h_c1 | h_c2
                              · rcases Bool.and_eq_true_iff.mp h_c1 with ⟨hf, hp_eq⟩
                                have hp := eq_of_beq hp_eq; subst hp
                                have hs1 : cartDegOriented H fuel deg refl s 1 = 7 :=
                                  h_fan 1 7 (eq_of_beq hf) (by decide)
                                exact cartDegOriented_fan2_s1_eq_in_14_of_deg7 H darts h_all h_le refl s h5 hs1
                              · rcases Bool.and_eq_true_iff.mp h_c2 with ⟨hf, hp_eq⟩
                                have hp := eq_of_beq hp_eq; subst hp
                                have hs1 : cartDegOriented H fuel deg refl s 1 = 8 :=
                                  h_fan 1 8 (eq_of_beq hf) (by decide)
                                exact cartDegOriented_fan3_s1_eq_in_14_of_deg8 H darts h_all h_le refl s h5 hs1
                            | true =>
                              have hp := eq_of_beq h_match; subst hp
                              rw [ruleVertexDart_refl_14]
                              exact cartDegOriented_fan1_s1_eq_in H fuel deg refl s h5
                          · simp only [beq_false_of_ne hz14, Bool.false_eq_true, ite_false] at h_match
                            by_cases hz15 : z = 15
                            · subst hz15; simp only [beq_self_eq_true, ite_true] at h_match
                              cases inv with
                              | false =>
                                have hp := eq_of_beq h_match; subst hp
                                exact cartDegOriented_deg_sub_2_eq_in H darts h_all h_le refl s h_deg h5
                              | true =>
                                have hp := eq_of_beq h_match; subst hp
                                exact cartDegOriented_4_eq_in_refl H fuel deg refl s h5
                            · simp only [beq_false_of_ne hz15, Bool.false_eq_true, ite_false] at h_match
                              by_cases hz16 : z = 16
                              · subst hz16; simp only [beq_self_eq_true, ite_true] at h_match
                                cases inv with
                                | false =>
                                  have hp := eq_of_beq h_match; subst hp
                                  exact cartDegOriented_deg_sub_3_eq_in H darts h_all h_le refl s h_deg h5
                                | true =>
                                  have hp := eq_of_beq h_match; subst hp
                                  exact cartDegOriented_5_eq_in_refl H fuel deg refl s h5
                              · simp only [beq_false_of_ne hz16, Bool.false_eq_true, ite_false] at h_match

theorem degMatchesBound_normRSSTBound {bnd : Nat × Nat} (d : Nat)
    (h_val : validRSSTBound bnd = true) :
    degMatchesBound d (normRSSTBound bnd) = degMatchesBound d bnd := by
  dsimp [validRSSTBound, normRSSTBound, degMatchesBound] at h_val ⊢
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  change (decide (5 ≤ low) && decide (low ≤ 9) && (decide (upp ≤ 8) || decide (upp == 12))) = true at h_val
  rcases Bool.and_eq_true_iff.mp h_val with ⟨h_low, h_upp⟩
  rcases Bool.and_eq_true_iff.mp h_low with ⟨h_5, _⟩
  have h5_low : 5 ≤ low := of_decide_eq_true h_5
  have h_low_ne0 : (low == 0) = false := beq_false_of_ne (by omega)
  have h_upp_ne9 : (upp == 9) = false := by
    rcases Bool.or_eq_true_iff.mp h_upp with hu8 | hu12
    · have : upp ≤ 8 := of_decide_eq_true hu8
      exact beq_false_of_ne (by omega)
    · have : upp = 12 := eq_of_beq (of_decide_eq_true hu12)
      exact beq_false_of_ne (by omega)
  change (decide ((if low == 0 then if upp == 9 then 12 else upp else low) ≤ d) &&
          (decide ((if upp == 9 then 12 else upp) == 12) ||
           decide (d ≤ (if upp == 9 then 12 else upp)))) =
    (decide (low ≤ d) && (decide (upp == 12) || decide (d ≤ upp)))
  rw [h_low_ne0, h_upp_ne9]
  rfl

theorem degMatchesBound_hub_eq {bnd : Nat × Nat} {deg : Nat}
    (h_val : validRSSTBound bnd = true) (h_deg11 : deg ≤ 11) :
    (decide ((normRSSTBound bnd).1 ≤ deg) && decide (deg ≤ (normRSSTBound bnd).2)) =
      degMatchesBound deg bnd := by
  dsimp [validRSSTBound, normRSSTBound, degMatchesBound] at h_val ⊢
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  change (decide (5 ≤ low) && decide (low ≤ 9) && (decide (upp ≤ 8) || decide (upp == 12))) = true at h_val
  rcases Bool.and_eq_true_iff.mp h_val with ⟨_, h_upp⟩
  change (decide (low ≤ deg) && decide (deg ≤ upp)) =
    (decide (low ≤ deg) && (decide (upp == 12) || decide (deg ≤ upp)))
  congr 1
  rcases Bool.or_eq_true_iff.mp h_upp with hu8 | hu12
  · have : upp ≤ 8 := of_decide_eq_true hu8
    have h_ne12 : (upp == 12) = false := beq_false_of_ne (by omega)
    have h_d12 : decide ((upp == 12) = true) = false := decide_eq_false (by rw [h_ne12]; decide)
    rw [h_d12, Bool.false_or]
  · rw [hu12, Bool.true_or]
    have hu : upp = 12 := eq_of_beq (of_decide_eq_true hu12)
    exact decide_eq_true (by omega : deg ≤ upp)

theorem eq_of_degMatchesBound_exact {bnd : Nat × Nat} {d : Nat}
    (h_val : validRSSTBound bnd = true)
    (h_ex : ((normRSSTBound bnd).1 == (normRSSTBound bnd).2) = true)
    (h_m : degMatchesBound d (normRSSTBound bnd) = true) :
    d = (normRSSTBound bnd).1 := by
  rw [degMatchesBound_normRSSTBound d h_val] at h_m
  dsimp [validRSSTBound, normRSSTBound, degMatchesBound] at h_val h_ex h_m ⊢
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  change (decide (5 ≤ low) && decide (low ≤ 9) && (decide (upp ≤ 8) || decide (upp == 12))) = true at h_val
  change (low == upp) = true at h_ex
  have h_lu : low = upp := eq_of_beq h_ex
  rcases Bool.and_eq_true_iff.mp h_val with ⟨h_low, _⟩
  rcases Bool.and_eq_true_iff.mp h_low with ⟨_, h_low9⟩
  have h_le9 : low ≤ 9 := of_decide_eq_true h_low9
  have h_ne12 : (upp == 12) = false := beq_false_of_ne (by omega)
  have h_d12 : decide ((upp == 12) = true) = false := decide_eq_false (by rw [h_ne12]; decide)
  change (decide (low ≤ d) && (decide (upp == 12) || decide (d ≤ upp))) = true at h_m
  rcases Bool.and_eq_true_iff.mp h_m with ⟨h_ge, h_le_or⟩
  rw [h_d12, Bool.false_or] at h_le_or
  have hd_ge : low ≤ d := of_decide_eq_true h_ge
  have hd_le : d ≤ upp := of_decide_eq_true h_le_or
  change d = low
  omega

theorem fanDegInvariant_nil (cd : Nat → Nat) : FanDegInvariant cd [] := by
  intro i k h_lk hk
  dsimp [lookupFanDeg] at h_lk
  exact False.elim (hk h_lk.symm)

theorem fanDegInvariant_cons {cd : Nat → Nat} {fanDeg : List (Nat × Nat)} {pos_i k : Nat}
    (h_fan : FanDegInvariant cd fanDeg) (h_eq : cd pos_i = k) :
    FanDegInvariant cd ((pos_i, k) :: fanDeg) := by
  intro i m h_lk hm
  dsimp [lookupFanDeg] at h_lk
  cases h_pi : (pos_i == i) with
  | true =>
    rw [h_pi] at h_lk
    dsimp at h_lk
    have h_i : pos_i = i := eq_of_beq h_pi
    subst h_i h_lk
    exact h_eq
  | false =>
    rw [h_pi] at h_lk
    dsimp at h_lk
    exact h_fan i m h_lk hm

/-- Inductive soundness of `compileRuleTriples` at spoke `1`:
    when `validTriplesCompilation deg isPos inv triples phi fanDeg = true` and `FanDegInvariant` holds,
    evaluating `(compileRuleTriples deg 1 inv triples phi fanDeg).all` on `cartDegOriented H fuel deg refl s`
    equals evaluating `triples.all` on `ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s)`. -/
theorem compileRuleTriples_sound (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl isPos inv : Bool) (s : H.Dart)
    (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg)
    (triples : List (Nat × (Nat × Nat))) :
    ∀ (phi fanDeg : List (Nat × Nat)),
      FanDegInvariant (cartDegOriented H fuel deg refl s) fanDeg →
      validTriplesCompilation deg isPos inv triples phi fanDeg = true →
      (compileRuleTriples deg 1 inv triples phi fanDeg).all
        (fun c => degMatchesBound (cartDegOriented H fuel deg refl s c.1) c.2) =
      triples.all (fun p =>
        degMatchesBound
          (Hypermap.nodeDegree H
            (ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s) p.1) fuel)
          p.2) := by
  induction triples with
  | nil =>
    intro _ _ _ _
    rfl
  | cons head rest ih =>
    rcases head with ⟨z, bnd⟩
    intro phi fanDeg h_fan h_val
    dsimp [validTriplesCompilation] at h_val
    rcases Bool.and_eq_true_iff.mp h_val with ⟨h123, h_rest_val⟩
    rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, h_val_bnd⟩
    rcases Bool.and_eq_true_iff.mp h12 with ⟨hp_eq_b, h_coord⟩
    let nb := normRSSTBound bnd
    let u := lookupPhi (if inv then ruleV z else ruleU z) phi
    let v := lookupPhi (if inv then ruleU z else ruleV z) phi
    let pos_i := pureCartAdj deg fanDeg u v
    let p := shiftCartPos deg 0 pos_i
    have hp_eq : p = pos_i := eq_of_beq hp_eq_b
    have h_deg_eq : cartDegOriented H fuel deg refl s p =
        Hypermap.nodeDegree H
          (ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s) z) fuel :=
      validCoordMatch_sound H darts h_all h_le h_tri3 refl isPos inv s fanDeg z p h_deg h5 h_fan h_coord
    have h_head_eq : degMatchesBound (cartDegOriented H fuel deg refl s p) nb =
        degMatchesBound
          (Hypermap.nodeDegree H
            (ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s) z) fuel)
          bnd := by
      rw [degMatchesBound_normRSSTBound _ h_val_bnd, h_deg_eq]
    dsimp [compileRuleTriples, List.all]
    change (degMatchesBound (cartDegOriented H fuel deg refl s p) nb &&
            (compileRuleTriples deg 1 inv rest ((z, pos_i) :: phi)
              (if pos_i ≤ deg && nb.1 == nb.2 then (pos_i, nb.1) :: fanDeg else fanDeg)).all
              (fun c => degMatchesBound (cartDegOriented H fuel deg refl s c.1) c.2)) =
      (degMatchesBound
          (Hypermap.nodeDegree H
            (ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s) z) fuel)
          bnd &&
        rest.all (fun q =>
          degMatchesBound
            (Hypermap.nodeDegree H
              (ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s) q.1) fuel)
            q.2))
    rw [← h_head_eq]
    cases h_cur : degMatchesBound (cartDegOriented H fuel deg refl s p) nb with
    | false => rfl
    | true =>
      rw [Bool.true_and, Bool.true_and]
      have h_fan' : FanDegInvariant (cartDegOriented H fuel deg refl s)
          (if pos_i ≤ deg && nb.1 == nb.2 then (pos_i, nb.1) :: fanDeg else fanDeg) := by
        cases h_cond : (decide (pos_i ≤ deg) && (nb.1 == nb.2)) with
        | false =>
          dsimp
          exact h_fan
        | true =>
          dsimp
          rcases Bool.and_eq_true_iff.mp h_cond with ⟨_, h_ex⟩
          have h_cd_p := eq_of_degMatchesBound_exact h_val_bnd h_ex h_cur
          rw [hp_eq] at h_cd_p
          exact fanDegInvariant_cons h_fan h_cd_p
      exact ih ((z, pos_i) :: phi) _ h_fan' h_rest_val

/-- Activation of an optional compiled outlet (`false` if `none`). -/
def compiledSingleOutletActive (cd : Nat → Nat) :
    Option (Bool × List (Nat × (Nat × Nat))) → Bool
  | some co => compiledOutletActive cd co
  | none => false

/-- Soundness of `compileRuleOutlet deg 1 isPos inv r`:
    when `validRuleOutletCompilation deg isPos inv r = true`, `compiledSingleOutletActive`
    on `cartDegOriented H fuel deg refl s` equals `matchesRawRule H fuel (if inv then refl else !refl) (if isPos then H.edge.f s else s) r`. -/
theorem compileRuleOutlet_sound (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl isPos inv : Bool) (s : H.Dart) (r : RawRule)
    (h_deg : Hypermap.nodeDegree H s fuel = deg) (h5 : 5 ≤ deg) (h11 : deg ≤ 11)
    (h_val : validRuleOutletCompilation deg isPos inv r = true) :
    compiledSingleOutletActive (cartDegOriented H fuel deg refl s)
      (compileRuleOutlet deg 1 isPos inv r) =
    matchesRawRule H fuel (if inv then refl else !refl) (if isPos then H.edge.f s else s) r := by
  dsimp [validRuleOutletCompilation] at h_val
  rcases Bool.and_eq_true_iff.mp h_val with ⟨h_b01, h_if⟩
  rcases Bool.and_eq_true_iff.mp h_b01 with ⟨h_vb0, h_vb1⟩
  let bHub_raw := if isPos then r.b1 else r.b0
  let bSpk_raw := if isPos then r.b0 else r.b1
  let bHub := normRSSTBound bHub_raw
  let bSpk := normRSSTBound bSpk_raw
  have h_vHub : validRSSTBound bHub_raw = true := by cases isPos <;> assumption
  have h_vSpk : validRSSTBound bSpk_raw = true := by cases isPos <;> assumption
  have h_hub_cond : (decide (bHub.1 ≤ deg) && decide (deg ≤ bHub.2)) =
      degMatchesBound deg bHub_raw :=
    degMatchesBound_hub_eq h_vHub h11
  dsimp [compileRuleOutlet]
  change compiledSingleOutletActive (cartDegOriented H fuel deg refl s)
      (if (decide (bHub.1 ≤ deg) && decide (deg ≤ bHub.2)) = true then
        some (isPos, (shiftCartPos deg 0 1, bSpk) ::
          compileRuleTriples deg 1 inv r.triples
            (if isPos then [(0, 1), (1, 0)] else [(0, 0), (1, 1)])
            (if bSpk.1 == bSpk.2 then [(1, bSpk.1)] else []))
       else none) =
    matchesRawRule H fuel (if inv then refl else !refl) (if isPos then H.edge.f s else s) r
  have h_matches_reord :
      matchesRawRule H fuel (if inv then refl else !refl) (if isPos then H.edge.f s else s) r =
      (degMatchesBound deg bHub_raw &&
       (degMatchesBound (Hypermap.nodeDegree H (H.edge.f s) fuel) bSpk_raw &&
        r.triples.all (fun p =>
          degMatchesBound
            (Hypermap.nodeDegree H
              (ruleVertexDart H (if inv then refl else !refl) (if isPos then H.edge.f s else s) p.1) fuel)
            p.2))) := by
    dsimp [matchesRawRule, bHub_raw, bSpk_raw]; rvd_simp
    cases isPos with
    | false =>
      dsimp; rvd_simp
      rw [h_deg, Bool.and_assoc]
    | true =>
      dsimp; rvd_simp
      rw [H.edge_involution, h_deg]
      cases degMatchesBound (Hypermap.nodeDegree H (H.edge.f s) fuel) r.b0 <;>
        cases degMatchesBound deg r.b1 <;> rfl
  rw [h_matches_reord]
  cases h_hub : (decide (bHub.1 ≤ deg) && decide (deg ≤ bHub.2)) with
  | false =>
    have h_m_false : degMatchesBound deg bHub_raw = false := by
      rw [← h_hub_cond]; exact h_hub
    rw [h_m_false]
    rfl
  | true =>
    have h_m_true : degMatchesBound deg bHub_raw = true := by
      rw [← h_hub_cond]; exact h_hub
    rw [h_hub] at h_if
    dsimp at h_if ⊢
    rw [h_m_true, Bool.true_and]
    rcases Bool.and_eq_true_iff.mp h_if with ⟨h_sh1, h_triples_val⟩
    have h_sh1_eq : shiftCartPos deg 0 1 = 1 := eq_of_beq h_sh1
    dsimp [compiledSingleOutletActive, compiledOutletActive, List.all]
    rw [h_sh1_eq, degMatchesBound_normRSSTBound _ h_vSpk,
        cartDegOriented_1_eq H fuel deg refl s h5]
    cases h_spk : degMatchesBound (Hypermap.nodeDegree H (H.edge.f s) fuel) bSpk_raw with
    | false => rfl
    | true =>
      rw [Bool.true_and, Bool.true_and]
      have h_fan0 : FanDegInvariant (cartDegOriented H fuel deg refl s)
          (if bSpk.1 == bSpk.2 then [(1, bSpk.1)] else []) := by
        cases h_ex : (bSpk.1 == bSpk.2) with
        | false =>
          dsimp
          exact fanDegInvariant_nil _
        | true =>
          dsimp
          have h_s1_m : degMatchesBound (cartDegOriented H fuel deg refl s 1) bSpk = true := by
            rw [degMatchesBound_normRSSTBound _ h_vSpk, cartDegOriented_1_eq H fuel deg refl s h5]
            exact h_spk
          have h_s1_eq := eq_of_degMatchesBound_exact h_vSpk h_ex h_s1_m
          exact fanDegInvariant_cons (fanDegInvariant_nil _) h_s1_eq
      exact compileRuleTriples_sound H darts h_all h_le h_tri3 refl isPos inv s h_deg h5
        r.triples _ _ h_fan0 h_triples_val

theorem compiledOutletsSum_append (cd : Nat → Nat)
    (l1 l2 : List (Bool × List (Nat × (Nat × Nat)))) :
    compiledOutletsSum cd (l1 ++ l2) =
      compiledOutletsSum cd l1 + compiledOutletsSum cd l2 := by
  induction l1 with
  | nil =>
    dsimp [List.append, compiledOutletsSum]
    omega
  | cons a rest ih =>
    dsimp [List.append, compiledOutletsSum]
    rw [ih]
    omega

theorem compiledOutletsSum_compileRuleOutlet (cd : Nat → Nat)
    (deg x : Nat) (isPos inv : Bool) (r : RawRule) :
    compiledOutletsSum cd
      (match compileRuleOutlet deg x isPos inv r with | some o => [o] | none => []) =
    if compiledSingleOutletActive cd (compileRuleOutlet deg x isPos inv r) then
      (if isPos then 1 else -1)
    else 0 := by
  cases h_cond : (decide ((normRSSTBound (if isPos then r.b1 else r.b0)).1 ≤ deg) &&
      decide (deg ≤ (normRSSTBound (if isPos then r.b1 else r.b0)).2)) with
  | false =>
    simp [compileRuleOutlet, h_cond, compiledOutletsSum, compiledSingleOutletActive]
  | true =>
    simp [compileRuleOutlet, h_cond, compiledOutletsSum, compiledSingleOutletActive]

/-- Per-Rule Spoke-1 Equivalence (Degrees 7–11):
    for any `r ∈ theRules` and spoke dart `s` with `Hypermap.nodeDegree H s fuel = deg` (`deg ∈ 7..11`),
    `compiledOutletsSum (cartDegOriented H fuel deg refl s) (compileRuleAllOutlets deg 1 r)`
    equals `rawRuleOutflow H fuel (H.edge.f s) r - rawRuleOutflow H fuel s r`. -/
theorem compiledRuleAllOutlets_spoke1_eq_rawRuleShift (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl : Bool) (s : H.Dart) (r : RawRule)
    (h_deg : Hypermap.nodeDegree H s fuel = deg)
    (h_deg_range : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11)
    (hr : r ∈ theRules) :
    compiledOutletsSum (cartDegOriented H fuel deg refl s) (compileRuleAllOutlets deg 1 r) =
      rawRuleOutflow H fuel (H.edge.f s) r - rawRuleOutflow H fuel s r := by
  have h5 : 5 ≤ deg := by rcases h_deg_range with rfl | rfl | rfl | rfl | rfl <;> omega
  have h11 : deg ≤ 11 := by rcases h_deg_range with rfl | rfl | rfl | rfl | rfl <;> omega
  have h_all_comp := validAllRulesCompilation_of_deg deg h_deg_range
  have h_r_comp := List.all_eq_true.mp h_all_comp r hr
  rcases Bool.and_eq_true_iff.mp h_r_comp with ⟨h123, h_ff_t⟩
  rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, h_tf⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨h_tf_f, h_ff_f⟩
  have h_s1 := compileRuleOutlet_sound H darts h_all h_le h_tri3 refl true false s r h_deg h5 h11 h_tf_f
  have h_s2 := compileRuleOutlet_sound H darts h_all h_le h_tri3 refl false false s r h_deg h5 h11 h_ff_f
  have h_s3 := compileRuleOutlet_sound H darts h_all h_le h_tri3 refl true true s r h_deg h5 h11 h_tf
  have h_s4 := compileRuleOutlet_sound H darts h_all h_le h_tri3 refl false true s r h_deg h5 h11 h_ff_t
  dsimp at h_s1 h_s2 h_s3 h_s4
  rw [rawRuleOutflow_eq_oriented H fuel refl (H.edge.f s) r hr,
      rawRuleOutflow_eq_oriented H fuel refl s r hr]
  unfold compileRuleAllOutlets
  rw [compiledOutletsSum_append, compiledOutletsSum_append,
      compiledOutletsSum_compileRuleOutlet _ deg 1 true false r,
      compiledOutletsSum_compileRuleOutlet _ deg 1 false false r,
      h_s1, h_s2]
  cases h_inv : r.invert with
  | false =>
    dsimp [compiledOutletsSum]
    cases matchesRawRule H fuel (!refl) (H.edge.f s) r <;>
      cases matchesRawRule H fuel (!refl) s r <;> rfl
  | true =>
    dsimp
    rw [compiledOutletsSum_append,
        compiledOutletsSum_compileRuleOutlet _ deg 1 true true r,
        compiledOutletsSum_compileRuleOutlet _ deg 1 false true r,
        h_s3, h_s4]
    cases matchesRawRule H fuel (!refl) (H.edge.f s) r <;>
      cases matchesRawRule H fuel (!refl) s r <;>
      cases matchesRawRule H fuel refl (H.edge.f s) r <;>
      cases matchesRawRule H fuel refl s r <;> rfl

theorem compiledOutletsSum_foldr_append (cd : Nat → Nat) (deg x : Nat) (rs : List RawRule) :
    compiledOutletsSum cd (rs.foldr (fun r acc => compileRuleAllOutlets deg x r ++ acc) []) =
      rs.foldl (fun acc r => acc + compiledOutletsSum cd (compileRuleAllOutlets deg x r)) 0 := by
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    rw [List.foldr_cons, foldl_add_cons, compiledOutletsSum_append, ih]

/-- Master Spoke-1 Rule-to-Hypermap Equivalence (Degrees 7–11):
    for any spoke dart `s` with `Hypermap.nodeDegree H s fuel = deg` (`deg ∈ {7, 8, 9, 10, 11}`)
    on a complete triangulated hypermap `H`,
    `compiledOutletsSum (cartDegOriented H fuel deg refl s) (compiledOutletsForSpoke deg 1)`
    equals `netDartShift H fuel s`. -/
theorem compiledOutletsSum_spoke1_eq_netDartShift (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    (refl : Bool) (s : H.Dart)
    (h_deg : Hypermap.nodeDegree H s fuel = deg)
    (h_deg_range : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    compiledOutletsSum (cartDegOriented H fuel deg refl s) (compiledOutletsForSpoke deg 1) =
      netDartShift H fuel s := by
  have h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x :=
    fun x => face_f_three_of_faceDegree_eq_three H darts h_all h_le (h_tri x (h_all x))
  unfold compiledOutletsForSpoke
  rw [compiledOutletsSum_foldr_append]
  dsimp [netDartShift, dartRuleOutflow]
  rw [← foldl_add_sub]
  apply foldl_add_congr
  intro r hr
  exact compiledRuleAllOutlets_spoke1_eq_rawRuleShift H darts h_all h_le h_tri3 refl s r h_deg h_deg_range hr

-- ============================================================================
-- Stage O.3: Degree 7–11 Real-Hypermap Discharging Dichotomy (`H` and `H.dual`)
-- ============================================================================

/-- Exact Spoke-to-Dart Equivalence for `activeOutletSum` (Degrees 7–11):
    for any hub `u` of degree `deg ∈ {7, 8, 9, 10, 11}`, any oriented hub dart
    `d0 ∈ getOrbit H.node fuel u`, and any spoke index `1 ≤ x ≤ deg` (with cartwheel degrees `≥ 5`),
    `activeOutletSum deg (cartDegOriented H fuel deg refl d0) (lookupListRec [] (getShiftedTableForDeg deg) x)`
    equals `netDartShift H fuel (spokeDartOriented H refl d0 x)`. -/
theorem activeOutletSum_spoke_eq_netDartShift (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    {u d0 : H.Dart} (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (x : Nat)
    (h_deg_range : Hypermap.nodeDegree H u fuel = 7 ∨
                   Hypermap.nodeDegree H u fuel = 8 ∨
                   Hypermap.nodeDegree H u fuel = 9 ∨
                   Hypermap.nodeDegree H u fuel = 10 ∨
                   Hypermap.nodeDegree H u fuel = 11)
    (hx1 : 1 ≤ x) (hx2 : x ≤ Hypermap.nodeDegree H u fuel)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * Hypermap.nodeDegree H u fuel →
      5 ≤ cartDegOriented H fuel (Hypermap.nodeDegree H u fuel) refl d0 p) :
    let deg := Hypermap.nodeDegree H u fuel
    activeOutletSum deg (cartDegOriented H fuel deg refl d0)
      (lookupListRec [] (getShiftedTableForDeg deg) x) =
    netDartShift H fuel (spokeDartOriented H refl d0 x) := by
  intro deg
  rw [activeOutletSum_eq_compiledOutletsSum deg x
        (cartDegOriented H fuel deg refl d0) h_deg_range hx1 hx2 h_min5,
      compiledOutletsSum_spoke_eq_spoke1 H darts h_all h_le hd0 refl x h_deg_range hx1 hx2]
  have hsx_mem : spokeDartOriented H refl d0 x ∈ getOrbit H.node fuel u :=
    spokeDartOriented_mem_getOrbit_of_complete H darts h_all h_le hd0 refl x
  have hsx_deg : Hypermap.nodeDegree H (spokeDartOriented H refl d0 x) fuel = deg :=
    nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hsx_mem
  exact compiledOutletsSum_spoke1_eq_netDartShift H darts h_all h_le h_tri refl
    (spokeDartOriented H refl d0 x) hsx_deg h_deg_range

/-- Total Spoke-Sum Equivalence for `orbitNetShift` (Degrees 7–11):
    summing `activeOutletSum` across all spokes `x ∈ 1..deg` around any `(d0, refl)`
    with `d0 ∈ getOrbit H.node fuel u` equals `orbitNetShift H fuel u`. -/
theorem activeOutletSum_hub_foldl_eq_orbitNetShift (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    {u d0 : H.Dart} (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool)
    (h_deg_range : Hypermap.nodeDegree H u fuel = 7 ∨
                   Hypermap.nodeDegree H u fuel = 8 ∨
                   Hypermap.nodeDegree H u fuel = 9 ∨
                   Hypermap.nodeDegree H u fuel = 10 ∨
                   Hypermap.nodeDegree H u fuel = 11)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * Hypermap.nodeDegree H u fuel →
      5 ≤ cartDegOriented H fuel (Hypermap.nodeDegree H u fuel) refl d0 p) :
    let deg := Hypermap.nodeDegree H u fuel
    (List.range' 1 deg).foldl
      (fun acc x => acc + activeOutletSum deg (cartDegOriented H fuel deg refl d0)
        (lookupListRec [] (getShiftedTableForDeg deg) x)) 0 =
    orbitNetShift H fuel u := by
  intro deg
  rw [orbitNetShift_eq_spokeDartOriented_foldl H darts h_all h_le hd0 refl]
  apply foldl_add_congr
  intro x hx
  rcases List.mem_range'.mp hx with ⟨j, hj, h_xj⟩
  exact activeOutletSum_spoke_eq_netDartShift H darts h_all h_le h_tri hd0 refl x
    h_deg_range (by omega) (by omega) h_min5

/-- Master Degree 7–11 Real-Hypermap Discharging Dichotomy Theorem:
    on any complete triangulated hypermap `H` with minimum vertex degree `≥ 5` and loopless hub `u`
    of degree `deg ∈ {7, 8, 9, 10, 11}`, if `DischargingTreesVerified configs` holds, then either:
    1. `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`, OR
    2. `u` admits an exact reduced RSST configuration `HasExactReducedAxle deg (cartDegOriented H fuel deg refl d0)`
       at some real oriented hub dart `d0 ∈ getOrbit H.node fuel u` and `refl : Bool`. -/
theorem finalCharge_le_zero_or_hasExactReducedAxle_deg_7_to_11 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    (h_min5 : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree H d fuel)
    (configs : List Configuration) (h_trees : DischargingTreesVerified configs)
    (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg_range : Hypermap.nodeDegree H u fuel = 7 ∨
                   Hypermap.nodeDegree H u fuel = 8 ∨
                   Hypermap.nodeDegree H u fuel = 9 ∨
                   Hypermap.nodeDegree H u fuel = 10 ∨
                   Hypermap.nodeDegree H u fuel = 11) :
    let deg := Hypermap.nodeDegree H u fuel
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 ∨
      ∃ d0 ∈ getOrbit H.node fuel u, ∃ refl : Bool,
        HasExactReducedAxle deg (cartDegOriented H fuel deg refl d0) := by
  intro deg
  rcases dischargingTreesVerified_hypermap_core_soundness H darts h_all h_le h_tri configs h_trees u h_deg_range
    with ⟨d0, hd0, refl, h_core⟩
  rcases coreCartLeaf_reducible_or_hub_sum_le_zero deg (getShiftedTableForDeg deg)
      (cartDegOriented H fuel deg refl d0) h_core with h_red | h_sum_le
  · exact Or.inr ⟨d0, hd0, refl, h_red⟩
  · left
    have h_cart_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cartDegOriented H fuel deg refl d0 p := by
      intro p _ _
      exact h_min5 _ (h_all _)
    rw [activeOutletSum_hub_foldl_eq_orbitNetShift H darts h_all h_le h_tri hd0 refl h_deg_range h_cart_min5] at h_sum_le
    rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
    exact h_sum_le

/-- Dual Master Degree 7–11 Discharging Dichotomy Theorem on `H.dual`:
    on any complete, bridgeless, cubic hypermap `H` whose faces all have degree `≥ 5`,
    if `DischargingTreesVerified configs` holds, then every dual vertex (face) `u` of degree `deg ∈ {7, 8, 9, 10, 11}`
    either satisfies `finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0` or admits an exact
    reduced RSST configuration `HasExactReducedAxle deg (cartDegOriented H.dual fuel deg refl d0)`
    at some `d0 ∈ getOrbit H.dual.node fuel u` and `refl : Bool`. -/
theorem dual_finalCharge_le_zero_or_hasExactReducedAxle_deg_7_to_11 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b)
    (h_cubic : ∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3)
    (h_min5 : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree H.dual d fuel)
    (configs : List Configuration) (h_trees : DischargingTreesVerified configs)
    (u : H.Dart)
    (h_deg_range : Hypermap.nodeDegree H.dual u fuel = 7 ∨
                   Hypermap.nodeDegree H.dual u fuel = 8 ∨
                   Hypermap.nodeDegree H.dual u fuel = 9 ∨
                   Hypermap.nodeDegree H.dual u fuel = 10 ∨
                   Hypermap.nodeDegree H.dual u fuel = 11) :
    let deg := Hypermap.nodeDegree H.dual u fuel
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 ∨
      ∃ d0 ∈ getOrbit H.dual.node fuel u, ∃ refl : Bool,
        HasExactReducedAxle deg (cartDegOriented H.dual fuel deg refl d0) := by
  have h_tri_dual : ∀ d ∈ darts, Hypermap.faceDegree H.dual d fuel = 3 :=
    (dual_triangulation_iff_cubic H darts h_all h_le).mpr h_cubic
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_or_hasExactReducedAxle_deg_7_to_11 H.dual darts h_all h_le
    h_tri_dual h_min5 configs h_trees u h_loopless h_deg_range

end Discharging
end Math
