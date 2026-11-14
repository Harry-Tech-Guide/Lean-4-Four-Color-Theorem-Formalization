/-
Stage P.2: All-Degrees Discharging Soundness (RSST 4.5, 4.6, 4.7, 4.8 & Euler-120 Unavoidability).

Combines the verified `deg = 5` and `deg = 6` discharging proof trees and RSST (4.8) outflow
bounds (`Deg56Trees`) with the degree `7..11` certificates (`DischargeMaster`) and analytical
high-degree bounds (`12 ≤ deg ≤ 19`, `20 ≤ deg`) to prove unconditionally (with zero axioms and
zero `DischargingTreesVerified` hypotheses) that every complete planar triangulation of minimum
degree ≥ 5 (and the dual `H.dual` of any bridgeless cubic planar 5-edge-connected map `H`)
contains a vertex hub whose oriented cartwheel degree table admits `HasExactReducedAxle`.
-/
import FourColorTheorem.Math.Discharging
import FourColorTheorem.Math.Batch.DischargeMaster
import FourColorTheorem.Math.Unavoidability.HintBounds
import FourColorTheorem.Math.Unavoidability.Deg56Trees

namespace Math.Unavoidability

open Math.Discharging

/-!
### 1. Bitmask State Initialization & Sym-Tree Family Soundness
-/

private theorem all31Nat_lanes_eq_31 :
    (List.range' 1 55).all (fun p => getLaneNat all31Nat p == 31) = true := by
  decide

private theorem getLaneNat_all31Nat_eq_31 {p : Nat} (hp1 : 1 ≤ p) (hp55 : p ≤ 55) :
    getLaneNat all31Nat p = 31 := by
  have hmem : p ∈ List.range' 1 55 := List.mem_range'.mpr ⟨p - 1, by omega, by omega⟩
  exact eq_of_beq (List.all_eq_true.mp all31Nat_lanes_eq_31 p hmem)

private theorem testBit_31_degBitIdx (d : Nat) :
    (31 : Nat).testBit (degBitIdx d) = true := by
  unfold degBitIdx
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split <;> decide

private theorem degBitIdx_eq_4_of_ge_9 {d : Nat} (hd : 9 ≤ d) :
    degBitIdx d = 4 := by
  unfold degBitIdx
  have h5 : ¬ (d ≤ 5) := by omega
  have h6 : (d == 6) = false := beq_false_of_ne (by omega)
  have h7 : (d == 7) = false := beq_false_of_ne (by omega)
  have h8 : (d == 8) = false := beq_false_of_ne (by omega)
  simp [h5, h6, h7, h8]

theorem matchesCartState31_initStateDeg {deg : Nat} (h11 : deg ≤ 11) (cd : Nat → Nat) :
    MatchesCartState31 deg cd (initStateDeg deg) := by
  constructor
  · intro p hp1 hp2
    have hlt60 : p < 60 := by omega
    have hne0 : p ≠ 0 := by omega
    have hlane : getLaneNat (initStateDeg deg) p = 31 := by
      unfold initStateDeg
      rw [getLaneNat_setLaneNat_ne all31Nat 0 (1 <<< (deg - 5)) p hlt60 hne0]
      exact getLaneNat_all31Nat_eq_31 hp1 (by omega)
    rw [hlane]
    exact testBit_31_degBitIdx (cd p)
  · intro p hp1 hp2
    have hlt60 : p < 60 := by omega
    have hne0 : p ≠ 0 := by omega
    unfold initStateDeg
    rw [getLaneNat_setLaneNat_ne all31Nat 0 (1 <<< (deg - 5)) p hlt60 hne0,
        getLaneNat_all31Nat_eq_31 hp1 (by omega)]
    decide

private theorem stGe12Deg_lane1_all :
    (List.range 12).all (fun d => getLaneNat (stGe12Deg d) 1 == 16) = true := by
  decide

theorem matchesCartState31_stGe12Deg {deg : Nat} (h11 : deg ≤ 11) (cd : Nat → Nat)
    (h_cd1 : 9 ≤ cd 1) :
    MatchesCartState31 deg cd (stGe12Deg deg) := by
  have hlane1 : getLaneNat (stGe12Deg deg) 1 = 16 :=
    eq_of_beq (List.all_eq_true.mp stGe12Deg_lane1_all deg (List.mem_range.mpr (by omega)))
  constructor
  · intro p hp1 hp2
    by_cases hp_eq : p = 1
    · subst hp_eq
      rw [hlane1, degBitIdx_eq_4_of_ge_9 h_cd1]
      decide
    · have hlt60 : p < 60 := by omega
      have hne0 : p ≠ 0 := by omega
      have hlane : getLaneNat (stGe12Deg deg) p = 31 := by
        unfold stGe12Deg initStateDeg
        rw [getLaneNat_setLaneNat_ne (setLaneNat all31Nat 0 (1 <<< (deg - 5))) 1 16 p hlt60 hp_eq,
            getLaneNat_setLaneNat_ne all31Nat 0 (1 <<< (deg - 5)) p hlt60 hne0]
        exact getLaneNat_all31Nat_eq_31 hp1 (by omega)
      rw [hlane]
      exact testBit_31_degBitIdx (cd p)
  · intro p hp1 hp2
    by_cases hp_eq : p = 1
    · subst hp_eq; rw [hlane1]; decide
    · have hlt60 : p < 60 := by omega
      have hne0 : p ≠ 0 := by omega
      unfold stGe12Deg initStateDeg
      rw [getLaneNat_setLaneNat_ne (setLaneNat all31Nat 0 (1 <<< (deg - 5))) 1 16 p hlt60 hp_eq,
          getLaneNat_setLaneNat_ne all31Nat 0 (1 <<< (deg - 5)) p hlt60 hne0,
          getLaneNat_all31Nat_eq_31 hp1 (by omega)]
      decide

/-- Family-level soundness of any pure `verifyTreePureRec` proof tree (`1 ≤ deg ≤ 11`)
    over any `DihedralClosedFamily deg ℱ`. -/
theorem verifyTreePureRec_family_core_soundness
    (deg : Nat) (shiftedTable : List (List FastPosOut))
    (ℱ : (Nat → Nat) → Prop) (h_fam : DihedralClosedFamily deg ℱ)
    (t : ProofTree) (maxLev : Nat) (hs : HintStream)
    (h1 : 1 ≤ deg) (h11 : deg ≤ 11)
    (h_val : ∀ row ∈ shiftedTable, ∀ po ∈ row, validFastPosOut deg po = true)
    (h_tree : validProofTree deg maxLev t = true) (h_lev : maxLev < 60)
    (h_hs : validHintStream hs = true)
    (h_ver : (verifyTreePureRec deg shiftedTable t (initStateDeg deg) 2 0 0 0 [] hs).1 = true)
    {cd0 : Nat → Nat} (hcd0 : ℱ cd0) :
    ∃ cd, ℱ cd ∧ CoreCartLeaf deg shiftedTable cd := by
  let P : (Nat → Nat) → Prop := fun cd =>
    ℱ cd → ∃ cd', ℱ cd' ∧ CoreCartLeaf deg shiftedTable cd'
  have hP := verifyTreePureRec_sound_of_pred deg shiftedTable P h1 h11 h_val
    (fun cd h_leaf hF => ⟨cd, hF, h_leaf⟩)
    (fun cd k refl conds hk hbnds h_sym_cond h_rec hF => by
      rcases h_fam cd k refl hk hF with ⟨cd', hF', h_agree⟩
      have h_conds' : ∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true := by
        intro c hc
        have ⟨hc1, hc2⟩ := hbnds c hc
        rw [h_agree c.1 hc1 hc2]
        exact h_sym_cond c hc
      exact h_rec cd' h_conds' hF')
    t maxLev (initStateDeg deg) 2 0 0 0 [] hs
    h_tree (by omega)
    (fun o hmem => by contradiction)
    (fun conds h_ext => by
      unfold extractCondsRec at h_ext
      contradiction)
    (fun cd' _ => Or.inr (matchesCartState31_initStateDeg h11 cd'))
    h_hs h_ver cd0
    (fun i hi => by omega)
  exact hP hcd0

/-!
### 2. Degree `5` and `6` Compiled-Outlet Soundness & Orbit Net Shift Identity
-/

theorem cartDegOriented_fan1_s2_eq_out_refl_11_of_deg6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (refl : Bool) (s : H.Dart) (h5 : 5 ≤ deg)
    (h_s2 : cartDegOriented H fuel deg refl s 2 = 6) :
    cartDegOriented H fuel deg refl s (2 * deg + 2) =
      Hypermap.nodeDegree H (ruleVertexDart H refl s 11) fuel := by
  have hs2_deg : Hypermap.nodeDegree H (H.edge.f (ruleRotInv H (!refl) s)) fuel = 6 := by
    have h_eq : H.edge.f (ruleRotInv H (!refl) s) = ruleVertexDart H (!refl) (H.edge.f s) 3 := by
      dsimp [ruleVertexDart]
      rw [H.edge_involution]
    rw [h_eq, ← cartDegOriented_2_eq_in H fuel deg refl s h5]
    exact h_s2
  dsimp [cartDegOriented]
  rw [cartDartOriented_fan1 H deg refl s (by omega) (by omega), spokeDartOriented_2,
      ruleVertexDart_refl_11]
  dsimp [ruleVertexDart]
  rw [fan_deg6_rotInv3_eq_rot3 H darts h_all h_le refl (H.edge.f (ruleRotInv H (!refl) s)) hs2_deg]

private theorem validRuleOutletCompilation_5_all :
    (theRules.all fun r =>
      ([true, false].all fun isPos =>
        ([true, false].all fun inv =>
          validRuleOutletCompilation 5 isPos inv r))) = true := by
  decide

theorem validRuleOutletCompilation_5_mem (r : RawRule) (hr : r ∈ theRules) (isPos inv : Bool) :
    validRuleOutletCompilation 5 isPos inv r = true := by
  have h1 := List.all_eq_true.mp validRuleOutletCompilation_5_all r hr
  have h2 := List.all_eq_true.mp h1 isPos (by cases isPos <;> decide)
  exact List.all_eq_true.mp h2 inv (by cases inv <;> decide)

private theorem validRuleOutletCompilation_6_all_except_aux :
    ((List.range theRules.length).all fun idx =>
      ([true, false].all fun isPos =>
        ([true, false].all fun inv =>
          ((idx == 5) && (isPos == false)) ||
          ((idx == 7) && (isPos == false)) ||
          validRuleOutletCompilation 6 isPos inv theRules[idx]!))) = true := by
  decide

private theorem validRuleOutletCompilation_6_all_except (idx : Nat) (hidx : idx < theRules.length)
    (isPos inv : Bool)
    (h_not_5 : ¬ (idx = 5 ∧ isPos = false))
    (h_not_7 : ¬ (idx = 7 ∧ isPos = false)) :
    validRuleOutletCompilation 6 isPos inv theRules[idx]! = true := by
  have h1 := List.all_eq_true.mp validRuleOutletCompilation_6_all_except_aux idx (List.mem_range.mpr hidx)
  have h2 := List.all_eq_true.mp h1 isPos (by cases isPos <;> decide)
  have h3 := List.all_eq_true.mp h2 inv (by cases inv <;> decide)
  have hb5 : ((idx == 5) && (isPos == false)) = false := by
    cases hb : (idx == 5)
    · rfl
    · cases hp : (isPos == false)
      · rfl
      · exact False.elim (h_not_5 ⟨eq_of_beq hb, eq_of_beq hp⟩)
  have hb7 : ((idx == 7) && (isPos == false)) = false := by
    cases hb : (idx == 7)
    · rfl
    · cases hp : (isPos == false)
      · rfl
      · exact False.elim (h_not_7 ⟨eq_of_beq hb, eq_of_beq hp⟩)
  rw [hb5, hb7] at h3
  simpa using h3

theorem compileRuleOutlet_sound_deg5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl isPos inv : Bool) (s : H.Dart) (r : RawRule) (hr : r ∈ theRules)
    (h_deg : Hypermap.nodeDegree H s fuel = 5) :
    compiledSingleOutletActive (cartDegOriented H fuel 5 refl s)
        (compileRuleOutlet 5 1 isPos inv r) =
      matchesRawRule H fuel (if inv then refl else !refl) (if isPos then H.edge.f s else s) r :=
  compileRuleOutlet_sound H darts h_all h_le h_tri3 refl isPos inv s r h_deg (by omega) (by omega)
    (validRuleOutletCompilation_5_mem r hr isPos inv)

private theorem eq_6_of_degMatchesBound_6_6 {d : Nat} (h : degMatchesBound d (6, 6) = true) :
    d = 6 := by
  change (decide (6 ≤ d) && decide (d ≤ 6)) = true at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem compileRuleOutlet_sound_deg6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (refl isPos inv : Bool) (s : H.Dart) (r : RawRule) (hr : r ∈ theRules)
    (h_deg : Hypermap.nodeDegree H s fuel = 6) :
    compiledSingleOutletActive (cartDegOriented H fuel 6 refl s)
        (compileRuleOutlet 6 1 isPos inv r) =
      matchesRawRule H fuel (if inv then refl else !refl) (if isPos then H.edge.f s else s) r := by
  rcases List.mem_iff_getElem.mp hr with ⟨idx, hidx, rfl⟩
  by_cases h5 : idx = 5 ∧ isPos = false
  · rcases h5 with ⟨rfl, rfl⟩
    have h_eq_get : theRules[5] = theRules[5]! := (getElem!_pos theRules 5 hidx).symm
    rw [h_eq_get]
    cases inv
    · have hco : compileRuleOutlet 6 1 false false theRules[5]! =
          some (false, [(1, 6, 12), (6, 6, 6), (5, 6, 6), (11, 5, 6), (18, 5, 5)]) := by decide
      rw [hco]
      dsimp [compiledSingleOutletActive, compiledOutletActive, matchesRawRule]
      have h1 : degMatchesBound (cartDegOriented H fuel 6 refl s 1) (6, 12) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 1) fuel) (6, 12) := by
        rw [cartDegOriented_1_eq H fuel 6 refl s (by omega)]; rfl
      have h3 : degMatchesBound (cartDegOriented H fuel 6 refl s 6) (6, 6) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 3) fuel) (6, 6) := by
        rw [cartDegOriented_deg_eq_out H darts h_all h_le h_tri3 refl s h_deg (by omega)]
      have h5' : degMatchesBound (cartDegOriented H fuel 6 refl s 5) (6, 6) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 5) fuel) (6, 6) := by
        rw [cartDegOriented_deg_sub_1_eq_out H darts h_all h_le refl s h_deg (by omega)]
      have h9 : degMatchesBound (cartDegOriented H fuel 6 refl s 11) (5, 6) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 9) fuel) (5, 6) := by
        rw [cartDegOriented_two_mul_deg_sub_1_eq_out H darts h_all h_le h_tri3 refl s h_deg (by omega)]
      have h11 : degMatchesBound (cartDegOriented H fuel 6 refl s 18) (5, 5) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 11) fuel) (5, 5) := by
        rw [cartDegOriented_fan1_sdeg_eq_out_11 H darts h_all h_le refl s h_deg (by omega)]
      rw [h1, h3, h5', h9, h11]
      have hm : theRules[5]! = RawRule.mk 11 (6, 6) (6, 12)
          [(3, 6, 6), (5, 6, 6), (9, 5, 6), (11, 5, 5)] true := rfl
      rw [hm]
      dsimp [ruleVertexDart]
      have hd6 : degMatchesBound (Hypermap.nodeDegree H s fuel) (6, 6) = true := by
        rw [h_deg]; decide
      rw [hd6]
      simp only [Bool.true_and, Bool.and_true]
    · have hco : compileRuleOutlet 6 1 false true theRules[5]! =
          some (false, [(1, 6, 12), (2, 6, 6), (3, 6, 6), (8, 5, 6), (14, 5, 5)]) := by decide
      rw [hco]
      dsimp [compiledSingleOutletActive, compiledOutletActive, matchesRawRule]
      have h1 : degMatchesBound (cartDegOriented H fuel 6 refl s 1) (6, 12) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 1) fuel) (6, 12) := by
        rw [cartDegOriented_1_eq H fuel 6 refl s (by omega)]; rfl
      have h3 : degMatchesBound (cartDegOriented H fuel 6 refl s 2) (6, 6) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 3) fuel) (6, 6) := by
        rw [cartDegOriented_2_eq_out H darts h_all h_le h_tri3 refl s (by omega), ruleVertexDart_refl_3]
      have h5' : degMatchesBound (cartDegOriented H fuel 6 refl s 3) (6, 6) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 5) fuel) (6, 6) := by
        rw [cartDegOriented_3_eq_out H fuel 6 refl s (by omega), ruleVertexDart_refl_5]
      have h9 : degMatchesBound (cartDegOriented H fuel 6 refl s 8) (5, 6) =
          degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 9) fuel) (5, 6) := by
        rw [cartDegOriented_deg_add_2_eq_out H fuel 6 refl s (by omega), ruleVertexDart_refl_9]
      rw [h1, h3, h5', h9]
      have hm : theRules[5]! = RawRule.mk 11 (6, 6) (6, 12)
          [(3, 6, 6), (5, 6, 6), (9, 5, 6), (11, 5, 5)] true := rfl
      rw [hm]
      dsimp
      have hd6 : degMatchesBound (Hypermap.nodeDegree H s fuel) (6, 6) = true := by
        rw [h_deg]; decide
      rw [show ruleVertexDart H refl s 0 = s from rfl, hd6]
      cases hcd2 : degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 3) fuel) (6, 6)
      · simp
      · have hs2_eq6 : cartDegOriented H fuel 6 refl s 2 = 6 := by
          apply eq_6_of_degMatchesBound_6_6
          rw [cartDegOriented_2_eq_out H darts h_all h_le h_tri3 refl s (by omega), ← ruleVertexDart_refl_3]
          exact hcd2
        have h11 : degMatchesBound (cartDegOriented H fuel 6 refl s 14) (5, 5) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 11) fuel) (5, 5) := by
          rw [cartDegOriented_fan1_s2_eq_out_refl_11_of_deg6 H darts h_all h_le refl s (by omega) hs2_eq6]
        rw [h11]
        simp only [Bool.true_and, Bool.and_true]
  · by_cases h7 : idx = 7 ∧ isPos = false
    · rcases h7 with ⟨rfl, rfl⟩
      have h_eq_get : theRules[7] = theRules[7]! := (getElem!_pos theRules 7 hidx).symm
      rw [h_eq_get]
      cases inv
      · have hco : compileRuleOutlet 6 1 false false theRules[7]! =
            some (false, [(1, 7, 12), (6, 6, 6), (5, 6, 6), (12, 5, 5), (11, 6, 6), (18, 5, 6)]) := by decide
        rw [hco]
        dsimp [compiledSingleOutletActive, compiledOutletActive, matchesRawRule]
        have h1 : degMatchesBound (cartDegOriented H fuel 6 refl s 1) (7, 12) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 1) fuel) (7, 12) := by
          rw [cartDegOriented_1_eq H fuel 6 refl s (by omega)]; rfl
        have h3 : degMatchesBound (cartDegOriented H fuel 6 refl s 6) (6, 6) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 3) fuel) (6, 6) := by
          rw [cartDegOriented_deg_eq_out H darts h_all h_le h_tri3 refl s h_deg (by omega)]
        have h5' : degMatchesBound (cartDegOriented H fuel 6 refl s 5) (6, 6) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 5) fuel) (6, 6) := by
          rw [cartDegOriented_deg_sub_1_eq_out H darts h_all h_le refl s h_deg (by omega)]
        have h7' : degMatchesBound (cartDegOriented H fuel 6 refl s 12) (5, 5) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 7) fuel) (5, 5) := by
          rw [cartDegOriented_two_mul_deg_eq_out H darts h_all h_le h_tri3 refl s h_deg (by omega)]
        have h9 : degMatchesBound (cartDegOriented H fuel 6 refl s 11) (6, 6) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 9) fuel) (6, 6) := by
          rw [cartDegOriented_two_mul_deg_sub_1_eq_out H darts h_all h_le h_tri3 refl s h_deg (by omega)]
        have h11 : degMatchesBound (cartDegOriented H fuel 6 refl s 18) (5, 6) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H (!refl) s 11) fuel) (5, 6) := by
          rw [cartDegOriented_fan1_sdeg_eq_out_11 H darts h_all h_le refl s h_deg (by omega)]
        rw [h1, h3, h5', h7', h9, h11]
        have hm : theRules[7]! = RawRule.mk 15 (6, 6) (7, 12)
            [(3, 6, 6), (5, 6, 6), (7, 5, 5), (9, 6, 6), (11, 5, 6)] true := rfl
        rw [hm]
        dsimp [ruleVertexDart]
        have hd6 : degMatchesBound (Hypermap.nodeDegree H s fuel) (6, 6) = true := by
          rw [h_deg]; decide
        rw [hd6]
        simp only [Bool.true_and, Bool.and_true]
      · have hco : compileRuleOutlet 6 1 false true theRules[7]! =
            some (false, [(1, 7, 12), (2, 6, 6), (3, 6, 6), (7, 5, 5), (8, 6, 6), (14, 5, 6)]) := by decide
        rw [hco]
        dsimp [compiledSingleOutletActive, compiledOutletActive, matchesRawRule]
        have h1 : degMatchesBound (cartDegOriented H fuel 6 refl s 1) (7, 12) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 1) fuel) (7, 12) := by
          rw [cartDegOriented_1_eq H fuel 6 refl s (by omega)]; rfl
        have h3 : degMatchesBound (cartDegOriented H fuel 6 refl s 2) (6, 6) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 3) fuel) (6, 6) := by
          rw [cartDegOriented_2_eq_out H darts h_all h_le h_tri3 refl s (by omega), ruleVertexDart_refl_3]
        have h5' : degMatchesBound (cartDegOriented H fuel 6 refl s 3) (6, 6) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 5) fuel) (6, 6) := by
          rw [cartDegOriented_3_eq_out H fuel 6 refl s (by omega), ruleVertexDart_refl_5]
        have h7' : degMatchesBound (cartDegOriented H fuel 6 refl s 7) (5, 5) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 7) fuel) (5, 5) := by
          rw [cartDegOriented_deg_add_1_eq_out H fuel 6 refl s (by omega), ruleVertexDart_refl_7]
        have h9 : degMatchesBound (cartDegOriented H fuel 6 refl s 8) (6, 6) =
            degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 9) fuel) (6, 6) := by
          rw [cartDegOriented_deg_add_2_eq_out H fuel 6 refl s (by omega), ruleVertexDart_refl_9]
        rw [h1, h3, h5', h7', h9]
        have hm : theRules[7]! = RawRule.mk 15 (6, 6) (7, 12)
            [(3, 6, 6), (5, 6, 6), (7, 5, 5), (9, 6, 6), (11, 5, 6)] true := rfl
        rw [hm]
        dsimp
        have hd6 : degMatchesBound (Hypermap.nodeDegree H s fuel) (6, 6) = true := by
          rw [h_deg]; decide
        rw [show ruleVertexDart H refl s 0 = s from rfl, hd6]
        cases hcd2 : degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 3) fuel) (6, 6)
        · simp
        · have hs2_eq6 : cartDegOriented H fuel 6 refl s 2 = 6 := by
            apply eq_6_of_degMatchesBound_6_6
            rw [cartDegOriented_2_eq_out H darts h_all h_le h_tri3 refl s (by omega), ← ruleVertexDart_refl_3]
            exact hcd2
          have h11 : degMatchesBound (cartDegOriented H fuel 6 refl s 14) (5, 6) =
              degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H refl s 11) fuel) (5, 6) := by
            rw [cartDegOriented_fan1_s2_eq_out_refl_11_of_deg6 H darts h_all h_le refl s (by omega) hs2_eq6]
          rw [h11]
          simp only [Bool.true_and, Bool.and_true]
    · have h_val := validRuleOutletCompilation_6_all_except idx hidx isPos inv h5 h7
      have h_eq_get : theRules[idx] = theRules[idx]! := (getElem!_pos theRules idx hidx).symm
      rw [h_eq_get]
      exact compileRuleOutlet_sound H darts h_all h_le h_tri3 refl isPos inv s theRules[idx]! h_deg
        (by omega) (by omega) h_val

private theorem list_foldl_sub_eq {α : Type} (l : List α) (f g : α → Int) (a b : Int) :
    List.foldl (fun acc x => acc + (f x - g x)) (a - b) l =
      List.foldl (fun acc x => acc + f x) a l - List.foldl (fun acc x => acc + g x) b l := by
  induction l generalizing a b with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    have h_eq : a - b + (f x - g x) = (a + f x) - (b + g x) := by omega
    rw [h_eq]
    exact ih (a + f x) (b + g x)

private theorem rawRuleOutflow_refl_swap (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat)
    (refl : Bool) (d : H.Dart) (r : RawRule) (hr : r ∈ theRules) :
    (if matchesRawRule H fuel (!refl) d r = true then (1 : Int) else 0) +
      (if r.invert = true then if matchesRawRule H fuel refl d r = true then (1 : Int) else 0 else 0) =
    rawRuleOutflow H fuel d r := by
  dsimp [rawRuleOutflow]
  cases hinv : r.invert
  · have h_eq := matchesRawRule_true_eq_false_of_invert_false H fuel d r hr hinv
    cases refl <;> simp [h_eq]
  · cases refl <;> simp [Int.add_comm]

theorem compiledOutletsSum_spoke1_eq_netDartShift_of_sound
    (H : Hypermap) [DecidableEq H.Dart] (_darts : List H.Dart)
    (fuel deg : Nat) (refl : Bool) (s : H.Dart)
    (h_rule_sound : ∀ isPos inv r, r ∈ theRules →
      compiledSingleOutletActive (cartDegOriented H fuel deg refl s)
          (compileRuleOutlet deg 1 isPos inv r) =
        matchesRawRule H fuel (if inv then refl else !refl) (if isPos then H.edge.f s else s) r) :
    compiledOutletsSum (cartDegOriented H fuel deg refl s) (compiledOutletsForSpoke deg 1) =
      netDartShift H fuel s := by
  unfold compiledOutletsForSpoke
  rw [compiledOutletsSum_foldr_append]
  have h_step : ∀ r ∈ theRules,
      compiledOutletsSum (cartDegOriented H fuel deg refl s) (compileRuleAllOutlets deg 1 r) =
        rawRuleOutflow H fuel (H.edge.f s) r - rawRuleOutflow H fuel s r := by
    intro r hr
    dsimp [compileRuleAllOutlets]
    rw [compiledOutletsSum_append, compiledOutletsSum_append,
        compiledOutletsSum_compileRuleOutlet, compiledOutletsSum_compileRuleOutlet,
        h_rule_sound true false r hr, h_rule_sound false false r hr]
    dsimp
    cases hinv : r.invert
    · dsimp
      change _ + 0 = _
      have hpos := rawRuleOutflow_refl_swap H fuel refl (H.edge.f s) r hr
      have hneg := rawRuleOutflow_refl_swap H fuel refl s r hr
      rw [hinv] at hpos hneg
      simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero] at hpos hneg
      rw [← hpos, ← hneg]
      cases matchesRawRule H fuel (!refl) (H.edge.f s) r <;> cases matchesRawRule H fuel (!refl) s r <;> rfl
    · dsimp
      rw [compiledOutletsSum_append, compiledOutletsSum_compileRuleOutlet,
          compiledOutletsSum_compileRuleOutlet, h_rule_sound true true r hr,
          h_rule_sound false true r hr]
      dsimp
      have hpos := rawRuleOutflow_refl_swap H fuel refl (H.edge.f s) r hr
      have hneg := rawRuleOutflow_refl_swap H fuel refl s r hr
      rw [hinv] at hpos hneg
      simp only [↓reduceIte] at hpos hneg
      rw [← hpos, ← hneg]
      cases matchesRawRule H fuel (!refl) (H.edge.f s) r <;>
        cases matchesRawRule H fuel refl (H.edge.f s) r <;>
        cases matchesRawRule H fuel (!refl) s r <;>
        cases matchesRawRule H fuel refl s r <;> decide
  have h_fold :
      List.foldl (fun acc r => acc + compiledOutletsSum (cartDegOriented H fuel deg refl s)
        (compileRuleAllOutlets deg 1 r)) 0 theRules =
      List.foldl (fun acc r => acc + (rawRuleOutflow H fuel (H.edge.f s) r - rawRuleOutflow H fuel s r))
        (0 - 0) theRules := by
    clear h_rule_sound
    have h_gen : ∀ (rs : List RawRule), (∀ r ∈ rs,
        compiledOutletsSum (cartDegOriented H fuel deg refl s) (compileRuleAllOutlets deg 1 r) =
          rawRuleOutflow H fuel (H.edge.f s) r - rawRuleOutflow H fuel s r) →
        ∀ a : Int,
        List.foldl (fun acc r => acc + compiledOutletsSum (cartDegOriented H fuel deg refl s)
          (compileRuleAllOutlets deg 1 r)) a rs =
        List.foldl (fun acc r => acc + (rawRuleOutflow H fuel (H.edge.f s) r - rawRuleOutflow H fuel s r))
          a rs := by
      intro rs hrs
      induction rs with
      | nil => intro a; rfl
      | cons r' rs' ih =>
        intro a
        simp only [List.foldl_cons]
        rw [hrs r' List.mem_cons_self]
        exact ih (fun r hm => hrs r (List.mem_cons_of_mem _ hm)) _
    exact h_gen theRules h_step 0
  rw [h_fold, list_foldl_sub_eq]
  rfl

private theorem validSpokeShiftTable_5 : validSpokeShiftTable 5 = true := by decide
private theorem validSpokeShiftTable_6 : validSpokeShiftTable 6 = true := by decide

theorem compiledOutletsSum_spoke_eq_spoke1_deg56 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (x : Nat)
    (h_deg : Hypermap.nodeDegree H u fuel = 5 ∨ Hypermap.nodeDegree H u fuel = 6)
    (hx1 : 1 ≤ x) (hx2 : x ≤ Hypermap.nodeDegree H u fuel) :
    let deg := Hypermap.nodeDegree H u fuel
    compiledOutletsSum (cartDegOriented H fuel deg refl d0) (compiledOutletsForSpoke deg x) =
      compiledOutletsSum (cartDegOriented H fuel deg refl (spokeDartOriented H refl d0 x))
        (compiledOutletsForSpoke deg 1) := by
  intro deg
  have h_tab : validSpokeShiftTable deg = true := by
    rcases h_deg with h5 | h6
    · dsimp [deg]; rw [h5]; exact validSpokeShiftTable_5
    · dsimp [deg]; rw [h6]; exact validSpokeShiftTable_6
  dsimp [validSpokeShiftTable] at h_tab
  rcases Bool.and_eq_true_iff.mp h_tab with ⟨h_conds, h_shifts⟩
  have hx_mem : x ∈ List.range' 1 deg := List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
  have h_shift_x : compiledOutletsForSpoke deg x =
      shiftCompiledOutlets deg (x - 1) (compiledOutletsForSpoke deg 1) :=
    eq_of_beq (List.all_eq_true.mp h_shifts x hx_mem)
  rw [h_shift_x]
  exact compiledOutletsSum_shiftCompiledOutlets_eq H darts h_all h_le hd0 refl x
    (compiledOutletsForSpoke deg 1) hx1 hx2 h_conds

theorem activeOutletSum_hub_foldl_eq_orbitNetShift_deg56 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    {u d0 : H.Dart} (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool)
    (h_deg : Hypermap.nodeDegree H u fuel = 5 ∨ Hypermap.nodeDegree H u fuel = 6)
    (h5_all : ∀ p, 1 ≤ p → p ≤ 5 * Hypermap.nodeDegree H u fuel →
      5 ≤ cartDegOriented H fuel (Hypermap.nodeDegree H u fuel) refl d0 p) :
    let deg := Hypermap.nodeDegree H u fuel
    let tbl := if deg = 5 then shiftedTable5Lit else shiftedTable6Lit
    List.foldl (fun acc x =>
        acc + activeOutletSum deg (cartDegOriented H fuel deg refl d0) (lookupListRec [] tbl x))
      0 (List.range' 1 deg) = orbitNetShift H fuel u := by
  intro deg tbl
  have h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x :=
    fun x => face_f_three_of_faceDegree_eq_three H darts h_all h_le (h_tri x (h_all x))
  rw [orbitNetShift_eq_spokeDartOriented_foldl H darts h_all h_le hd0 refl]
  have h_step : ∀ x ∈ List.range' 1 deg,
      activeOutletSum deg (cartDegOriented H fuel deg refl d0) (lookupListRec [] tbl x) =
        netDartShift H fuel (spokeDartOriented H refl d0 x) := by
    intro x hx_mem
    have hx_bnds := List.mem_range'.mp hx_mem
    have hx1 : 1 ≤ x := by omega
    have hx2 : x ≤ deg := by omega
    have hs_mem : spokeDartOriented H refl d0 x ∈ getOrbit H.node fuel u :=
      spokeDartOriented_mem_getOrbit_of_complete H darts h_all h_le hd0 refl x
    have hs_deg : Hypermap.nodeDegree H (spokeDartOriented H refl d0 x) fuel = deg :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hs_mem
    have h_match : matchesCompiledOutlets deg (lookupListRec [] tbl x) (compiledOutletsForSpoke deg x) = true := by
      rcases h_deg with h5 | h6
      · have hx5 : x ∈ List.range' 1 5 := by dsimp [deg] at hx_mem; rw [h5] at hx_mem; exact hx_mem
        have h_all5 := List.all_eq_true.mp validCompiledTable_5 x hx5
        have htbl : tbl = shiftedTable5Lit := by dsimp [tbl, deg]; rw [h5, if_pos rfl]
        rw [htbl]
        dsimp [deg] at h5 ⊢
        rw [show Hypermap.nodeDegree H u fuel = 5 from h5]
        exact h_all5
      · have hx6 : x ∈ List.range' 1 6 := by dsimp [deg] at hx_mem; rw [h6] at hx_mem; exact hx_mem
        have h_all6 := List.all_eq_true.mp validCompiledTable_6 x hx6
        have htbl : tbl = shiftedTable6Lit := by dsimp [tbl, deg]; rw [h6, if_neg (by decide)]
        rw [htbl]
        dsimp [deg] at h6 ⊢
        rw [show Hypermap.nodeDegree H u fuel = 6 from h6]
        exact h_all6
    rw [activeOutletSum_eq_of_matchesCompiledOutlets deg _ _ _ h_match h5_all,
        compiledOutletsSum_spoke_eq_spoke1_deg56 H darts h_all h_le hd0 refl x h_deg hx1 hx2]
    rcases h_deg with h5 | h6
    · have hs5 : Hypermap.nodeDegree H (spokeDartOriented H refl d0 x) fuel = 5 := hs_deg.trans h5
      rw [show Hypermap.nodeDegree H u fuel = 5 from h5]
      exact compiledOutletsSum_spoke1_eq_netDartShift_of_sound H darts fuel 5 refl _
        (fun isPos inv r hr => compileRuleOutlet_sound_deg5 H darts h_all h_le h_tri3 refl isPos inv _ r hr hs5)
    · have hs6 : Hypermap.nodeDegree H (spokeDartOriented H refl d0 x) fuel = 6 := hs_deg.trans h6
      rw [show Hypermap.nodeDegree H u fuel = 6 from h6]
      exact compiledOutletsSum_spoke1_eq_netDartShift_of_sound H darts fuel 6 refl _
        (fun isPos inv r hr => compileRuleOutlet_sound_deg6 H darts h_all h_le h_tri3 refl isPos inv _ r hr hs6)
  have h_gen : ∀ (xs : List Nat),
      (∀ x ∈ xs, activeOutletSum deg (cartDegOriented H fuel deg refl d0) (lookupListRec [] tbl x) =
        netDartShift H fuel (spokeDartOriented H refl d0 x)) →
      ∀ a : Int,
      List.foldl (fun acc x =>
        acc + activeOutletSum deg (cartDegOriented H fuel deg refl d0) (lookupListRec [] tbl x)) a xs =
      List.foldl (fun acc i => acc + netDartShift H fuel (spokeDartOriented H refl d0 i)) a xs := by
    intro xs hxs
    induction xs with
    | nil => intro a; rfl
    | cons y ys ih =>
      intro a
      simp only [List.foldl_cons]
      rw [hxs y List.mem_cons_self]
      exact ih (fun z hz => hxs z (List.mem_cons_of_mem _ hz)) _
  exact h_gen (List.range' 1 deg) h_step 0

/-!
### 3. RSST (4.8): Outflow Bound `≤ 5` When Target Degree `≥ 12`
-/

private theorem valid_negAsPos_match_5 :
    matchesCompiledOutlets 5 (negAsPosDeg 5)
      (((compiledOutletsForSpoke 5 1).filter (fun co => !co.1)).map (fun co => (true, co.2))) = true := by
  decide

private theorem valid_negAsPos_match_6 :
    matchesCompiledOutlets 6 (negAsPosDeg 6)
      (((compiledOutletsForSpoke 6 1).filter (fun co => !co.1)).map (fun co => (true, co.2))) = true := by
  decide

private theorem valid_negAsPos_match_7 :
    matchesCompiledOutlets 7 (negAsPosDeg 7)
      (((compiledOutletsForSpoke 7 1).filter (fun co => !co.1)).map (fun co => (true, co.2))) = true := by
  decide

private theorem pos_outlets_forbid_ge9_5 :
    ((compiledOutletsForSpoke 5 1).all fun co =>
      !co.1 || co.2.any fun c => c.1 == 1 && decide (c.2.2 < 9)) = true := by
  decide

private theorem pos_outlets_forbid_ge9_6 :
    ((compiledOutletsForSpoke 6 1).all fun co =>
      !co.1 || co.2.any fun c => c.1 == 1 && decide (c.2.2 < 9)) = true := by
  decide

private theorem pos_outlets_forbid_ge9_7 :
    ((compiledOutletsForSpoke 7 1).all fun co =>
      !co.1 || co.2.any fun c => c.1 == 1 && decide (c.2.2 < 9)) = true := by
  decide

private theorem degMatchesBound_false_of_lt_9_of_ge_9 {d : Nat} {bnd : Nat × Nat}
    (hd : 9 ≤ d) (hb : bnd.2 < 9) : degMatchesBound d bnd = false := by
  unfold degMatchesBound
  have hne9 : (bnd.2 == 9) = false := beq_false_of_ne (by omega)
  have hne12 : (bnd.2 == 12) = false := beq_false_of_ne (by omega)
  have hnot_le : decide (d ≤ bnd.2) = false := decide_eq_false (by omega)
  dsimp
  rw [hne9]
  simp [hne12, hnot_le]

private theorem compiledOutletsSum_negAsPos_eq_neg
    (cd : Nat → Nat) (cos : List (Bool × List (Nat × Nat × Nat)))
    (h_pos_inactive : ∀ co ∈ cos, co.1 = true → compiledOutletActive cd co = false) :
    compiledOutletsSum cd ((cos.filter (fun co => !co.1)).map (fun co => (true, co.2))) =
      - compiledOutletsSum cd cos := by
  induction cos with
  | nil => rfl
  | cons co rest ih =>
    rcases co with ⟨b, conds⟩
    have ih' := ih (fun x hx h1 => h_pos_inactive x (List.mem_cons_of_mem _ hx) h1)
    cases b
    · have hact : compiledOutletActive cd (true, conds) = compiledOutletActive cd (false, conds) := rfl
      change (if compiledOutletActive cd (true, conds) = true then (1 : Int) else 0) +
          compiledOutletsSum cd ((rest.filter (fun co => !co.1)).map (fun co => (true, co.2))) =
        -((if compiledOutletActive cd (false, conds) = true then (-1 : Int) else 0) +
          compiledOutletsSum cd rest)
      rw [hact, ih']
      cases compiledOutletActive cd (false, conds) <;> dsimp <;> omega
    · have hinact : compiledOutletActive cd (true, conds) = false :=
        h_pos_inactive (true, conds) List.mem_cons_self rfl
      change compiledOutletsSum cd ((rest.filter (fun co => !co.1)).map (fun co => (true, co.2))) =
        -((if compiledOutletActive cd (true, conds) = true then (1 : Int) else 0) +
          compiledOutletsSum cd rest)
      rw [hinact, ih']
      simp

theorem activeOutletSum_negAsPos_eq_dartRuleOutflow_deg_5_to_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel deg : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    (h5_all : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree H d fuel)
    (s : H.Dart) (h_deg : Hypermap.nodeDegree H s fuel = deg)
    (h_deg_range : deg = 5 ∨ deg = 6 ∨ deg = 7)
    (h_tgt : 9 ≤ Hypermap.nodeDegree H (H.edge.f s) fuel) :
    activeOutletSum deg (cartDegOriented H fuel deg false s) (negAsPosDeg deg) =
      dartRuleOutflow H fuel s := by
  let cd := cartDegOriented H fuel deg false s
  have h5_cd : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cd p :=
    fun p _ _ => h5_all _ (h_all _)
  have h_match : matchesCompiledOutlets deg (negAsPosDeg deg)
      (((compiledOutletsForSpoke deg 1).filter (fun co => !co.1)).map (fun co => (true, co.2))) = true := by
    rcases h_deg_range with rfl | rfl | rfl
    · exact valid_negAsPos_match_5
    · exact valid_negAsPos_match_6
    · exact valid_negAsPos_match_7
  have h_pos_forb : ∀ co ∈ compiledOutletsForSpoke deg 1, co.1 = true →
      co.2.any (fun c => c.1 == 1 && decide (c.2.2 < 9)) = true := by
    have h_all_b : ((compiledOutletsForSpoke deg 1).all fun co =>
        !co.1 || co.2.any fun c => c.1 == 1 && decide (c.2.2 < 9)) = true := by
      rcases h_deg_range with rfl | rfl | rfl
      · exact pos_outlets_forbid_ge9_5
      · exact pos_outlets_forbid_ge9_6
      · exact pos_outlets_forbid_ge9_7
    intro co hmem h1
    have hc := List.all_eq_true.mp h_all_b co hmem
    rw [h1] at hc
    exact hc
  have h_pos_inact : ∀ co ∈ compiledOutletsForSpoke deg 1, co.1 = true →
      compiledOutletActive cd co = false := by
    intro co hmem h1
    have hany := h_pos_forb co hmem h1
    rcases List.any_eq_true.mp hany with ⟨c, hc_mem, hc_pred⟩
    rcases Bool.and_eq_true_iff.mp hc_pred with ⟨hc1, hcb⟩
    have hc1_eq : c.1 = 1 := eq_of_beq hc1
    have hc_lt9 : c.2.2 < 9 := of_decide_eq_true hcb
    have hcd1_ge9 : 9 ≤ cd 1 := by
      change 9 ≤ cartDegOriented H fuel deg false s 1
      rw [cartDegOriented_1_eq H fuel deg false s (by omega)]
      exact h_tgt
    have h_bad : degMatchesBound (cd c.1) c.2 = false := by
      rw [hc1_eq]
      exact degMatchesBound_false_of_lt_9_of_ge_9 hcd1_ge9 hc_lt9
    dsimp [compiledOutletActive]
    cases h_act : co.2.all (fun x => degMatchesBound (cd x.1) x.2)
    · rfl
    · have hx := List.all_eq_true.mp h_act c hc_mem
      rw [h_bad] at hx
      contradiction
  have h_net_eq : netDartShift H fuel s = - dartRuleOutflow H fuel s := by
    unfold netDartShift
    rw [dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel (H.edge.f s) h_tgt]
    omega
  have h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x :=
    fun x => face_f_three_of_faceDegree_eq_three H darts h_all h_le (h_tri x (h_all x))
  have h_sum_cos : compiledOutletsSum cd (compiledOutletsForSpoke deg 1) = netDartShift H fuel s := by
    dsimp [cd]
    rcases h_deg_range with rfl | rfl | rfl
    · exact compiledOutletsSum_spoke1_eq_netDartShift_of_sound H darts fuel 5 false s
        (fun isPos inv r hr => compileRuleOutlet_sound_deg5 H darts h_all h_le h_tri3 false isPos inv s r hr h_deg)
    · exact compiledOutletsSum_spoke1_eq_netDartShift_of_sound H darts fuel 6 false s
        (fun isPos inv r hr => compileRuleOutlet_sound_deg6 H darts h_all h_le h_tri3 false isPos inv s r hr h_deg)
    · have hs_mem : s ∈ getOrbit H.node fuel s := Hypermap.mem_getOrbit_self H.node fuel s
      have h7_or : Hypermap.nodeDegree H s fuel = 7 ∨ Hypermap.nodeDegree H s fuel = 8 ∨
          Hypermap.nodeDegree H s fuel = 9 ∨ Hypermap.nodeDegree H s fuel = 10 ∨
          Hypermap.nodeDegree H s fuel = 11 := Or.inl h_deg
      have h_eq := activeOutletSum_spoke_eq_netDartShift H darts h_all h_le h_tri hs_mem false 1 h7_or
        (by omega) (by rw [h_deg]; omega) (by rw [h_deg]; exact h5_cd)
      dsimp at h_eq
      rw [h_deg] at h_eq
      rw [← h_eq]
      exact (activeOutletSum_eq_compiledOutletsSum 7 1 _ (Or.inl rfl) (by omega) (by omega) h5_cd).symm
  rw [activeOutletSum_eq_of_matchesCompiledOutlets deg cd _ _ h_match h5_cd,
      compiledOutletsSum_negAsPos_eq_neg cd (compiledOutletsForSpoke deg 1) h_pos_inact,
      h_sum_cos, h_net_eq]
  omega

/-- RSST (4.8): Any dart `d` targeting a high-degree vertex (`9 ≤ deg(H.edge.f d)`, in particular `≥ 12`)
    either sends at most `5` fifths (`dartRuleOutflow ≤ 5`) or originates at a degree `5..7` vertex
    emitting `HasExactReducedAxle`. -/
theorem dartRuleOutflow_le_5_or_hasExactReducedAxle_of_target_deg_ge_9
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    (h5_all : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree H d fuel)
    (s : H.Dart) (h_tgt : 9 ≤ Hypermap.nodeDegree H (H.edge.f s) fuel) :
    dartRuleOutflow H fuel s ≤ 5 ∨
      ∃ d0 : H.Dart,
        let deg := Hypermap.nodeDegree H d0 fuel
        5 ≤ deg ∧ deg ≤ 11 ∧ HasExactReducedAxle deg (cartDegOriented H fuel deg false d0) := by
  have h5_s : 5 ≤ Hypermap.nodeDegree H s fuel := h5_all s (h_all s)
  by_cases h9 : 9 ≤ Hypermap.nodeDegree H s fuel
  · left
    rw [dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel s h9]
    omega
  · by_cases h8 : Hypermap.nodeDegree H s fuel = 8
    · left
      have h4 := dartRuleOutflow_le_4_of_deg_8_of_target_deg_ge_8 H fuel s h8 (by omega)
      omega
    · have h567 : Hypermap.nodeDegree H s fuel = 5 ∨ Hypermap.nodeDegree H s fuel = 6 ∨
          Hypermap.nodeDegree H s fuel = 7 := by omega
      have hcd1 : 9 ≤ cartDegOriented H fuel (Hypermap.nodeDegree H s fuel) false s 1 := by
        rw [cartDegOriented_1_eq H fuel (Hypermap.nodeDegree H s fuel) false s h5_s]
        exact h_tgt
      rcases h567 with h5 | h6 | h7
      · have h_st := matchesCartState31_stGe12Deg (by omega : 5 ≤ 11)
            (cartDegOriented H fuel 5 false s) (by rw [← h5]; exact hcd1)
        have h_val : ∀ po ∈ negAsPosDeg 5, validFastPosOut 5 po = true :=
          fun po hmem => List.all_eq_true.mp validFastPosOut_negAsPos_5 po hmem
        have h_res := checkBoundRec_sound31 5 (cartDegOriented H fuel 5 false s) (by omega)
            256 (stGe12Deg 5) 0 [] (negAsPosDeg 5) [] 5 hints48_5
            h_st (fun _ hm => by contradiction) h_val (fun _ hm => by contradiction)
            valid_hints48_5 cb_48_5
        rcases h_res with h_axle | h_bound
        · right; refine ⟨s, ?_⟩; dsimp; rw [h5]; exact ⟨by omega, by omega, h_axle⟩
        · left
          have h_eq := activeOutletSum_negAsPos_eq_dartRuleOutflow_deg_5_to_7 H darts h_all h_le
              h_tri h5_all s h5 (Or.inl rfl) h_tgt
          dsimp [activeOutletSum] at h_bound
          omega
      · have h_st := matchesCartState31_stGe12Deg (by omega : 6 ≤ 11)
            (cartDegOriented H fuel 6 false s) (by rw [← h6]; exact hcd1)
        have h_val : ∀ po ∈ negAsPosDeg 6, validFastPosOut 6 po = true :=
          fun po hmem => List.all_eq_true.mp validFastPosOut_negAsPos_6 po hmem
        have h_res := checkBoundRec_sound31 6 (cartDegOriented H fuel 6 false s) (by omega)
            256 (stGe12Deg 6) 0 [] (negAsPosDeg 6) [] 5 hints48_6
            h_st (fun _ hm => by contradiction) h_val (fun _ hm => by contradiction)
            valid_hints48_6 cb_48_6
        rcases h_res with h_axle | h_bound
        · right; refine ⟨s, ?_⟩; dsimp; rw [h6]; exact ⟨by omega, by omega, h_axle⟩
        · left
          have h_eq := activeOutletSum_negAsPos_eq_dartRuleOutflow_deg_5_to_7 H darts h_all h_le
              h_tri h5_all s h6 (Or.inr (Or.inl rfl)) h_tgt
          dsimp [activeOutletSum] at h_bound
          omega
      · have h_st := matchesCartState31_stGe12Deg (by omega : 7 ≤ 11)
            (cartDegOriented H fuel 7 false s) (by rw [← h7]; exact hcd1)
        have h_val : ∀ po ∈ negAsPosDeg 7, validFastPosOut 7 po = true :=
          fun po hmem => List.all_eq_true.mp validFastPosOut_negAsPos_7 po hmem
        have h_res := checkBoundRec_sound31 7 (cartDegOriented H fuel 7 false s) (by omega)
            256 (stGe12Deg 7) 0 [] (negAsPosDeg 7) [] 5 hints48_7
            h_st (fun _ hm => by contradiction) h_val (fun _ hm => by contradiction)
            valid_hints48_7 cb_48_7
        rcases h_res with h_axle | h_bound
        · right; refine ⟨s, ?_⟩; dsimp; rw [h7]; exact ⟨by omega, by omega, h_axle⟩
        · left
          have h_eq := activeOutletSum_negAsPos_eq_dartRuleOutflow_deg_5_to_7 H darts h_all h_le
              h_tri h5_all s h7 (Or.inr (Or.inr rfl)) h_tgt
          dsimp [activeOutletSum] at h_bound
          omega

/-!
### 4. RSST (4.5)–(4.7) & Unconditional Euler-120 All-Degrees Unavoidability
-/



theorem finalCharge_le_zero_or_hasExactReducedAxle_deg_5_or_6
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    (h5_all : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree H d fuel)
    (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg : Hypermap.nodeDegree H u fuel = 5 ∨ Hypermap.nodeDegree H u fuel = 6) :
    let deg := Hypermap.nodeDegree H u fuel
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 ∨
      ∃ d0 ∈ getOrbit H.node fuel u, ∃ refl, HasExactReducedAxle deg (cartDegOriented H fuel deg refl d0) := by
  intro deg
  have h_fam := dihedralClosedFamily_realHypermapHubFamily H darts h_all h_le h_tri u
  have hu_orb : u ∈ getOrbit H.node fuel u := Hypermap.mem_getOrbit_self H.node fuel u
  have hcd0 : RealHypermapHubFamily H fuel deg u (cartDegOriented H fuel deg false u) :=
    ⟨u, hu_orb, false, rfl⟩
  have h_core : ∃ cd, RealHypermapHubFamily H fuel deg u cd ∧
      CoreCartLeaf deg (if deg = 5 then shiftedTable5Lit else shiftedTable6Lit) cd := by
    rcases h_deg with h5 | h6
    · have h_fam5 : DihedralClosedFamily 5 (RealHypermapHubFamily H fuel 5 u) := by
        simpa [deg, h5] using h_fam
      have hcd05 : RealHypermapHubFamily H fuel 5 u (cartDegOriented H fuel 5 false u) := by
        simpa [deg, h5] using hcd0
      have h_val5 : ∀ row ∈ shiftedTable5Lit, ∀ po ∈ row, validFastPosOut 5 po = true :=
        fun row hrow po hpo =>
          List.all_eq_true.mp (List.all_eq_true.mp validFastPosOut_mkShiftedTable_5 row hrow) po hpo
      have h_res5 := verifyTreePureRec_family_core_soundness 5 shiftedTable5Lit
          (RealHypermapHubFamily H fuel 5 u) h_fam5 tree5 58 hints5 (by omega) (by omega)
          h_val5 valid_tree5 (by omega) valid_hints5 ver_tree5 hcd05
      simpa [deg, h5] using h_res5
    · have h_fam6 : DihedralClosedFamily 6 (RealHypermapHubFamily H fuel 6 u) := by
        simpa [deg, h6] using h_fam
      have hcd06 : RealHypermapHubFamily H fuel 6 u (cartDegOriented H fuel 6 false u) := by
        simpa [deg, h6] using hcd0
      have h_val6 : ∀ row ∈ shiftedTable6Lit, ∀ po ∈ row, validFastPosOut 6 po = true :=
        fun row hrow po hpo =>
          List.all_eq_true.mp (List.all_eq_true.mp validFastPosOut_mkShiftedTable_6 row hrow) po hpo
      have h_res6 := verifyTreePureRec_family_core_soundness 6 shiftedTable6Lit
          (RealHypermapHubFamily H fuel 6 u) h_fam6 tree6 58 hints6 (by omega) (by omega)
          h_val6 valid_tree6 (by omega) valid_hints6 ver_tree6 hcd06
      simpa [deg, h6] using h_res6
  rcases h_core with ⟨cd, ⟨d0, hd0, refl, rfl⟩, h_leaf⟩
  rcases coreCartLeaf_reducible_or_hub_sum_le_zero deg
      (if deg = 5 then shiftedTable5Lit else shiftedTable6Lit)
      (cartDegOriented H fuel deg refl d0) h_leaf with h_axle | h_hub_le
  · exact Or.inr ⟨d0, hd0, refl, h_axle⟩
  · left
    have h_fc := finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless
    have h_init : initialCharge H u fuel = 10 * (6 - (deg : Int)) := by
      unfold initialCharge
      rfl
    have h_orbit := activeOutletSum_hub_foldl_eq_orbitNetShift_deg56 H darts h_all h_le h_tri
        hd0 refl h_deg (fun p _ _ => h5_all _ (h_all _))
    dsimp [deg] at h_init h_orbit h_hub_le ⊢
    omega

/-- Unconditional All-Degrees Euler-120 Unavoidability for any complete loopless planar
    triangulation `T` with `initialCharge` sum `120` and minimum vertex degree `≥ 5`. -/
theorem exists_hasExactReducedAxle_of_complete_triangulation_sum120
    (T : Hypermap) [DecidableEq T.Dart] (darts : List T.Dart)
    (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_sum120 : sumCharges (fun v => initialCharge T v darts.length)
      (Hypermap.extractGraph T darts).vertices = 120)
    (h_loopless : ∀ d : T.Dart, Hypermap.sameVertex T d (T.edge.f d) darts.length = false)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree T d darts.length = 3)
    (h5_all : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree T d darts.length) :
    ∃ d0 : T.Dart,
      let deg := Hypermap.nodeDegree T d0 darts.length
      5 ≤ deg ∧ deg ≤ 11 ∧ HasExactReducedAxle deg (cartDegOriented T darts.length deg false d0) ∨
      5 ≤ deg ∧ deg ≤ 11 ∧ HasExactReducedAxle deg (cartDegOriented T darts.length deg true d0) := by
  apply Classical.byContradiction
  intro h_none
  have h_no_axle : ∀ (d0 : T.Dart) (refl : Bool),
      let deg := Hypermap.nodeDegree T d0 darts.length
      5 ≤ deg → deg ≤ 11 → ¬ HasExactReducedAxle deg (cartDegOriented T darts.length deg refl d0) := by
    intro d0 refl deg h5 h11 h_axle
    apply h_none
    refine ⟨d0, ?_⟩
    cases refl
    · exact Or.inl ⟨h5, h11, h_axle⟩
    · exact Or.inr ⟨h5, h11, h_axle⟩
  have h_final_le : ∀ u : T.Dart, u ∈ (Hypermap.extractGraph T darts).vertices →
      finalCharge T (rsstChargeShift T darts.length) darts u ≤ 0 := by
    intro u _
    have h_loop_u := loopless_orbit_of_forall_sameVertex_edge_false T darts h_all (Nat.le_refl _) h_loopless u
    have h5_u : 5 ≤ Hypermap.nodeDegree T u darts.length := h5_all u (h_all u)
    by_cases h56 : Hypermap.nodeDegree T u darts.length = 5 ∨ Hypermap.nodeDegree T u darts.length = 6
    · have h_res := finalCharge_le_zero_or_hasExactReducedAxle_deg_5_or_6 T darts h_all (Nat.le_refl _)
          h_tri h5_all u h_loop_u h56
      rcases h_res with h_le0 | ⟨d0, hd0, refl, h_axle⟩
      · exact h_le0
      · have hd0_deg : Hypermap.nodeDegree T d0 darts.length = Hypermap.nodeDegree T u darts.length :=
          nodeDegree_eq_of_mem_getOrbit T darts h_all (Nat.le_refl _) hd0
        exact False.elim (h_no_axle d0 refl (by omega) (by omega) (by rw [hd0_deg]; exact h_axle))
    · by_cases h711 :
          Hypermap.nodeDegree T u darts.length = 7 ∨
          Hypermap.nodeDegree T u darts.length = 8 ∨
          Hypermap.nodeDegree T u darts.length = 9 ∨
          Hypermap.nodeDegree T u darts.length = 10 ∨
          Hypermap.nodeDegree T u darts.length = 11
      · have h_res := finalCharge_le_zero_or_hasExactReducedAxle_deg_7_to_11 T darts h_all (Nat.le_refl _)
            h_tri h5_all theUnavoidableSet.toList Math.Discharging.discharging_trees_verified u h_loop_u h711
        rcases h_res with h_le0 | ⟨d0, hd0, refl, h_axle⟩
        · exact h_le0
        · have hd0_deg : Hypermap.nodeDegree T d0 darts.length = Hypermap.nodeDegree T u darts.length :=
            nodeDegree_eq_of_mem_getOrbit T darts h_all (Nat.le_refl _) hd0
          exact False.elim (h_no_axle d0 refl (by omega) (by omega) (by rw [hd0_deg]; exact h_axle))
      · have h12 : 12 ≤ Hypermap.nodeDegree T u darts.length := by omega
        by_cases h20 : 20 ≤ Hypermap.nodeDegree T u darts.length
        · exact finalCharge_le_zero_of_deg_ge_20 T darts h_all (Nat.le_refl _) u h_loop_u h20
        · have h_out5 : ∀ d ∈ getOrbit T.node darts.length u,
              dartRuleOutflow T darts.length (T.edge.f d) ≤ 5 := by
            intro d hd
            have hd_deg : Hypermap.nodeDegree T d darts.length = Hypermap.nodeDegree T u darts.length :=
              nodeDegree_eq_of_mem_getOrbit T darts h_all (Nat.le_refl _) hd
            have h_tgt : 9 ≤ Hypermap.nodeDegree T (T.edge.f (T.edge.f d)) darts.length := by
              rw [T.edge_involution]
              omega
            rcases dartRuleOutflow_le_5_or_hasExactReducedAxle_of_target_deg_ge_9
                T darts h_all (Nat.le_refl _) h_tri h5_all (T.edge.f d) h_tgt with h_le5 | ⟨d0, h5d, h11d, h_axle⟩
            · exact h_le5
            · exact False.elim (h_no_axle d0 false h5d h11d h_axle)
          exact finalCharge_le_zero_of_deg_ge_12 T darts h_all (Nat.le_refl _) u h_loop_u h12 h_out5
  have h_sum_final := sumCharges_finalCharge_eq_120 T (rsstChargeShift T darts.length) darts h_sum120
  exact positive_charge_contradiction
    (finalCharge T (rsstChargeShift T darts.length) darts)
    (Hypermap.extractGraph T darts).vertices h_sum_final h_final_le

/-- Normalized existence statement: any complete loopless triangulation with `sumCharges = 120`
    admits `(d0, refl)` with `5 ≤ deg ≤ 11` and `HasExactReducedAxle`. -/
theorem exists_hasExactReducedAxle_of_complete_triangulation_sum120'
    (T : Hypermap) [DecidableEq T.Dart] (darts : List T.Dart)
    (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_sum120 : sumCharges (fun v => initialCharge T v darts.length)
      (Hypermap.extractGraph T darts).vertices = 120)
    (h_loopless : ∀ d : T.Dart, Hypermap.sameVertex T d (T.edge.f d) darts.length = false)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree T d darts.length = 3)
    (h5_all : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree T d darts.length) :
    ∃ d0 : T.Dart, ∃ refl : Bool,
      let deg := Hypermap.nodeDegree T d0 darts.length
      5 ≤ deg ∧ deg ≤ 11 ∧ HasExactReducedAxle deg (cartDegOriented T darts.length deg refl d0) := by
  rcases exists_hasExactReducedAxle_of_complete_triangulation_sum120 T darts h_all h_sum120
      h_loopless h_tri h5_all with ⟨d0, ⟨h5, h11, ha⟩ | ⟨h5, h11, ha⟩⟩
  · exact ⟨d0, false, h5, h11, ha⟩
  · exact ⟨d0, true, h5, h11, ha⟩

/-- Unconditional All-Degrees Unavoidability for a complete planar triangulation `T`. -/
theorem exists_hasExactReducedAxle_of_complete_triangulation
    (T : Hypermap) [DecidableEq T.Dart] (darts : List T.Dart)
    (h_nodup : darts.Nodup) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_bridge : Hypermap.isBridgeless T darts)
    (h_planar : T.isPlanar darts.length darts = true)
    (h_conn : T.numComponents darts.length darts = 1)
    (h_loopless : ∀ d : T.Dart, Hypermap.sameVertex T d (T.edge.f d) darts.length = false)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree T d darts.length = 3)
    (h5_all : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree T d darts.length) :
    ∃ d0 : T.Dart, ∃ refl : Bool,
      let deg := Hypermap.nodeDegree T d0 darts.length
      5 ≤ deg ∧ deg ≤ 11 ∧ HasExactReducedAxle deg (cartDegOriented T darts.length deg refl d0) :=
  exists_hasExactReducedAxle_of_complete_triangulation_sum120' T darts h_all
    (initial_charge_sum_eq_120_of_complete_triangulation T darts h_nodup h_all h_bridge h_planar h_conn h_tri)
    h_loopless h_tri h5_all

/-- Unconditional All-Degrees Unavoidability on the dual triangulation `H.dual` of any
    cubic bridgeless connected planar map `H` of minimum face degree ≥ 5. -/
theorem dual_exists_hasExactReducedAxle_of_cubic
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b : Nat} (h_le_b : darts.length ≤ fuel_b)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_cubic : ∀ d ∈ darts, Hypermap.nodeDegree H d darts.length = 3)
    (h_face5 : ∀ d ∈ darts, 5 ≤ Hypermap.faceDegree H d darts.length) :
    ∃ d0 : H.Dart, ∃ refl : Bool,
      let deg := Hypermap.nodeDegree H.dual d0 darts.length
      5 ≤ deg ∧ deg ≤ 11 ∧
        HasExactReducedAxle deg (cartDegOriented H.dual darts.length deg refl d0) := by
  have h_sum120 := dual_initial_charge_sum_eq_120_of_cubic H darts h_nodup h_all h_bridge (Nat.le_refl _)
      h_planar h_conn h_cubic
  have h_loopless : ∀ d : H.Dart,
      Hypermap.sameVertex H.dual d (H.dual.edge.f d) darts.length = false :=
    dual_sameVertex_edge_eq_false_of_isBridgeless H darts h_all h_le_b (Nat.le_refl _) h_bridge
  have h_tri : ∀ d ∈ darts, Hypermap.faceDegree H.dual d darts.length = 3 := by
    intro d hd
    rw [faceDegree_dual_eq_nodeDegree_of_complete H darts h_all (Nat.le_refl _) d]
    exact h_cubic d hd
  have h5_all : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree H.dual d darts.length := by
    intro d hd
    rw [nodeDegree_dual_eq_faceDegree_of_complete H darts h_all (Nat.le_refl _) d]
    exact h_face5 d hd
  exact exists_hasExactReducedAxle_of_complete_triangulation_sum120' H.dual darts h_all
    h_sum120 h_loopless h_tri h5_all

end Math.Unavoidability
