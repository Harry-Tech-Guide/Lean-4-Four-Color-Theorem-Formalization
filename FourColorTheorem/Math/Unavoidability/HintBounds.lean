import FourColorTheorem.Math.Discharging
import FourColorTheorem.Math.Batch.DischargeMaster

namespace Math
namespace Unavoidability

open Math.Discharging

/-- Decidable check that every interior vertex `iv ∈ fc.intVerts` has RSST degree `5 ≤ iv.d ≤ 11`. -/
def validFastConfDegs (fc : FastConf) : Bool :=
  fc.intVerts.all (fun iv => decide (5 ≤ iv.d) && decide (iv.d ≤ 11))

set_option maxRecDepth 200000 in
private theorem validFastConfDegs_all_633 :
    (List.range 633).all (fun h => validFastConfDegs (lookupFastConfRec h)) = true := by
  rfl

/-- Every RSST precomputed configuration `h < 633` has all interior vertex degrees in `5..11`. -/
theorem validFastConfDegs_lookupFastConfRec (h : Nat) (hh : h < 633) :
    validFastConfDegs (lookupFastConfRec h) = true :=
  List.all_eq_true.mp validFastConfDegs_all_633 h (List.mem_range.mpr hh)

theorem validFastConfDegs_intVert_bounds {fc : FastConf}
    (h_val : validFastConfDegs fc = true) {iv : IntVert} (hiv : iv ∈ fc.intVerts) :
    5 ≤ iv.d ∧ iv.d ≤ 11 := by
  have h_all := List.all_eq_true.mp h_val iv hiv
  rcases Bool.and_eq_true_iff.mp h_all with ⟨h5, h11⟩
  exact ⟨of_decide_eq_true h5, of_decide_eq_true h11⟩

theorem laneUpp_eq_cases (m : Nat) :
    laneUpp m = 5 ∨ laneUpp m = 6 ∨ laneUpp m = 7 ∨ laneUpp m = 8 ∨ laneUpp m = 12 := by
  unfold laneUpp
  split
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · split
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · split
      · exact Or.inr (Or.inr (Or.inl rfl))
      · split
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl

theorem eq_of_degBitIdx_eq_of_le_8 {a b : Nat}
    (ha : 5 ≤ a) (hb5 : 5 ≤ b) (hb8 : b ≤ 8)
    (h_idx : degBitIdx a = degBitIdx b) : a = b := by
  rcases (by omega : b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8) with rfl | rfl | rfl | rfl <;>
  ( by_cases ha5 : a ≤ 5 <;> by_cases ha6 : a = 6 <;> by_cases ha7 : a = 7 <;> by_cases ha8 : a = 8 <;>
    simp_all [degBitIdx] <;> omega )

/-- Strengthened RSST reducible axle witness with exact interior vertex degrees
    `cartDeg (getImgNat img iv.u) = iv.d` (requiring no upper degree cap on `cartDeg`). -/
def HasExactCartwheelConf (deg : Nat) (cartDeg : Nat → Nat) : Prop :=
  ∃ (cur h x y : Nat) (cw : Bool) (img : Nat),
    h < 633 ∧
    MatchesCartState31 deg cartDeg cur ∧
    let fc := lookupFastConfRec h
    rootedSubConfRec deg cur fc.z0 fc.z1 fc.qSteps x y cw = some img ∧
    checkIsoRec fc.ring fc.adjMat fc.intVerts deg cur img = true ∧
    ∀ iv ∈ fc.intVerts,
      getImgNat img iv.u ≤ 5 * deg ∧
      iv.d = getUppStrict deg cur (getImgNat img iv.u) ∧
      cartDeg (getImgNat img iv.u) = iv.d

/-- Upgrades `HasExactReducedAxle` to `HasExactCartwheelConf` without any upper cap on `cartDeg`,
    using `laneUpp` only returning `{5, 6, 7, 8, 12}` while every `fc_h` (`h < 633`) has `iv.d ≤ 11`. -/
theorem hasExactReducedAxle_exact_intVert_deg (deg : Nat) (cartDeg : Nat → Nat)
    (h0 : cartDeg 0 = deg)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cartDeg p)
    (h_red : HasExactReducedAxle deg cartDeg) :
    HasExactCartwheelConf deg cartDeg := by
  rcases h_red with ⟨cur, h, x, y, cw, img, hh, h_match31, h_root, h_iso, h_ivs⟩
  refine ⟨cur, h, x, y, cw, img, hh, h_match31, h_root, h_iso, ?_⟩
  intro iv hiv
  rcases h_ivs iv hiv with ⟨hp_le, hiv_upp, h_bit⟩
  refine ⟨hp_le, hiv_upp, ?_⟩
  have h_bounds := validFastConfDegs_intVert_bounds (validFastConfDegs_lookupFastConfRec h hh) hiv
  cases hp : getImgNat img iv.u with
  | zero =>
    rw [hp, getUppStrict_zero] at hiv_upp
    rw [h0, hiv_upp]
  | succ p' =>
    have hp1 : 1 ≤ getImgNat img iv.u := by rw [hp]; omega
    have h_upp_eq : getUppStrict deg cur (getImgNat img iv.u) = laneUpp (getLaneNat cur (getImgNat img iv.u)) :=
      getUppStrict_eq_laneUpp deg cur (getImgNat img iv.u) hp1
    rw [h_upp_eq] at hiv_upp
    have h_cases := laneUpp_eq_cases (getLaneNat cur (getImgNat img iv.u))
    rw [← hiv_upp] at h_cases
    have hiv8 : iv.d ≤ 8 := by rcases h_cases with h5 | h6 | h7 | h8 | h12 <;> omega
    have h_bit_eq := h_bit hp1
    have h_cd_min5 : 5 ≤ cartDeg (getImgNat img iv.u) := h_min5 (getImgNat img iv.u) hp1 hp_le
    rw [← hp]
    exact eq_of_degBitIdx_eq_of_le_8 h_cd_min5 h_bounds.1 hiv8 h_bit_eq

/-- Unconditional Master Degree 7–11 Discharging Dichotomy Theorem on `H` (eliminating `DischargingTreesVerified`):
    for every hub `u` of degree `deg ∈ {7, 8, 9, 10, 11}`, either `finalCharge ≤ 0` or `u` admits an
    exact `HasExactCartwheelConf` witness. -/
theorem unconditional_deg_7_to_11_dichotomy (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    (h_min5 : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree H d fuel)
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
        HasExactCartwheelConf deg (cartDegOriented H fuel deg refl d0) := by
  intro deg
  rcases finalCharge_le_zero_or_hasExactReducedAxle_deg_7_to_11 H darts h_all h_le h_tri h_min5
      theUnavoidableSet.toList discharging_trees_verified u h_loopless h_deg_range with h_le0 | h_red
  · exact Or.inl h_le0
  · rcases h_red with ⟨d0, hd0, refl, h_axle⟩
    refine Or.inr ⟨d0, hd0, refl, ?_⟩
    have h0 : cartDegOriented H fuel deg refl d0 0 = deg := by
      rw [cartDegOriented_zero]
      exact nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd0
    have h_cart_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cartDegOriented H fuel deg refl d0 p := by
      intro p _ _
      exact h_min5 _ (h_all _)
    exact hasExactReducedAxle_exact_intVert_deg deg (cartDegOriented H fuel deg refl d0) h0 h_cart_min5 h_axle

/-- Unconditional Master Degree 7–11 Discharging Dichotomy Theorem on `H.dual`. -/
theorem dual_unconditional_deg_7_to_11_dichotomy (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b)
    (h_cubic : ∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3)
    (h_min5 : ∀ d ∈ darts, 5 ≤ Hypermap.nodeDegree H.dual d fuel)
    (u : H.Dart)
    (h_deg_range : Hypermap.nodeDegree H.dual u fuel = 7 ∨
                   Hypermap.nodeDegree H.dual u fuel = 8 ∨
                   Hypermap.nodeDegree H.dual u fuel = 9 ∨
                   Hypermap.nodeDegree H.dual u fuel = 10 ∨
                   Hypermap.nodeDegree H.dual u fuel = 11) :
    let deg := Hypermap.nodeDegree H.dual u fuel
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 ∨
      ∃ d0 ∈ getOrbit H.dual.node fuel u, ∃ refl : Bool,
        HasExactCartwheelConf deg (cartDegOriented H.dual fuel deg refl d0) := by
  have h_tri_dual : ∀ d ∈ darts, Hypermap.faceDegree H.dual d fuel = 3 :=
    (dual_triangulation_iff_cubic H darts h_all h_le).mpr h_cubic
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact unconditional_deg_7_to_11_dichotomy H.dual darts h_all h_le h_tri_dual h_min5 u h_loopless h_deg_range

end Unavoidability
end Math
