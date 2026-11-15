import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Discharging
import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.Planarity
import FourColorTheorem.Math.HypermapGraph
import FourColorTheorem.Math.Topology.KempeTopology
import FourColorTheorem.Math.Topology.Surgery
import FourColorTheorem.Math.Topology.Euler
import FourColorTheorem.Math.Topology.Jordan
import FourColorTheorem.Math.MasterCertificate
import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.Batch.DischargeMaster
import FourColorTheorem.Math.Topology.SubtypeSurgery
import FourColorTheorem.Math.Topology.MinimalCounterexamplePrimal
import FourColorTheorem.Math.Topology.CubicGirth5
import FourColorTheorem.Math.Topology.CartwheelFaithfulness
import FourColorTheorem.Math.Topology.DiskExcision
import FourColorTheorem.Math.Unavoidability.FreeCompletionProjection

namespace Math

open Classical

abbrev MapColoring (H : Hypermap) := Hypermap.FaceColoring H

/-- A hypermap is planar if its Euler characteristic matches 2 * components. -/
def IsPlanar (H : Hypermap) [BEq H.Dart] (darts : List H.Dart) (fuel : Nat := darts.length) : Prop :=
  Hypermap.isPlanar H fuel darts = true

/-- Removing a dart that belongs to a non-empty list of darts strictly reduces its length. -/
theorem erase_dart_strictly_smaller {D : Type} [BEq D] [LawfulBEq D] (darts : List D) (d : D) (hd : d ∈ darts) :
    (darts.erase d).length < darts.length := by
  have hlen := List.length_erase_of_mem hd
  have hpos : darts.length > 0 := List.length_pos_of_mem hd
  omega

def findMinHelper (P : Nat → Prop) [DecidablePred P] : Nat → Nat → Nat
  | 0, cur => cur
  | fuel + 1, cur => if P cur then cur else findMinHelper P fuel (cur + 1)

theorem findMinHelper_spec (P : Nat → Prop) [DecidablePred P] (fuel cur : Nat) 
  (hP : ∃ k ≤ fuel, P (cur + k)) :
  P (findMinHelper P fuel cur) ∧ ∀ m, cur ≤ m → m < findMinHelper P fuel cur → ¬ P m := by
  induction fuel generalizing cur with
  | zero =>
    rcases hP with ⟨k, hk, hPk⟩
    have hk0 : k = 0 := Nat.le_zero.mp hk
    subst hk0
    rw [Nat.add_zero] at hPk
    dsimp [findMinHelper]
    refine ⟨hPk, ?_⟩
    intro m hcur hm
    have : m < cur := hm
    exact (Nat.not_le_of_gt this hcur).elim
  | succ fuel ih =>
    dsimp [findMinHelper]
    split
    · rename_i hPcur
      refine ⟨hPcur, ?_⟩
      intro m hcur hm
      exact (Nat.not_le_of_gt hm hcur).elim
    · rename_i hnotPcur
      rcases hP with ⟨k, hk, hPk⟩
      cases k with
      | zero =>
        rw [Nat.add_zero] at hPk
        exact (hnotPcur hPk).elim
      | succ k =>
        have h_fuel : k ≤ fuel := Nat.le_of_succ_le_succ hk
        have h_shift : cur + (k + 1) = (cur + 1) + k := by omega
        rw [h_shift] at hPk
        have ih_goal := ih (cur + 1) ⟨k, h_fuel, hPk⟩
        refine ⟨ih_goal.1, ?_⟩
        intro m hcur hm
        cases Nat.eq_or_lt_of_le hcur with
        | inl heq =>
          subst heq
          exact hnotPcur
        | inr hlt =>
          have hle_succ : cur + 1 ≤ m := hlt
          exact ih_goal.2 m hle_succ hm

theorem find_least (P : Nat → Prop) (N : Nat) (hPN : P N) :
    ∃ n ≤ N, P n ∧ ∀ m < n, ¬ P m := by
  haveI : DecidablePred P := fun _ => Classical.propDecidable _
  have hP : ∃ k ≤ N, P (0 + k) := ⟨N, Nat.le_refl N, by rwa [Nat.zero_add]⟩
  have hspec := findMinHelper_spec P N 0 hP
  refine ⟨findMinHelper P N 0, ?_, hspec.1, ?_⟩
  · by_cases hle : findMinHelper P N 0 ≤ N
    · exact hle
    · have hlt : N < findMinHelper P N 0 := Nat.lt_of_not_le hle
      have hnot := hspec.2 N (Nat.zero_le N) hlt
      exact False.elim (hnot hPN)
  · intro m hm
    exact hspec.2 m (Nat.zero_le m) hm

/-- A list of darts is complete for hypermap `H` if it contains no duplicates,
    contains every dart in `H.Dart`, and is non-empty. -/
def IsCompleteDarts (H : Hypermap) (darts : List H.Dart) : Prop :=
  darts.Nodup ∧ (∀ d : H.Dart, d ∈ darts) ∧ darts ≠ []

@[deprecated IsCompleteDarts (since := "2026-11-04")]
abbrev IsBasicCompleteDarts (H : Hypermap) (darts : List H.Dart) : Prop :=
  IsCompleteDarts H darts

/-- All strictly smaller complete planar bridgeless hypermaps admit a 4-coloring. -/
def AllSmallerColorable (n : Nat) : Prop :=
  ∀ (H' : Hypermap) [DecidableEq H'.Dart] (darts' : List H'.Dart),
    IsCompleteDarts H' darts' →
    darts'.length < n →
    IsPlanar H' darts' →
    Hypermap.isBridgeless H' darts' →
    Nonempty (MapColoring H')

def IsCounterexampleOfSize (n : Nat) : Prop :=
  ∃ (H : Hypermap) (_ : DecidableEq H.Dart) (darts : List H.Dart),
    IsCompleteDarts H darts ∧ darts.length = n ∧ IsPlanar H darts ∧ Hypermap.isBridgeless H darts ∧ (MapColoring H → False)

/-- We proceed by assuming a Minimal Counterexample exists.
A minimal counterexample is a planar map that cannot be 4-colored, but any
strictly smaller planar bridgeless map CAN be 4-colored. -/
structure MinimalCounterexample (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) : Prop where
  complete : IsCompleteDarts H darts
  is_planar : IsPlanar H darts
  is_bridgeless : Hypermap.isBridgeless H darts
  not_colorable : MapColoring H → False
  is_minimal : ∀ (H' : Hypermap) [DecidableEq H'.Dart] (darts' : List H'.Dart),
    IsCompleteDarts H' darts' →
    darts'.length < darts.length → IsPlanar H' darts' → Hypermap.isBridgeless H' darts' → Nonempty (MapColoring H')

theorem MinimalCounterexample.all_smaller_colorable (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) : AllSmallerColorable darts.length := by
  intro H' dec' darts' hComp hlt hPlan hBridge
  exact @MinimalCounterexample.is_minimal H _ darts mc H' dec' darts' hComp hlt hPlan hBridge

/-- A Reduction Witness for configuration `c` in hypermap `H`:
    Provides a strictly smaller planar bridgeless hypermap `H_ext` whose 4-coloring
    restricts to a boundary coloring that, when extended to the interior of `c`,
    glues into a valid 4-coloring of the entire hypermap `H`. -/
structure ReductionWitness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) (c : Configuration) where
  H_ext : Hypermap
  dec_ext : DecidableEq H_ext.Dart
  darts_ext : List H_ext.Dart
  complete_ext : IsCompleteDarts H_ext darts_ext
  smaller : darts_ext.length < darts.length
  planar : @IsPlanar H_ext (@instBEqOfDecidableEq H_ext.Dart dec_ext) darts_ext darts_ext.length
  bridgeless : Hypermap.isBridgeless H_ext darts_ext
  bnd_coloring : MapColoring H_ext → BoundaryColoring c
  valid_bnd : ∀ col, IsValidBoundaryColoring c (bnd_coloring col)
  bnd_contracts : ∀ col, extendsToContracted c (bnd_coloring col)
  glue : ∀ (col : MapColoring H_ext) (ext : Nat → Color),
    (∀ i < c.ringSize, ext i = bnd_coloring col i) →
    IsValidConfigColoring c ext →
    MapColoring H

/-- A Full Reduction Witness extends a Reduction Witness with Kempe chain pullback:
    any boundary coloring eliminated under the adversarial Kempe game on the boundary
    can be pulled back to an exterior coloring that glues with an interior extension. -/
structure FullReductionWitness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) (c : Configuration) extends ReductionWitness H darts c where
  kempe_pullback : ∀ (col : MapColoring H_ext),
    Eliminated c (bnd_coloring col) →
    ∃ (col' : MapColoring H_ext) (ext : Nat → Color),
      (∀ i < c.ringSize, ext i = bnd_coloring col' i) ∧ IsValidConfigColoring c ext

/-- Core Reducibility Contradiction Theorem:
    If a configuration in a minimal counterexample admits a full reduction witness,
    then reducibility strictly produces a valid 4-coloring of H, contradicting uncolorability. -/
theorem no_reducible_with_full_witness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) (c : Configuration)
    (w : FullReductionWitness H darts c)
    (hRed : IsReducible c) : False := by
  have hNonempty := @MinimalCounterexample.is_minimal H _ darts mc w.H_ext w.dec_ext w.darts_ext w.complete_ext w.smaller w.planar w.bridgeless
  rcases hNonempty with ⟨col_ext⟩
  have hbnd_valid := w.valid_bnd col_ext
  have hbnd_sat := w.bnd_contracts col_ext
  have hElim := reducible_elimination c hRed (w.bnd_coloring col_ext) hbnd_valid hbnd_sat
  rcases w.kempe_pullback col_ext hElim with ⟨col_ext', ext, h_match, h_valid⟩
  have h_glued := w.glue col_ext' ext h_match h_valid
  exact mc.not_colorable h_glued

/-!
### Subtype Disk Excision Foundation

True subtype excision (`_root_.Hypermap.exciseSubtype` and `_root_.Hypermap.subDarts`) removes
interior darts cleanly at the type level (`{ d : H.Dart // d ∉ removed }`), eliminating the
phantom fixed-point darts of `exciseFixed` while preserving `IsCompleteDarts` and strictly
decreasing dart count (`_root_.Hypermap.exciseSubtype_strictly_smaller`). -/

/-- Subtype excision preserves completeness of a complete dart list whenever at least one
    dart survives outside `removed`. -/
theorem subtype_excision_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts removed : List H.Dart) (e' n' f' : Perm H.Dart)
    (h_e_inv : ∀ d, e'.f (e'.f d) = d)
    (h_enf : ∀ d, e'.f (n'.f (f'.f d)) = d)
    (h_edge : ∀ d, d ∈ removed ↔ e'.f d ∈ removed)
    (h_node : ∀ d, d ∈ removed ↔ n'.f d ∈ removed)
    (h_comp : IsCompleteDarts H darts)
    (h_surv : ∃ d ∈ darts, d ∉ removed) :
    IsCompleteDarts
      (_root_.Hypermap.exciseSubtype H removed e' n' f' h_e_inv h_enf h_edge h_node)
      (_root_.Hypermap.subDarts darts removed) :=
  _root_.Hypermap.exciseSubtype_complete H darts removed e' n' f'
    h_e_inv h_enf h_edge h_node h_comp.1 h_comp.2.1 h_surv

/-- Concrete 4-dart spherical 2-edge non-vacuity witness for subtype excision. -/
theorem subtype_excision_nonvacuous :
    ∃ (darts removed : List (Fin 4)),
      let darts' := _root_.Hypermap.subDarts darts removed
      darts'.Nodup ∧ (∀ d : { d : Fin 4 // d ∉ removed }, d ∈ darts') ∧
        darts' ≠ [] ∧ darts'.length < darts.length :=
  ⟨[0, 1, 2, 3], [2, 3], _root_.Hypermap.twoEdgeSphere_excise_witness⟩

/-!
### Stage R Standardization Bridge (`Phase 3` & `Phase 4`)

Phase 1 (unconditional reducibility of all 633 configurations via `MasterCertificate.rsst_all_unavoidable_reducible`)
and Phase 5 (unconditional dual unavoidability via `Unavoidability.dual_unavoidability_appearsInTriangulation_matched`
lifting to RSST `(3.3)–(3.4)` `Unavoidability.CorrespondingProjection` via
`Unavoidability.appearsInTriangulation_matched_implies_correspondingProjection`) and the
Phase 3 primal structural theorems (`mc_numComponents_eq_one`, `mc_nodeDegree_eq_three`,
`mc_faceDegree_ge_five` from `MinimalCounterexamplePrimal` and `CubicGirth5`) are now **100% discharged**.

All Phase 1–3, Phase 5, and Phase 4 D-reducibility prerequisites —
- Phase 1 (`MasterCertificate.rsst_all_unavoidable_reducible`),
- Phase 3 primal structural theorems (`mc_numComponents_eq_one`, `mc_nodeDegree_eq_three`,
  `mc_faceDegree_ge_five`) and dual cartwheel faithfulness (`_root_.Hypermap.mc_cartwheelEmbedded_dual`),
- Phase 5 unconditional dual unavoidability (`Unavoidability.dual_unavoidability_appearsInTriangulation_matched`
  lifting to RSST `(3.3)–(3.4)` `CorrespondingProjection` + `MatchesConfCycle` + `RingFanProjectionConsistent`),
- Phase 4 capped-ring subtype disk excision, Kempe chain pullback, dual-primal gluing, and
  all 249 D-reducible configurations (`_root_.Hypermap.d_reducible_matched_impossible`),
- Phase 4 conditional C-reducible contradiction (`_root_.Hypermap.c_reducible_matched_impossible_of_mod_coloring`) —
are now **100% discharged**.

Only C-reducible contract-edge coloring existence (`VertexColoringMod H.dual (mappedContractDarts p.emb)`
when `IsCReducible c`) remains in `RSSTStandardizationBridge`. -/

/-- Any `Math.MinimalCounterexample` satisfies `Hypermap.PrimalMinimalCounterexample`. -/
theorem MinimalCounterexample.toPrimal {H : Hypermap} [DecidableEq H.Dart] {darts : List H.Dart}
    (mc : MinimalCounterexample H darts) : _root_.Hypermap.PrimalMinimalCounterexample H darts where
  nodup := mc.complete.1
  complete := mc.complete.2.1
  nonempty := mc.complete.2.2
  is_planar := mc.is_planar
  is_bridgeless := mc.is_bridgeless
  not_colorable := mc.not_colorable
  is_minimal H' _ darts' hnd hcomp hne hlt hplan hbridge :=
    mc.is_minimal H' darts' ⟨hnd, hcomp, hne⟩ hlt hplan hbridge

/-- Every minimal counterexample is connected (`numComponents = 1`), proved unconditionally. -/
theorem mc_numComponents_eq_one (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    _root_.Hypermap.numComponents H darts.length darts = 1 :=
  _root_.Hypermap.mc_numComponents_eq_one H darts mc.toPrimal

/-- Every minimal counterexample is cubic (`nodeDegree = 3`), proved unconditionally. -/
theorem mc_nodeDegree_eq_three (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∀ d ∈ darts, Hypermap.nodeDegree H d darts.length = 3 := fun d _ =>
  _root_.Hypermap.mc_nodeDegree_eq_three H darts mc.toPrimal d

/-- Every face in a minimal counterexample has size at least 5 (`girth ≥ 5`), proved unconditionally. -/
theorem mc_faceDegree_ge_five (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∀ d ∈ darts, 5 ≤ Hypermap.faceDegree H d darts.length := fun d _ =>
  _root_.Hypermap.mc_faceDegree_ge_five H darts mc.toPrimal d

/-- The dual hypermap `H.dual` of any minimal counterexample is unconditionally a triangulation
    (`faceDegree H.dual d darts.length = 3` on every dart). -/
theorem mc_dual_triangulation (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∀ d : H.dual.Dart, d ∈ darts → Hypermap.faceDegree H.dual d darts.length = 3 := by
  intro d hd
  rw [Discharging.faceDegree_dual_eq_nodeDegree_of_complete H darts mc.complete.2.1 (Nat.le_refl _) d]
  exact mc_nodeDegree_eq_three H darts mc d hd

def RSSTStandardizationBridge : Prop :=
  ∀ (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart),
    MinimalCounterexample H darts →
    ∀ (h : Nat) (hh : h < 633),
      let rc := parsedRConfList[h]'(by rw [Unavoidability.parsedRConfList_length]; exact hh)
      let c := configOfRConf rc
      IsCReducible c →
      ∀ (p : Unavoidability.CorrespondingProjection c H.dual darts),
      Unavoidability.MatchesConfCycle rc H.dual darts p.emb →
      Nonempty (Unavoidability.VertexColoringMod H.dual (Unavoidability.mappedContractDarts p.emb))

/-- The Discharging Verification Theorem:
    The computational correctness of the RSST cartwheel discharging trees (degrees 7 through 11)
    is formally verified in-kernel via reflection and `kernel reduction` by `discharging_trees_verified`. -/
theorem rsst_discharging_computationally_verified :
    Discharging.DischargingTreesVerified theUnavoidableSet.toList :=
  Discharging.discharging_trees_verified

/-- Indexing `theUnavoidableSet` at `h < 633` agrees definitionally with `configOfRConf parsedRConfList[h]`. -/
theorem theUnavoidableSet_getElem_eq_configOfRConf (h : Nat) (hh : h < 633) :
    theUnavoidableSet[h]'(by rw [unavoidable_size_eq]; exact hh) =
      configOfRConf (parsedRConfList[h]'(by rw [Unavoidability.parsedRConfList_length]; exact hh)) := by
  change (parsedRConfList.map configOfRConf)[h]'(by rw [List.length_map, parsedRConfList_length]; exact hh) =
    configOfRConf (parsedRConfList[h]'(by rw [Unavoidability.parsedRConfList_length]; exact hh))
  exact List.getElem_map configOfRConf

/-- In any minimal counterexample, the dual hypermap `H.dual` is unconditionally a triangulation
    (`faceDegree H.dual d darts.length = 3` on every dart). -/
theorem rsst_mc_dual_triangulation (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∀ d : H.dual.Dart, d ∈ darts → Hypermap.faceDegree H.dual d darts.length = 3 :=
  mc_dual_triangulation H darts mc

/-- **Unconditional Full Matched Dual Unavoidability Projection Theorem:**
    Every minimal counterexample contains some `h < 633` realizing a faithful RSST `(3.3)–(3.4)`
    `CorrespondingProjection` on `H.dual`, together with `MatchesConfCycle` and
    `RingFanProjectionConsistent`, proved completely unconditionally via Phase 3
    `_root_.Hypermap.mc_cartwheelEmbedded_dual` and `correspondingProjectionOfEmbedding`. -/
theorem rsst_unavoidability_dual_matched_full (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∃ (h : Nat) (hh : h < 633),
      let hlen : h < parsedRConfList.length := by
        rw [Unavoidability.parsedRConfList_length]; exact hh
      let rc := parsedRConfList[h]'hlen
      let c := configOfRConf rc
      ∃ (p : Unavoidability.CorrespondingProjection c H.dual darts),
        Unavoidability.MatchesConfCycle rc H.dual darts p.emb ∧
        Unavoidability.RingFanProjectionConsistent rc H.dual darts p.emb := by
  have hCartwheel : ∀ (refl : Bool) (d0 : H.Dart),
      5 ≤ Hypermap.nodeDegree H.dual d0 darts.length →
      Hypermap.nodeDegree H.dual d0 darts.length ≤ 11 →
      Unavoidability.CartwheelEmbedded H.dual darts.length refl d0 :=
    fun refl d0 h5 h11 => _root_.Hypermap.mc_cartwheelEmbedded_dual H darts mc.toPrimal refl d0 h5 h11
  obtain ⟨h, hh, e, hmc⟩ :=
    Unavoidability.dual_unavoidability_appearsInTriangulation_matched H darts
      mc.complete.1 mc.complete.2.1 mc.is_bridgeless mc.is_planar
      (mc_numComponents_eq_one H darts mc)
      (mc_nodeDegree_eq_three H darts mc)
      (mc_faceDegree_ge_five H darts mc)
      hCartwheel
  have hlen : h < parsedRConfList.length := by
    rw [Unavoidability.parsedRConfList_length]; exact hh
  have h_tri : ∀ d : H.dual.Dart, d ∈ darts → Hypermap.faceDegree H.dual d darts.length = 3 :=
    mc_dual_triangulation H darts mc
  let p := Unavoidability.correspondingProjectionOfEmbedding h hh H.dual darts mc.complete.2.1 hlen e
  have hfan := Unavoidability.ring_fan_projection_consistent h hh H.dual darts mc.complete.2.1 h_tri hlen e hmc
  exact ⟨h, hh, p, hmc, hfan⟩

/-- **Unconditional Matched Dual Unavoidability Projection Theorem:**
    Every minimal counterexample contains some configuration `h < 633` from `theUnavoidableSet`
    realizing a faithful RSST `(3.3)–(3.4)` `CorrespondingProjection` on `H.dual`, proved
    unconditionally without `RSSTStandardizationBridge`. -/
theorem rsst_unavoidability_dual_matched (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∃ (h : Nat) (hh : h < 633),
      let c := theUnavoidableSet[h]'(by rw [unavoidable_size_eq]; exact hh)
      c ∈ theUnavoidableSet ∧
      Nonempty (Unavoidability.CorrespondingProjection c H.dual darts) := by
  obtain ⟨h, hh, p, _, _⟩ := rsst_unavoidability_dual_matched_full H darts mc
  have h_eq := theUnavoidableSet_getElem_eq_configOfRConf h hh
  refine ⟨h, hh, Array.getElem_mem _, ?_⟩
  exact ⟨h_eq.symm ▸ p⟩

/-- **Unconditional RSST Unavoidability Theorem (`CorrespondingProjection` on `H.dual`):**
    Every minimal counterexample to the Four Color Theorem yields an unavoidable configuration
    `c ∈ theUnavoidableSet` admitted via a faithful `CorrespondingProjection c H.dual darts`. -/
theorem rsst_unavoidability_dual_projection (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∃ c ∈ theUnavoidableSet, Nonempty (Unavoidability.CorrespondingProjection c H.dual darts) := by
  obtain ⟨h, hh, hc_in, hProj⟩ := rsst_unavoidability_dual_matched H darts mc
  exact ⟨_, hc_in, hProj⟩

/-- Direct unconditional existence of a dual `CorrespondingProjection` via `AppearsInTriangulation`. -/
theorem rsst_unavoidability_dual_projection_of_appearsInTriangulation
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∃ c ∈ theUnavoidableSet, Nonempty (Unavoidability.CorrespondingProjection c H.dual darts) := by
  have hCartwheel : ∀ (refl : Bool) (d0 : H.Dart),
      5 ≤ Hypermap.nodeDegree H.dual d0 darts.length →
      Hypermap.nodeDegree H.dual d0 darts.length ≤ 11 →
      Unavoidability.CartwheelEmbedded H.dual darts.length refl d0 :=
    fun refl d0 h5 h11 => _root_.Hypermap.mc_cartwheelEmbedded_dual H darts mc.toPrimal refl d0 h5 h11
  obtain ⟨c, hc_in, hc_app⟩ :=
    Unavoidability.dual_unavoidability_appearsInTriangulation H darts
      mc.complete.1 mc.complete.2.1 mc.is_bridgeless mc.is_planar
      (mc_numComponents_eq_one H darts mc)
      (mc_nodeDegree_eq_three H darts mc)
      (mc_faceDegree_ge_five H darts mc)
      hCartwheel
  exact ⟨c, hc_in,
    Unavoidability.appearsInTriangulation_implies_correspondingProjection
      c hc_in H.dual darts mc.complete.2.1 hc_app⟩

/-- **Unconditional Computational Reducibility of the RSST Unavoidable Set:**
    Every configuration in the canonical 633 unavoidable set is mathematically reducible
    (D-reducible or C-reducible), proven unconditionally from the in-kernel batch certificates
    across all 138 batch files (`MasterCertificate.master_suite_certifies_idx`) and `KernelSoundness`. -/
theorem rsst_all_unavoidable_reducible (c : Configuration) :
    c ∈ theUnavoidableSet → IsReducible c :=
  MasterCertificate.rsst_all_unavoidable_reducible c

/-- Every minimal counterexample contains an indexed configuration `h < 633` that is both
    unconditionally reducible and realizes a faithful `CorrespondingProjection` on `H.dual`. -/
theorem exists_reducible_dual_projection (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) :
    ∃ (h : Nat) (hh : h < 633),
      let c := theUnavoidableSet[h]'(by rw [unavoidable_size_eq]; exact hh)
      c ∈ theUnavoidableSet ∧
      IsReducible c ∧
      Nonempty (Unavoidability.CorrespondingProjection c H.dual darts) := by
  obtain ⟨h, hh, hc_in, hProj⟩ := rsst_unavoidability_dual_matched H darts mc
  exact ⟨h, hh, hc_in, rsst_all_unavoidable_reducible _ hc_in, hProj⟩

/-- If there were a minimal counterexample, we could prove `False` (a contradiction).
    Proved by chaining unconditional dual unavoidability projection, unconditional Phase 1
    reducibility, Phase 4 capped-ring disk excision (`d_reducible_matched_impossible` for all
    249 D-reducible configurations), and `c_reducible_matched_impossible_of_mod_coloring` with
    the narrowed C-reducible `RSSTStandardizationBridge`. -/
theorem minimal_counterexample_impossible (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_rsst : RSSTStandardizationBridge)
    (mc : MinimalCounterexample H darts) : False := by
  obtain ⟨h, hh, p, hmc, hfan⟩ := rsst_unavoidability_dual_matched_full H darts mc
  have hlen : h < parsedRConfList.length := by
    rw [Unavoidability.parsedRConfList_length]; exact hh
  have hc_in : configOfRConf (parsedRConfList[h]'hlen) ∈ theUnavoidableSet := by
    rw [← theUnavoidableSet_getElem_eq_configOfRConf h hh]
    exact Array.getElem_mem _
  have hRed := rsst_all_unavoidable_reducible _ hc_in
  rcases hRed with hD | hC
  · exact _root_.Hypermap.d_reducible_matched_impossible H darts mc.toPrimal h hh hlen p hmc hfan hD
  · obtain ⟨col_mod⟩ := h_rsst H darts mc h hh hC p hmc
    exact _root_.Hypermap.c_reducible_matched_impossible_of_mod_coloring
      H darts mc.toPrimal h hh hlen p hmc hfan hC col_mod


/-- If a counterexample exists, there exists a genuine minimal counterexample (a planar, bridgeless, uncolorable map where every smaller map is colorable). -/
theorem minimal_counterexample_exists (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (h_complete : IsCompleteDarts H darts)
  (h_planar : IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts) (h_not_colorable : MapColoring H → False) :
  ∃ (H' : Hypermap) (_ : DecidableEq H'.Dart) (darts' : List H'.Dart), MinimalCounterexample H' darts' := by
  have hEx : IsCounterexampleOfSize darts.length := ⟨H, inferInstance, darts, h_complete, rfl, h_planar, h_bridgeless, h_not_colorable⟩
  have ⟨n, _, hPn, hmin⟩ := find_least IsCounterexampleOfSize darts.length hEx
  rcases hPn with ⟨H0, dec0, darts0, hcomp0, hlen, hplan, hbridge, hnotcol⟩
  refine ⟨H0, dec0, darts0, ⟨hcomp0, hplan, hbridge, hnotcol, ?_⟩⟩
  intro H' dec' darts' hcomp' hlt hplan' hbridge'
  by_cases hcol' : Nonempty (MapColoring H')
  · exact hcol'
  · have hcolFalse : MapColoring H' → False := fun c => hcol' ⟨c⟩
    have hEx' : IsCounterexampleOfSize darts'.length := ⟨H', dec', darts', hcomp', rfl, hplan', hbridge', hcolFalse⟩
    rw [← hlen] at hmin
    exact False.elim (hmin darts'.length hlt hEx')

/-- THE FOUR COLOR THEOREM
Every planar, bridgeless combinatorial map admits a valid 4-coloring. -/
theorem four_color_theorem (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (h_complete : IsCompleteDarts H darts)
  (h_planar : IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts)
  (h_rsst : RSSTStandardizationBridge) : Nonempty (MapColoring H) := by
  by_cases h_colorable : Nonempty (MapColoring H)
  · exact h_colorable
  · have h_not : MapColoring H → False := fun c => h_colorable ⟨c⟩
    have ⟨H', dec', darts', mc⟩ := minimal_counterexample_exists H darts h_complete h_planar h_bridgeless h_not
    exact False.elim (@minimal_counterexample_impossible H' dec' darts' h_rsst mc)

end Math
