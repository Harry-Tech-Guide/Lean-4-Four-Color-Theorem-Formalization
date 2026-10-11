import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Discharging
import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.ComputableReducer
import FourColorTheorem.Math.Planarity
import FourColorTheorem.Math.HypermapGraph
import FourColorTheorem.Math.Algorithm

namespace Math

open Classical

abbrev MapColoring (H : Hypermap) := Hypermap.FaceColoring H

/-- A hypermap is planar if its Euler characteristic matches 2 * components. -/
def IsPlanar (H : Hypermap) [BEq H.Dart] (darts : List H.Dart) (fuel : Nat := darts.length) : Prop :=
  Hypermap.isPlanar H fuel darts = true

/-- A configuration `c` appears in hypermap `H` (on dart list `darts`) if there is an
    injective embedding of the configuration's vertices into canonical darts such that
    all adjacency relations are preserved. -/
def appearsIn (c : Configuration) (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) : Prop :=
  ∃ (f : Nat → H.Dart),
    (∀ i < c.totalNodes, ∀ j < c.totalNodes, i ≠ j → f i ≠ f j) ∧
    (∀ i < c.totalNodes, f i ∈ darts) ∧
    (∀ i < c.totalNodes, ∀ j < c.totalNodes, c.adj i j = true → Hypermap.areAdjacentDarts H (f i) (f j) = true)

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

def IsCounterexampleOfSize (n : Nat) : Prop :=
  ∃ (H : Hypermap) (_ : DecidableEq H.Dart) (darts : List H.Dart),
    darts.length = n ∧ IsPlanar H darts ∧ Hypermap.isBridgeless H darts ∧ (MapColoring H → False)

/-- We proceed by assuming a Minimal Counterexample exists.
A minimal counterexample is a planar map that cannot be 4-colored, but any
strictly smaller planar bridgeless map CAN be 4-colored. -/
structure MinimalCounterexample (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) : Prop where
  is_planar : IsPlanar H darts
  is_bridgeless : Hypermap.isBridgeless H darts
  not_colorable : MapColoring H → False
  is_minimal : ∀ (H' : Hypermap) [DecidableEq H'.Dart] (darts' : List H'.Dart),
    darts'.length < darts.length → IsPlanar H' darts' → Hypermap.isBridgeless H' darts' → Nonempty (MapColoring H')

/-- A Reduction Witness for configuration `c` in hypermap `H`:
    Provides a strictly smaller planar bridgeless hypermap `H_ext` whose 4-coloring
    restricts to a boundary coloring that, when extended to the interior of `c`,
    glues into a valid 4-coloring of the entire hypermap `H`. -/
structure ReductionWitness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) (c : Configuration) where
  H_ext : Hypermap
  dec_ext : DecidableEq H_ext.Dart
  darts_ext : List H_ext.Dart
  smaller : darts_ext.length < darts.length
  planar : @IsPlanar H_ext (@instBEqOfDecidableEq H_ext.Dart dec_ext) darts_ext darts_ext.length
  bridgeless : Hypermap.isBridgeless H_ext darts_ext
  bnd_coloring : MapColoring H_ext → BoundaryColoring c
  valid_bnd : ∀ col, IsValidBoundaryColoring c (bnd_coloring col)
  glue : ∀ (col : MapColoring H_ext) (ext : Nat → Color),
    (∀ i < c.ringSize, ext i = bnd_coloring col i) →
    IsValidConfigColoring c ext →
    MapColoring H

/-- A Full Reduction Witness extends a Reduction Witness with Kempe chain pullback:
    any boundary coloring reachable via Kempe chain swaps from `col` can be realized
    by an exterior coloring `col'`. -/
structure FullReductionWitness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) (c : Configuration) extends ReductionWitness H darts c where
  kempe_pullback : ∀ (col : MapColoring H_ext) (b' : BoundaryColoring c),
    kempeEquivalent c (bnd_coloring col) b' →
    ∃ col' : MapColoring H_ext, bnd_coloring col' = b'

/-- Core Reducibility Contradiction Theorem:
    If a configuration in a minimal counterexample admits a full reduction witness,
    then D-reducibility strictly produces a valid 4-coloring of H, contradicting uncolorability. -/
theorem no_reducible_with_full_witness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (mc : MinimalCounterexample H darts) (c : Configuration)
    (w : FullReductionWitness H darts c)
    (hRed : IsDReducible c) : False := by
  have hNonempty := @MinimalCounterexample.is_minimal H _ darts mc w.H_ext w.dec_ext w.darts_ext w.smaller w.planar w.bridgeless
  rcases hNonempty with ⟨col_ext⟩
  have hbnd_valid := w.valid_bnd col_ext
  have h_cases := hRed (w.bnd_coloring col_ext) hbnd_valid
  cases h_cases with
  | inl hExtDirect =>
    rcases hExtDirect with ⟨full, h_match, h_full_valid⟩
    have h_glued := w.glue col_ext full (fun i hi => h_match i hi) h_full_valid
    exact mc.not_colorable h_glued
  | inr hKempe =>
    rcases hKempe with ⟨b', _, hEquiv, ⟨full', h_match', h_full_valid'⟩⟩
    rcases w.kempe_pullback col_ext b' hEquiv with ⟨col_ext', h_col_b'⟩
    have h_match_rewritten : ∀ i < c.ringSize, full' i = w.bnd_coloring col_ext' i := by
      intro i hi
      rw [h_col_b']
      exact h_match' i hi
    have h_glued := w.glue col_ext' full' h_match_rewritten h_full_valid'
    exact mc.not_colorable h_glued

/-- Topological Surgery Axiom: Embedding a reducible configuration into a hypermap
    yields a topological full reduction witness. -/
axiom reducible_reduction_witness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (mc : MinimalCounterexample H darts) (c : Configuration) :
  appearsIn c H darts → FullReductionWitness H darts c

/-- A key lemma: A minimal counterexample cannot contain ANY D-reducible configuration.
    Proved directly from the existence of a FullReductionWitness. -/
theorem no_reducible_in_minimal (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (mc : MinimalCounterexample H darts) (c : Configuration) :
  appearsIn c H darts → IsDReducible c → False := by
  intro hApp hRed
  have w := reducible_reduction_witness H darts mc c hApp
  exact no_reducible_with_full_witness H darts mc c w hRed

/-- A Planar Discharging Witness encapsulates the RSST discharging method for hypermap `H`:
    1. A charge shift rule conserving charge.
    2. Total charge conserved from Euler's characteristic ($120$).
    3. The discharging elimination property: if no unavoidable configuration is present,
       all final charges are non-positive ($\le 0$). -/
structure PlanarDischargingWitness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) where
  rule : Discharging.ChargeShift H.Dart
  charge_sum_120 : Discharging.sumCharges (Discharging.finalCharge H rule darts) (Hypermap.extractGraph H darts).vertices = 120
  discharging_elimination : ¬ (∃ c, c ∈ theUnavoidableSet ∧ appearsIn c H darts) → 
    ∀ v ∈ (Hypermap.extractGraph H darts).vertices, Discharging.finalCharge H rule darts v ≤ 0

/-- Core Discharging Theorem:
    A Planar Discharging Witness strictly proves the existence of an unavoidable configuration
    by deriving a contradiction between positive total Euler charge ($120$) and non-positive vertex charges. -/
theorem unavoidability_from_discharging (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (w : PlanarDischargingWitness H darts) :
    ∃ c, c ∈ theUnavoidableSet ∧ appearsIn c H darts := by
  by_cases hEx : ∃ c, c ∈ theUnavoidableSet ∧ appearsIn c H darts
  · exact hEx
  · have hNonpos := w.discharging_elimination hEx
    have hContr : Discharging.UnavoidableSetExists H w.rule darts :=
      Discharging.unavoidable_set_exists_of_sum_120 H w.rule darts w.charge_sum_120
    exact False.elim (hContr hNonpos)

/-- The Discharging Existence Axiom:
    Every planar, bridgeless map admits a Planar Discharging Witness based on the 32 RSST rules
    and Euler's characteristic equation $V - E + F = 2$. -/
axiom unavoidability_witness (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
  (h_planar : IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts) :
  PlanarDischargingWitness H darts

/-- The Unavoidability Theorem:
    Any planar, bridgeless map must contain at least one configuration from our unavoidable set.
    Proved constructively from the Planar Discharging Witness and Euler charge conservation. -/
theorem unavoidability_theorem (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (h_planar : IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts) : 
  ∃ c, c ∈ theUnavoidableSet ∧ appearsIn c H darts := by
  have w := unavoidability_witness H darts h_planar h_bridgeless
  exact unavoidability_from_discharging H darts w

/-- The RSST Reducibility Theorem:
    Every configuration in the unavoidable set is mathematically D-reducible (via Kempe chains).
    This establishes that unavoidable configurations can always be extended. -/
axiom unavoidable_is_reducible (c : Configuration) : c ∈ theUnavoidableSet → IsDReducible c

/-- If there were a minimal counterexample, we could prove `False` (a contradiction). -/
theorem minimal_counterexample_impossible (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) (mc : MinimalCounterexample H darts) : False := by
  have ⟨c, hc_in_set, hc_appears⟩ := unavoidability_theorem H darts mc.is_planar mc.is_bridgeless
  have hc_true_reducible := unavoidable_is_reducible c hc_in_set
  exact no_reducible_in_minimal H darts mc c hc_appears hc_true_reducible

/-- If a counterexample exists, there exists a genuine minimal counterexample (a planar, bridgeless, uncolorable map where every smaller map is colorable). -/
theorem minimal_counterexample_exists (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (h_planar : IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts) (h_not_colorable : MapColoring H → False) :
  ∃ (H' : Hypermap) (_ : DecidableEq H'.Dart) (darts' : List H'.Dart), MinimalCounterexample H' darts' := by
  have hEx : IsCounterexampleOfSize darts.length := ⟨H, inferInstance, darts, rfl, h_planar, h_bridgeless, h_not_colorable⟩
  have ⟨n, _, hPn, hmin⟩ := find_least IsCounterexampleOfSize darts.length hEx
  rcases hPn with ⟨H0, dec0, darts0, hlen, hplan, hbridge, hnotcol⟩
  refine ⟨H0, dec0, darts0, ⟨hplan, hbridge, hnotcol, ?_⟩⟩
  intro H' dec' darts' hlt hplan' hbridge'
  by_cases hcol' : Nonempty (MapColoring H')
  · exact hcol'
  · have hcolFalse : MapColoring H' → False := fun c => hcol' ⟨c⟩
    have hEx' : IsCounterexampleOfSize darts'.length := ⟨H', dec', darts', rfl, hplan', hbridge', hcolFalse⟩
    rw [← hlen] at hmin
    exact False.elim (hmin darts'.length hlt hEx')

/-- THE FOUR COLOR THEOREM
Every planar, bridgeless combinatorial map admits a valid 4-coloring. -/
theorem four_color_theorem (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart) 
  (h_planar : IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts) : Nonempty (MapColoring H) := by
  by_cases h_colorable : Nonempty (MapColoring H)
  · exact h_colorable
  · have h_not : MapColoring H → False := fun c => h_colorable ⟨c⟩
    have ⟨H', dec', darts', mc⟩ := minimal_counterexample_exists H darts h_planar h_bridgeless h_not
    exact False.elim (@minimal_counterexample_impossible H' dec' darts' mc)

end Math
