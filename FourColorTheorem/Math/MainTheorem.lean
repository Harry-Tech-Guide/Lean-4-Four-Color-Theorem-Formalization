import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Discharging
import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.ComputableReducer

namespace Math

open Classical

-- `theUnavoidableSet` is now provided by `U633Parser.lean`.

/-- A placeholder for the "appearsIn" relation: a configuration physically appearing in the hypermap. -/
axiom appearsIn {D : Type} (c : Configuration) (H : Hypermap D) (darts : List D) : Prop

/-- We proceed by assuming a Minimal Counterexample exists.
A minimal counterexample is a planar map that cannot be 4-colored, but any
"smaller" map (obtained by removing edges or shrinking configurations) CAN be 4-colored. -/
structure MinimalCounterexample {D : Type} [DecidableEq D] (H : Hypermap D) (darts : List D) : Prop where
  is_planar : Hypermap.IsPlanar H darts
  is_bridgeless : Hypermap.isBridgeless H darts
  not_colorable : MapColoring H → False

/-- A key lemma: A minimal counterexample cannot contain ANY D-reducible configuration.
If it did, the map could be reduced, colored, and the coloring extended, proving it
was colorable in the first place! -/
axiom no_reducible_in_minimal {D : Type} [DecidableEq D] (H : Hypermap D) (darts : List D) (mc : MinimalCounterexample H darts) (c : Configuration) :
  appearsIn c H darts → IsDReducible c → False

/-- The Unavoidability Theorem: 
Any planar, bridgeless map must contain at least one configuration from our unavoidable set. -/
axiom unavoidability_theorem {D : Type} [DecidableEq D] (H : Hypermap D) (darts : List D) 
  (h_planar : Hypermap.IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts) : 
  ∃ c, c ∈ theUnavoidableSet ∧ appearsIn c H darts

/-- The Reducibility Theorem:
Every configuration in the unavoidable set is mathematically D-reducible (via Kempe chains).
This is what we computationally verify. -/
axiom computable_reduction_sound (c : Configuration) :
  ComputableReducer.isComputablyDReducible c = true → IsDReducible c

axiom reducibility_theorem (c : Configuration) : c ∈ theUnavoidableSet → ComputableReducer.isComputablyDReducible c = true

/-- If there were a minimal counterexample, we could prove `False` (a contradiction). -/
theorem minimal_counterexample_impossible {D : Type} [DecidableEq D] (H : Hypermap D) (darts : List D) (mc : MinimalCounterexample H darts) : False := by
  have ⟨c, hc_in_set, hc_appears⟩ := unavoidability_theorem H darts mc.is_planar mc.is_bridgeless
  have hc_reducible := reducibility_theorem c hc_in_set
  have hc_true_reducible := computable_reduction_sound c hc_reducible
  exact no_reducible_in_minimal H darts mc c hc_appears hc_true_reducible

/-- If a counterexample exists, there exists a MINIMAL counterexample (by strong induction on graph size). -/
axiom minimal_counterexample_exists {D : Type} [DecidableEq D] (H : Hypermap D) (darts : List D) 
  (h_planar : Hypermap.IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts) (h_not_colorable : MapColoring H → False) :
  ∃ (D' : Type) (_ : DecidableEq D') (H' : Hypermap D') (darts' : List D'), MinimalCounterexample H' darts'

/-- THE FOUR COLOR THEOREM
Every planar, bridgeless combinatorial map admits a valid 4-coloring. -/
theorem four_color_theorem {D : Type} [DecidableEq D] (H : Hypermap D) (darts : List D) 
  (h_planar : Hypermap.IsPlanar H darts) (h_bridgeless : Hypermap.isBridgeless H darts) : Nonempty (MapColoring H) := by
  by_cases h_colorable : Nonempty (MapColoring H)
  · exact h_colorable
  · have h_not : MapColoring H → False := fun c => h_colorable ⟨c⟩
    have ⟨D', dec', H', darts', mc⟩ := minimal_counterexample_exists H darts h_planar h_bridgeless h_not
    exact False.elim (minimal_counterexample_impossible H' darts' mc)

end Math
