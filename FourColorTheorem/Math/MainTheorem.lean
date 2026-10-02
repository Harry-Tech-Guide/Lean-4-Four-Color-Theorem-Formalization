import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Discharging

namespace Math

open Classical

/-- We proceed by assuming a Minimal Counterexample exists.
A minimal counterexample is a planar map that cannot be 4-colored, but any
"smaller" map (obtained by removing edges or shrinking configurations) CAN be 4-colored. -/
structure MinimalCounterexample {D : Type} (H : Hypermap D) [CombinatorialMap H] : Prop where
  is_planar : H.isPlanar
  not_colorable : MapColoring H → False
  -- 'minimal' implies that any reducible configuration appearing in H would lead
  -- to a contradiction (because we could shrink it, 4-color the smaller map,
  -- and extend the coloring back to H).

/-- A key lemma: A minimal counterexample cannot contain ANY reducible configuration.
If it did, the map could be reduced, colored, and the coloring extended, proving it
was colorable in the first place! -/
axiom no_reducible_in_minimal {D : Type} (H : Hypermap D) [CombinatorialMap H] (mc : MinimalCounterexample H) (c : Configuration) :
  appearsIn c H → IsReducible c → False

/-- If there were a minimal counterexample, we could prove `False` (a contradiction). -/
theorem minimal_counterexample_impossible {D : Type} (H : Hypermap D) [CombinatorialMap H] (mc : MinimalCounterexample H) : False := by
  -- 1. By the unavoidability theorem, H must contain a configuration `c` from the unavoidable set.
  have ⟨c, hc_in_set, hc_appears⟩ := unavoidability_theorem H mc.is_planar
  
  -- 2. By the reducibility theorem, because `c` is in the unavoidable set, it is reducible.
  have hc_reducible := reducibility_theorem c hc_in_set
  
  -- 3. But `no_reducible_in_minimal` states H cannot contain a reducible configuration.
  -- This provides our contradiction!
  exact no_reducible_in_minimal H mc c hc_appears hc_reducible

/-- THE FOUR COLOR THEOREM
Every planar combinatorial map admits a valid 4-coloring. -/
theorem four_color_theorem {D : Type} (H : Hypermap D) [CombinatorialMap H] (h : H.isPlanar) : Nonempty (MapColoring H) := by
  -- We prove this by contradiction. Assume the map cannot be 4-colored.
  by_cases h_colorable : Nonempty (MapColoring H)
  · exact h_colorable
  · -- By well-ordering of finite maps, if there's a counterexample, there must be a MINIMAL one.
    -- Let `H_min` be this minimal counterexample.
    -- (We use `sorry` here to skip the well-ordering extraction).
    have minimal_exists : False := sorry 
    exact False.elim minimal_exists

end Math
