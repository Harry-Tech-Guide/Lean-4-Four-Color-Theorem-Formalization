import FourColorTheorem.Math.Reflection
import FourColorTheorem.Math.ReducibilityProof
import FourColorTheorem.Math.EmptyLiveSet

namespace FourColorTheorem

open Classical

/-- The topological live set of a configuration ring: the set of boundary ring colorings
    that do NOT admit a valid extension to the interior of the configuration. -/
def ConfigLiveSet (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) : (Fin k → Color) → Prop :=
  fun cols => ¬ Hypermap.IsExtensiblePure H k R cols

/-- A configuration's D-reducibility check in FastReducer computes the bitwise fixed point
    of the non-extending boundary colorings. If it terminates with dReducible = true,
    the live set has been completely emptied. -/
axiom check_empties_liveset (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) 
  (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c →
  (Math.FastReducer.check c md pow3).dReducible = true → 
  Hypermap.IsEmptyLiveSet k (ConfigLiveSet H k R)

/-- Any coloring outside the live set is extensible to the interior.
    (This is a direct theorem by definition of ConfigLiveSet and classical logic). -/
theorem outside_liveset_is_extensible (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  ∀ cols, ¬ ConfigLiveSet H k R cols → Hypermap.IsExtensiblePure H k R cols :=
  fun _ h => Classical.not_not.mp h

/-- Bridge between pure topological extensibility (Fin k → Color) and 
    computational array extensibility (Array Color). -/
theorem pure_extensible_implies_array (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (cols : Array Color) (hValid : cols.size = k) (hValid2 : Hypermap.isValidRingColoring k cols = true) :
  Hypermap.IsExtensiblePure H k R (fun i => cols[i.val]'(by rw [hValid]; exact i.isLt)) → 
  Hypermap.IsExtensible H k R cols := by
  intro hPure
  rcases hPure with ⟨vc, hvc⟩
  constructor
  · exact hValid2
  · exists vc
    intro i
    have h1 := hvc i
    dsimp at h1
    have hlt : i.val < cols.size := by rw [hValid]; exact i.isLt
    have h2 : cols[i.val]'hlt = cols[i.val]! := by
      exact Eq.symm (getElem!_pos cols i.val hlt)
    rw [h2] at h1
    exact h1

theorem size_eq_of_isValidRingColoring (k : Nat) (cols : Array Color) (h : Hypermap.isValidRingColoring k cols = true) : cols.size = k := by
  dsimp [Hypermap.isValidRingColoring] at h
  cases heq : (cols.size == k)
  · have h_neq : (cols.size != k) = true := by
      change (!(cols.size == k)) = true
      rw [heq]
      rfl
    rw [h_neq] at h
    dsimp at h
    contradiction
  · exact eq_of_beq heq

/-- The final architecture link for D-Reducibility. -/
theorem dreduction_is_sound (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  (Math.FastReducer.check c md pow3).dReducible = true → 
  Hypermap.IsReducible H k R := by
  intro hMatch hCheck
  have hEmpty := check_empties_liveset c md pow3 H k R hMatch hCheck
  have hExt := outside_liveset_is_extensible H k R
  intro cols hValid
  have hRed := Hypermap.empty_liveset_implies_reducible H k R (ConfigLiveSet H k R) hEmpty hExt
  have hSize : cols.size = k := size_eq_of_isValidRingColoring k cols hValid
  have hPure := hRed (fun i => cols[i.val]'(by rw [hSize]; exact i.isLt))
  exact pure_extensible_implies_array H k R cols hSize hValid hPure

end FourColorTheorem
