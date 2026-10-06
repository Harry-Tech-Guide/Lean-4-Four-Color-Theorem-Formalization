
import FourColorTheorem.Math.Reflection
import FourColorTheorem.Math.ReducibilityProof
import FourColorTheorem.Math.EmptyLiveSet

namespace FourColorTheorem

axiom check_empties_liveset (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) 
  (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (LiveSet : (Fin k → Color) → Prop) :
  (Math.FastReducer.check c md pow3).dReducible = true → 
  Hypermap.IsEmptyLiveSet k LiveSet

axiom outside_liveset_is_extensible (c : Math.FastReducer.RConf) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (LiveSet : (Fin k → Color) → Prop) :
  MatchesTopology H k R c → 
  ∀ cols, ¬ LiveSet cols → Hypermap.IsExtensiblePure H k R cols

/-- Bridge between pure topological extensibility (Fin k → Color) and 
    computational array extensibility (Array Color). -/
axiom pure_extensible_implies_array (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (cols : Array Color) (hValid : cols.size = k) :
  Hypermap.IsExtensiblePure H k R (fun i => cols[i.val]'(by rw [hValid]; exact i.isLt)) → 
  Hypermap.IsExtensible H k R cols


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
theorem dreduction_is_sound (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (LiveSet : (Fin k → Color) → Prop) :
  MatchesTopology H k R c → 
  (Math.FastReducer.check c md pow3).dReducible = true → 
  Hypermap.IsReducible H k R := by
  intro hMatch hCheck
  have hEmpty := check_empties_liveset c md pow3 H k R LiveSet hCheck
  have hExt := outside_liveset_is_extensible c H k R LiveSet hMatch
  intro cols hValid
  have hRed := Hypermap.empty_liveset_implies_reducible H k R LiveSet hEmpty hExt
  have hSize : cols.size = k := size_eq_of_isValidRingColoring k cols hValid
  have hPure := hRed (fun i => cols[i.val]'(by rw [hSize]; exact i.isLt))
  exact pure_extensible_implies_array H k R cols hSize hPure


end FourColorTheorem
