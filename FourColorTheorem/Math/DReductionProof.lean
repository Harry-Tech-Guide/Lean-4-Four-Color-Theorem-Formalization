import FourColorTheorem.Math.Reflection
import FourColorTheorem.Math.ReducibilityProof
import FourColorTheorem.Math.EmptyLiveSet

namespace FourColorTheorem

open Classical

/-- The topological live set of a configuration ring: the set of boundary ring colorings
    that do NOT admit a valid extension to the interior of the configuration. -/
def ConfigLiveSet (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) : (Fin k → Color) → Prop :=
  fun cols => ¬ Hypermap.IsExtensiblePure H k R cols


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

-- The bridge between empty live set and D-reducibility is
-- proven directly in `FourColorTheorem.Math.Reflection` via `fast_reducer_soundness`.

end FourColorTheorem
