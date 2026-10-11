
import FourColorTheorem.Math.DReductionProof

namespace FourColorTheorem
variable (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (cols : Array Color) (hValid : Hypermap.isValidRingColoring k cols = true) 

theorem pure_extensible_implies_array_proof :
  Hypermap.IsExtensiblePure H k R (fun i => cols[i.val]'(by have hs := size_eq_of_isValidRingColoring k cols hValid; rw [hs]; exact i.isLt)) → 
  Hypermap.IsExtensible H k R cols := by
  intro hPure
  rcases hPure with ⟨vc, hvc⟩
  constructor
  · exact hValid
  · exists vc
    intro i
    have h1 := hvc i
    dsimp at h1
    have hs := size_eq_of_isValidRingColoring k cols hValid
    have hlt : i.val < cols.size := by rw [hs]; exact i.isLt
    have h2 : cols[i.val]'hlt = cols[i.val]! := by
      -- in lean 4, getElem! a i is defined via getElem? and getD
      -- actually we can just apply getElem_eq_getElem! or similar
      exact Eq.symm (getElem!_pos cols i.val hlt)
    rw [h2] at h1
    exact h1

end FourColorTheorem
