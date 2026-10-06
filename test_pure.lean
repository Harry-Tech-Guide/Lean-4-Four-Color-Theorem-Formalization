
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
      apply Eq.symm
      -- Array.get! definition is if h : i < a.size then a.get ⟨i, h⟩ else default
      -- I can just use Array.get!_eq_getElem if it exists. Let's see if exact Array.getD_get? works.
      -- Let's try simp
      simp [getElem!, getElem]
    rw [h2] at h1
    exact h1

end FourColorTheorem
