
import FourColorTheorem.Math.Configuration

namespace Hypermap

theorem size_eq_of_isValidRingColoring (k : Nat) (cols : Array Color) (h : isValidRingColoring k cols = true) : cols.size = k := by
  dsimp [isValidRingColoring] at h
  cases heq : (cols.size == k)
  · have h_neq : (cols.size != k) = true := by
      change (!(cols.size == k)) = true
      rw [heq]
      rfl
    rw [h_neq] at h
    dsimp at h
    contradiction
  · exact eq_of_beq heq

end Hypermap
