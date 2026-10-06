
import FourColorTheorem.Math.Kempe

namespace Hypermap
variable (H : Hypermap)

theorem swapColor_closed (col a b : Color) (h : col = a ∨ col = b) : swapColor col a b = a ∨ swapColor col a b = b := by
  revert h
  cases col <;> cases a <;> cases b <;> decide

def kempeSwap_valid_proof (c : FaceColoring H) (a b : Color) (S : H.Dart → Bool) (hS : KempeClosed H c a b S) : FaceColoring H where
  color := kempeSwap H c a b S
  face_invariant := fun d => by
    dsimp [kempeSwap]
    have hs := hS.1 d
    have hc := c.face_invariant d
    rw [hs, hc]
  edge_proper := fun d h_eq => by
    dsimp [kempeSwap] at h_eq
    have hd_edge := c.edge_proper d
    split at h_eq
    · split at h_eq
      · exact hd_edge (swapColor_inj _ _ _ _ h_eq)
      · rename_i h1 h2
        have hd1 : c.color d = a ∨ c.color d = b := hS.2.1 d h1
        have hd2 : c.color (H.edge.f d) = a ∨ c.color (H.edge.f d) = b := by
          have h_closed := swapColor_closed (c.color d) a b hd1
          rw [h_eq] at h_closed
          cases h_closed with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr h
        have h3 := hS.2.2 d hd1 hd2
        rw [h1, h2] at h3
        contradiction
    · split at h_eq
      · rename_i h1 h2
        have he1 : c.color (H.edge.f d) = a ∨ c.color (H.edge.f d) = b := hS.2.1 (H.edge.f d) h2
        have he2 : c.color d = a ∨ c.color d = b := by
          have h_closed := swapColor_closed (c.color (H.edge.f d)) a b he1
          rw [← h_eq] at h_closed
          cases h_closed with
          | inl h => exact Or.inl h
          | inr h => exact Or.inr h
        have h3 := hS.2.2 d he2 he1
        rw [h1, h2] at h3
        contradiction
      · exact hd_edge h_eq
end Hypermap
