
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
      · -- h1: S (edge d) = true, h2: S d = true
        exact hd_edge (swapColor_inj _ _ _ _ h_eq)
      · -- h1: S (edge d) = true, h2: ¬S d = true
        rename_i h1 h2
        -- h_eq : swapColor (c.color (edge d)) a b = c.color d
        have he1 : c.color (H.edge.f d) = a ∨ c.color (H.edge.f d) = b := hS.2.1 (H.edge.f d) h1
        have he2 : c.color d = a ∨ c.color d = b := by
          have h_closed := swapColor_closed (c.color (H.edge.f d)) a b he1
          rw [h_eq] at h_closed
          exact h_closed
        have h3 := hS.2.2 d he2 he1
        -- h3: S (edge d) = S d
        rw [h1] at h3
        -- true = S d
        have hd_false : S d = false := by
          cases hd : S d
          · rfl
          · contradiction
        rw [hd_false] at h3
        contradiction
    · split at h_eq
      · -- h1: ¬S (edge d) = true, h2: S d = true
        rename_i h1 h2
        -- h_eq : c.color (edge d) = swapColor (c.color d) a b
        have hd1 : c.color d = a ∨ c.color d = b := hS.2.1 d h2
        have hd2 : c.color (H.edge.f d) = a ∨ c.color (H.edge.f d) = b := by
          have h_closed := swapColor_closed (c.color d) a b hd1
          rw [← h_eq] at h_closed
          exact h_closed
        have h3 := hS.2.2 d hd1 hd2
        -- h3: S (edge d) = S d
        rw [h2] at h3
        -- S (edge d) = true
        have he_false : S (H.edge.f d) = false := by
          cases he : S (H.edge.f d)
          · rfl
          · contradiction
        rw [he_false] at h3
        contradiction
      · -- h1: ¬S (edge d) = true, h2: ¬S d = true
        exact hd_edge h_eq
end Hypermap
