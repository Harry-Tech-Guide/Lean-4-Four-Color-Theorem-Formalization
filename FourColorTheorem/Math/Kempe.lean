
import FourColorTheorem.Math.Coloring

namespace Hypermap

variable (H : Hypermap)

/-- A boolean predicate S represents a valid Kempe Chain component for colors a and b if:
    1. It is composed of entire faces (face-invariant).
    2. It only contains darts of color a or b.
    3. It is topologically closed across edges: if an edge connects two faces that are both colored a or b, 
       they must either both be in the chain, or both be outside it. -/
def KempeClosed (c : FaceColoring H) (a b : Color) (S : H.Dart → Bool) : Prop :=
  (∀ d, S (H.face.f d) = S d) ∧
  (∀ d, S d = true → c.color d = a ∨ c.color d = b) ∧
  (∀ d, (c.color d = a ∨ c.color d = b) → 
        (c.color (H.edge.f d) = a ∨ c.color (H.edge.f d) = b) → 
        S (H.edge.f d) = S d)

/-- Swaps colors a and b, leaving other colors unchanged. -/
def swapColor (col a b : Color) : Color :=
  if col = a then b
  else if col = b then a
  else col

/-- Theorem: Swapping colors is a perfectly injective operation. -/
theorem swapColor_inj (col1 col2 a b : Color) (h : swapColor col1 a b = swapColor col2 a b) : col1 = col2 := by
  revert h
  cases col1 <;> cases col2 <;> cases a <;> cases b <;> decide



theorem swapColor_closed (col a b : Color) (h : col = a ∨ col = b) : swapColor col a b = a ∨ swapColor col a b = b := by
  revert h
  cases col <;> cases a <;> cases b <;> decide

/-- Theorem: Swapping colors twice is the identity operation (involution). -/
theorem swapColor_inv (col a b : Color) : swapColor (swapColor col a b) a b = col := by
  cases col <;> cases a <;> cases b <;> decide

/-- The new color assignment after performing a Kempe swap on component S. -/
def kempeSwap (c : FaceColoring H) (a b : Color) (S : H.Dart → Bool) (d : H.Dart) : Color :=
  if S d then swapColor (c.color d) a b else c.color d

/-- Theorem: The resulting color assignment is a mathematically valid 4-coloring of the Hypermap. -/
def kempeSwap_valid (c : FaceColoring H) (a b : Color) (S : H.Dart → Bool) (hS : KempeClosed H c a b S) : FaceColoring H where
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
        have he1 : c.color (H.edge.f d) = a ∨ c.color (H.edge.f d) = b := hS.2.1 (H.edge.f d) h1
        have he2 : c.color d = a ∨ c.color d = b := by
          have h_closed := swapColor_closed (c.color (H.edge.f d)) a b he1
          rw [h_eq] at h_closed
          exact h_closed
        have h3 := hS.2.2 d he2 he1
        rw [h1] at h3
        have hd_false : S d = false := by
          cases hd : S d
          · rfl
          · contradiction
        rw [hd_false] at h3
        contradiction
    · split at h_eq
      · rename_i h1 h2
        have hd1 : c.color d = a ∨ c.color d = b := hS.2.1 d h2
        have hd2 : c.color (H.edge.f d) = a ∨ c.color (H.edge.f d) = b := by
          have h_closed := swapColor_closed (c.color d) a b hd1
          rw [← h_eq] at h_closed
          exact h_closed
        have h3 := hS.2.2 d hd1 hd2
        rw [h2] at h3
        have he_false : S (H.edge.f d) = false := by
          cases he : S (H.edge.f d)
          · rfl
          · contradiction
        rw [he_false] at h3
        contradiction
      · exact hd_edge h_eq

end Hypermap
