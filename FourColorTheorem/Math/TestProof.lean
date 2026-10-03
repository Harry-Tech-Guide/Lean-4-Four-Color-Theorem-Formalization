import FourColorTheorem.Math.Kempe

namespace Math
open Classical

variable {D : Type} (H : Hypermap D) (C : MapColoring H) (c_a c_b : Color)

theorem kempeSwap_edge_diff_proof (start : D) (d : D) (hcab : c_a ≠ c_b) :
    kempeSwap H C c_a c_b start (H.edge.fw d) ≠ kempeSwap H C c_a c_b start d := by
  unfold kempeSwap
  by_cases h1 : KempeChain H C c_a c_b start d
  · by_cases h2 : KempeChain H C c_a c_b start (H.edge.fw d)
    · simp [h1, h2]
      have c1 := kempeChain_colors_y H C c_a c_b h1
      have c2 := kempeChain_colors_y H C c_a c_b h2
      have diff := C.edge_diff d
      by_cases hd : C.color d = c_a
      · rw [if_pos hd]
        have he : C.color (H.edge.fw d) = c_b := by
          cases c2 with
          | inl h => rw [h, hd] at diff; contradiction
          | inr h => exact h
        rw [if_neg (by intro h_eq; rw [he] at h_eq; rw [h_eq] at hcab; exact hcab rfl)]
        intro h_eq
        rw [h_eq] at hcab
        exact hcab rfl
      · have hd2 : C.color d = c_b := by
          cases c1 with
          | inl h => contradiction
          | inr h => exact h
        rw [if_neg hd]
        have he : C.color (H.edge.fw d) = c_a := by
          cases c2 with
          | inl h => exact h
          | inr h => rw [h, hd2] at diff; contradiction
        rw [if_pos he]
        intro h_eq
        rw [h_eq] at hcab
        exact hcab rfl
    · simp [h1, h2]
      have c1 := kempeChain_colors_y H C c_a c_b h1
      have hc : C.color (H.edge.fw d) ≠ c_a ∧ C.color (H.edge.fw d) ≠ c_b := by
        constructor
        · intro h
          have h2_contra := KempeChain.trans _ _ _ h1 (KempeChain.edge_step d c1 (Or.inl h))
          contradiction
        · intro h
          have h2_contra := KempeChain.trans _ _ _ h1 (KempeChain.edge_step d c1 (Or.inr h))
          contradiction
      by_cases hd : C.color d = c_a
      · rw [if_pos hd]
        intro h_eq
        rw [h_eq] at hc
        exact hc.right rfl
      · rw [if_neg hd]
        intro h_eq
        rw [h_eq] at hc
        exact hc.left rfl
  · by_cases h2 : KempeChain H C c_a c_b start (H.edge.fw d)
    · simp [h1, h2]
      have c2 := kempeChain_colors_y H C c_a c_b h2
      have hc : C.color d ≠ c_a ∧ C.color d ≠ c_b := by
        constructor
        · intro h
          have h_edge : KempeChain H C c_a c_b (H.edge.fw d) d := by
            have h_rw : C.color (H.edge.fw (H.edge.fw d)) = c_a := by rw [H.edge_involution]; exact h
            have step := KempeChain.edge_step (H.edge.fw d) c2 (Or.inl h_rw)
            rw [H.edge_involution] at step
            exact step
          have h1_contra := KempeChain.trans _ _ _ h2 h_edge
          contradiction
        · intro h
          have h_edge : KempeChain H C c_a c_b (H.edge.fw d) d := by
            have h_rw : C.color (H.edge.fw (H.edge.fw d)) = c_b := by rw [H.edge_involution]; exact h
            have step := KempeChain.edge_step (H.edge.fw d) c2 (Or.inr h_rw)
            rw [H.edge_involution] at step
            exact step
          have h1_contra := KempeChain.trans _ _ _ h2 h_edge
          contradiction
      by_cases hd : C.color (H.edge.fw d) = c_a
      · rw [if_pos hd]
        intro h_eq
        rw [← h_eq] at hc
        exact hc.right rfl
      · rw [if_neg hd]
        intro h_eq
        rw [← h_eq] at hc
        exact hc.left rfl
    · simp [h1, h2]
      exact C.edge_diff d

end Math
