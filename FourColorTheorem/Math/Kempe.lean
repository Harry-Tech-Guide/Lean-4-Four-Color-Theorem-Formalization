import FourColorTheorem.Math.Coloring

namespace Math

open Classical

/-- Two darts are in the same Kempe (c_a, c_b)-chain if they are connected
by a path of darts exclusively colored `c_a` or `c_b` under node or edge steps. -/
inductive KempeChain {D : Type} (H : Hypermap D) (C : MapColoring H) (c_a c_b : Color) : D -> D -> Prop
  | refl (x : D) (hx : C.color x = c_a ∨ C.color x = c_b) : KempeChain H C c_a c_b x x
  | symm (x y : D) : KempeChain H C c_a c_b x y -> KempeChain H C c_a c_b y x
  | trans (x y z : D) : KempeChain H C c_a c_b x y -> KempeChain H C c_a c_b y z -> KempeChain H C c_a c_b x z
  | node_step (x : D) (hx : C.color x = c_a ∨ C.color x = c_b) : KempeChain H C c_a c_b x (H.node.fw x)
  | node_bw_step (x : D) (hx : C.color x = c_a ∨ C.color x = c_b) : KempeChain H C c_a c_b x (H.node.bw x)
  | edge_step (x : D) 
      (hx : C.color x = c_a ∨ C.color x = c_b)
      (hex : C.color (H.edge.fw x) = c_a ∨ C.color (H.edge.fw x) = c_b) : 
      KempeChain H C c_a c_b x (H.edge.fw x)

variable {D : Type} (H : Hypermap D) (C : MapColoring H) (c_a c_b : Color)

theorem kempeChain_colors_both {x y : D} (h : KempeChain H C c_a c_b x y) :
    (C.color x = c_a ∨ C.color x = c_b) ∧ (C.color y = c_a ∨ C.color y = c_b) := by
  induction h with
  | refl v hv => exact ⟨hv, hv⟩
  | symm u v _ ih => exact ⟨ih.right, ih.left⟩
  | trans u v w _ _ ih1 ih2 => exact ⟨ih1.left, ih2.right⟩
  | node_step u hu =>
    have hnode := C.node_const u
    exact ⟨hu, by rw [hnode]; exact hu⟩
  | node_bw_step u hu =>
    have hnode : C.color (H.node.fw (H.node.bw u)) = C.color (H.node.bw u) := C.node_const (H.node.bw u)
    rw [H.node.fw_bw] at hnode
    exact ⟨hu, by rw [← hnode]; exact hu⟩
  | edge_step u hu hex => exact ⟨hu, hex⟩

theorem kempeChain_colors_y {x y : D} (h : KempeChain H C c_a c_b x y) :
    C.color y = c_a ∨ C.color y = c_b :=
  (kempeChain_colors_both H C c_a c_b h).right

/-- Swaps colors `c_a` and `c_b` on the connected Kempe chain starting at `start`. -/
noncomputable def kempeSwap (start : D) : D → Color :=
  fun x =>
    if KempeChain H C c_a c_b start x then
      if C.color x = c_a then c_b
      else c_a
    else
      C.color x

theorem kempeSwap_node_const (start : D) (d : D) :
    kempeSwap H C c_a c_b start (H.node.fw d) = kempeSwap H C c_a c_b start d := by
  unfold kempeSwap
  by_cases h1 : KempeChain H C c_a c_b start d
  · have h2 : KempeChain H C c_a c_b start (H.node.fw d) := by
      have hc := kempeChain_colors_y H C c_a c_b h1
      exact KempeChain.trans _ _ _ h1 (KempeChain.node_step d hc)
    simp [h1, h2]
    rw [C.node_const]
  · by_cases h2 : KempeChain H C c_a c_b start (H.node.fw d)
    · have hc := kempeChain_colors_y H C c_a c_b h2
      have h1_contra : KempeChain H C c_a c_b start d := by
        have step := KempeChain.node_bw_step (H.node.fw d) hc
        rw [H.node.bw_fw] at step
        exact KempeChain.trans _ _ _ h2 step
      contradiction
    · simp [h1, h2]
      rw [C.node_const]

theorem kempeSwap_edge_diff (start : D) (d : D) (hcab : c_a ≠ c_b) :
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
        have h_symm := Eq.symm h_eq
        rw [h_symm] at hc
        exact hc.right rfl
      · rw [if_neg hd]
        intro h_eq
        have h_symm := Eq.symm h_eq
        rw [h_symm] at hc
        exact hc.left rfl
    · simp [h1, h2]
      exact C.edge_diff d

/-- A Kempe swap produces a valid map coloring! -/
noncomputable def kempeSwapColoring (start : D) (hcab : c_a ≠ c_b) : MapColoring H where
  color := kempeSwap H C c_a c_b start
  node_const := kempeSwap_node_const H C c_a c_b start
  edge_diff := fun d => kempeSwap_edge_diff H C c_a c_b start d hcab

axiom kempeSwap_involutive (start : D) (hcab : c_a ≠ c_b) :
    kempeSwap H (kempeSwapColoring H C c_a c_b start hcab) c_b c_a start = C.color

end Math
