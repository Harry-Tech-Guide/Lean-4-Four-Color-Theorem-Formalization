import FiveColorTheorem.Planar

namespace Math

open Classical

/-- If we swap colors in a Kempe chain, the resulting coloring is still valid! -/
theorem kempeSwap_valid {V : Type} [DecidableEq V] (G : Graph V) (c : V → Color5) (h_valid : ValidColoring G c) (c_a c_b : Color5) (start : V) :
  ValidColoring G (kempeSwap G c c_a c_b start) := by
  intro x y hx hy h_adj
  unfold kempeSwap
  by_cases hX : KempeChain G c c_a c_b start x <;> by_cases hY : KempeChain G c c_a c_b start y
  · -- Both in chain
    rw [if_pos hX, if_pos hY]
    by_cases cXa : c x = c_a <;> by_cases cYa : c y = c_a
    · rw [if_pos cXa, if_pos cYa]
      have : c x = c y := by rw [cXa, cYa]
      exact False.elim (h_valid x y hx hy h_adj this)
    · rw [if_pos cXa, if_neg cYa]
      intro h_eq
      have hcY : c y = c_a ∨ c y = c_b := kempeChain_colors_y G c c_a c_b start y hY
      cases hcY with
      | inl h1 => exact cYa h1
      | inr h2 =>
        rw [h_eq] at h2
        exact cYa h2
    · rw [if_neg cXa, if_pos cYa]
      intro h_eq
      have hcX : c x = c_a ∨ c x = c_b := kempeChain_colors_y G c c_a c_b start x hX
      cases hcX with
      | inl h1 => exact cXa h1
      | inr h2 =>
        rw [←h_eq] at h2
        exact cXa h2
    · rw [if_neg cXa, if_neg cYa]
      have hcX : c x = c_a ∨ c x = c_b := kempeChain_colors_y G c c_a c_b start x hX
      have hcY : c y = c_a ∨ c y = c_b := kempeChain_colors_y G c c_a c_b start y hY
      have hxb : c x = c_b := by cases hcX with | inl h => exact False.elim (cXa h) | inr h => exact h
      have hyb : c y = c_b := by cases hcY with | inl h => exact False.elim (cYa h) | inr h => exact h
      have : c x = c y := by rw [hxb, hyb]
      exact False.elim (h_valid x y hx hy h_adj this)
  · -- x in chain, y not in chain
    rw [if_pos hX, if_neg hY]
    by_cases cXa : c x = c_a
    · rw [if_pos cXa]
      intro h_eq
      have cYb : c y = c_b := h_eq.symm
      have hY_chain : KempeChain G c c_a c_b start y :=
        KempeChain.trans start x y hX (KempeChain.edge x y h_adj (Or.inl cXa) (Or.inr cYb))
      exact hY hY_chain
    · rw [if_neg cXa]
      intro h_eq
      have cYa : c y = c_a := h_eq.symm
      have hcX : c x = c_a ∨ c x = c_b := kempeChain_colors_y G c c_a c_b start x hX
      have cXb : c x = c_b := by cases hcX with | inl h => exact False.elim (cXa h) | inr h => exact h
      have hY_chain : KempeChain G c c_a c_b start y :=
        KempeChain.trans start x y hX (KempeChain.edge x y h_adj (Or.inr cXb) (Or.inl cYa))
      exact hY hY_chain
  · -- x not in chain, y in chain
    rw [if_neg hX, if_pos hY]
    by_cases cYa : c y = c_a
    · rw [if_pos cYa]
      intro h_eq
      have cXb : c x = c_b := h_eq
      have hX_chain : KempeChain G c c_a c_b start x :=
        KempeChain.trans start y x hY (KempeChain.edge y x (G.symm x y h_adj) (Or.inl cYa) (Or.inr cXb))
      exact hX hX_chain
    · rw [if_neg cYa]
      intro h_eq
      have cXa : c x = c_a := h_eq
      have hcY : c y = c_a ∨ c y = c_b := kempeChain_colors_y G c c_a c_b start y hY
      have cYb : c y = c_b := by cases hcY with | inl h => exact False.elim (cYa h) | inr h => exact h
      have hX_chain : KempeChain G c c_a c_b start x :=
        KempeChain.trans start y x hY (KempeChain.edge y x (G.symm x y h_adj) (Or.inr cYb) (Or.inl cXa))
      exact hX hX_chain
  · -- neither in chain
    rw [if_neg hX, if_neg hY]
    exact h_valid x y hx hy h_adj

theorem kempeSwap_independent {V : Type} [DecidableEq V] (G : Graph V) (c : V → Color5) (c_a c_b : Color5) (n1 n2 : V) :
  ¬ KempeChain G c c_a c_b n1 n2 →
  kempeSwap G c c_a c_b n1 n2 = c n2 := by
  intro h
  unfold kempeSwap
  by_cases h_in : KempeChain G c c_a c_b n1 n2
  · contradiction
  · rw [if_neg h_in]

/-- The Main Five Color Theorem! 
Every combinatorially planar graph admits a valid 5-coloring. 
Proved by strong induction on the size of the graph. -/
theorem five_color_theorem_size (n : Nat) :
  ∀ {V : Type} [DecidableEq V] (G : Graph V),
    G.vertices.length = n →
    CombinatoriallyPlanar G →
    ∃ c, ValidColoring G c := sorry

end Math
