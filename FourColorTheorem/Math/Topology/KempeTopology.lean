import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Topology.Paths

open Classical

namespace Hypermap

variable (H : Hypermap)

/-- `d` lies in the `(a, b)`-Kempe chain of `start`: `start` has colour `a` and there is a
    walk from `start` to `d` all of whose darts have colour `a` or `b`. -/
def KempeChain (vc : VertexColoring H) (a b : Color) (start : H.Dart) (d : H.Dart) : Prop :=
  vc.color start = a ∧
  ∃ (w : Walk H start d),
    ∀ d' ∈ Walk.toList H w, vc.color d' = a ∨ vc.color d' = b

/-- A Kempe chain is closed under any step that lands on an `a`/`b`-coloured dart. -/
theorem KempeChain.step {vc : VertexColoring H} {a b : Color} {start d d2 : H.Dart}
    (h : KempeChain H vc a b start d) (s : Step H d d2)
    (hc : vc.color d2 = a ∨ vc.color d2 = b) : KempeChain H vc a b start d2 := by
  obtain ⟨hs, w, hw⟩ := h
  refine ⟨hs, Walk.snoc H w s, ?_⟩
  intro x hx
  rw [Walk.toList_snoc, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | hx
  · exact hw x hx
  · subst hx; exact hc

/-- Every dart of a Kempe chain has colour `a` or `b`. -/
theorem KempeChain.color {vc : VertexColoring H} {a b : Color} {start d : H.Dart}
    (h : KempeChain H vc a b start d) : vc.color d = a ∨ vc.color d = b := by
  obtain ⟨_, w, hw⟩ := h
  apply hw
  cases w with
  | refl _ => simp [Walk.toList]
  | step s w' =>
    -- the endpoint is always in the visited list
    have : ∀ {x y : H.Dart} (v : Walk H x y), y ∈ Walk.toList H v := by
      intro x y v
      induction v with
      | refl z => simp [Walk.toList]
      | step _ _ ih => simp [Walk.toList, ih]
    exact this _

/-- The colour swap `a ↔ b` used inside a Kempe chain. -/
def kempeSwapColor (a b c : Color) : Color := if c = a then b else a

/-- Swapping the colours `a` and `b` on a Kempe chain yields another proper vertex colouring.
    (Fully proved: this is the local half of Kempe's argument; it needs no planarity.) -/
noncomputable def swapKempeChain (vc : VertexColoring H) (a b : Color) (start : H.Dart) :
    VertexColoring H :=
  { color := fun d =>
      if KempeChain H vc a b start d then kempeSwapColor a b (vc.color d) else vc.color d,
    node_invariant := by
      intro d
      have hcol : vc.color (H.node.f d) = vc.color d := vc.node_invariant d
      by_cases hd : KempeChain H vc a b start d
      · have hn : KempeChain H vc a b start (H.node.f d) :=
          KempeChain.step H hd (Step.node rfl) (hcol ▸ KempeChain.color H hd)
        simp only [hd, hn, if_true, hcol]
      · have hn : ¬ KempeChain H vc a b start (H.node.f d) := by
          intro hn
          apply hd
          have hc' : vc.color d = a ∨ vc.color d = b := hcol ▸ KempeChain.color H hn
          exact KempeChain.step H hn (Step.node_back H d) hc'
        simp only [hd, hn, if_false, hcol],
    edge_proper := by
      intro d
      have hp : vc.color (H.edge.f d) ≠ vc.color d := vc.edge_proper d
      by_cases hd : KempeChain H vc a b start d <;>
        by_cases he : KempeChain H vc a b start (H.edge.f d)
      · -- both swapped
        simp only [hd, he, if_true, kempeSwapColor]
        have cd := KempeChain.color H hd
        have ce := KempeChain.color H he
        by_cases h1 : vc.color d = a
        · have h2 : vc.color (H.edge.f d) ≠ a := by rw [← h1]; exact hp
          have hb : vc.color (H.edge.f d) = b := ce.resolve_left h2
          have hab : a ≠ b := by intro e; apply hp; rw [hb, h1, e]
          simp only [h1, h2, if_true, if_false]
          exact fun e => hab (by first | exact e | exact e.symm)
        · have hb : vc.color d = b := cd.resolve_left h1
          by_cases h2 : vc.color (H.edge.f d) = a
          · have hab : a ≠ b := by intro e; apply hp; rw [h2, hb, e]
            simp only [h1, h2, if_true, if_false]
            exact fun e => hab (by first | exact e | exact e.symm)
          · exact absurd (by rw [ce.resolve_left h2, hb]) hp
      · -- d swapped, edge d not: edge d is not a/b coloured
        simp only [hd, he, if_true, if_false, kempeSwapColor]
        have hne : ¬ (vc.color (H.edge.f d) = a ∨ vc.color (H.edge.f d) = b) :=
          fun hc => he (KempeChain.step H hd (Step.edge rfl) hc)
        intro e
        apply hne
        split at e
        · exact Or.inr e
        · exact Or.inl e
      · -- edge d swapped, d not: d is not a/b coloured
        simp only [hd, he, if_true, if_false, kempeSwapColor]
        have hne : ¬ (vc.color d = a ∨ vc.color d = b) :=
          fun hc => hd (KempeChain.step H he (Step.edge_back H d) hc)
        intro e
        apply hne
        split at e
        · exact Or.inr e.symm
        · exact Or.inl e.symm
      · simp only [hd, he, if_false]
        exact hp }

end Hypermap
