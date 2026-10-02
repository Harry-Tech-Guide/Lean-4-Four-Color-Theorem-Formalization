import FiveColorTheorem.Graph

namespace Math

open Classical

/-- Two vertices are in the same Kempe (c_a, c_b)-chain if they are connected
by a path of vertices that are exclusively colored `c_a` or `c_b`. -/
inductive KempeChain {V : Type} [DecidableEq V] (G : Graph V) (c : V → Color5) (c_a c_b : Color5) : V → V → Prop
  | refl (x : V) :
      (c x = c_a ∨ c x = c_b) →
      KempeChain G c c_a c_b x x
  | symm (x y : V) : KempeChain G c c_a c_b x y → KempeChain G c c_a c_b y x
  | trans (x y z : V) : KempeChain G c c_a c_b x y → KempeChain G c c_a c_b y z → KempeChain G c c_a c_b x z
  | edge (x y : V) :
      G.adj x y = true →
      (c x = c_a ∨ c x = c_b) →
      (c y = c_a ∨ c y = c_b) →
      KempeChain G c c_a c_b x y

theorem kempeChain_colors_both {V : Type} [DecidableEq V] (G : Graph V) (c : V → Color5) (c_a c_b : Color5) (x y : V) (h : KempeChain G c c_a c_b x y) : 
  (c x = c_a ∨ c x = c_b) ∧ (c y = c_a ∨ c y = c_b) := by
  induction h with
  | refl x hc => exact ⟨hc, hc⟩
  | symm x y _ ih => exact ⟨ih.2, ih.1⟩
  | trans x y z _ _ ih1 ih2 => exact ⟨ih1.1, ih2.2⟩
  | edge x y _ hc_x hc_y => exact ⟨hc_x, hc_y⟩

theorem kempeChain_colors_y {V : Type} [DecidableEq V] (G : Graph V) (c : V → Color5) (c_a c_b : Color5) (x y : V) :
  KempeChain G c c_a c_b x y → (c y = c_a ∨ c y = c_b) :=
  fun h => (kempeChain_colors_both G c c_a c_b x y h).2

/-- Swaps colors `c_a` and `c_b` on the connected Kempe chain starting at `start`. -/
noncomputable def kempeSwap {V : Type} [DecidableEq V] (G : Graph V) (c : V → Color5) (c_a c_b : Color5) (start : V) : V → Color5 :=
  fun x =>
    if KempeChain G c c_a c_b start x then
      if c x = c_a then c_b
      else c_a
    else
      c x

end Math
