import FiveColorTheorem.Graph

namespace Math

inductive KempeChain {V : Type} [DecidableEq V] (G : Graph V) (c : V → Color5) (ca cb : Color5) : V → V → Prop
  | refl (x : V) : KempeChain G c ca cb x x

theorem test {V : Type} [DecidableEq V] (G : Graph V) (c : V → Color5) (ca cb : Color5) (x : V) : KempeChain G c ca cb x x := KempeChain.refl x

end Math
