inductive MyEq (A : Type) : A → A → Prop
  | refl (x : A) : MyEq x x
