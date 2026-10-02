inductive KempeChain (A : Type) : A → A → Prop
  | refl (x : A) : KempeChain A x x
