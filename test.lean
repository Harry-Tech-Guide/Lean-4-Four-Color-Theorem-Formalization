
import Lean

example (d x P : Nat) (hd : d < 3) (hx : x < P) : d + 3 * x < 3 * P := by
  omega
