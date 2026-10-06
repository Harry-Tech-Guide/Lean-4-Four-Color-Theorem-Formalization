
import FourColorTheorem.Math.Configuration

namespace Hypermap

/-- The Klein four-group operation on colors (bitwise XOR). 
    This is used to compute the Kempe trace of a ring coloring. -/
def colorXor : Color → Color → Color
  | Color.c0, Color.c0 => Color.c0 | Color.c0, Color.c1 => Color.c1 | Color.c0, Color.c2 => Color.c2 | Color.c0, Color.c3 => Color.c3
  | Color.c1, Color.c0 => Color.c1 | Color.c1, Color.c1 => Color.c0 | Color.c1, Color.c2 => Color.c3 | Color.c1, Color.c3 => Color.c2
  | Color.c2, Color.c0 => Color.c2 | Color.c2, Color.c1 => Color.c3 | Color.c2, Color.c2 => Color.c0 | Color.c2, Color.c3 => Color.c1
  | Color.c3, Color.c0 => Color.c3 | Color.c3, Color.c1 => Color.c2 | Color.c3, Color.c2 => Color.c1 | Color.c3, Color.c3 => Color.c0

/-- In a valid ring coloring, adjacent colors are different, so their XOR is c1, c2, or c3.
    We map these to 0, 1, and 2 to compute a base-3 index. -/
def colorDiff (a b : Color) : Nat :=
  match colorXor a b with
  | Color.c0 => 0 -- Invalid edge (adjacent vertices have the same color)
  | Color.c1 => 0
  | Color.c2 => 1
  | Color.c3 => 2


/-- Recursive definition of the ring trace (base-3 index). -/
def ringTraceAux (cols : Array Color) (idx k rem : Nat) : Nat :=
  match rem with
  | 0 => 0
  | rem_minus_1 + 1 =>
    let nxt := if idx + 1 == k then 0 else idx + 1
    let d := colorDiff cols[idx]! cols[nxt]!
    d + 3 * ringTraceAux cols nxt k rem_minus_1

def ringTraceRec (k : Nat) (cols : Array Color) : Nat :=
  ringTraceAux cols 0 k k


/-- Theorem: A color difference is always less than 3. -/
theorem colorDiff_lt_3 (a b : Color) : colorDiff a b < 3 := by
  dsimp [colorDiff]
  cases (colorXor a b) <;> decide




/-- Theorem: The recursive trace function is strictly bounded by 3^rem. -/
theorem ringTraceAux_lt_pow3 (cols : Array Color) (idx k rem : Nat) :
  ringTraceAux cols idx k rem < 3 ^ rem := by
  induction rem generalizing idx with
  | zero =>
    unfold ringTraceAux
    decide
  | succ r ih =>
    unfold ringTraceAux
    dsimp
    have hd := colorDiff_lt_3 cols[idx]! cols[if idx + 1 == k then 0 else idx + 1]!
    have hrec := ih (if idx + 1 == k then 0 else idx + 1)
    change colorDiff _ _ + 3 * _ < 3 ^ r * 3
    generalize 3 ^ r = P at hrec ⊢
    omega
/-- Theorem: The base-3 index of any ring coloring of size k is strictly less than 3^k. 
    This mathematically guarantees that array lookups in the live array will never go out of bounds. -/
theorem ringTraceRec_lt_pow3 (k : Nat) (cols : Array Color) :
  ringTraceRec k cols < 3 ^ k := by
  unfold ringTraceRec
  exact ringTraceAux_lt_pow3 cols 0 k k

end Hypermap
