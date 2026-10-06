
import FourColorTheorem.Math.Trace

-- Step 7: Symmetry and Klein Four-Group Invariance

namespace Hypermap

/-- The Klein four-group V4 is defined by bitwise XOR on the 4 colors. 
    It is commutative, associative, and every element is its own inverse. -/
theorem colorXor_comm (a b : Color) : colorXor a b = colorXor b a := by
  cases a <;> cases b <;> decide

theorem colorXor_assoc (a b c : Color) : colorXor (colorXor a b) c = colorXor a (colorXor b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem colorXor_self (a : Color) : colorXor a a = Color.c0 := by
  cases a <;> decide

theorem colorXor_zero (a : Color) : colorXor a Color.c0 = a := by
  cases a <;> decide

/-- The fundamental symmetry of the Four Color Theorem's ring trace:
    If we globally shift the entire coloring of the map by any color shift in V4,
    the relative color difference between any two adjacent vertices remains exactly the same! -/
theorem v4_trace_invariance (a b shift : Color) : 
  colorDiff (colorXor a shift) (colorXor b shift) = colorDiff a b := by
  cases a <;> cases b <;> cases shift <;> decide

/-- Two colorings are V4-equivalent if one can be transformed into the other by a global shift. -/
def v4_equivalent (cols1 cols2 : Array Color) : Prop :=
  ∃ shift : Color, ∀ i : Fin cols1.size, 
    cols2[i.val]! = colorXor cols1[i.val]! shift

end Hypermap
