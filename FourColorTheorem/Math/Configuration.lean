
import FourColorTheorem.Math.Coloring

-- Step 5: Configurations and Rings

instance : Inhabited Color where
  default := Color.c0

namespace Hypermap

variable (H : Hypermap)

def IsConfiguration (C : H.Dart → Bool) : Prop :=
  (∀ d, C (H.node.f d) = C d)

structure Ring (k : Nat) where
  darts : Array H.Dart
  size_eq : darts.size = k
  outside_config : ∀ C : H.Dart → Bool, IsConfiguration H C → ∀ d ∈ darts.toList, C d = false

def isValidRingColoring (k : Nat) (cols : Array Color) : Bool :=
  if cols.size != k then false
  else Id.run do
    for i in [0:k] do
      let nxt := if i + 1 == k then 0 else i + 1
      if cols[i]! == cols[nxt]! then return false
    return true

def IsExtensible (k : Nat) (R : Ring H k) (cols : Array Color) : Prop :=
  isValidRingColoring k cols = true ∧ 
  ∃ (vc : VertexColoring H), ∀ i : Fin k, 
    vc.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt)) = cols[i.val]!

/-- A configuration is Reducible if every valid coloring of its surrounding ring 
    is extensible (potentially after Kempe swaps on the exterior map). 
    This is the exact mathematical property that runCReduction guarantees. -/
def IsReducible (k : Nat) (R : Ring H k) : Prop :=
  ∀ cols, isValidRingColoring k cols = true → IsExtensible H k R cols

end Hypermap
