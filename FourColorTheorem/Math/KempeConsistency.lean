
import FourColorTheorem.Math.Kempe
import FourColorTheorem.Math.Configuration

-- Step 8: Exterior Kempe Matchings

namespace Hypermap

variable (H : Hypermap) (k : Nat) (R : Ring H k)

/-- For a given 4-coloring and two colors a and b, the exterior map naturally partitions
    the boundary ring darts into connected Kempe components. 
    This relation represents whether dart i and dart j belong to the same component. -/
def IsValidExteriorKempePartition (c : VertexColoring H) (a b : Color) (equiv : Fin k → Fin k → Prop) : Prop :=
  -- It is an equivalence relation on the subset of darts colored a or b
  (∀ i, (c.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt)) = a ∨ c.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt)) = b) → equiv i i) ∧
  (∀ i j, equiv i j → equiv j i) ∧
  (∀ i j l, equiv i j → equiv j l → equiv i l) ∧
  -- It strictly only relates boundary darts that are colored a or b
  (∀ i j, equiv i j → (c.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt)) = a ∨ c.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt)) = b)) ∧
  -- The fundamental topological constraint: because the exterior map is Planar,
  -- Kempe chains cannot cross each other. If they alternate (i < j < l < m), 
  -- they MUST merge into the exact same component.
  (∀ i j l m, i.val < j.val → j.val < l.val → l.val < m.val → 
              equiv i l → equiv j m → equiv i j)

/-- A valid exterior Kempe swap must swap entire connected components at once. 
    swapSet determines whether a boundary dart's component is swapped. -/
def ValidSwapChoice (equiv : Fin k → Fin k → Prop) (swapSet : Fin k → Bool) : Prop :=
  ∀ i j, equiv i j → swapSet i = swapSet j

/-- The Resulting Ring Coloring after applying a valid exterior Kempe swap. -/
def swappedRingColoring (c : VertexColoring H) (a b : Color) (swapSet : Fin k → Bool) : Fin k → Color :=
  fun i => if swapSet i then swapColor (c.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt))) a b 
           else c.color (R.darts[i.val]'(by rw [R.size_eq]; exact i.isLt))

end Hypermap
