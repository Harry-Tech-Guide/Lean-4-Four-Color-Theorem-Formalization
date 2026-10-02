import FourColorTheorem
import FourColorTheorem.Math.Checker

open Math

/-- A configuration with a boundary ring of 3 nodes and 1 interior node.
The interior node (3) is connected to all boundary nodes (0, 1, 2).
Boundary nodes are connected in a cycle: (0,1), (1,2), (2,0). -/
def degree3_adj : Nat → Nat → Bool
  | 0, 1 => true | 1, 0 => true
  | 1, 2 => true | 2, 1 => true
  | 2, 0 => true | 0, 2 => true
  | 0, 3 => true | 3, 0 => true
  | 1, 3 => true | 3, 1 => true
  | 2, 3 => true | 3, 2 => true
  | _, _ => false

def degree3_config : Configuration := {
  ringSize := 3,
  interiorSize := 1,
  adj := degree3_adj
}

/-- A configuration with a boundary ring of 4 nodes and 1 interior node.
The interior node (4) is connected to all boundary nodes (0, 1, 2, 3).
Boundary nodes are connected in a cycle. -/
def degree4_adj : Nat → Nat → Bool
  | 0, 1 => true | 1, 0 => true
  | 1, 2 => true | 2, 1 => true
  | 2, 3 => true | 3, 2 => true
  | 3, 0 => true | 0, 3 => true
  | 0, 4 => true | 4, 0 => true
  | 1, 4 => true | 4, 1 => true
  | 2, 4 => true | 4, 2 => true
  | 3, 4 => true | 4, 3 => true
  | _, _ => false

def degree4_config : Configuration := {
  ringSize := 4,
  interiorSize := 1,
  adj := degree4_adj
}

def main : IO Unit := do
  IO.println s!"Four Color Theorem Project Initialized!"
  
  -- Test the D-Reducibility checker on a degree 3 node configuration
  let res3 := checkDReducible degree3_config
  IO.println s!"Is a degree-3 node configuration D-Reducible? {res3}"
  
  -- Test the D-Reducibility checker on a degree 4 node configuration
  -- Note: A degree 4 node is NOT D-reducible because if the boundary is colored
  -- with 4 different colors, the center node has no available colors.
  let res4 := checkDReducible degree4_config
  IO.println s!"Is a degree-4 node configuration D-Reducible? {res4}"

