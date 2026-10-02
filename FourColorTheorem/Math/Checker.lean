import FourColorTheorem.Math.Reducibility

namespace Math

/-- Evaluate adjacency between two nodes. -/
def areAdjacent (c : Configuration) (i j : Nat) : Bool := c.adj i j

/-- Check if assigning `color` to node `idx` is valid given an array of existing color assignments. -/
def isValidColorAssignment (c : Configuration) (idx : Nat) (color : Color) (assignments : Array (Option Color)) : Bool :=
  let rec loop (j : Nat) : Bool :=
    if h : j < idx then
      if areAdjacent c idx j then
        match assignments[j]! with
        | some col => if col == color then false else loop (j + 1)
        | none => loop (j + 1)
      else loop (j + 1)
    else true
  loop 0

/-- Backtracking search to color nodes starting from `nodeIdx` up to `c.totalNodes`.
Returns true if a valid extension exists. -/
partial def canExtendInterior (c : Configuration) (nodeIdx : Nat) (assignments : Array (Option Color)) : Bool :=
  if nodeIdx >= c.totalNodes then
    true -- We successfully colored all interior nodes
  else
    let tryColor (col : Color) : Bool :=
      if isValidColorAssignment c nodeIdx col assignments then
        canExtendInterior c (nodeIdx + 1) (assignments.set! nodeIdx (some col))
      else false
    
    tryColor Color.c1 || tryColor Color.c2 || tryColor Color.c3 || tryColor Color.c4

/-- Given a boundary coloring array, verify it's a valid boundary and if so, check if it extends. -/
def checkBoundaryAndExtend (c : Configuration) (boundary : Array Color) : Bool :=
  -- First, check if boundary is valid internally
  let rec checkValid (i : Nat) (j : Nat) : Bool :=
    if i < c.ringSize then
      if j < c.ringSize then
        if areAdjacent c i j && boundary[i]! == boundary[j]! then false
        else checkValid i (j + 1)
      else checkValid (i + 1) 0
    else true
    
  if !checkValid 0 0 then
    true -- Vacuously true: if boundary is invalid, we don't need to extend it.
  else Id.run (α := Bool) do
    -- Initialize the assignments array with boundary colors
    let mut assignments : Array (Option Color) := #[]
    for i in [0:c.ringSize] do
      assignments := assignments.push (some boundary[i]!)
    for _ in [c.ringSize:c.totalNodes] do
      assignments := assignments.push none
      
    return canExtendInterior c c.ringSize assignments

/-- Generates all 4^ringSize boundary colorings and checks if ALL valid ones can be extended. -/
partial def checkAllBoundaries (c : Configuration) (nodeIdx : Nat) (currentBoundary : Array Color) : Bool :=
  if nodeIdx >= c.ringSize then
    checkBoundaryAndExtend c currentBoundary
  else
    checkAllBoundaries c (nodeIdx + 1) (currentBoundary.push Color.c1) &&
    checkAllBoundaries c (nodeIdx + 1) (currentBoundary.push Color.c2) &&
    checkAllBoundaries c (nodeIdx + 1) (currentBoundary.push Color.c3) &&
    checkAllBoundaries c (nodeIdx + 1) (currentBoundary.push Color.c4)

/-- The executable function to check if a configuration is D-Reducible! -/
def checkDReducible (c : Configuration) : Bool :=
  checkAllBoundaries c 0 #[]

end Math
