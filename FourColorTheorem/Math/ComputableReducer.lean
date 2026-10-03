import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Reducibility

set_option linter.unusedVariables false

namespace Math
namespace ComputableReducer

/-- A computable representation of a boundary coloring. -/
abbrev ColorList := Array Nat

/-- Check if a color list is valid on the boundary ring. -/
def isValidRing (ringSize : Nat) (colors : ColorList) : Bool :=
  if colors.size != ringSize then false
  else if ringSize == 0 then true
  else Id.run do
    let mut valid := true
    for i in [0:ringSize] do
      let c1 := colors[i]!
      let c2 := colors[(i + 1) % ringSize]!
      if c1 == c2 then
        valid := false
        break
    return valid

/-- Generate all valid ring colorings of size N using colors 0, 1, 2, 3. -/
def generateRingColorings (ringSize : Nat) : Array ColorList :=
  let rec build (current : ColorList) (acc : Array ColorList) : Array ColorList :=
    if h : current.size < ringSize then
      Id.run do
        let mut newAcc := acc
        for c in [0, 1, 2, 3] do
          if current.size > 0 && current[current.size - 1]! == c then
            continue
          newAcc := build (current.push c) newAcc
        return newAcc
    else
      if isValidRing ringSize current then acc.push current else acc
  termination_by ringSize - current.size
  
  if ringSize == 0 then #[]
  else build #[0] #[]

/-- Backtracking solver to check if a valid boundary coloring can be extended
to a full valid coloring of the configuration's interior nodes. -/
def extendsToInterior (c : Configuration) (boundary : ColorList) : Bool :=
  let total := c.totalNodes
  let rec solve (idx : Nat) (currentColors : Array Nat) : Bool :=
    if h : idx < total then Id.run do
      let mut canExtend := false
      for color in [0, 1, 2, 3] do
        let mut valid := true
        for neighbor in [0:idx] do
          if c.adj idx neighbor && currentColors[neighbor]! == color then
            valid := false
            break
        if valid then
          if solve (idx + 1) (currentColors.push color) then
            canExtend := true
            break
      return canExtend
    else 
      true
  termination_by total - idx
  
  -- The boundary is already colored, so we start with it.
  solve c.ringSize boundary

/-- Get all boundary colorings that DO NOT extend. These are the "live" colorings
that we must reduce via Kempe swaps. -/
def getNonExtendingColorings (c : Configuration) : Array ColorList :=
  let allColorings := generateRingColorings c.ringSize
  allColorings.filter (fun b => not (extendsToInterior c b))

-- The new namespace continues down to the end of the file.
/-- Map a 4-coloring of the boundary vertices to a 3-coloring of the boundary edges using the Klein four-group.
In the Klein 4-group, elements are 0 (00), 1 (01), 2 (10), 3 (11).
The edge color is the bitwise XOR of the two adjacent vertex colors. -/
def vertexToEdgeColoring (ringSize : Nat) (col : ColorList) : Array Nat :=
  Id.run do
    let mut edgeCol := #[]
    for i in [0:ringSize] do
      let c1 := col[i]!
      let c2 := col[(i + 1) % ringSize]!
      edgeCol := edgeCol.push (c1.xor c2)
    return edgeCol

/-- A computable representation of a signed matching on the boundary ring edges. -/
structure SignedMatching where
  /-- The number of matched pairs -/
  numPairs : Nat
  /-- Array of size 2 * numPairs, containing the 0-indexed edge indices of the pairs -/
  pairs : Array Nat
  /-- The sign associated with each pair (+1 represented as true, -1 as false) -/
  signs : Array Bool

/-- 
RSST Theta-Fitting:
An edge coloring `ecol` theta-fits a matching `m` for color `theta` (1, 2, or 3) if:
1. No matched edge has color `theta`.
2. For every matched pair, their colors are equal iff the pair's sign is +1 (true).
3. Every edge that is NOT matched MUST have color `theta`.
-/
def checkThetaFit (ringSize : Nat) (col : ColorList) (theta : Nat) (m : SignedMatching) : Bool :=
  let ecol := vertexToEdgeColoring ringSize col
  Id.run do
    let mut matchedEdges := mkArray ringSize false
    let mut fits := true
    
    for i in [0:m.numPairs] do
      let e1 := m.pairs[2 * i]!
      let e2 := m.pairs[2 * i + 1]!
      
      matchedEdges := matchedEdges.set! e1 true
      matchedEdges := matchedEdges.set! e2 true
      
      let c1 := ecol[e1]!
      let c2 := ecol[e2]!
      
      if c1 == theta || c2 == theta then
        fits := false
        break
        
      let sign := m.signs[i]!
      let colorsEqual := (c1 == c2)
      if colorsEqual != sign then
        fits := false
        break
        
    if not fits then return false
    
    for i in [0:ringSize] do
      if not matchedEdges[i]! then
        if ecol[i]! != theta then
          fits := false
          break
          
    return fits

/-- Generate all perfect matchings of a given array of elements. -/
partial def getMatchings (elements : Array Nat) : Array (Array (Nat × Nat)) :=
  if elements.size == 0 then #[ #[] ]
  else Id.run do
    let first := elements[0]!
    let rest := elements.extract 1 elements.size
    let mut res := #[]
    for i in [0:rest.size] do
      let pair := (first, rest[i]!)
      let remaining := (rest.extract 0 i) ++ (rest.extract (i+1) rest.size)
      for m in getMatchings remaining do
        res := res.push (m.push pair)
    return res

/-- Check if a matching is non-crossing. -/
def isNonCrossing (m : Array (Nat × Nat)) : Bool :=
  Id.run do
    for i in [0:m.size] do
      for j in [0:m.size] do
        let (a, b) := m[i]!
        let (c, d) := m[j]!
        let (a, b) := if a < b then (a, b) else (b, a)
        let (c, d) := if c < d then (c, d) else (d, c)
        
        if (a < c && c < b && b < d) || (c < a && a < d && d < b) then
          return false
    return true

/-- Generate all sign assignments (+1=true, -1=false) for a given number of pairs. -/
partial def getSignAssignments (numPairs : Nat) : Array (Array Bool) :=
  if numPairs == 0 then #[ #[] ]
  else Id.run do
    let mut res := #[]
    for s in getSignAssignments (numPairs - 1) do
      res := res.push (s.push true)
      res := res.push (s.push false)
    return res

/-- Generate balanced signed matchings for a given ring size. -/
partial def generateBalancedSignedMatchings (ringSize : Nat) : Array SignedMatching :=
  Id.run do
    let mut results := #[]
    let numSubsets := 1 <<< ringSize
    for subsetMask in [0:numSubsets] do
      let mut k := subsetMask
      let mut bitCount := 0
      while k > 0 do
        if k % 2 == 1 then bitCount := bitCount + 1
        k := k / 2
        
      if bitCount % 2 == 0 then
        let mut subset := #[]
        for i in [0:ringSize] do
          if (subsetMask >>> i) % 2 == 1 then
            subset := subset.push i
            
        for m in getMatchings subset do
          if isNonCrossing m then
            let numPairs := m.size
            for signs in getSignAssignments numPairs do
              let mut negCount := 0
              for s in signs do
                if not s then negCount := negCount + 1
              if negCount % 2 == ringSize % 2 then
                let mut flatPairs := #[]
                for (a,b) in m do
                  flatPairs := flatPairs.push a
                  flatPairs := flatPairs.push b
                results := results.push { numPairs := numPairs, pairs := flatPairs, signs := signs }
    return results

/-- The computable implementation of `computeMaxConsistentSubset`.
It computes the greatest fixed point of the reduction operator over the live colorings.
Returns the final array of live colorings. If empty, the configuration is D-reducible! -/
def computeMaxConsistentSubset (c : Configuration) : Array ColorList :=
  let ringSize := c.ringSize
  let initialLive := getNonExtendingColorings c
  let matchings := generateBalancedSignedMatchings ringSize
  
  set_option linter.unusedVariables false in
  let rec fixpoint (live : Array ColorList) : Array ColorList :=
    let M_live := matchings.filter (fun m => Id.run do
      let mut isAlive := true
      for col in (generateRingColorings ringSize) do
        for x in [0, 1, 2, 3] do
          if checkThetaFit ringSize col x m then
            if not (live.contains col) then
              isAlive := false
              break
        if not isAlive then break
      return isAlive
    )
    
    let nextLive := live.filter (fun col => Id.run do
      let mut survives := true
      for x in [0, 1, 2, 3] do
        let mut fitsAny := false
        for m in M_live do
          if checkThetaFit ringSize col x m then
            fitsAny := true
            break
        if not fitsAny then
          survives := false
          break
      return survives
    )
    
    if h : nextLive.size < live.size then 
      fixpoint nextLive
    else 
      live
  termination_by live.size
  decreasing_by exact h
  
  fixpoint initialLive

/-- The final computable D-reducibility check! -/
def isComputablyDReducible (c : Configuration) : Bool :=
  (computeMaxConsistentSubset c).size == 0


end ComputableReducer
end Math
