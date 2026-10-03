import FourColorTheorem.Math.ComputableReducer

namespace Math
namespace ComputableReducer

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

/-- Check if a matching is non-crossing. 
A crossing happens if there are two pairs (a,b) and (c,d) with a < c < b < d (assuming sorted elements).
Since our elements are drawn from 0..ringSize-1, they are naturally sorted. -/
def isNonCrossing (m : Array (Nat × Nat)) : Bool :=
  Id.run do
    for i in [0:m.size] do
      for j in [0:m.size] do
        let (a, b) := m[i]!
        let (c, d) := m[j]!
        -- Ensure a < b and c < d
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
partial def generateBalancedSignedMatchingsReal (ringSize : Nat) : Array SignedMatching :=
  Id.run do
    let mut results := #[]
    let numSubsets := 1 <<< ringSize
    for subsetMask in [0:numSubsets] do
      -- Count bits to see if subset is even sized
      let mut k := subsetMask
      let mut bitCount := 0
      while k > 0 do
        if k % 2 == 1 then bitCount := bitCount + 1
        k := k / 2
        
      if bitCount % 2 == 0 then
        -- Extract elements
        let mut subset := #[]
        for i in [0:ringSize] do
          if (subsetMask >>> i) % 2 == 1 then
            subset := subset.push i
            
        -- Get matchings
        for m in getMatchings subset do
          if isNonCrossing m then
            let numPairs := m.size
            for signs in getSignAssignments numPairs do
              -- Count false (negative) signs
              let mut negCount := 0
              for s in signs do
                if not s then negCount := negCount + 1
              
              -- Balanced condition: parity of negCount equals parity of ringSize
              if negCount % 2 == ringSize % 2 then
                -- Pack into SignedMatching
                let mut flatPairs := #[]
                for (a,b) in m do
                  flatPairs := flatPairs.push a
                  flatPairs := flatPairs.push b
                results := results.push { numPairs := numPairs, pairs := flatPairs, signs := signs }
    return results

end ComputableReducer
end Math
