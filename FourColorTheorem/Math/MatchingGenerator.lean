import FourColorTheorem.Math.ComputableReducer

namespace Math
namespace ComputableReducer

/-- Generate all perfect matchings of a given array of elements (fuel-bounded). -/
def getMatchingsAux : Nat → Array Nat → Array (Array (Nat × Nat))
  | 0, _ => #[ #[] ]
  | fuel + 1, elements =>
    if elements.size == 0 then #[ #[] ]
    else Id.run do
      let first := elements[0]!
      let rest := elements.extract 1 elements.size
      let mut res := #[]
      for i in [0:rest.size] do
        let pair := (first, rest[i]!)
        let remaining := (rest.extract 0 i) ++ (rest.extract (i+1) rest.size)
        for m in getMatchingsAux fuel remaining do
          res := res.push (m.push pair)
      return res

def getMatchings (elements : Array Nat) : Array (Array (Nat × Nat)) :=
  getMatchingsAux elements.size elements

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
def getSignAssignments : Nat → Array (Array Bool)
  | 0 => #[ #[] ]
  | numPairs + 1 => Id.run do
    let mut res := #[]
    for s in getSignAssignments numPairs do
      res := res.push (s.push true)
      res := res.push (s.push false)
    return res

/-- Count bits of a natural number (fuel-bounded). -/
def countBitsAux : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
    if k == 0 then acc
    else countBitsAux fuel (k / 2) (if k % 2 == 1 then acc + 1 else acc)

/-- Generate balanced signed matchings for a given ring size. -/
def generateBalancedSignedMatchingsReal (ringSize : Nat) : Array SignedMatching :=
  Id.run do
    let mut results := #[]
    let numSubsets := 1 <<< ringSize
    for subsetMask in [0:numSubsets] do
      let bitCount := countBitsAux ringSize subsetMask 0
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

end ComputableReducer
end Math
