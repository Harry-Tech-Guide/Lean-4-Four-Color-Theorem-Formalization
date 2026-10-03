import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.U633String

namespace Math

def splitString (s : String) (c : Char) : List String :=
  s.split (fun x => x == c)

def parseNatList (s : String) : List Nat :=
  (splitString s ' ').filterMap (fun x => 
    if x == "" then none else x.toNat?)

def mkAdjFromFlat (n : Nat) (data : Array Bool) : Nat -> Nat -> Bool :=
  fun i j => if i * n + j < data.size then data[i * n + j]! else false

def parseConfig (s : String) : Configuration :=
  let nums := parseNatList s
  if nums.length >= 2 then
    let numVertices := nums[0]!
    let ringSize := nums[1]!
    
    Id.run do
      let mut flat := mkArray (numVertices * numVertices) false
      let mut idx := 2
      -- Skip metadata until we see the first vertex '1'
      while idx < nums.length && nums[idx]! != 1 do
        idx := idx + 1
        
      for _ in [0:numVertices] do
        if idx < nums.length then
          let v := nums[idx]!
          idx := idx + 1
          if idx < nums.length then
            let degree := nums[idx]!
            idx := idx + 1
            for _ in [0:degree] do
              if idx < nums.length then
                let nb := nums[idx]!
                idx := idx + 1
                let i := v - 1
                let j := nb - 1
                if i < numVertices && j < numVertices then
                  flat := flat.set! (i * numVertices + j) true
                  flat := flat.set! (j * numVertices + i) true
      
      return {
        ringSize := ringSize,
        interiorSize := numVertices - ringSize,
        adj := mkAdjFromFlat numVertices flat
      }
  else
    { ringSize := 0, interiorSize := 0, adj := fun _ _ => false }

/-- Parse the entire U633 dataset into an array of Configurations at runtime. -/
def parseAllConfigs : Array Configuration :=
  Id.run do
    let blocks := splitString u633_data '|'
    let mut arr := #[]
    for b in blocks do
      if b != "" then
        arr := arr.push (parseConfig b)
    return arr

/-- The unavoidable set of configurations, directly computable in the Kernel via string parsing. -/
def theUnavoidableSet : List Configuration := parseAllConfigs.toList

end Math
