import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.U633String

namespace Math

def splitString (s : String) (c : Char) : List String :=
  s.split (fun x => x == c)

def parseNatList (s : String) : List Nat :=
  (s.split (fun ch => ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t')).filterMap (fun x => 
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
      -- Header: n r X Y a, followed by the 2·a contract vertices; adjacency starts after that.
      let a := nums.getD 4 0
      let mut idx := 5 + 2 * a
        
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
def parseAllConfigs (_ : Unit) : Array Configuration :=
  Id.run do
    let blocks := splitString u633_data '|'
    let mut arr := #[]
    for b in blocks do
      if b != "" then
        arr := arr.push (parseConfig b)
    return arr




end Math
