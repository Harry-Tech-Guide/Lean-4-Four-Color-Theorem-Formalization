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

/-- The 633 unavoidable configurations from the RSST dataset. -/
def theUnavoidableSet : Array Configuration :=
  parseAllConfigs ()

/-- Computational certificate: every configuration in the unavoidable set has interior size ≥ 4. -/
theorem unavoidable_data_all_int : theUnavoidableSet.data.all (fun c => c.interiorSize >= 4) = true := by
  native_decide

/-- Every configuration in the RSST unavoidable set has at least 4 interior vertices. -/
theorem unavoidable_interior_ge_4 (c : Configuration) (h : c ∈ theUnavoidableSet) :
  c.interiorSize ≥ 4 := by
  have hMem : c ∈ theUnavoidableSet.data := Array.mem_data.mpr h
  have hTrue := List.all_eq_true.mp unavoidable_data_all_int c hMem
  exact of_decide_eq_true hTrue

/-- Every configuration in the RSST unavoidable set has strictly positive interior size. -/
theorem unavoidable_interior_pos (c : Configuration) (h : c ∈ theUnavoidableSet) :
  c.interiorSize > 0 := by
  have h4 := unavoidable_interior_ge_4 c h
  omega

end Math
