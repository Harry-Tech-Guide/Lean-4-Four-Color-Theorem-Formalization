module

public import FourColorTheorem.Math.Reducibility
public import FourColorTheorem.Math.U633String
public import FourColorTheorem.Math.Batch.Runner

@[expose] public section

set_option maxRecDepth 500000

namespace Math

def splitString (s : String) (c : Char) : List String :=
  (s.split (fun x => x == c)).toList.map (·.toString)

def parseNatList (s : String) : List Nat :=
  ((s.split (fun ch => ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t')).toList).filterMap (fun x => if x.toString == "" then none else x.toString.toNat?)

def mkAdjFromFlat (n : Nat) (data : Array Bool) : Nat -> Nat -> Bool :=
  fun i j => if i * n + j < data.size then data[i * n + j]! else false

def parseConfig (s : String) : Configuration :=
  let nums := parseNatList s
  if nums.length >= 2 then
    let numVertices := nums[0]!
    let ringSize := nums[1]!

    Id.run do
      let mut flat := Array.replicate (numVertices * numVertices) false
      -- Header: n r X Y a, followed by the 2·a contract vertices; adjacency starts after that.
      let a := nums.getD 4 0
      let mut contracts : List (Nat × Nat) := []
      for i in [0:a] do
        if 5 + 2 * i + 1 < nums.length then
          contracts := contracts.concat (nums[5 + 2 * i]! - 1, nums[5 + 2 * i + 1]! - 1)
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
        adj := mkAdjFromFlat numVertices flat,
        contractEdges := contracts
      }
  else
    { ringSize := 0, interiorSize := 0, adj := fun _ _ => false, contractEdges := [] }

/-- Parse the entire U633 dataset into an array of Configurations at runtime. -/
def parseAllConfigs (_ : Unit) : Array Configuration :=
  Id.run do
    let blocks := splitString u633_data '|'
    let mut arr := #[]
    for b in blocks do
      if b != "" then
        arr := arr.push (parseConfig b)
    return arr

/-- Canonical symmetric irreflexive adjacency relation generated from `earlier` lists. -/
def symAdj (earlier : Array (Array Nat)) (i j : Nat) : Bool :=
  if i < j then
    (earlier.getD j #[]).toList.contains i
  else if j < i then
    (earlier.getD i #[]).toList.contains j
  else
    false

/-- Canonical conversion of a parsed `RConf` from `FastReducer` into a `Configuration`. -/
def configOfRConf (rc : FastReducer.RConf) : Configuration where
  ringSize := rc.r
  interiorSize := rc.n - rc.r
  adj := symAdj rc.earlier
  contractEdges := rc.contractEdges.toList

/-- The 633 unavoidable configurations from the RSST dataset. -/
def theUnavoidableSet : Array Configuration :=
  ⟨parsedRConfList.map configOfRConf⟩

/-- The pre-elaborated RSST configuration list has length 633. -/
theorem parsedRConfList_length : parsedRConfList.length = 633 := by rfl

/-- The canonical RSST unavoidable set has exactly 633 configurations. -/
theorem unavoidable_size_eq : theUnavoidableSet.size = 633 := by
  unfold Array.size theUnavoidableSet
  rw [List.length_map, parsedRConfList_length]

/-- Every configuration in the unavoidable set has interior size ≥ 4 (list boolean form),
    verified directly in the Lean 4 kernel by `rfl` over all 633 configurations. -/
-- maxRecDepth set at top of file
theorem unavoidable_data_all_int : theUnavoidableSet.toList.all (fun c => c.interiorSize >= 4) = true := by
  rfl

/-- Every configuration in the RSST unavoidable set has at least 4 interior vertices. -/
theorem unavoidable_interior_ge_4 (c : Configuration) (h : c ∈ theUnavoidableSet) :
    c.interiorSize ≥ 4 := by
  have hMem : c ∈ theUnavoidableSet.toList := Array.mem_toList_iff.mpr h
  have hDec : decide (c.interiorSize >= 4) = true :=
    List.all_eq_true.mp unavoidable_data_all_int c hMem
  exact of_decide_eq_true hDec

/-- General indexing lemma for an array built by mapping `f` over a list `L`. -/
theorem array_map_getElem! (L : List FastReducer.RConf) (f : FastReducer.RConf → Configuration)
    (idx : Nat) (h_lt : idx < L.length) :
    (⟨L.map f⟩ : Array Configuration)[idx]! = f (⟨L⟩ : Array FastReducer.RConf)[idx]! := by
  let arr1 : Array Configuration := ⟨L.map f⟩
  let arr2 : Array FastReducer.RConf := ⟨L⟩
  have h1 : idx < arr1.size := by
    dsimp [arr1, Array.size]
    rw [List.length_map]
    exact h_lt
  have h2 : idx < arr2.size := h_lt
  rw [getElem!_pos arr1 idx h1, getElem!_pos arr2 idx h2]
  change (L.map f)[idx]'h1 = f (L[idx]'h2)
  exact List.getElem_map f

/-- Indexing into `theUnavoidableSet` at `idx < 633` yields `configOfRConf Batch.sharedCfgs[idx]!`. -/
theorem theUnavoidableSet_getElem! (idx : Nat) (h_lt : idx < 633) :
    theUnavoidableSet[idx]! = configOfRConf Batch.sharedCfgs[idx]! := by
  have h_len : idx < parsedRConfList.length := by
    rw [parsedRConfList_length]
    exact h_lt
  unfold theUnavoidableSet Batch.sharedCfgs parsedRConfArray
  exact array_map_getElem! parsedRConfList configOfRConf idx h_len

/-- Every configuration in the RSST unavoidable set has strictly positive interior size. -/
theorem unavoidable_interior_pos (c : Configuration) (h : c ∈ theUnavoidableSet) :
  c.interiorSize > 0 := by
  have h4 := unavoidable_interior_ge_4 c h
  omega

end Math
