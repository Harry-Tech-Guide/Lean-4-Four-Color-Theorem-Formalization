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
  else
    (List.range ringSize).all fun i =>
      colors.toList.get! i != colors.toList.get! ((i + 1) % ringSize)

/-- Generate all canonical valid ring colorings of size N using colors 0, 1, 2, 3 (up to S_4 color symmetry). -/
def genRingLists : Nat → Nat → Nat → List (List Nat)
  | 0, _, _ => [[]]
  | fuel + 1, prev, maxCol =>
    let limit := if Nat.blt maxCol 3 then maxCol + 1 else 3
    match fuel with
    | 0 =>
      (if prev != 1 && Nat.ble 1 limit then [[1]] else []) ++
      (if prev != 2 && Nat.ble 2 limit then [[2]] else []) ++
      (if prev != 3 && Nat.ble 3 limit then [[3]] else [])
    | _ =>
      (if prev != 0 then (genRingLists fuel 0 maxCol).map (0 :: ·) else []) ++
      (if prev != 1 && Nat.ble 1 limit then (genRingLists fuel 1 (if Nat.blt maxCol 1 then 1 else maxCol)).map (1 :: ·) else []) ++
      (if prev != 2 && Nat.ble 2 limit then (genRingLists fuel 2 (if Nat.blt maxCol 2 then 2 else maxCol)).map (2 :: ·) else []) ++
      (if prev != 3 && Nat.ble 3 limit then (genRingLists fuel 3 3).map (3 :: ·) else [])

def generateRingColorings (ringSize : Nat) : Array ColorList :=
  match ringSize with
  | 0 => #[]
  | 1 => #[#[0]]
  | r + 1 => Array.mk ((genRingLists r 0 0).map (fun tail => Array.mk (0 :: tail)))

def colorAt : List Nat → Nat → Nat
  | [], _ => 99
  | x :: xs, n =>
    match n with
    | 0 => x
    | m + 1 => colorAt xs m

def strictNat (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

def forceBoolListRev : List Bool → List Bool → List Bool
  | [], acc => acc
  | b :: xs, acc =>
    match b with
    | true => forceBoolListRev xs (true :: acc)
    | false => forceBoolListRev xs (false :: acc)

def strictBoolList (l : List Bool) (k : List Bool → α) : α :=
  match forceBoolListRev (forceBoolListRev l []) [] with
  | [] => k []
  | x :: xs => k (x :: xs)

def forceNatListRev : List Nat → List Nat → List Nat
  | [], acc => acc
  | x :: xs, acc =>
    strictNat x fun x' => forceNatListRev xs (x' :: acc)

def strictNatList (l : List Nat) (k : List Nat → α) : α :=
  match forceNatListRev (forceNatListRev l []) [] with
  | [] => k []
  | x :: xs => k (x :: xs)

def forceListOfNatListRev : List (List Nat) → List (List Nat) → List (List Nat)
  | [], acc => acc
  | x :: xs, acc =>
    strictNatList x fun x' => forceListOfNatListRev xs (x' :: acc)

def strictListOfNatList (l : List (List Nat)) (k : List (List Nat) → α) : α :=
  match forceListOfNatListRev (forceListOfNatListRev l []) [] with
  | [] => k []
  | x :: xs => k (x :: xs)

def interiorNeighborOffsets (c : Configuration) : List (List Nat) :=
  (List.range c.interiorSize).map fun k =>
    let idx := c.ringSize + k
    ((List.range idx).filter fun nb => c.adj idx nb).map fun nb => idx - 1 - nb

def extendsRev : List (List Nat) → List Nat → Bool
  | [], _ => true
  | offsets :: rest, revColors =>
    (offsets.all (fun off => colorAt revColors off != 0) && extendsRev rest (0 :: revColors)) ||
    (offsets.all (fun off => colorAt revColors off != 1) && extendsRev rest (1 :: revColors)) ||
    (offsets.all (fun off => colorAt revColors off != 2) && extendsRev rest (2 :: revColors)) ||
    (offsets.all (fun off => colorAt revColors off != 3) && extendsRev rest (3 :: revColors))

/-- Backtracking solver to check if a valid boundary coloring can be extended
to a full valid coloring of the configuration's interior nodes. -/
def extendsToInterior (c : Configuration) (boundary : ColorList) : Bool :=
  strictListOfNatList (interiorNeighborOffsets c) fun offsetLists =>
    extendsRev offsetLists (forceNatListRev boundary.toList [])

/-- Get all boundary colorings that DO NOT extend. These are the "live" colorings
that we must reduce via Kempe swaps. -/
def getNonExtendingColorings (c : Configuration) : Array ColorList :=
  let allColorings := generateRingColorings c.ringSize
  strictListOfNatList (interiorNeighborOffsets c) fun offsetLists =>
    Array.mk (allColorings.toList.filter (fun b => not (extendsRev offsetLists (forceNatListRev b.toList []))))

def xor4 (a b : Nat) : Nat :=
  match a, b with
  | 0, x => x
  | x, 0 => x
  | 1, 1 | 2, 2 | 3, 3 => 0
  | 1, 2 | 2, 1 => 3
  | 1, 3 | 3, 1 => 2
  | 2, 3 | 3, 2 => 1
  | _, _ => 0

/-- Map a 4-coloring of the boundary vertices to a 3-coloring of the boundary edges using the Klein four-group.
In the Klein 4-group, elements are 0 (00), 1 (01), 2 (10), 3 (11).
The edge color is the bitwise XOR of the two adjacent vertex colors. -/
def vertexToEdgeColoring (ringSize : Nat) (col : ColorList) : Array Nat :=
  let l := col.toList
  Array.mk ((List.range ringSize).map fun i =>
    xor4 (l.get! i) (l.get! ((i + 1) % ringSize)))

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
def checkThetaFit (ringSize : Nat) (ecol : Array Nat) (theta : Nat) (m : SignedMatching) : Bool :=
  let el := ecol.toList
  let pl := m.pairs.toList
  let sl := m.signs.toList
  let pairsOk := (List.range m.numPairs).all fun i =>
    let e1 := pl.get! (2 * i)
    let e2 := pl.get! (2 * i + 1)
    let c1 := el.get! e1
    let c2 := el.get! e2
    let sign := sl.get! i
    c1 != theta && c2 != theta && ((c1 == c2) == sign)
  if !pairsOk then false
  else
    (List.range ringSize).all fun i =>
      if pl.contains i then true
      else el.get! i == theta

/-- Generate all perfect matchings of a given list of elements. -/
def getMatchingsList : Nat → List Nat → List (List (Nat × Nat))
  | 0, _ => [[]]
  | fuel + 1, elems =>
    match elems with
    | [] => [[]]
    | first :: rest =>
      (List.range rest.length).bind fun i =>
        let partner := rest.get! i
        let remaining := rest.take i ++ rest.drop (i + 1)
        (getMatchingsList fuel remaining).map fun m => (first, partner) :: m

def getMatchings (elements : Array Nat) : Array (Array (Nat × Nat)) :=
  let l := elements.toList
  Array.mk ((getMatchingsList l.length l).map Array.mk)

/-- Check if a matching is non-crossing. -/
def isNonCrossingList (m : List (Nat × Nat)) : Bool :=
  m.all fun (a0, b0) =>
    m.all fun (c0, d0) =>
      let (a, b) := if Nat.blt a0 b0 then (a0, b0) else (b0, a0)
      let (c, d) := if Nat.blt c0 d0 then (c0, d0) else (d0, c0)
      !((Nat.blt a c && Nat.blt c b && Nat.blt b d) || (Nat.blt c a && Nat.blt a d && Nat.blt d b))

def isNonCrossing (m : Array (Nat × Nat)) : Bool :=
  isNonCrossingList m.toList

/-- Generate all sign assignments (+1=true, -1=false) for a given number of pairs. -/
def getSignAssignmentsList : Nat → List (List Bool)
  | 0 => [[]]
  | numPairs + 1 =>
    (getSignAssignmentsList numPairs).bind fun s => [true :: s, false :: s]

def getSignAssignments (numPairs : Nat) : Array (Array Bool) :=
  Array.mk ((getSignAssignmentsList numPairs).map Array.mk)

def allSubsets : List Nat → List (List Nat)
  | [] => [[]]
  | y :: ys =>
    let s := allSubsets ys
    s ++ s.map (y :: ·)

def subsetsOfEvenSize (l : List Nat) : List (List Nat) :=
  (allSubsets l).filter (fun s => s.length % 2 == 0)

/-- Generate balanced signed matchings for a given ring size. -/
def generateBalancedSignedMatchings (ringSize : Nat) : Array SignedMatching :=
  let subsets := subsetsOfEvenSize (List.range ringSize)
  let listRes := subsets.bind fun subset =>
    let matchings := (getMatchingsList subset.length subset).filter isNonCrossingList
    matchings.bind fun m =>
      let numPairs := m.length
      let signAssigns := (getSignAssignmentsList numPairs).filter fun signs =>
        (signs.filter (!·)).length % 2 == ringSize % 2
      signAssigns.map fun signs =>
        let flatPairs := m.bind (fun (a, b) => [a, b])
        { numPairs := numPairs, pairs := Array.mk flatPairs, signs := Array.mk signs }
  Array.mk listRes

/-- The computable implementation of `computeMaxConsistentSubset`.
It computes the greatest fixed point of the reduction operator over the live colorings.
Returns the final array of live colorings. If empty, the configuration is D-reducible! -/
def getNonExtendingMask (c : Configuration) (allColorings : Array ColorList) : Array Bool :=
  strictListOfNatList (interiorNeighborOffsets c) fun offsetLists =>
    Array.mk (allColorings.toList.map (fun b => not (extendsRev offsetLists (forceNatListRev b.toList []))))

structure FastMatching where
  pairs : List (Nat × Nat × Bool)
  unmatched : List Nat

def forcePairListRev : List (Nat × Nat × Bool) → List (Nat × Nat × Bool) → List (Nat × Nat × Bool)
  | [], acc => acc
  | p :: xs, acc =>
    match p with
    | (e1, e2, sign) =>
      strictNat e1 fun e1' =>
        strictNat e2 fun e2' =>
          match sign with
          | true => forcePairListRev xs ((e1', e2', true) :: acc)
          | false => forcePairListRev xs ((e1', e2', false) :: acc)

def strictPairList (l : List (Nat × Nat × Bool)) (k : List (Nat × Nat × Bool) → α) : α :=
  match forcePairListRev (forcePairListRev l []) [] with
  | [] => k []
  | x :: xs => k (x :: xs)

def forceFastMatchingListRev : List FastMatching → List FastMatching → List FastMatching
  | [], acc => acc
  | m :: ms, acc =>
    strictPairList m.pairs fun ps =>
      strictNatList m.unmatched fun us =>
        forceFastMatchingListRev ms ({ pairs := ps, unmatched := us } :: acc)

def strictFastMatchingList (l : List FastMatching) (k : List FastMatching → α) : α :=
  match forceFastMatchingListRev (forceFastMatchingListRev l []) [] with
  | [] => k []
  | x :: xs => k (x :: xs)

def toFastMatching (ringSize : Nat) (m : SignedMatching) : FastMatching :=
  let pl := m.pairs.toList
  let sl := m.signs.toList
  let pairs := (List.range m.numPairs).map fun i =>
    (colorAt pl (2 * i), colorAt pl (2 * i + 1), sl.getD i false)
  let unmatched := (List.range ringSize).filter fun i => !pl.contains i
  { pairs := pairs, unmatched := unmatched }

def checkThetaFitFast (ecol : List Nat) (theta : Nat) (m : FastMatching) : Bool :=
  m.unmatched.all (fun u => colorAt ecol u == theta) &&
  m.pairs.all fun (e1, e2, sign) =>
    let c1 := colorAt ecol e1
    let c2 := colorAt ecol e2
    c1 != theta && c2 != theta && ((c1 == c2) == sign)

def checkEcolFitsM (ecol : List Nat) (m : FastMatching) : Bool :=
  checkThetaFitFast ecol 1 m || checkThetaFitFast ecol 2 m || checkThetaFitFast ecol 3 m

def isMatchingAlive : List (List Nat) → List Bool → FastMatching → Bool
  | [], _, _ => true
  | ecol :: ecols, ls, m =>
    match ls with
    | [] => true
    | true :: rest => isMatchingAlive ecols rest m
    | false :: rest =>
      if checkEcolFitsM ecol m then false else isMatchingAlive ecols rest m

def coloringSurvives (ecol : List Nat) (mLive : List FastMatching) : Bool :=
  (mLive.any (checkThetaFitFast ecol 1)) &&
  (mLive.any (checkThetaFitFast ecol 2)) &&
  (mLive.any (checkThetaFitFast ecol 3))

def nextMaskLoop : List (List Nat) → List Bool → List FastMatching → List Bool
  | [], _, _ => []
  | ecol :: ecols, ls, mLive =>
    match ls with
    | [] => []
    | true :: rest => coloringSurvives ecol mLive :: nextMaskLoop ecols rest mLive
    | false :: rest => false :: nextMaskLoop ecols rest mLive

def forceListRev : List α → List α → List α
  | [], acc => acc
  | x :: xs, acc => forceListRev xs (x :: acc)

def strictList (l : List α) (k : List α → β) : β :=
  match forceListRev (forceListRev l []) [] with
  | [] => k []
  | x :: xs => k (x :: xs)

def fixpoint (allEcols : List (List Nat)) : List FastMatching → Nat → List Bool → Nat → List Bool
  | _, 0, liveMask, _ => liveMask
  | matchings, fuel + 1, liveMask, liveCount =>
    strictList (matchings.filter (isMatchingAlive allEcols liveMask)) fun mLive =>
    strictBoolList (nextMaskLoop allEcols liveMask mLive) fun nextLiveMask =>
    strictNat (nextLiveMask.filter (· == true)).length fun nextLiveCount =>
      if Nat.blt nextLiveCount liveCount then
        fixpoint allEcols mLive fuel nextLiveMask nextLiveCount
      else
        liveMask

def collectFinal : List (List Nat) → List Bool → List ColorList
  | [], _ => []
  | col :: cols, ls =>
    match ls with
    | [] => []
    | true :: rest => Array.mk col :: collectFinal cols rest
    | false :: rest => collectFinal cols rest

/-- The computable implementation of `computeMaxConsistentSubset`.
It computes the greatest fixed point of the reduction operator over the live colorings.
Returns the final array of live colorings. If empty, the configuration is D-reducible! -/
def computeMaxConsistentSubset (c : Configuration) : Array ColorList :=
  let ringSize := c.ringSize
  strictListOfNatList (interiorNeighborOffsets c) fun offsetLists =>
  strictFastMatchingList ((generateBalancedSignedMatchings ringSize).toList.map (toFastMatching ringSize)) fun matchings =>
  strictListOfNatList ((generateRingColorings ringSize).toList.map Array.toList) fun allCols =>
  strictBoolList (allCols.map (fun b => not (extendsRev offsetLists (forceNatListRev b [])))) fun initialLiveMask =>
  strictListOfNatList (allCols.map (fun b => (vertexToEdgeColoring ringSize (Array.mk b)).toList)) fun allEcols =>
    strictNat (initialLiveMask.filter (· == true)).length fun initialLiveCount =>
      let finalMask := fixpoint allEcols matchings initialLiveCount initialLiveMask initialLiveCount
      Array.mk (collectFinal allCols finalMask)

/-- The final computable D-reducibility check! -/
def isComputablyDReducible (c : Configuration) : Bool :=
  (computeMaxConsistentSubset c).size == 0


end ComputableReducer
end Math
