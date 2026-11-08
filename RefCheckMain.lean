import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.Soundness.CReduce
import FourColorTheorem.Math.KernelReducer

open Math
open Math.FastReducer
open Math.Batch
open Math.Soundness

namespace ExecKernel

open FastReducer

structure StrictBox (α : Type) where
  val : α

instance {α : Type} [Inhabited α] : Inhabited (StrictBox α) where
  default := StrictBox.mk default

scoped macro "selectBool" c:term:arg onTrue:term:arg onFalse:term:arg : term =>
  `(if $c then $onTrue else $onFalse)

scoped macro "andLazy" a:term:arg b:term:arg : term =>
  `($a && $b)

scoped macro "orLazy" a:term:arg b:term:arg : term =>
  `($a || $b)

def seqNat {α : Type} (_x : Nat) (res : α) : α := res

def pow3 : Nat → Nat
  | 0 => 1
  | n + 1 => 3 * pow3 n

def binomAux : Nat → Nat → Nat → Nat → Nat
  | 0, _n, _i, acc => acc
  | k + 1, n, i, acc =>
    let nextI := i + 1
    let nextAcc := (acc * (n - i)) / nextI
    binomAux k n nextI nextAcc

def binom (n k : Nat) : Nat :=
  if n < k then 0 else binomAux k n 0 1

def repeatBlock (cell stride count : Nat) : Nat :=
  if count == 0 || cell == 0 then 0
  else if count == 1 then cell
  else
    cell * (((1 <<< (count * stride)) - 1) / ((1 <<< stride) - 1))

def getRepeatMask (count stride width : Nat) : Nat :=
  let base := (1 <<< width) - 1
  repeatBlock base stride count

def revList {α : Type} (xs : List α) : List α := xs.reverse

inductive PackStep where
  | mk (shiftDiff m0 m1 : Nat) : PackStep

def buildPackStepsRevAux : Nat → Nat → Nat → Nat → Nat → List PackStep → List PackStep
  | 0, _N, _W, _S, _b, revAcc => revAcc
  | fuel + 1, N, W, S, b, revAcc =>
    let pow2b := 1 <<< b
    if pow2b < N then
      let nextB := b + 1
      let pow2b1 := 1 <<< nextB
      let curW := pow2b * W
      let oldStep := pow2b * S
      let shiftDiff := oldStep - curW
      let numPairs := (N + (pow2b1 - 1)) >>> nextB
      let m0 := getRepeatMask numPairs (2 * oldStep) curW
      let m1 :=
        if N <= pow2b1 then
          (1 <<< (N * W)) - (1 <<< curW)
        else
          m0 <<< curW
      buildPackStepsRevAux fuel N W S nextB (PackStep.mk shiftDiff m0 m1 :: revAcc)
    else
      revAcc

def withPackSteps (N W S : Nat) (maskWhenOne : Bool) : List PackStep × List PackStep :=
  if N <= 1 then
    if maskWhenOne then
      let m0 := (1 <<< W) - 1
      ([PackStep.mk 0 m0 0], [])
    else
      ([], [])
  else
    let revSt := buildPackStepsRevAux 20 N W S 0 []
    let fwdSt := revSt.reverse
    (fwdSt, revSt)

def runPackSteps (steps : List PackStep) (X : Nat) : Nat :=
  if X == 0 then 0
  else
    steps.foldl (fun acc step =>
      match step with
      | PackStep.mk shiftDiff m0 m1 =>
        let g0 := Nat.land acc m0
        let s1 := Nat.land (acc >>> shiftDiff) m1
        Nat.lor g0 s1) X

def runUnpack (X : Nat) (revSteps : List PackStep) : Nat :=
  if X == 0 then 0
  else
    revSteps.foldl (fun acc step =>
      match step with
      | PackStep.mk shiftDiff m0 m1 =>
        let g0 := Nat.land acc m0
        let s1 := (Nat.land acc m1) <<< shiftDiff
        Nat.lor g0 s1) X

inductive PackCellSpec where
  | mk (P lowBits : Nat) (steps0 steps12 : List PackStep) : PackCellSpec

inductive UnpackCellSpec where
  | mk (P nextLowBits : Nat) (revSteps0 revSteps12 : List PackStep) : UnpackCellSpec

def packLevelRev : List PackCellSpec → List Nat → Nat → List Nat → List Nat
  | [], _D, prevS12, acc => prevS12 :: acc
  | PackCellSpec.mk P lowBits steps0 steps12 :: restSpecs, D, prevS12, acc =>
    match D with
    | [] => prevS12 :: acc
    | dk :: restD =>
      let s0_k := runPackSteps steps0 dk
      let s12_k := runPackSteps steps12 (dk >>> P)
      let nextDk := Nat.lor s0_k (prevS12 <<< lowBits)
      packLevelRev restSpecs restD s12_k (nextDk :: acc)

def packToBuckets (levels : List (List PackCellSpec)) (initD : List Nat) : List Nat :=
  levels.foldl (fun D lvlSpecs => (packLevelRev lvlSpecs D 0 []).reverse) initD

def unpackLevelRev : List UnpackCellSpec → Nat → List Nat → List Nat → List Nat
  | [], _dk, _restD, acc => acc
  | UnpackCellSpec.mk P nextLowBits revSteps0 revSteps12 :: restSpecs, dk, restD, acc =>
    let s0_k := runUnpack dk revSteps0
    match restD with
    | [] => s0_k :: acc
    | dkNext :: restD' =>
      let s12_k := runUnpack (dkNext >>> nextLowBits) revSteps12
      let prevDk := Nat.lor s0_k (s12_k <<< P)
      unpackLevelRev restSpecs dkNext restD' (prevDk :: acc)

def withUnpackFromBucketsPair {α : Type} (revLevels : List (List UnpackCellSpec)) (buckets : List Nat)
    (k : Nat → Nat → α) (defVal : α) : α :=
  let finalD :=
    revLevels.foldl (fun D lvlSpecs =>
      match D with
      | [] => []
      | d0 :: restD => (unpackLevelRev lvlSpecs d0 restD []).reverse) buckets
  match finalD with
  | [] => defVal
  | u0 :: restD =>
    match restD with
    | [] => k u0 0
    | u12 :: _ => k u0 u12

def buildLevelSpecsAux (m P P2 P3 : Nat) :
    Nat → List PackCellSpec → List UnpackCellSpec → List PackCellSpec × List UnpackCellSpec
  | 0, pAcc, uAcc => (pAcc, uAcc)
  | kIdx + 1, pAcc, uAcc =>
    let N := (binom m kIdx) * (1 <<< kIdx)
    let lowBits := N * P
    let nextLowBits :=
      if kIdx + 1 <= m then
        ((binom m (kIdx + 1)) * (1 <<< (kIdx + 1))) * P
      else 0
    let (st0, revSt0) := withPackSteps N P P3 true
    let (st12, revSt12) := withPackSteps N P2 P3 false
    let isM1K1 := m == 1 && kIdx == 1
    let rev0 := if isM1K1 then [PackStep.mk 0 ((1 <<< P) - 1) 0] else revSt0
    let rev12 := if isM1K1 then [PackStep.mk 0 ((1 <<< P2) - 1) 0] else revSt12
    buildLevelSpecsAux m P P2 P3 kIdx
      (PackCellSpec.mk P lowBits st0 st12 :: pAcc)
      (UnpackCellSpec.mk P nextLowBits rev0 rev12 :: uAcc)

def buildLevelSpecs (m P : Nat) : List PackCellSpec × List UnpackCellSpec :=
  buildLevelSpecsAux m P (2 * P) (3 * P) (m + 1) [] []

def buildAllPackUnpackLevelsAux (mMax : Nat) :
    Nat → List (List PackCellSpec) → List (List UnpackCellSpec) →
    List (List PackCellSpec) × List (List UnpackCellSpec)
  | 0, pAcc, uAcc => (pAcc, uAcc.reverse)
  | mIdx + 1, pAcc, uAcc =>
    let m := mIdx + 1
    let e := (mMax - 1) - m
    let P := pow3 e
    let (pLvl, uLvl) := buildLevelSpecs m P
    buildAllPackUnpackLevelsAux mMax mIdx (pLvl :: pAcc) (uLvl :: uAcc)

def buildAllPackUnpackLevels (mMax : Nat) : List (List PackCellSpec) × List (List UnpackCellSpec) :=
  buildAllPackUnpackLevelsAux mMax (mMax - 1) [] []

inductive ChordOp where
  | pair (dPlus dMinus mask00 mask10 : Nat) : ChordOp
  | last (dShift mask0 : Nat) : ChordOp

inductive CatalanTrie where
  | leaf : CatalanTrie
  | nil : CatalanTrie
  | leafOp : ChordOp → CatalanTrie
  | only : ChordOp → CatalanTrie → CatalanTrie
  | branch : ChordOp → CatalanTrie → CatalanTrie → CatalanTrie

instance : Inhabited CatalanTrie where
  default := CatalanTrie.nil

def mkCatalanNode (op : ChordOp) (child sib : CatalanTrie) : CatalanTrie :=
  match sib with
  | CatalanTrie.nil =>
    match child with
    | CatalanTrie.leaf => CatalanTrie.leafOp op
    | _ => CatalanTrie.only op child
  | _ => CatalanTrie.branch op child sib

def evalCatalanTrie : CatalanTrie → Nat → Nat
  | CatalanTrie.leaf, curB => curB
  | CatalanTrie.nil, _ => 0
  | CatalanTrie.leafOp op, curB =>
    match op with
    | ChordOp.pair dPlus dMinus mask00 mask10 =>
      let mPlus := Nat.land (Nat.land curB (curB >>> dPlus)) mask00
      let mMinus := Nat.land (Nat.land curB (curB >>> dMinus)) mask10
      let mBase := Nat.lor mPlus mMinus
      if mBase == 0 then 0
      else Nat.lor mBase (Nat.lor (mPlus <<< dPlus) (mMinus <<< dMinus))
    | ChordOp.last dShift mask0 =>
      let m := Nat.land (Nat.land curB (curB >>> dShift)) mask0
      if m == 0 then 0 else Nat.lor m (m <<< dShift)
  | CatalanTrie.only op child, curB =>
    match op with
    | ChordOp.pair dPlus dMinus mask00 mask10 =>
      let mPlus := Nat.land (Nat.land curB (curB >>> dPlus)) mask00
      let mMinus := Nat.land (Nat.land curB (curB >>> dMinus)) mask10
      let mBase := Nat.lor mPlus mMinus
      if mBase == 0 then 0
      else
        let mNext := Nat.lor mBase (Nat.lor (mPlus <<< dPlus) (mMinus <<< dMinus))
        evalCatalanTrie child mNext
    | ChordOp.last dShift mask0 =>
      let m := Nat.land (Nat.land curB (curB >>> dShift)) mask0
      if m == 0 then 0
      else
        let mNext := Nat.lor m (m <<< dShift)
        evalCatalanTrie child mNext
  | CatalanTrie.branch op child sib, curB =>
    let sibCov := evalCatalanTrie sib curB
    match op with
    | ChordOp.pair dPlus dMinus mask00 mask10 =>
      let mPlus := Nat.land (Nat.land curB (curB >>> dPlus)) mask00
      let mMinus := Nat.land (Nat.land curB (curB >>> dMinus)) mask10
      let mBase := Nat.lor mPlus mMinus
      if mBase == 0 then sibCov
      else
        let mNext := Nat.lor mBase (Nat.lor (mPlus <<< dPlus) (mMinus <<< dMinus))
        Nat.lor (evalCatalanTrie child mNext) sibCov
    | ChordOp.last dShift mask0 =>
      let m := Nat.land (Nat.land curB (curB >>> dShift)) mask0
      if m == 0 then sibCov
      else
        let mNext := Nat.lor m (m <<< dShift)
        Nat.lor (evalCatalanTrie child mNext) sibCov

def makeSingleBitMask0 (kBucket numBits M a : Nat) : Nat :=
  let countInCell := 1 <<< ((numBits - 1) - a)
  let width := 1 <<< a
  let stride := 1 <<< (a + 1)
  let cell := getRepeatMask countInCell stride width
  repeatBlock cell (1 <<< kBucket) M

def buildM0List (kBucket numBits M : Nat) : List (Nat × Nat) :=
  let rec go : Nat → List (Nat × Nat) → List (Nat × Nat)
    | 0, acc => acc
    | a + 1, acc => go a ((a, makeSingleBitMask0 kBucket numBits M a) :: acc)
  go numBits []

def lookupM0 (a : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (ha, m0) :: rest => if ha == a then m0 else lookupM0 a rest

mutual
def buildCatalanTrieSibLoop (twoP : Nat) (m0List : List (Nat × Nat)) (fuel : Nat)
    (lo hi bitLo m0Lo loPlus1 : Nat) (rest : List (Nat × Nat)) : Nat → CatalanTrie → CatalanTrie
  | 0, sibAcc => sibAcc
  | idx + 1, sibAcc =>
    let kIdx := loPlus1 + 2 * idx
    let kPlus1 := kIdx + 1
    let rest1 := if kPlus1 < hi then (kPlus1, hi) :: rest else rest
    let rest2 := if loPlus1 < kIdx then (loPlus1, kIdx) :: rest1 else rest1
    let childTrie := buildCatalanTrieAux twoP m0List fuel rest2
    let nextSib :=
      if kIdx == twoP - 1 then
        mkCatalanNode (ChordOp.last bitLo m0Lo) childTrie sibAcc
      else
        let m0K := lookupM0 kIdx m0List
        let m00 := Nat.land m0Lo m0K
        let m10 := m00 <<< bitLo
        let bitK := 1 <<< kIdx
        let dPlus := bitK + bitLo
        let dMinus := bitK - bitLo
        mkCatalanNode (ChordOp.pair dPlus dMinus m00 m10) childTrie sibAcc
    buildCatalanTrieSibLoop twoP m0List fuel lo hi bitLo m0Lo loPlus1 rest idx nextSib

def buildCatalanTrieAux (twoP : Nat) (m0List : List (Nat × Nat)) : Nat → List (Nat × Nat) → CatalanTrie
  | 0, _ => CatalanTrie.leaf
  | _ + 1, [] => CatalanTrie.leaf
  | fuel + 1, (lo, hi) :: rest =>
    let numSteps := (hi - lo) >>> 1
    let bitLo := 1 <<< lo
    let m0Lo := lookupM0 lo m0List
    let loPlus1 := lo + 1
    buildCatalanTrieSibLoop twoP m0List fuel lo hi bitLo m0Lo loPlus1 rest numSteps CatalanTrie.nil
end

inductive BucketCatalanSpec where
  | mk (kBucket : Nat) (isEven : Bool) (halfShift evenHalfMask evenParityMask : Nat) (trie : CatalanTrie) : BucketCatalanSpec

instance : Inhabited BucketCatalanSpec where
  default := BucketCatalanSpec.mk 0 true 0 0 0 CatalanTrie.leaf

def buildThueMorseParityAux (rMod2 : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _W, evenM, oddM => if rMod2 == 0 then evenM else oddM
  | k + 1, W, evenM, oddM =>
    let nextEven := Nat.lor evenM (oddM <<< W)
    let nextOdd := Nat.lor oddM (evenM <<< W)
    buildThueMorseParityAux rMod2 k (W <<< 1) nextEven nextOdd

def buildBucketCatalanSpec (r mMax kBucket : Nat) : BucketCatalanSpec :=
  if kBucket == 0 then
    BucketCatalanSpec.mk 0 true 0 0 0 CatalanTrie.leaf
  else
    let M := binom mMax kBucket
    let isEven := kBucket % 2 == 0
    let numBits := if isEven then kBucket - 1 else kBucket
    let twoP := if isEven then kBucket else kBucket + 1
    let halfShift := if isEven then 1 <<< (kBucket - 1) else 0
    let eh :=
      if isEven then
        let hCell := (1 <<< (1 <<< (kBucket - 1))) - 1
        repeatBlock hCell (1 <<< kBucket) M
      else 0
    let ep :=
      if isEven then
        let pCell := buildThueMorseParityAux (r % 2) kBucket 1 1 0
        repeatBlock pCell (1 <<< kBucket) M
      else 0
    let m0List := buildM0List kBucket numBits M
    let trie := buildCatalanTrieAux twoP m0List 20 [(0, twoP)]
    BucketCatalanSpec.mk kBucket isEven halfShift eh ep trie

def buildAllBucketSpecs (r mMax : Nat) : List BucketCatalanSpec :=
  let rec go : Nat → List BucketCatalanSpec → List BucketCatalanSpec
    | 0, acc => acc
    | kIdx + 1, acc => go kIdx (buildBucketCatalanSpec r mMax kIdx :: acc)
  go r []

def evalBucketCatalan (bSpec : BucketCatalanSpec) (B : Nat) : Nat :=
  match bSpec with
  | BucketCatalanSpec.mk kBucket isEven halfShift evenHalfMask evenParityMask trie =>
    if kBucket == 0 || B == 0 then B
    else
      let workB :=
        if isEven then
          Nat.lor (Nat.land B evenHalfMask) (Nat.land (B >>> halfShift) evenHalfMask)
        else B
      if workB == 0 then 0
      else
        let cov := evalCatalanTrie trie workB
        if isEven then
          Nat.land (Nat.lor cov (cov <<< halfShift)) evenParityMask
        else cov

def evalAllBuckets : List BucketCatalanSpec → List Nat → List Nat
  | [], _ => []
  | _, [] => []
  | bSpec :: restSpecs, B :: restB =>
    evalBucketCatalan bSpec B :: evalAllBuckets restSpecs restB

inductive SwapStep where
  | mk (P P2 m0 m1 m2 : Nat) : SwapStep

def buildSwapSteps (nDigits : Nat) : List SwapStep :=
  let rec go : Nat → List SwapStep → List SwapStep
    | 0, acc => acc
    | e + 1, acc =>
      let P := pow3 e
      let P2 := 2 * P
      let count := pow3 ((nDigits - 1) - e)
      let m0 := getRepeatMask count (3 * P) P
      let m1 := m0 <<< P
      let m2 := m0 <<< P2
      go e (SwapStep.mk P P2 m0 m1 m2 :: acc)
  go nDigits []

def swapDigits01 (steps : List SwapStep) (X : Nat) : Nat :=
  if X == 0 then 0
  else
    steps.foldl (fun acc step =>
      match step with
      | SwapStep.mk P _ m0 _ m2 =>
        let g01 := (Nat.land acc m0) <<< P
        let g10 := Nat.land (acc >>> P) m0
        let g22 := Nat.land acc m2
        Nat.lor g22 (Nat.lor g10 g01)) X

def swapDigits02 (steps : List SwapStep) (X : Nat) : Nat :=
  if X == 0 then 0
  else
    steps.foldl (fun acc step =>
      match step with
      | SwapStep.mk _ P2 m0 m1 _ =>
        let g02 := (Nat.land acc m0) <<< P2
        let g20 := Nat.land (acc >>> P2) m0
        let g11 := Nat.land acc m1
        Nat.lor g11 (Nat.lor g20 g02)) X

def swapDigits12 (steps : List SwapStep) (X : Nat) : Nat :=
  if X == 0 then 0
  else
    steps.foldl (fun acc step =>
      match step with
      | SwapStep.mk P _ m0 m1 _ =>
        let g00 := Nat.land acc m0
        let g12 := (Nat.land acc m1) <<< P
        let g21 := Nat.land (acc >>> P) m1
        Nat.lor g00 (Nat.lor g21 g12)) X

inductive RingColMasks where
  | mk (u c0 c1 c2 c3 : Nat) : RingColMasks

inductive IntVertexStep where
  | mk (bitV reqMask checkMask f0 f1 f2 f3 : Nat) : IntVertexStep

def stepRow8 (P P2 v00 v01 v10 v11 v20 v21 v30 v31 : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let s01_1 := v01 <<< P
  let s11_1 := v11 <<< P
  let s21_1 := v21 <<< P
  let s31_1 := v31 <<< P
  let s01_2 := v01 <<< P2
  let s11_2 := v11 <<< P2
  let s21_2 := v21 <<< P2
  let s31_2 := v31 <<< P2
  let n00 := Nat.lor v10 s21_1
  let n01 := Nat.lor v11 (Nat.lor s21_1 s31_2)
  let n10 := Nat.lor v00 s31_1
  let n11 := Nat.lor v01 (Nat.lor s31_1 s21_2)
  let n20 := Nat.lor v30 s01_1
  let n21 := Nat.lor v31 (Nat.lor s01_1 s11_2)
  let n30 := Nat.lor v20 s11_1
  let n31 := Nat.lor v21 (Nat.lor s11_1 s01_2)
  (n00, n01, n10, n11, n20, n21, n30, n31)

def buildRingColLoop (mMax : Nat) :
    Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    Nat × Nat × List RingColMasks
  | 0, _u, P, x1_00, _, _, _, x1_20, _, x1_30, _ =>
    let canonValid := Nat.lor x1_00 (Nat.lor x1_30 x1_20)
    let totalMask := (1 <<< P) - 1
    (canonValid, totalMask,
      [RingColMasks.mk 0 0 canonValid 0 0,
       RingColMasks.mk (mMax - 1) 0 x1_00 x1_30 x1_20,
       RingColMasks.mk mMax x1_00 0 x1_20 x1_30])
  | steps + 1, u, P, x1_00, x1_01, x1_10, x1_11, x1_20, x1_21, x1_30, x1_31 =>
    let P2 := 2 * P
    let nextP := 3 * P
    let nextU := u + 1
    let (n1_00, n1_01, n1_10, n1_11, n1_20, n1_21, n1_30, n1_31) :=
      stepRow8 P P2 x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31
    let (canonValid, totalMask, rest) :=
      buildRingColLoop mMax steps nextU nextP n1_00 n1_01 n1_10 n1_11 n1_20 n1_21 n1_30 n1_31
    let repFactor := totalMask / ((1 <<< P) - 1)
    let c0_u := Nat.land canonValid (x1_11 * repFactor)
    let c1_u := Nat.land canonValid (x1_01 * repFactor)
    let c2_u := Nat.land canonValid (x1_31 * repFactor)
    let c3_u := Nat.land canonValid (x1_21 * repFactor)
    (canonValid, totalMask, RingColMasks.mk (u - 1) c0_u c1_u c2_u c3_u :: rest)

def withRingColMasks (mMax : Nat) : Nat × List RingColMasks :=
  let nSteps := mMax - 2
  let (x1_00, x1_01, x1_10, x1_11, x1_20, x1_21, x1_30, x1_31) :=
    stepRow8 1 2 1 1 0 0 0 0 0 0
  let (canonValid, _totalMask, rings) :=
    buildRingColLoop mMax nSteps 2 3 x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31
  (canonValid, rings)

def lookupRingCols (u : Nat) : List RingColMasks → Nat × Nat × Nat × Nat
  | [] => (0, 0, 0, 0)
  | RingColMasks.mk hu c0 c1 c2 c3 :: rest =>
    if hu == u then (c0, c1, c2, c3) else lookupRingCols u rest

def buildIntForbidAux (r : Nat) (rings : List RingColMasks) (us : List Nat) :
    Nat × Nat × Nat × Nat × Nat :=
  us.foldl (fun (intMask, u0, u1, u2, u3) u =>
    if r <= u then
      (Nat.lor intMask (1 <<< u), u0, u1, u2, u3)
    else
      let (c0, c1, c2, c3) := lookupRingCols u rings
      (intMask, Nat.lor u0 c0, Nat.lor u1 c1, Nat.lor u2 c2, Nat.lor u3 c3))
    (0, 0, 0, 0, 0)

def withIntStepsD (r canonValid : Nat) (rings : List RingColMasks) (rows : List (Array Nat)) :
    List IntVertexStep :=
  let rec go : List (Array Nat) → Nat → List IntVertexStep
    | [], _ => []
    | row :: rest, v =>
      let nextV := v + 1
      if r <= v then
        let bitV := 1 <<< v
        let (intMask, u0, u1, u2, u3) := buildIntForbidAux r rings row.toList
        let f0 := Nat.xor canonValid u0
        let f1 := Nat.xor canonValid u1
        let f2 := Nat.xor canonValid u2
        let f3 := Nat.xor canonValid u3
        IntVertexStep.mk bitV 0 intMask f0 f1 f2 f3 :: go rest nextV
      else
        go rest nextV
  go rows 0

def dfsInterior : List IntVertexStep → Nat → Nat → Nat → Nat → Nat → Nat → Nat
  | [], _c0, _c1, _c2, _c3, compat, remCanon => Nat.xor remCanon compat
  | IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: rest, c0, c1, c2, c3, compat, rem0 =>
    let r1 :=
      if Nat.land c0 checkMask == reqMask then
        let next0 := Nat.land compat f0
        if next0 == 0 then rem0 else dfsInterior rest (Nat.lor c0 bitV) c1 c2 c3 next0 rem0
      else rem0
    let r2 :=
      if Nat.land c1 checkMask == reqMask then
        let next1 := Nat.land (Nat.land compat r1) f1
        if next1 == 0 then r1 else dfsInterior rest c0 (Nat.lor c1 bitV) c2 c3 next1 r1
      else r1
    let r3 :=
      if Nat.land c2 checkMask == reqMask then
        let next2 := Nat.land (Nat.land compat r2) f2
        if next2 == 0 then r2 else dfsInterior rest c0 c1 (Nat.lor c2 bitV) c3 next2 r2
      else r2
    if Nat.land c3 checkMask == reqMask then
      let next3 := Nat.land (Nat.land compat r3) f3
      if next3 == 0 then r3 else dfsInterior rest c0 c1 c2 (Nat.lor c3 bitV) next3 r3
    else r3

def getAlias (v : Nat) : List (Nat × Nat) → Nat
  | [] => v
  | (k, val) :: rest => if k == v then val else getAlias v rest

def setAliasMin (k mn : Nat) (alias : List (Nat × Nat)) : List (Nat × Nat) :=
  if mn < getAlias k alias then (k, mn) :: alias else alias

def relaxContractEdges (edges : List (Nat × Nat)) (al : List (Nat × Nat)) : List (Nat × Nat) :=
  edges.foldl (fun acc (u, v) =>
    let ru := getAlias u acc
    let rv := getAlias v acc
    let mn := if ru <= rv then ru else rv
    let al1 := setAliasMin rv mn acc
    let al2 := setAliasMin ru mn al1
    let al3 := setAliasMin v mn al2
    setAliasMin u mn al3) al

def buildAlias (edges : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec go : Nat → List (Nat × Nat) → List (Nat × Nat)
    | 0, al => al
    | k + 1, al => go k (relaxContractEdges edges al)
  go 4 []

def sameRingColMask (u v : Nat) (rings : List RingColMasks) : Nat :=
  let (uc0, uc1, uc2, uc3) := lookupRingCols u rings
  let (vc0, vc1, vc2, vc3) := lookupRingCols v rings
  let m0 := Nat.land uc0 vc0
  let m1 := Nat.land uc1 vc1
  let m2 := Nat.land uc2 vc2
  let m3 := Nat.land uc3 vc3
  Nat.lor (Nat.lor m0 m1) (Nat.lor m2 m3)

def filterRingContractNbrs (v rv canonValid : Nat) (alias : List (Nat × Nat))
    (rings : List RingColMasks) (us : List Nat) (compat : Nat) : Nat :=
  us.foldl (fun acc u =>
    let ru := getAlias u alias
    if ru == rv then 0
    else
      let sameVU := sameRingColMask v u rings
      let diffVU := Nat.xor canonValid sameVU
      Nat.land acc diffVU) compat

def buildContractIntForbidAux (r rv canonValid : Nat)
    (alias : List (Nat × Nat)) (rings : List RingColMasks) (us : List Nat)
    (initF0 initF1 initF2 initF3 : Nat) : Nat × Nat × Nat × Nat × Nat :=
  us.foldl (fun (intDiff, f0, f1, f2, f3) u =>
    let ru := getAlias u alias
    if ru == rv then (intDiff, f0, f1, f2, f3)
    else if r <= u then (Nat.lor intDiff (1 <<< u), f0, f1, f2, f3)
    else
      let (uc0, uc1, uc2, uc3) := lookupRingCols u rings
      (intDiff,
       Nat.land f0 (Nat.xor canonValid uc0),
       Nat.land f1 (Nat.xor canonValid uc1),
       Nat.land f2 (Nat.xor canonValid uc2),
       Nat.land f3 (Nat.xor canonValid uc3)))
    (0, initF0, initF1, initF2, initF3)

def withContractStepsC (r canonValid initCompat : Nat)
    (alias : List (Nat × Nat)) (rings : List RingColMasks) (rows : List (Array Nat)) :
    Nat × List IntVertexStep :=
  let rec go : List (Array Nat) → Nat → Nat → Nat × List IntVertexStep
    | [], _, compat => (compat, [])
    | row :: rest, v, compat =>
      let nextV := v + 1
      let rv := getAlias v alias
      if v < r then
        let compat1 := if rv < v then Nat.land compat (sameRingColMask v rv rings) else compat
        let compat2 := filterRingContractNbrs v rv canonValid alias rings row.toList compat1
        go rest nextV compat2
      else
        let bitV := 1 <<< v
        let reqMask := if r <= rv && rv < v then 1 <<< rv else 0
        let (i0, i1, i2, i3) :=
          if rv < r then lookupRingCols rv rings
          else (canonValid, canonValid, canonValid, canonValid)
        let (intDiff, f0, f1, f2, f3) :=
          buildContractIntForbidAux r rv canonValid alias rings row.toList i0 i1 i2 i3
        let checkMask := Nat.lor reqMask intDiff
        let (finalCompat, stepsRest) := go rest nextV compat
        (finalCompat, IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: stepsRest)
  go rows 0 initCompat

def computeInitialLiveDWithRings (rVal canonValid : Nat) (rings : List RingColMasks)
    (swapSteps1 : List SwapStep) (c : RConf) : Nat :=
  let intSteps := withIntStepsD rVal canonValid rings c.earlier.toList
  let canonLive := dfsInterior intSteps 0 0 0 0 canonValid canonValid
  let s12 := swapDigits12 swapSteps1 canonLive
  Nat.lor canonLive s12

def computeContractCanonWithRings (rVal canonValid : Nat) (rings : List RingColMasks) (c : RConf) : Nat :=
  let al := buildAlias c.contractEdges.toList
  let (ringCompat, intStepsC) := withContractStepsC rVal canonValid canonValid al rings c.earlier.toList
  let unextContract := dfsInterior intStepsC 0 0 0 0 ringCompat ringCompat
  Nat.xor ringCompat unextContract

def kempeRound
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (L2 : Nat) : Nat :=
  let l2_01 := swapDigits01 swapSteps1 L2
  let l2_02 := swapDigits02 swapSteps1 L2
  let d0_1 := Nat.lor l2_01 (l2_02 <<< pTop)
  let buckets := packToBuckets packLevels [L2, d0_1]
  let covBuckets := evalAllBuckets bucketSpecs buckets
  withUnpackFromBucketsPair unpackRevLevels covBuckets
    (fun u0 u1 =>
      let m0 := Nat.land L2 u0
      if m0 == 0 then 0
      else
        let w1 := swapDigits01 swapSteps1 u1
        let m1 := Nat.land m0 w1
        if m1 == 0 then 0
        else Nat.land m1 (swapDigits12 swapSteps1 m1))
    0

structure KempeEngine where
  pTop : Nat
  swapSteps1 : List SwapStep
  packLevels : List (List PackCellSpec)
  unpackRevLevels : List (List UnpackCellSpec)
  bucketSpecs : List BucketCatalanSpec
  deriving Inhabited

def buildKempeEngine (rVal : Nat) : KempeEngine :=
  let mMaxVal := rVal - 1
  let mMax1 := mMaxVal - 1
  let pTop := pow3 mMax1
  let swapSteps1 := buildSwapSteps mMax1
  let (packLevels, unpackRevLevels) := buildAllPackUnpackLevels mMaxVal
  let bucketSpecs := buildAllBucketSpecs rVal mMaxVal
  { pTop := pTop, swapSteps1 := swapSteps1, packLevels := packLevels,
    unpackRevLevels := unpackRevLevels, bucketSpecs := bucketSpecs }

def stepEngineOne (ke : KempeEngine) (L2 : Nat) : Nat :=
  kempeRound ke.pTop ke.swapSteps1 ke.packLevels ke.unpackRevLevels ke.bucketSpecs L2

end ExecKernel

/-- `checkFastTotal` is definitionally `(computeFinalState rc sms pow3).orbits.isEmpty`,
    so `refcheck` computes `st := computeFinalState rc sms pow3` once and reads `st.orbits.isEmpty`. -/
theorem checkFastTotal_eq_finalState_isEmpty (rc : RConf) (sms : Array SMData) (pow3 : Array Nat) :
    checkFastTotal rc sms pow3 = (computeFinalState rc sms pow3).orbits.isEmpty := rfl

structure DiffResult where
  idx : Nat
  r : Nat
  expectedD : Bool
  dTotal : Bool
  cTotal : Bool
  dRef : Bool
  cRef : Bool
  itersTotal : Nat
  liveOrbits : Nat
  msTotal : Nat
  msRef : Nat

structure PrecomputedRingEngine where
  r : Nat
  canonValid : Nat
  rings : List ExecKernel.RingColMasks
  swapSteps1 : List ExecKernel.SwapStep
  ke : ExecKernel.KempeEngine
  deriving Inhabited

structure KernelTraceResult where
  idx : Nat
  r : Nat
  expectedD : Bool
  dOk : Bool
  cOk : Bool
  dRound : Option Nat
  cRound : Option Nat
  fixpointRound : Nat
  trace : Array Nat
  ms : Nat
  deriving Inhabited

def natToHex (n : Nat) : String :=
  if n == 0 then "0x0"
  else "0x" ++ String.ofList (Nat.toDigits 16 n)

def runKernelTrace (pre : PrecomputedRingEngine) (idx : Nat) (c : RConf) : KernelTraceResult :=
  let r := pre.r
  let expectedD := c.contract == 0
  let live0 := ExecKernel.computeInitialLiveDWithRings r pre.canonValid pre.rings pre.swapSteps1 c
  let cc := if expectedD then 0 else ExecKernel.computeContractCanonWithRings r pre.canonValid pre.rings c
  let rec loop (fuel round L2 : Nat) (dRound cRound : Option Nat) (acc : Array Nat) :
      Option Nat × Option Nat × Nat × Array Nat :=
    let acc' := acc.push L2
    let dRound' := match dRound with | some _ => dRound | none => if L2 == 0 then some round else none
    let cRound' :=
      if expectedD then none
      else match cRound with | some _ => cRound | none => if Nat.land L2 cc == 0 then some round else none
    match fuel with
    | 0 => (dRound', cRound', round, acc')
    | fuel' + 1 =>
      if L2 == 0 then
        (dRound', cRound', round, acc')
      else
        let nextL2 := ExecKernel.stepEngineOne pre.ke L2
        if nextL2 == L2 then
          (dRound', cRound', round, acc')
        else
          loop fuel' (round + 1) nextL2 dRound' cRound' acc'
  let (dRound, cRound, fixRound, trace) := loop 120 0 live0 none none #[]
  {
    idx := idx
    r := r
    expectedD := expectedD
    dOk := dRound.isSome
    cOk := if expectedD then dRound.isSome else cRound.isSome
    dRound := dRound
    cRound := cRound
    fixpointRound := fixRound
    trace := trace
    ms := 0
  }

def buildCheckpointList (chunk stopAt : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _cur, acc => acc.reverse
  | fuel + 1, cur, acc =>
    if cur >= stopAt then
      (stopAt :: acc).reverse
    else
      buildCheckpointList chunk stopAt fuel (cur + chunk) (cur :: acc)

def buildCheckpointListStrict (chunk stopBefore : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _cur, acc => acc.reverse
  | fuel + 1, cur, acc =>
    if cur >= stopBefore then
      acc.reverse
    else
      buildCheckpointListStrict chunk stopBefore fuel (cur + chunk) (cur :: acc)

/-- Compute checkpoint round numbers `0 < t_1 < t_2 < ... < t_m <= T` for step-splitting.
    Returns `[]` when a single `by kernel_rfl` suffices. -/
def chooseCheckpoints (r : Nat) (expectedD : Bool) (targetRound : Nat) : List Nat :=
  if r <= 12 then
    []
  else if r == 13 then
    if expectedD || targetRound <= 5 then []
    else
      buildCheckpointList 4 (targetRound - 1) 40 4 []
  else
    -- r == 14: keep every `kernel_rfl` step <= 2 rounds (and final C-step <= 1 round)
    if expectedD then
      if targetRound <= 1 then []
      else
        buildCheckpointListStrict 2 targetRound 70 2 []
    else
      if targetRound == 0 then []
      else if targetRound == 1 then [1]
      else
        buildCheckpointList 2 (targetRound - 1) 70 2 []

def buildTailExpr (midFn : String) (idx m : Nat) (ptsArr : Array Nat) (k : Nat) : String :=
  if _h : k + 1 < m then
    let sk1 := ptsArr[k + 1]! - ptsArr[k]!
    let remk1 := 120 - ptsArr[k + 1]!
    let inner := buildTailExpr midFn idx m ptsArr (k + 1)
    let indent := String.ofList (List.replicate (4 + 2 * k) ' ')
    s!"\n{indent}(KernelReducer.{midFn} {idx} {sk1} {remk1} mid_{idx}_{k + 1} mid_{idx}_{k + 2} cert_config_{idx}_step{k + 2}{inner})"
  else
    s!" cert_config_{idx}_step{m + 1}"
termination_by m - k

/-- Format the Lean declaration(s) for configuration `idx` from its `KernelTraceResult`. -/
def renderConfigCertBlock (ktr : KernelTraceResult) : String := Id.run do
  let idx := ktr.idx
  let r := ktr.r
  let expectedD := ktr.expectedD
  let checkFn :=
    if expectedD then
      if r == 14 then "checkIdxFast14" else if r == 13 then "checkIdxFast13" else "checkIdxFast"
    else
      if r == 14 then "checkIdxCFast14" else if r == 13 then "checkIdxCFast13" else "checkIdxCFast"
  let suffix := if expectedD then "d_red" else "c_red"
  let thmName := s!"cert_config_{idx}_{suffix}"
  let thmType := s!"{checkFn} (buildSMData {r} sharedPow3) {idx} = true"
  let targetRound := (if expectedD then ktr.dRound else ktr.cRound).getD 0
  let pts := chooseCheckpoints r expectedD targetRound
  match pts with
  | [] =>
    return s!"theorem {thmName} : {thmType} := by kernel_rfl\n"
  | _ =>
    let ptsArr := pts.toArray
    let m := ptsArr.size
    let mut lines : Array String := #[]
    for k in [0:m] do
      let t := ptsArr[k]!
      let mask := ktr.trace[t]!
      lines := lines.push s!"def mid_{idx}_{k + 1} : Nat := {natToHex mask}"
    let s1 := ptsArr[0]!
    lines := lines.push s!"theorem cert_config_{idx}_step1 : KernelReducer.checkStepInit {idx} {s1} mid_{idx}_1 = true := by kernel_rfl"
    for k in [1:m] do
      let sk := ptsArr[k]! - ptsArr[k - 1]!
      lines := lines.push s!"theorem cert_config_{idx}_step{k + 1} : KernelReducer.checkStepMid {idx} {sk} mid_{idx}_{k} mid_{idx}_{k + 1} = true := by kernel_rfl"
    let remLast := 120 - ptsArr[m - 1]!
    let finalFn := if expectedD then "checkStepFinalD" else "checkStepFinalC"
    lines := lines.push s!"theorem cert_config_{idx}_step{m + 1} : KernelReducer.{finalFn} {idx} {remLast} mid_{idx}_{m} = true := by kernel_rfl"
    let splitFn := if expectedD then "verifyIdxD_of_split2" else "verifyIdxC_of_split2"
    let midFn := if expectedD then "checkStepFinalD_of_mid" else "checkStepFinalC_of_mid"
    let tailStr := buildTailExpr midFn idx m ptsArr 0
    let rem1 := 120 - s1
    lines := lines.push s!"theorem {thmName} : {thmType} :=\n  KernelReducer.{splitFn} {idx} {s1} {rem1} mid_{idx}_1 rfl cert_config_{idx}_step1{tailStr}\n"
    return String.intercalate "\n" lines.toList

/-- Parse `[i1, i2, ...]` from a line like `  [202, 206, 212]`. -/
def parseIndicesLine (s : String) : List Nat :=
  let cleaned := s.replace "[" " " |>.replace "]" " " |>.replace "," " "
  (cleaned.splitOn " ").filterMap (fun tok => tok.toNat?)

/-- Update all batch files in `FourColorTheorem/Math/Batch` that need regeneration. -/
def regenerateBatchCerts (results : Array KernelTraceResult) (onlyIndices : List Nat := []) : IO Unit := do
  let batchDir : System.FilePath := "FourColorTheorem/Math/Batch"
  let entries ← batchDir.readDir
  let mut updatedCount := 0
  for entry in entries do
    let fname := entry.fileName
    let isDBatch := fname.startsWith "Batch" && fname.endsWith ".lean" && fname != "Batch01_R6to9.lean"
    let isCBatch := fname.startsWith "CBatch" && fname.endsWith ".lean"
    if isDBatch || isCBatch then
      let content ← IO.FS.readFile entry.path
      let rawLines := (content.replace "\r\n" "\n").splitOn "\n"
      let linesArr := rawLines.toArray
      let mut defIdx? : Option Nat := none
      let mut footerIdx? : Option Nat := none
      for li in [0:linesArr.size] do
        let ln := linesArr[li]!
        if (ln.startsWith "def batch" || ln.startsWith "def cbatch") && defIdx?.isNone then
          defIdx? := some li
        if (ln.startsWith "theorem cert_batch" || ln.startsWith "theorem cert_cbatch") && footerIdx?.isNone then
          footerIdx? := some li
      match defIdx?, footerIdx? with
      | some defLi, some footLi =>
        let indicesLine := linesArr[defLi + 1]!
        let indices := parseIndicesLine indicesLine
        let allPresent := onlyIndices.isEmpty || indices.all (fun idx => onlyIndices.contains idx)
        if allPresent then
          let needsSplit := indices.any (fun idx =>
            let ktr := results[idx]!
            !(chooseCheckpoints ktr.r ktr.expectedD ((if ktr.expectedD then ktr.dRound else ktr.cRound).getD 0)).isEmpty)
          let isR14DBatch := isDBatch && indices.any (fun idx => results[idx]!.r == 14)
          if isCBatch || isR14DBatch || needsSplit then
            let headerLines := (linesArr.extract 0 (defLi + 2)).toList
            let footerLines := (linesArr.extract footLi linesArr.size).toList
            let blocks := indices.map (fun idx => renderConfigCertBlock results[idx]!)
            let newContent :=
              String.intercalate "\n" headerLines ++ "\n\n" ++
              String.intercalate "\n" blocks ++ "\n" ++
              String.intercalate "\n" footerLines
            if newContent != content.replace "\r\n" "\n" then
              IO.FS.writeFile entry.path newContent
              updatedCount := updatedCount + 1
              IO.println s!"Updated {fname} (indices: {indices})"
      | _, _ => pure ()
  IO.println s!"Certificate regeneration complete: {updatedCount} batch files updated."

def runKernelCheckMode (minRing maxRing : Nat) (genCerts : Bool) (onlyIndices : List Nat := []) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let out ← IO.getStdout
  IO.println s!"--- Stage K2 KernelReducer Verification (minRing = {minRing}, maxRing = {maxRing}, genCerts = {genCerts}) ---"
  let mut preEngines : Array PrecomputedRingEngine := #[]
  for r in [0:15] do
    let rNeeded := onlyIndices.isEmpty || onlyIndices.any (fun idx => sharedCfgs[idx]!.r == r)
    if r < 6 || r < minRing || r > maxRing || !rNeeded then
      preEngines := preEngines.push default
    else
      let ts0 ← IO.monoMsNow
      let mMaxVal := r - 1
      let mMax1 := mMaxVal - 1
      let (canonValid, rings) := ExecKernel.withRingColMasks mMaxVal
      let swapSteps1 := ExecKernel.buildSwapSteps mMax1
      let ke := ExecKernel.buildKempeEngine r
      preEngines := preEngines.push {
        r := r, canonValid := canonValid, rings := rings, swapSteps1 := swapSteps1, ke := ke
      }
      IO.println s!"Precomputed KernelReducer engine for r={r} in {(← IO.monoMsNow) - ts0} ms."
      out.flush

  let totalCfgs := sharedCfgs.size
  let order := ((List.range totalCfgs).toArray.filter
    (fun i => minRing ≤ sharedCfgs[i]!.r && sharedCfgs[i]!.r ≤ maxRing &&
      (onlyIndices.isEmpty || onlyIndices.contains i))).qsort
    (fun i j => sharedCfgs[i]!.r > sharedCfgs[j]!.r || (sharedCfgs[i]!.r == sharedCfgs[j]!.r && i < j))
  let total := order.size
  let done ← IO.mkRef 0
  let mut tasks : Array (Nat × Task (Except IO.Error KernelTraceResult)) := #[]

  for i in order do
    let cfg := sharedCfgs[i]!
    let c := theUnavoidableSet[i]!
    let rc := rconfOfConfig c cfg.earlier
    let pre := preEngines[rc.r]!
    let t ← IO.asTask do
      let ts0 ← IO.monoMsNow
      let res := runKernelTrace pre i rc
      let ok := if res.expectedD then res.dOk else (res.cOk && !res.dOk)
      let ts1 ← IO.monoMsNow
      let res := { res with ms := ts1 - ts0 }
      let k ← done.modifyGet (fun k => (k + 1, k + 1))
      let status := if ok then "OK" else "*** MISMATCH ***"
      IO.println s!"[{k}/{total}] Config {i} (r={rc.r}): {status} | expectedD={res.expectedD} dOk={res.dOk} cOk={res.cOk} | dRound={res.dRound} cRound={res.cRound} fixRound={res.fixpointRound} | {res.ms} ms"
      (← IO.getStdout).flush
      return res
    tasks := tasks.push (i, t)

  let mut allResults : Array KernelTraceResult := (List.replicate totalCfgs default).toArray
  let mut dCount := 0
  let mut dPass := 0
  let mut cCount := 0
  let mut cPass := 0
  let mut cFalseD := 0
  let mut mismatches : Array Nat := #[]
  let mut maxDRound := 0
  let mut maxCRound := 0

  for (i, t) in tasks do
    match ← IO.wait t with
    | .ok r =>
      allResults := allResults.set! i r
      if r.expectedD then
        dCount := dCount + 1
        if r.dOk then
          dPass := dPass + 1
          let dr := r.dRound.getD 0
          if dr > maxDRound then maxDRound := dr
        else
          mismatches := mismatches.push i
      else
        cCount := cCount + 1
        if r.dOk then cFalseD := cFalseD + 1
        if r.cOk && !r.dOk then
          cPass := cPass + 1
          let cr := r.cRound.getD 0
          if cr > maxCRound then maxCRound := cr
        else
          mismatches := mismatches.push i
    | .error e =>
      mismatches := mismatches.push i
      IO.println s!"Error on config {i}: {e}"

  IO.println "\n--- Stage K2 KernelReducer Summary ---"
  IO.println s!"Configurations checked: {total}"
  IO.println s!"D-configurations (`verifyIdxD == true`): {dPass}/{dCount} (max rounds: {maxDRound})"
  IO.println s!"C-configurations (`verifyIdxC == true && verifyIdxDFast == false`): {cPass}/{cCount} (false D-reducible: {cFalseD}, max rounds: {maxCRound})"
  IO.println s!"Mismatches: {mismatches.size} {mismatches.toList}"
  IO.println s!"Total wall time: {((← IO.monoMsNow) - t0) / 1000}s"

  if genCerts && mismatches.isEmpty && ((minRing <= 6 && maxRing >= 14) || !onlyIndices.isEmpty) then
    regenerateBatchCerts allResults onlyIndices

  return (if mismatches.isEmpty then 0 else 1)

def main (args : List String) : IO UInt32 := do
  let posArgs := args.filter (fun s => !s.startsWith "--")
  let maxRing := (posArgs[0]? >>= String.toNat?).getD 14
  let minRing := (posArgs[1]? >>= String.toNat?).getD 2
  let proofOnly := args.contains "--proof-only"
  let kernelCheck := args.contains "--kernel-check"
  let genCerts := args.contains "--gen-certs"
  let onlyArg := (args.find? (fun s => s.startsWith "--only=")).map (fun s => (s.drop 7).toString)
  let onlyIndices := match onlyArg with
    | some s => (s.splitOn ",").filterMap String.toNat?
    | none => []
  if kernelCheck || genCerts then
    return (← runKernelCheckMode minRing maxRing genCerts onlyIndices)

  let out ← IO.getStdout
  IO.println s!"--- Stage K0.7 Differential Checker (minRing = {minRing}, maxRing = {maxRing}, proofOnly = {proofOnly}) ---"
  let configs := loadAll ()
  let pow3 := sharedPow3
  let t0 ← IO.monoMsNow

  -- Verify `loadAll ()` matches `sharedCfgs` field-by-field
  let mut cfgDiffs : Array Nat := #[]
  for i in [0:configs.size] do
    let a := configs[i]!
    let b := sharedCfgs[i]!
    let ok := a.r == b.r && a.n == b.n && a.contract == b.contract &&
              a.X == b.X && a.earlier == b.earlier && a.contractEdges == b.contractEdges &&
              a.adj == b.adj
    if !ok then cfgDiffs := cfgDiffs.push i
  IO.println s!"Config table check (`loadAll ()` == `sharedCfgs`): {configs.size - cfgDiffs.size}/{configs.size} match (diffs: {cfgDiffs.toList})"

  -- Build `SMData` tables (proof target) and optionally `MData` tables (`FastReducer.check`)
  let mut smTables : Array (Array SMData) := #[]
  let mut mTables : Array (Array MData × Nat) := #[]
  for r in [0:15] do
    if r < 2 || r < minRing || r > maxRing then
      smTables := smTables.push #[]
      mTables := mTables.push (#[], 0)
    else
      smTables := smTables.push (buildSMData r pow3)
      mTables := mTables.push (if proofOnly then (#[], 0) else buildMData r pow3)
  IO.println s!"Matching tables built in {(← IO.monoMsNow) - t0} ms."
  out.flush

  let order := ((List.range configs.size).toArray.filter
    (fun i => minRing ≤ configs[i]!.r && configs[i]!.r ≤ maxRing)).qsort
    (fun i j => configs[i]!.r > configs[j]!.r || (configs[i]!.r == configs[j]!.r && i < j))
  let total := order.size
  let done ← IO.mkRef 0
  let mut tasks : Array (Nat × Task (Except IO.Error DiffResult)) := #[]

  for i in order do
    let cfg := sharedCfgs[i]!
    let c := theUnavoidableSet[i]!
    let rc := rconfOfConfig c cfg.earlier
    let sms := smTables[rc.r]!
    let md := mTables[rc.r]!
    let t ← IO.asTask do
      let ts0 ← IO.monoMsNow
      let st := computeFinalState rc sms pow3
      let dTotal := st.orbits.isEmpty
      let cTotal := if dTotal then false else runContractCheckTotal rc pow3 st.live
      let ts1 ← IO.monoMsNow
      let (dRef, cRef) :=
        if proofOnly then
          (cfg.contract == 0, cfg.contract != 0)
        else
          let res := check configs[i]! md pow3
          (res.dReducible, res.cReducible)
      let ts2 ← IO.monoMsNow
      let k ← done.modifyGet (fun k => (k + 1, k + 1))
      let expectedD := cfg.contract == 0
      let dMatch := dTotal == dRef && dTotal == expectedD && dTotal == st.orbits.isEmpty
      let cMatch := if expectedD then true else (cTotal == cRef && cTotal == true)
      let status := if dMatch && cMatch then "OK" else "*** MISMATCH ***"
      IO.println s!"[{k}/{total}] Config {i} (r={rc.r}): {status} | dTotal={dTotal} cTotal={cTotal} dRef={dRef} cRef={cRef} | remOrbits={st.orbits.size} iters={st.iter} | totalMs={ts1 - ts0} refMs={ts2 - ts1}"
      (← IO.getStdout).flush
      return {
        idx := i, r := rc.r, expectedD := expectedD,
        dTotal := dTotal, cTotal := cTotal, dRef := dRef, cRef := cRef,
        itersTotal := st.iter, liveOrbits := st.orbits.size,
        msTotal := ts1 - ts0, msRef := ts2 - ts1
      }
    tasks := tasks.push (i, t)

  let mut dAgree := 0
  let mut cAgree := 0
  let mut cTotalCount := 0
  let mut dMismatches : Array Nat := #[]
  let mut cMismatches : Array Nat := #[]
  let mut rsstMismatches : Array Nat := #[]
  let mut errors := 0

  for (i, t) in tasks do
    match ← IO.wait t with
    | .ok r =>
      if r.dTotal == r.dRef then dAgree := dAgree + 1 else dMismatches := dMismatches.push i
      if !r.expectedD then
        cTotalCount := cTotalCount + 1
        if r.cTotal == r.cRef && r.cTotal == true then cAgree := cAgree + 1
        else cMismatches := cMismatches.push i
      if r.dTotal != r.expectedD || (!r.expectedD && !r.cTotal) then
        rsstMismatches := rsstMismatches.push i
    | .error e =>
      errors := errors + 1
      IO.println s!"Error on config {i}: {e}"

  IO.println "\n--- Stage K0.7 Differential Summary ---"
  IO.println s!"Configurations checked: {total}"
  IO.println s!"D-verdict agreement (`checkFastTotal` == ref): {dAgree}/{total} (mismatches: {dMismatches.toList})"
  IO.println s!"C-verdict agreement (`runContractCheckTotal` == ref): {cAgree}/{cTotalCount} (mismatches: {cMismatches.toList})"
  IO.println s!"RSST ground-truth mismatches: {rsstMismatches.size} {rsstMismatches.toList}"
  IO.println s!"Errors: {errors}"
  IO.println s!"Total wall time: {((← IO.monoMsNow) - t0) / 1000}s"
  return (if cfgDiffs.isEmpty && dMismatches.isEmpty && cMismatches.isEmpty && rsstMismatches.isEmpty && errors == 0 then 0 else 1)
