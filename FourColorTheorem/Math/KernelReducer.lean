module

public import FourColorTheorem.Math.FastReducer
public import FourColorTheorem.Math.ParsedRConf633
public import FourColorTheorem.Math.KernelRfl

@[expose] public section

namespace Math
namespace KernelReducer

noncomputable section

open FastReducer

/-- Single-constructor box used to force any non-`Nat` structure to WHNF in complete isolation
    via `@StrictBox.rec` (`letStrictBox`), with the continuation appearing only once. -/
structure StrictBox (α : Type) where
  val : α

instance {α : Type} [Inhabited α] : Inhabited (StrictBox α) where
  default := StrictBox.mk default

/-- Forces Lean 4's C++ kernel (`type_checker::reduce_rec`) to evaluate `n` to a
    raw GMP `mpz` literal `val` (`Expr::Lit(NatVal)`) before beta-reducing `k val`, with `k` appearing only once. -/
scoped macro "letStrictNat" n:term:arg k:term:arg : term =>
  `(@Nat.rec (fun _ => _) default (fun val _ih => $k val) (Nat.succ $n))

/-- Branch on a `Bool` via `Bool.rec` with `onTrue` first and `onFalse` second. -/
scoped macro "selectBool" c:term:arg onTrue:term:arg onFalse:term:arg : term =>
  `(@Bool.rec (fun _ => _) $onFalse $onTrue $c)

/-- Short-circuiting `a && b` via `Bool.rec` where `b` appears only once. -/
scoped macro "andLazy" a:term:arg b:term:arg : term =>
  `(@Bool.rec (fun _ => Bool) false $b $a)

/-- Short-circuiting `a || b` via `Bool.rec` where `b` appears only once. -/
scoped macro "orLazy" a:term:arg b:term:arg : term =>
  `(@Bool.rec (fun _ => Bool) $b true $a)

scoped macro "natBne" a:term:arg b:term:arg : term =>
  `(@Bool.rec (fun _ => Bool) true false (Nat.beq $a $b))

/-- Forces Lean's kernel (`reduce_rec`) to evaluate `b : StrictBox α` to `StrictBox.mk val` in WHNF
    in complete isolation before beta-reducing `k val`, with `k` appearing only once. -/
scoped macro "letStrictBox" b:term:arg k:term:arg : term =>
  `(@StrictBox.rec _ (fun _ => _) (fun val => $k val) $b)

/-- Forces Lean's kernel (`reduce_rec`) to evaluate `p : α × β` to `(a, b)` in WHNF
    in complete isolation before beta-reducing `k a b`, with `k` appearing only once. -/
scoped macro "letStrictPair" p:term:arg k:term:arg : term =>
  `(@Prod.rec _ _ (fun _ => _) (fun a b => $k a b) $p)

/-- Force `x` to be evaluated and cached in `m_whnf_cache` / `m_whnf_core_cache` via `Bool.rec`
    without allocating a `Nat.succ` wrapper or a `@Nat.rec` closure. -/
def seqNat {α : Type} (x : Nat) (res : α) : α :=
  @Bool.rec (fun _ => α) res res (Nat.beq x 0)

theorem seqNat_eq {α : Type} (x : Nat) (res : α) : seqNat x res = res := by
  unfold seqNat
  cases Nat.beq x 0 <;> rfl

/-- Compute $3^n$ by primitive recursion. -/
def pow3 (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => Nat.mul 3 ih) n

/-- Compute binomial coefficient $\binom{n}{k}$ in $k$ multiplicative steps. -/
def binomAux : Nat → Nat → Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Nat)
    (fun _n _i acc => acc)
    (fun _ ih n i acc =>
      let nextI := Nat.succ i
      let nextAcc := Nat.div (Nat.mul acc (Nat.sub n i)) nextI
      ih n nextI nextAcc)

def binom (n k : Nat) : Nat :=
  selectBool (Nat.blt n k) 0 (binomAux k n 0 1)

/-- Population count (number of set bits) of a small `Nat` ($< 2^{16}$). -/
def popcountAux (fuel : Nat) : Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat)
    (fun _ acc => acc)
    (fun _ ih x acc =>
      @Nat.rec (fun _ => Nat) acc
        (fun _ _ => ih (Nat.shiftRight x 1) (Nat.add acc (Nat.land x 1)))
        x)
    fuel

def popcount (x : Nat) : Nat :=
  popcountAux 16 x 0

/-- Exact single-shot repetition of `cell` `count` times at bit stride `stride` via geometric series division
    $\text{cell} \cdot \frac{2^{\text{count} \cdot \text{stride}} - 1}{2^{\text{stride}} - 1}$, avoiding 22-step recursive cache entries. -/
def repeatBlock (cell stride count : Nat) : Nat :=
  selectBool (orLazy (Nat.beq count 0) (Nat.beq cell 0))
    0
    (selectBool (Nat.beq count 1)
      cell
      (Nat.mul cell
        (Nat.div
          (Nat.sub (Nat.shiftLeft 1 (Nat.mul count stride)) 1)
          (Nat.sub (Nat.shiftLeft 1 stride) 1))))

/-- Construct a periodic mask of `count` blocks, each of `width` ones, spaced at `stride`. -/
def getRepeatMask (count stride width : Nat) : Nat :=
  let base := Nat.sub (Nat.shiftLeft 1 width) 1
  repeatBlock base stride count

/-- Reverse a list using primitive recursion. -/
def revList {α : Type} (xs : List α) : List α :=
  @List.rec α (fun _ => List α → List α)
    (fun acc => acc)
    (fun h _ ih acc => ih (h :: acc))
    xs []

/-- Reverse a list into a `StrictBox` using primitive recursion. -/
def revListBox {α : Type} (xs : List α) : StrictBox (List α) :=
  @List.rec α (fun _ => List α → StrictBox (List α))
    (fun acc => StrictBox.mk acc)
    (fun h _ ih acc => ih (h :: acc))
    xs []

/-- A single binary-doubling pack/unpack step `(shiftDiff, m0, m1)` where `shiftDiff = oldStep - curW` and `m1 = m0 <<< curW`. -/
inductive PackStep where
  | mk (shiftDiff m0 m1 : Nat) : PackStep

/-- Build reversed pack steps `(shiftDiff, m0, m1)` for `b = 0, 1, ...` while `2^b < N` tail-recursively.
    At the final doubling step (`2^{b+1} >= N`), `m1` is bounded strictly to `[curW, N * W)` so `runUnpack`
    automatically masks out all bits `>= N * W` without needing a separate `Nat.land dk lowMask` operation. -/
def buildPackStepsRevAux (fuel N W S : Nat) :
    Nat → List PackStep → StrictBox (List PackStep) :=
  @Nat.rec (fun _ => Nat → List PackStep → StrictBox (List PackStep))
    (fun _ revAcc => StrictBox.mk revAcc)
    (fun _ ih b revAcc =>
      let pow2b := Nat.shiftLeft 1 b
      selectBool (Nat.blt pow2b N)
        (let nextB := Nat.succ b
         let pow2b1 := Nat.shiftLeft 1 nextB
         let curW := Nat.mul pow2b W
         let oldStep := Nat.mul pow2b S
         let shiftDiff := Nat.sub oldStep curW
         let numPairs := Nat.shiftRight (Nat.add N (Nat.sub pow2b1 1)) nextB
         let m0 := getRepeatMask numPairs (Nat.mul 2 oldStep) curW
         let m1 :=
           selectBool (Nat.ble N pow2b1)
             (Nat.sub (Nat.shiftLeft 1 (Nat.mul N W)) (Nat.shiftLeft 1 curW))
             (Nat.shiftLeft m0 curW)
         ih nextB (PackStep.mk shiftDiff m0 m1 :: revAcc))
        (StrictBox.mk revAcc))
    fuel

def withPackSteps (N W S : Nat) (maskWhenOne : Bool) : List PackStep × List PackStep :=
  selectBool (Nat.ble N 1)
    (selectBool maskWhenOne
      (let m0 := Nat.sub (Nat.shiftLeft 1 W) 1
       ([PackStep.mk 0 m0 0], []))
      ([], []))
    (let revSt := (buildPackStepsRevAux 20 N W S 0 []).val
     let fwdSt := (revListBox revSt).val
     (fwdSt, revSt))

/-- Execute a list of binary-doubling pack steps on `X`, short-circuiting when `X == 0`. -/
def runPackSteps (steps : List PackStep) (X : Nat) : Nat :=
  selectBool (Nat.beq X 0) 0
    (@List.rec PackStep (fun _ => Nat → Nat)
      (fun acc => acc)
      (fun step _ ih acc =>
        @PackStep.rec (fun _ => Nat)
          (fun shiftDiff m0 m1 =>
            let g0 := Nat.land acc m0
            let s1 := Nat.land (Nat.shiftRight acc shiftDiff) m1
            ih (Nat.lor g0 s1))
          step)
      steps X)

/-- Execute a list of reversed binary-doubling unpack steps on `X`, short-circuiting when `X == 0`. -/
def runUnpack (X : Nat) (revSteps : List PackStep) : Nat :=
  selectBool (Nat.beq X 0) 0
    (@List.rec PackStep (fun _ => Nat → Nat)
      (fun acc => acc)
      (fun step _ ih acc =>
        @PackStep.rec (fun _ => Nat)
          (fun shiftDiff m0 m1 =>
            let g0 := Nat.land acc m0
            let s1 := Nat.shiftLeft (Nat.land acc m1) shiftDiff
            ih (Nat.lor g0 s1))
          step)
      revSteps X)

/-- Specification for one cell `(m, k)` in `packToBuckets`. -/
inductive PackCellSpec where
  | mk (P lowBits : Nat) (steps0 steps12 : List PackStep) : PackCellSpec

/-- Specification for one cell `(m, k)` in `unpackFromBuckets`. -/
inductive UnpackCellSpec where
  | mk (P nextLowBits : Nat) (revSteps0 revSteps12 : List PackStep) : UnpackCellSpec

/-- Tail-recursive zipper for level `m` of `packToBuckets` returning the reversed row. -/
def packLevelRev (specs : List PackCellSpec) : List Nat → Nat → List Nat → List Nat :=
  @List.rec PackCellSpec (fun _ => List Nat → Nat → List Nat → List Nat)
    (fun _ prevS12 acc => prevS12 :: acc)
    (fun spec _ ih D prevS12 acc =>
      @PackCellSpec.rec (fun _ => List Nat)
        (fun P lowBits steps0 steps12 =>
          @List.rec Nat (fun _ => List Nat)
            (prevS12 :: acc)
            (fun dk restD _ =>
              let s0_k := runPackSteps steps0 dk
              let s12_k := runPackSteps steps12 (Nat.shiftRight dk P)
              let nextDk := Nat.lor s0_k (Nat.shiftLeft prevS12 lowBits)
              ih restD s12_k (nextDk :: acc))
            D)
        spec)
    specs

/-- Run levels $m = 1 \dots mMax - 1$ of `packToBuckets` starting from `initD = [L2, d0_1]`. -/
def packToBuckets (levels : List (List PackCellSpec)) (initD : List Nat) : List Nat :=
  @List.rec (List PackCellSpec) (fun _ => List Nat → List Nat)
    (fun D => D)
    (fun lvlSpecs _ ih D =>
      let nextD := revList (packLevelRev lvlSpecs D 0 [])
      ih nextD)
    levels initD

/-- Tail-recursive 1-element-lookahead zipper for level `m` of `unpackFromBuckets` returning the reversed row. -/
def unpackLevelRev (specs : List UnpackCellSpec) : Nat → List Nat → List Nat → List Nat :=
  @List.rec UnpackCellSpec (fun _ => Nat → List Nat → List Nat → List Nat)
    (fun _ _ acc => acc)
    (fun spec _ ih dk restD acc =>
      @UnpackCellSpec.rec (fun _ => List Nat)
        (fun P nextLowBits revSteps0 revSteps12 =>
          let s0_k := runUnpack dk revSteps0
          @List.rec Nat (fun _ => List Nat)
            (s0_k :: acc)
            (fun dkNext restD' _ =>
              let s12_k := runUnpack (Nat.shiftRight dkNext nextLowBits) revSteps12
              let prevDk := Nat.lor s0_k (Nat.shiftLeft s12_k P)
              ih dkNext restD' (prevDk :: acc))
            restD)
        spec)
    specs

/-- Run levels $m = mMax - 1 \dots 1$ of `unpackFromBuckets` and pass `u0, u12` to continuation `k`. -/
def withUnpackFromBucketsPair {α : Type} (revLevels : List (List UnpackCellSpec)) (buckets : List Nat)
    (k : Nat → Nat → α) (defVal : α) : α :=
  let finalD :=
    @List.rec (List UnpackCellSpec) (fun _ => List Nat → List Nat)
      (fun D => D)
      (fun lvlSpecs _ ih D =>
        @List.rec Nat (fun _ => List Nat)
          []
          (fun d0 restD _ =>
            let prevD := revList (unpackLevelRev lvlSpecs d0 restD [])
            ih prevD)
          D)
      revLevels buckets
  @List.rec Nat (fun _ => α)
    defVal
    (fun u0 restD _ =>
      @List.rec Nat (fun _ => α)
        (k u0 0)
        (fun u12 _ _ => k u0 u12)
        restD)
    finalD

/-- Build both `List PackCellSpec` and `List UnpackCellSpec` for level `m` ($k = 0 \dots m$) using countdown tail-recursion.
    At $(m = 1, k = 1)$, `UnpackCellSpec` masks directly to block 0 (`u1`, width $3^{mMax-1}$) without unpacking `u2`. -/
def buildLevelSpecs (m P : Nat) : List PackCellSpec × List UnpackCellSpec :=
  let P2 := Nat.mul 2 P
  let P3 := Nat.mul 3 P
  @Nat.rec (fun _ => List PackCellSpec → List UnpackCellSpec → List PackCellSpec × List UnpackCellSpec)
    (fun pAcc uAcc => (pAcc, uAcc))
    (fun kIdx ih pAcc uAcc =>
      let N := Nat.mul (binom m kIdx) (Nat.shiftLeft 1 kIdx)
      let lowBits := Nat.mul N P
      let nextLowBits :=
        selectBool (Nat.ble (Nat.succ kIdx) m)
          (Nat.mul (Nat.mul (binom m (Nat.succ kIdx)) (Nat.shiftLeft 1 (Nat.succ kIdx))) P)
          0
      @Prod.rec _ _ (fun _ => _)
        (fun st0 revSt0 =>
          @Prod.rec _ _ (fun _ => _)
            (fun st12 revSt12 =>
              let isM1K1 := and (Nat.beq m 1) (Nat.beq kIdx 1)
              let rev0 :=
                selectBool isM1K1
                  (let m0 := Nat.sub (Nat.shiftLeft 1 P) 1
                   [PackStep.mk 0 m0 0])
                  revSt0
              let rev12 :=
                selectBool isM1K1
                  (let m12 := Nat.sub (Nat.shiftLeft 1 P2) 1
                   [PackStep.mk 0 m12 0])
                  revSt12
              ih (PackCellSpec.mk P lowBits st0 st12 :: pAcc)
                 (UnpackCellSpec.mk P nextLowBits rev0 rev12 :: uAcc))
            (withPackSteps N P2 P3 false))
        (withPackSteps N P P3 true))
    (Nat.succ m) [] []

/-- Build `packLevels` (forward $m = 1 \dots mMax - 1$) and `unpackRevLevels` (reverse $m = mMax - 1 \dots 1$) using countdown tail-recursion. -/
def buildAllPackUnpackLevels (mMax : Nat) : List (List PackCellSpec) × List (List UnpackCellSpec) :=
  @Nat.rec (fun _ =>
    List (List PackCellSpec) → List (List UnpackCellSpec) →
    List (List PackCellSpec) × List (List UnpackCellSpec))
    (fun pAcc uAcc =>
      @List.rec (List UnpackCellSpec)
        (fun _ => List (List UnpackCellSpec) → List (List PackCellSpec) × List (List UnpackCellSpec))
        (fun uRev => (pAcc, uRev))
        (fun h _ ihRev uRev => ihRev (h :: uRev))
        uAcc [])
    (fun mIdx ih pAcc uAcc =>
      let m := Nat.succ mIdx
      let e := Nat.sub (Nat.sub mMax 1) m
      let P := pow3 e
      @Prod.rec _ _ (fun _ => _)
        (fun pLvl uLvl => ih (pLvl :: pAcc) (uLvl :: uAcc))
        (buildLevelSpecs m P))
    (Nat.sub mMax 1) [] []

/-!
## Precompiled Catalan Chord Trie
-/

/-- A single chord operation inside a Catalan bucket. -/
inductive ChordOp where
  | pair (dPlus dMinus mask00 mask10 : Nat) : ChordOp
  | last (dShift mask0 : Nat) : ChordOp

/-- Apply a `ChordOp` to bucket bitmask `B` at a leaf chord, skipping upward shifts when `mBase == 0`. -/
scoped macro "applyChordOp" op:term:arg B:term:arg : term =>
  `(@ChordOp.rec (fun _ => Nat)
    (fun dPlus dMinus mask00 mask10 =>
      let mPlus := Nat.land (Nat.land $B (Nat.shiftRight $B dPlus)) mask00
      let mMinus := Nat.land (Nat.land $B (Nat.shiftRight $B dMinus)) mask10
      let mBase := Nat.lor mPlus mMinus
      selectBool (Nat.beq mBase 0)
        0
        (Nat.lor mBase (Nat.lor (Nat.shiftLeft mPlus dPlus) (Nat.shiftLeft mMinus dMinus))))
    (fun dShift mask0 =>
      let m := Nat.land (Nat.land $B (Nat.shiftRight $B dShift)) mask0
      selectBool (Nat.beq m 0)
        0
        (Nat.lor m (Nat.shiftLeft m dShift)))
    $op)

/-- Apply a `ChordOp` at a single-child internal trie node (`sibling = nil`), short-circuiting `ihChild` when `mBase == 0`. -/
scoped macro "evalChordOnly" op:term:arg B:term:arg ihChild:term:arg : term =>
  `(@ChordOp.rec (fun _ => Nat)
    (fun dPlus dMinus mask00 mask10 =>
      let mPlus := Nat.land (Nat.land $B (Nat.shiftRight $B dPlus)) mask00
      let mMinus := Nat.land (Nat.land $B (Nat.shiftRight $B dMinus)) mask10
      let mBase := Nat.lor mPlus mMinus
      selectBool (Nat.beq mBase 0)
        0
        (let mNext := Nat.lor mBase (Nat.lor (Nat.shiftLeft mPlus dPlus) (Nat.shiftLeft mMinus dMinus))
         $ihChild mNext))
    (fun dShift mask0 =>
      let m := Nat.land (Nat.land $B (Nat.shiftRight $B dShift)) mask0
      selectBool (Nat.beq m 0)
        0
        (let mNext := Nat.lor m (Nat.shiftLeft m dShift)
         $ihChild mNext))
    $op)

/-- Apply a `ChordOp` at a branching internal trie node, binding `sibCov := $ihSibling $B` once and short-circuiting `ihChild` when `mBase == 0`. -/
scoped macro "evalChordBranch" op:term:arg B:term:arg ihChild:term:arg ihSibling:term:arg : term =>
  `(@ChordOp.rec (fun _ => Nat)
    (fun dPlus dMinus mask00 mask10 =>
      let sibCov := $ihSibling $B
      let mPlus := Nat.land (Nat.land $B (Nat.shiftRight $B dPlus)) mask00
      let mMinus := Nat.land (Nat.land $B (Nat.shiftRight $B dMinus)) mask10
      let mBase := Nat.lor mPlus mMinus
      selectBool (Nat.beq mBase 0)
        sibCov
        (let mNext := Nat.lor mBase (Nat.lor (Nat.shiftLeft mPlus dPlus) (Nat.shiftLeft mMinus dMinus))
         Nat.lor ($ihChild mNext) sibCov))
    (fun dShift mask0 =>
      let sibCov := $ihSibling $B
      let m := Nat.land (Nat.land $B (Nat.shiftRight $B dShift)) mask0
      selectBool (Nat.beq m 0)
        sibCov
        (let mNext := Nat.lor m (Nat.shiftLeft m dShift)
         Nat.lor ($ihChild mNext) sibCov))
    $op)

/-- Non-nested tree representing the Catalan non-crossing matching trie with specialized leaf and single-child nodes. -/
inductive CatalanTrie where
  | leaf : CatalanTrie
  | nil : CatalanTrie
  | leafOp : ChordOp → CatalanTrie
  | only : ChordOp → CatalanTrie → CatalanTrie
  | branch : ChordOp → CatalanTrie → CatalanTrie → CatalanTrie

instance : Inhabited CatalanTrie where
  default := CatalanTrie.nil

def isLeafTrie (t : CatalanTrie) : Bool :=
  @CatalanTrie.rec (fun _ => Bool) true false (fun _ => false) (fun _ _ _ => false) (fun _ _ _ _ _ => false) t

def isNilTrie (t : CatalanTrie) : Bool :=
  @CatalanTrie.rec (fun _ => Bool) false true (fun _ => false) (fun _ _ _ => false) (fun _ _ _ _ _ => false) t

def mkCatalanNode (op : ChordOp) (child sib : CatalanTrie) : CatalanTrie :=
  selectBool (isNilTrie sib)
    (selectBool (isLeafTrie child)
      (CatalanTrie.leafOp op)
      (CatalanTrie.only op child))
    (CatalanTrie.branch op child sib)

/-- Evaluate a `CatalanTrie` on `workB` using primitive recursion as a pure arithmetic DAG,
    pruning dead subtrees before upward shifts whenever `mBase == 0`. -/
def evalCatalanTrie (trie : CatalanTrie) (workB : Nat) : Nat :=
  @CatalanTrie.rec (fun _ => Nat → Nat)
    (fun curB => curB)
    (fun _ => 0)
    (fun op curB => applyChordOp op curB)
    (fun op _ ihChild curB => evalChordOnly op curB ihChild)
    (fun op _ _ ihChild ihSibling curB => evalChordBranch op curB ihChild ihSibling)
    trie workB

/-- Build `makeSingleBitMask0` in $O(\log(\text{numBits}) + \log M)$ binary-doubling steps without per-bit loops. -/
def makeSingleBitMask0 (kBucket numBits M a : Nat) : Nat :=
  let countInCell := Nat.shiftLeft 1 (Nat.sub (Nat.sub numBits 1) a)
  let width := Nat.shiftLeft 1 a
  let stride := Nat.shiftLeft 1 (Nat.succ a)
  let cell := getRepeatMask countInCell stride width
  repeatBlock cell (Nat.shiftLeft 1 kBucket) M

/-- Precompute association list `(a, mask0)` for `0 <= a < numBits` using countdown tail-recursion. -/
def buildM0List (kBucket numBits M : Nat) : StrictBox (List (Nat × Nat)) :=
  @Nat.rec (fun _ => List (Nat × Nat) → StrictBox (List (Nat × Nat)))
    (fun acc => StrictBox.mk acc)
    (fun a ih acc =>
      let m0 := makeSingleBitMask0 kBucket numBits M a
      ih ((a, m0) :: acc))
    numBits []

/-- Lookup `m0` for `a` in `m0List`. -/
def lookupM0 (a : Nat) (xs : List (Nat × Nat)) : Nat :=
  @List.rec (Nat × Nat) (fun _ => Nat)
    0
    (fun h _ ih =>
      @Prod.rec Nat Nat (fun _ => Nat)
        (fun ha m0 => selectBool (Nat.beq ha a) m0 ih)
        h)
    xs

/-- Build the `CatalanTrie` for an interval stack `intervals : List (Nat × Nat)` using `StrictBox` and countdown tail-recursion. -/
def buildCatalanTrieAux (twoP : Nat) (m0List : List (Nat × Nat)) (fuel : Nat) :
    List (Nat × Nat) → StrictBox CatalanTrie :=
  @Nat.rec (fun _ => List (Nat × Nat) → StrictBox CatalanTrie)
    (fun _ => StrictBox.mk CatalanTrie.leaf)
    (fun _ ihFuel intervals =>
      @List.rec (Nat × Nat) (fun _ => StrictBox CatalanTrie)
        (StrictBox.mk CatalanTrie.leaf)
        (fun top rest _ =>
          @Prod.rec Nat Nat (fun _ => StrictBox CatalanTrie)
            (fun lo hi =>
              let numSteps := Nat.shiftRight (Nat.sub hi lo) 1
              let bitLo := Nat.shiftLeft 1 lo
              let m0Lo := lookupM0 lo m0List
              let loPlus1 := Nat.add lo 1
              @Nat.rec (fun _ => CatalanTrie → StrictBox CatalanTrie)
                (fun sibAcc => StrictBox.mk sibAcc)
                (fun idx ihSib sibAcc =>
                  let kIdx := Nat.add loPlus1 (Nat.mul 2 idx)
                  let kPlus1 := Nat.add kIdx 1
                  let rest1 := selectBool (Nat.blt kPlus1 hi) ((kPlus1, hi) :: rest) rest
                  let rest2 := selectBool (Nat.blt loPlus1 kIdx) ((loPlus1, kIdx) :: rest1) rest1
                  let childTrie := (ihFuel rest2).val
                  selectBool (Nat.beq kIdx (Nat.sub twoP 1))
                    (ihSib (mkCatalanNode (ChordOp.last bitLo m0Lo) childTrie sibAcc))
                    (let m0K := lookupM0 kIdx m0List
                     let m00 := Nat.land m0Lo m0K
                     let m10 := Nat.shiftLeft m00 bitLo
                     let bitK := Nat.shiftLeft 1 kIdx
                     let dPlus := Nat.add bitK bitLo
                     let dMinus := Nat.sub bitK bitLo
                     ihSib (mkCatalanNode (ChordOp.pair dPlus dMinus m00 m10) childTrie sibAcc)))
                numSteps CatalanTrie.nil)
            top)
        intervals)
    fuel

/-- Specification for Catalan Kempe closure on bucket `kBucket`. -/
inductive BucketCatalanSpec where
  | mk (kBucket : Nat) (isEven : Bool) (halfShift evenHalfMask evenParityMask : Nat) (trie : CatalanTrie) : BucketCatalanSpec

instance : Inhabited BucketCatalanSpec where
  default := BucketCatalanSpec.mk 0 true 0 0 0 CatalanTrie.leaf

/-- Build the $2^k$-bit Thue-Morse parity cell mask in $k$ binary-doubling steps. -/
def buildThueMorseParityAux (rMod2 : Nat) : Nat → Nat → Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat → Nat)
    (fun _W evenM oddM => selectBool (Nat.beq rMod2 0) evenM oddM)
    (fun _ ih W evenM oddM =>
      let nextEven := Nat.lor evenM (Nat.shiftLeft oddM W)
      let nextOdd := Nat.lor oddM (Nat.shiftLeft evenM W)
      let nextW := Nat.shiftLeft W 1
      ih nextW nextEven nextOdd)

/-- Build the `BucketCatalanSpec` for a single `kBucket` in `StrictBox`. -/
def buildBucketCatalanSpec (r mMax kBucket : Nat) : StrictBox BucketCatalanSpec :=
  @Nat.rec (fun _ => StrictBox BucketCatalanSpec)
    (StrictBox.mk (BucketCatalanSpec.mk 0 true 0 0 0 CatalanTrie.leaf))
    (fun _ _ =>
      let M := binom mMax kBucket
      let isEven := Nat.beq (Nat.mod kBucket 2) 0
      let numBits := selectBool isEven (Nat.sub kBucket 1) kBucket
      let twoP := selectBool isEven kBucket (Nat.add kBucket 1)
      let halfShift := selectBool isEven (Nat.shiftLeft 1 (Nat.sub kBucket 1)) 0
      let eh :=
        selectBool isEven
          (let hCell := Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 (Nat.sub kBucket 1))) 1
           repeatBlock hCell (Nat.shiftLeft 1 kBucket) M)
          0
      let ep :=
        selectBool isEven
          (let pCell := buildThueMorseParityAux (Nat.mod r 2) kBucket 1 1 0
           repeatBlock pCell (Nat.shiftLeft 1 kBucket) M)
          0
      let m0List := (buildM0List kBucket numBits M).val
      let trie := (buildCatalanTrieAux twoP m0List 20 [(0, twoP)]).val
      StrictBox.mk (BucketCatalanSpec.mk kBucket isEven halfShift eh ep trie))
    kBucket

/-- Build all `r` bucket specifications in forward order $k = 0 \dots r - 1$ using countdown tail-recursion. -/
def buildAllBucketSpecs (r mMax : Nat) : StrictBox (List BucketCatalanSpec) :=
  @Nat.rec (fun _ => List BucketCatalanSpec → StrictBox (List BucketCatalanSpec))
    (fun acc => StrictBox.mk acc)
    (fun kIdx ih acc =>
      let spec := (buildBucketCatalanSpec r mMax kIdx).val
      ih (spec :: acc))
    r []

/-- Evaluate Catalan Kempe closure on a single bucket `B` using `bSpec`, short-circuiting when `B == 0` or `workB == 0`. -/
scoped macro "evalBucketCatalan" bSpec:term:arg B:term:arg : term =>
  `(@BucketCatalanSpec.rec (fun _ => Nat)
    (fun kBucket isEven halfShift evenHalfMask evenParityMask trie =>
      selectBool (orLazy (Nat.beq kBucket 0) (Nat.beq $B 0)) $B
        (let workB :=
           selectBool isEven
             (Nat.lor (Nat.land $B evenHalfMask)
                      (Nat.land (Nat.shiftRight $B halfShift) evenHalfMask))
             $B
         selectBool (Nat.beq workB 0) 0
           (let cov := evalCatalanTrie trie workB
            selectBool isEven
              (Nat.land (Nat.lor cov (Nat.shiftLeft cov halfShift)) evenParityMask)
              cov)))
    $bSpec)

/-- Tail-recursive evaluation of Catalan Kempe closure across all buckets, returning the reversed list. -/
def evalAllBucketsRev : List BucketCatalanSpec → List Nat → List Nat → List Nat :=
  @List.rec BucketCatalanSpec (fun _ => List Nat → List Nat → List Nat)
    (fun _ acc => acc)
    (fun bSpec _ ih buckets acc =>
      @List.rec Nat (fun _ => List Nat)
        acc
        (fun B restB _ =>
          let covB := evalBucketCatalan bSpec B
          ih restB (covB :: acc))
        buckets)

/-- Evaluate Catalan Kempe closure across all buckets. -/
def evalAllBuckets (bucketSpecs : List BucketCatalanSpec) (buckets : List Nat) : List Nat :=
  revList (evalAllBucketsRev bucketSpecs buckets [])

/-!
## $S_3$ Digit Swap Operations
-/

/-- Precomputed step `(P, P2, m0, m1, m2)` for ternary digit swaps. -/
inductive SwapStep where
  | mk (P P2 m0 m1 m2 : Nat) : SwapStep

/-- Build all `nDigits` digit swap steps in forward order $e = 0 \dots nDigits - 1$ using countdown tail-recursion. -/
def buildSwapSteps (nDigits : Nat) : StrictBox (List SwapStep) :=
  @Nat.rec (fun _ => List SwapStep → StrictBox (List SwapStep))
    (fun acc => StrictBox.mk acc)
    (fun e ih acc =>
      let P := pow3 e
      let P2 := Nat.mul 2 P
      let count := pow3 (Nat.sub (Nat.sub nDigits 1) e)
      let m0 := getRepeatMask count (Nat.mul 3 P) P
      let m1 := Nat.shiftLeft m0 P
      let m2 := Nat.shiftLeft m0 P2
      ih (SwapStep.mk P P2 m0 m1 m2 :: acc))
    nDigits []

def swapDigits01 (steps : List SwapStep) (X : Nat) : Nat :=
  selectBool (Nat.beq X 0) 0
    (@List.rec SwapStep (fun _ => Nat → Nat)
      (fun acc => acc)
      (fun step _ ih acc =>
        @SwapStep.rec (fun _ => Nat)
          (fun P _ m0 _ m2 =>
            let g01 := Nat.shiftLeft (Nat.land acc m0) P
            let g10 := Nat.land (Nat.shiftRight acc P) m0
            let g22 := Nat.land acc m2
            ih (Nat.lor g22 (Nat.lor g10 g01)))
          step)
      steps X)

def swapDigits02 (steps : List SwapStep) (X : Nat) : Nat :=
  selectBool (Nat.beq X 0) 0
    (@List.rec SwapStep (fun _ => Nat → Nat)
      (fun acc => acc)
      (fun step _ ih acc =>
        @SwapStep.rec (fun _ => Nat)
          (fun _ P2 m0 m1 _ =>
            let g02 := Nat.shiftLeft (Nat.land acc m0) P2
            let g20 := Nat.land (Nat.shiftRight acc P2) m0
            let g11 := Nat.land acc m1
            ih (Nat.lor g11 (Nat.lor g20 g02)))
          step)
      steps X)

def swapDigits12 (steps : List SwapStep) (X : Nat) : Nat :=
  selectBool (Nat.beq X 0) 0
    (@List.rec SwapStep (fun _ => Nat → Nat)
      (fun acc => acc)
      (fun step _ ih acc =>
        @SwapStep.rec (fun _ => Nat)
          (fun P _ m0 m1 _ =>
            let g00 := Nat.land acc m0
            let g12 := Nat.shiftLeft (Nat.land acc m1) P
            let g21 := Nat.land (Nat.shiftRight acc P) m1
            ih (Nat.lor g00 (Nat.lor g21 g12)))
          step)
      steps X)

/-- Complete precomputed mask & trie engine for ring size `r`. -/
structure EngineMasks where
  r : Nat
  mMax : Nat

/-- Build the `EngineMasks` for ring size `r`. -/
def buildEngine (r : Nat) : EngineMasks :=
  { r := r, mMax := Nat.sub r 1 }

/-!
## 8-State Bottom-Up Ring Masks & Bit-Parallel Interior-First DFS
-/

/-- Precomputed $3^{r-1}$-bit color masks `(c0, c1, c2, c3)` for a single ring vertex `u`. -/
inductive RingColMasks where
  | mk (u c0 c1 c2 c3 : Nat) : RingColMasks

/-- Precomputed step for a single interior vertex `v` in `dfsInterior`. -/
inductive IntVertexStep where
  | mk (bitV reqMask checkMask f0 f1 f2 f3 : Nat) : IntVertexStep

/-- Apply one bottom-up level step (at ternary power `P = 3^(e-1)`) to an 8-state row `(v00..v31)` in CPS. -/
def stepRow8 {α : Type} [Inhabited α] (P P2 : Nat)
    (v00 v01 v10 v11 v20 v21 v30 v31 : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → α) : α :=
  let s01_1 := Nat.shiftLeft v01 P
  let s11_1 := Nat.shiftLeft v11 P
  let s21_1 := Nat.shiftLeft v21 P
  let s31_1 := Nat.shiftLeft v31 P
  let s01_2 := Nat.shiftLeft v01 P2
  let s11_2 := Nat.shiftLeft v11 P2
  let s21_2 := Nat.shiftLeft v21 P2
  let s31_2 := Nat.shiftLeft v31 P2
  let n00 := Nat.lor v10 s21_1
  let n01 := Nat.lor v11 (Nat.lor s21_1 s31_2)
  let n10 := Nat.lor v00 s31_1
  let n11 := Nat.lor v01 (Nat.lor s31_1 s21_2)
  let n20 := Nat.lor v30 s01_1
  let n21 := Nat.lor v31 (Nat.lor s01_1 s11_2)
  let n30 := Nat.lor v20 s11_1
  let n31 := Nat.lor v21 (Nat.lor s11_1 s01_2)
  k n00 n01 n10 n11 n20 n21 n30 n31

/-- Single-pass bottom-up loop computing `(canonValidMask, List RingColMasks)` for `u = 0 .. mMax`.
    Uses the disjoint color-prefix partition property: at depth `u` (stride `P = 3^(u-1)`),
    the color of ring vertex `u` depends only on the prefix `j mod P`, whose 4 color masks
    are `(x1_11, x1_01, x1_31, x1_21)`. Tiling each `P`-bit mask across `3^(mMax-1)` via
    `repFactor = totalMask / (2^P - 1)` and intersecting with `canonValid` avoids all 264
    calls to `propRow8ToTop` and reduces `stepRow8` calls by 25x. -/
def buildRingColLoop {α : Type} [Inhabited α] (mMax : Nat) :
    Nat → Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    (Nat → Nat → List RingColMasks → α) → α :=
  @Nat.rec (fun _ =>
    Nat → Nat →
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat →
    (Nat → Nat → List RingColMasks → α) → α)
    (fun _u P
         x1_00 _ _ _ x1_20 _ x1_30 _
         k =>
      let canonValid := Nat.lor x1_00 (Nat.lor x1_30 x1_20)
      let totalMask := Nat.sub (Nat.shiftLeft 1 P) 1
      seqNat canonValid (seqNat totalMask
        (k canonValid totalMask
          (RingColMasks.mk 0 0 canonValid 0 0 ::
           RingColMasks.mk (Nat.sub mMax 1) 0 x1_00 x1_30 x1_20 ::
           RingColMasks.mk mMax x1_00 0 x1_20 x1_30 :: []))))
    (fun _ ih u P
         x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31
         k =>
      let P2 := Nat.mul 2 P
      let nextP := Nat.mul 3 P
      let nextU := Nat.succ u
      stepRow8 P P2 x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31
        (fun n1_00 n1_01 n1_10 n1_11 n1_20 n1_21 n1_30 n1_31 =>
          ih nextU nextP
            n1_00 n1_01 n1_10 n1_11 n1_20 n1_21 n1_30 n1_31
            (fun canonValid totalMask rest =>
              let repFactor := Nat.div totalMask (Nat.sub (Nat.shiftLeft 1 P) 1)
              let c0_u := Nat.land canonValid (Nat.mul x1_11 repFactor)
              let c1_u := Nat.land canonValid (Nat.mul x1_01 repFactor)
              let c2_u := Nat.land canonValid (Nat.mul x1_31 repFactor)
              let c3_u := Nat.land canonValid (Nat.mul x1_21 repFactor)
              seqNat c0_u (seqNat c1_u (seqNat c2_u (seqNat c3_u
                (k canonValid totalMask (RingColMasks.mk (Nat.sub u 1) c0_u c1_u c2_u c3_u :: rest))))))))

/-- Compute `canonValidMask` and `rings : List RingColMasks` for ring size `r = mMax + 1` in CPS. -/
def withRingColMasks {α : Type} [Inhabited α] (mMax : Nat) (k : Nat → List RingColMasks → α) : α :=
  let nSteps := Nat.sub mMax 2
  stepRow8 1 2 1 1 0 0 0 0 0 0
    (fun x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31 =>
      buildRingColLoop mMax nSteps 2 3
        x1_00 x1_01 x1_10 x1_11 x1_20 x1_21 x1_30 x1_31
        (fun canonValid _totalMask rings => k canonValid rings))

/-- Lookup `(c0, c1, c2, c3)` for ring vertex `u` in `rings`. -/
def lookupRingCols {α : Type} (u : Nat) (rings : List RingColMasks)
    (k : Nat → Nat → Nat → Nat → α) : α :=
  @List.rec RingColMasks (fun _ => α)
    (k 0 0 0 0)
    (fun h _ ih =>
      @RingColMasks.rec (fun _ => α)
        (fun hu c0 c1 c2 c3 =>
          selectBool (Nat.beq hu u) (k c0 c1 c2 c3) ih)
        h)
    rings

/-- Accumulate `(intMask, u0, u1, u2, u3)` for an interior vertex's `earlier` list in CPS. -/
def buildIntForbidAux {α : Type} [Inhabited α] (r : Nat) (rings : List RingColMasks) (us : List Nat)
    (k : Nat → Nat → Nat → Nat → Nat → α) : α :=
  @List.rec Nat (fun _ => Nat → Nat → Nat → Nat → Nat → α)
    (fun intMask u0 u1 u2 u3 => k intMask u0 u1 u2 u3)
    (fun u _ ih intMask u0 u1 u2 u3 =>
      selectBool (Nat.ble r u)
        (let nextInt := Nat.lor intMask (Nat.shiftLeft 1 u)
         ih nextInt u0 u1 u2 u3)
        (lookupRingCols u rings (fun c0 c1 c2 c3 =>
          let nu0 := Nat.lor u0 c0
          let nu1 := Nat.lor u1 c1
          let nu2 := Nat.lor u2 c2
          let nu3 := Nat.lor u3 c3
          ih intMask nu0 nu1 nu2 nu3)))
    us 0 0 0 0 0

/-- Build `List IntVertexStep` for D-reducibility in CPS. -/
def withIntStepsD {α : Type} [Inhabited α] (r canonValid : Nat) (rings : List RingColMasks)
    (rows : List (Array Nat)) (k : List IntVertexStep → α) : α :=
  @List.rec (Array Nat) (fun _ => Nat → (List IntVertexStep → α) → α)
    (fun _ k => k [])
    (fun row _ ih v k =>
      let nextV := Nat.succ v
      selectBool (Nat.ble r v)
        (let bitV := Nat.shiftLeft 1 v
         buildIntForbidAux r rings row.toList (fun intMask u0 u1 u2 u3 =>
           let f0 := Nat.xor canonValid u0
           let f1 := Nat.xor canonValid u1
           let f2 := Nat.xor canonValid u2
           let f3 := Nat.xor canonValid u3
           seqNat bitV (seqNat intMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
             (ih nextV (fun rest =>
               k (IntVertexStep.mk bitV 0 intMask f0 f1 f2 f3 :: rest))))))))))
        (ih nextV k))
    rows 0 k

/-- Try the first color branch in `dfsInterior`, exploiting the invariant `compat ⊆ rem` so no `Nat.land compat rem` is needed. -/
scoped macro "tryDfsBranch0" cMask:term:arg checkMask:term:arg reqMask:term:arg compat:term:arg rem:term:arg fMask:term:arg recCall:term:arg : term =>
  `(selectBool (Nat.beq (Nat.land $cMask $checkMask) $reqMask)
    (let nextCompat := Nat.land $compat $fMask
     selectBool (Nat.beq nextCompat 0)
       $rem
       ($recCall nextCompat))
    $rem)

/-- Try a subsequent color branch in `dfsInterior` without continuation duplication or `@Nat.rec` closures. -/
scoped macro "tryDfsBranch" cMask:term:arg checkMask:term:arg reqMask:term:arg compat:term:arg rem:term:arg fMask:term:arg recCall:term:arg : term =>
  `(selectBool (Nat.beq (Nat.land $cMask $checkMask) $reqMask)
    (let nextCompat := Nat.land (Nat.land $compat $rem) $fMask
     selectBool (Nat.beq nextCompat 0)
       $rem
       ($recCall nextCompat))
    $rem)

/-- Bit-parallel interior-first DFS threading `remCanon` (the mask of not-yet-extended ring colorings)
    and returning the updated `remCanon` with all extendable ring colorings cleared to 0.
    Invariant: `compat` is always a submask of `remCanon`. -/
def dfsInterior (steps : List IntVertexStep) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat :=
  @List.rec IntVertexStep (fun _ => Nat → Nat → Nat → Nat → Nat → Nat → Nat)
    (fun _c0 _c1 _c2 _c3 compat remCanon => Nat.xor remCanon compat)
    (fun step _ ih c0 c1 c2 c3 compat rem0 =>
      @IntVertexStep.rec (fun _ => Nat)
        (fun bitV reqMask checkMask f0 f1 f2 f3 =>
          let r1 :=
            tryDfsBranch0 c0 checkMask reqMask compat rem0 f0
              (fun next0 => ih (Nat.lor c0 bitV) c1 c2 c3 next0 rem0)
          let r2 :=
            tryDfsBranch c1 checkMask reqMask compat r1 f1
              (fun next1 => ih c0 (Nat.lor c1 bitV) c2 c3 next1 r1)
          let r3 :=
            tryDfsBranch c2 checkMask reqMask compat r2 f2
              (fun next2 => ih c0 c1 (Nat.lor c2 bitV) c3 next2 r2)
          tryDfsBranch c3 checkMask reqMask compat r3 f3
            (fun next3 => ih c0 c1 c2 (Nat.lor c3 bitV) next3 r3))
        step)
    steps

/-- Lookup `v` in an association list `alias : List (Nat × Nat)`, defaulting to `v`. -/
def getAlias (v : Nat) (alias : List (Nat × Nat)) : Nat :=
  @List.rec (Nat × Nat) (fun _ => Nat)
    v
    (fun h _ ih =>
      @Prod.rec Nat Nat (fun _ => Nat)
        (fun k val => selectBool (Nat.beq k v) val ih)
        h)
    alias

/-- Update key `k` to `mn` in `alias` only when `mn < getAlias k alias`, forcing `(k, mn)` via `seqNat`. -/
def withSetAliasMin {α : Type} [Inhabited α] (k mn : Nat) (alias : List (Nat × Nat))
    (cont : List (Nat × Nat) → α) : α :=
  let cur := getAlias k alias
  selectBool (Nat.blt mn cur)
    (seqNat k (seqNat mn (cont ((k, mn) :: alias))))
    (cont alias)

/-- Relax all `contractEdges` once across `alias` in CPS. -/
def withRelaxContractEdges {α : Type} [Inhabited α] (edges : List (Nat × Nat)) :
    List (Nat × Nat) → (List (Nat × Nat) → α) → α :=
  @List.rec (Nat × Nat) (fun _ => List (Nat × Nat) → (List (Nat × Nat) → α) → α)
    (fun al cont => cont al)
    (fun uv _ ih al cont =>
      @Prod.rec Nat Nat (fun _ => (List (Nat × Nat) → α) → α)
        (fun u v cont =>
          let ru := getAlias u al
          let rv := getAlias v al
          let mn := selectBool (Nat.ble ru rv) ru rv
          withSetAliasMin rv mn al (fun al1 =>
          withSetAliasMin ru mn al1 (fun al2 =>
          withSetAliasMin v mn al2 (fun al3 =>
          withSetAliasMin u mn al3 (fun al4 =>
            ih al4 cont)))))
        uv cont)
    edges

/-- Compute the transitive closure of `contractEdges` in CPS. -/
def withBuildAlias {α : Type} [Inhabited α] (edges : List (Nat × Nat))
    (cont : List (Nat × Nat) → α) : α :=
  @Nat.rec (fun _ => List (Nat × Nat) → (List (Nat × Nat) → α) → α)
    (fun al cont => cont al)
    (fun _ ih al cont =>
      withRelaxContractEdges edges al (fun nextAl => ih nextAl cont))
    4 [] cont

/-- Mask of canonical ring colorings where ring vertices `u` and `v` have the same color. -/
def sameRingColMask (u v : Nat) (rings : List RingColMasks) : Nat :=
  lookupRingCols u rings (fun uc0 uc1 uc2 uc3 =>
    lookupRingCols v rings (fun vc0 vc1 vc2 vc3 =>
      let m0 := Nat.land uc0 vc0
      let m1 := Nat.land uc1 vc1
      let m2 := Nat.land uc2 vc2
      let m3 := Nat.land uc3 vc3
      Nat.lor (Nat.lor m0 m1) (Nat.lor m2 m3)))

/-- Filter `ringCompat` across earlier ring neighbors `us` of ring vertex `v` (with rep `rv`). -/
def filterRingContractNbrs (v rv canonValid : Nat) (alias : List (Nat × Nat))
    (rings : List RingColMasks) (us : List Nat) (compat : Nat) : Nat :=
  @List.rec Nat (fun _ => Nat → Nat)
    (fun acc => acc)
    (fun u _ ih acc =>
      let ru := getAlias u alias
      selectBool (Nat.beq ru rv)
        0
        (let sameVU := sameRingColMask v u rings
         let diffVU := Nat.xor canonValid sameVU
         let nextAcc := Nat.land acc diffVU
         seqNat nextAcc (ih nextAcc)))
    us compat

/-- Accumulate `(intDiffMask, f0, f1, f2, f3)` for contracted interior vertex `v` (with rep `rv`). -/
def buildContractIntForbidAux {α : Type} [Inhabited α] (r rv canonValid : Nat)
    (alias : List (Nat × Nat)) (rings : List RingColMasks) (us : List Nat)
    (initF0 initF1 initF2 initF3 : Nat)
    (k : Nat → Nat → Nat → Nat → Nat → α) : α :=
  @List.rec Nat (fun _ => Nat → Nat → Nat → Nat → Nat → α)
    (fun intDiff f0 f1 f2 f3 => k intDiff f0 f1 f2 f3)
    (fun u _ ih intDiff f0 f1 f2 f3 =>
      let ru := getAlias u alias
      selectBool (Nat.beq ru rv)
        (ih intDiff f0 f1 f2 f3)
        (selectBool (Nat.ble r u)
          (let nextDiff := Nat.lor intDiff (Nat.shiftLeft 1 u)
           ih nextDiff f0 f1 f2 f3)
          (lookupRingCols u rings (fun uc0 uc1 uc2 uc3 =>
            let nf0 := Nat.land f0 (Nat.xor canonValid uc0)
            let nf1 := Nat.land f1 (Nat.xor canonValid uc1)
            let nf2 := Nat.land f2 (Nat.xor canonValid uc2)
            let nf3 := Nat.land f3 (Nat.xor canonValid uc3)
            ih intDiff nf0 nf1 nf2 nf3))))
    us 0 initF0 initF1 initF2 initF3

/-- Build `(ringCompat, List IntVertexStep)` for C-reducibility in CPS. -/
def withContractStepsC {α : Type} [Inhabited α] (r canonValid initCompat : Nat)
    (alias : List (Nat × Nat)) (rings : List RingColMasks) (rows : List (Array Nat))
    (k : Nat → List IntVertexStep → α) : α :=
  @List.rec (Array Nat) (fun _ => Nat → Nat → (Nat → List IntVertexStep → α) → α)
    (fun _ compat k => k compat [])
    (fun row _ ih v compat k =>
      let nextV := Nat.succ v
      let rv := getAlias v alias
      selectBool (Nat.blt v r)
        (let compat1 :=
          selectBool (Nat.blt rv v)
            (Nat.land compat (sameRingColMask v rv rings))
            compat
         let compat2 := filterRingContractNbrs v rv canonValid alias rings row.toList compat1
         seqNat compat2 (ih nextV compat2 k))
        (let bitV := Nat.shiftLeft 1 v
         let reqMask := selectBool (and (Nat.ble r rv) (Nat.blt rv v)) (Nat.shiftLeft 1 rv) 0
         let withInitF {β : Type} (kf : Nat → Nat → Nat → Nat → β) : β :=
           selectBool (Nat.blt rv r)
             (lookupRingCols rv rings kf)
             (kf canonValid canonValid canonValid canonValid)
         withInitF (fun i0 i1 i2 i3 =>
           buildContractIntForbidAux r rv canonValid alias rings row.toList i0 i1 i2 i3
             (fun intDiff f0 f1 f2 f3 =>
               let checkMask := Nat.lor reqMask intDiff
               seqNat bitV (seqNat reqMask (seqNat checkMask (seqNat f0 (seqNat f1 (seqNat f2 (seqNat f3
                 (ih nextV compat (fun finalCompat rest =>
                   k finalCompat
                     (IntVertexStep.mk bitV reqMask checkMask f0 f1 f2 f3 :: rest)))))))))))))
    rows 0 initCompat k

/-- Compute $3^{mMax-1}$-bit `L2` slice (`d_{mMax-1} = 0`) for D-reducibility of `c`. -/
def computeInitialLiveDWithRings (rVal canonValid : Nat) (rings : List RingColMasks)
    (swapSteps1 : List SwapStep) (c : RConf) : Nat :=
  let intSteps := (withIntStepsD rVal canonValid rings c.earlier.toList StrictBox.mk).val
  let canonLive := dfsInterior intSteps 0 0 0 0 canonValid canonValid
  seqNat canonLive
    (let s12 := swapDigits12 swapSteps1 canonLive
     Nat.lor canonLive s12)

/-- Compute $3^{mMax-1}$-bit `L2` slice for D-reducibility of `c` using `rVal, mMaxVal, swapSteps1`. -/
def computeInitialLiveD (rVal mMaxVal : Nat) (swapSteps1 : List SwapStep) (c : RConf) : Nat :=
  @Prod.rec _ _ (fun _ => _)
    (fun canonValid rings =>
      computeInitialLiveDWithRings rVal canonValid rings swapSteps1 c)
    (withRingColMasks mMaxVal Prod.mk)

/-- Compute `contractCanon` ($3^{mMax-1}$-bit canonical mask of colorings extendable to the contracted configuration) for `c`. -/
def computeContractCanonWithRings (rVal canonValid : Nat) (rings : List RingColMasks) (c : RConf) : Nat :=
  let al := (withBuildAlias c.contractEdges.toList StrictBox.mk).val
  @Prod.rec _ _ (fun _ => _)
    (fun ringCompat intStepsC =>
      seqNat ringCompat
        (let unextContract := dfsInterior intStepsC 0 0 0 0 ringCompat ringCompat
         let contractCanon := Nat.xor ringCompat unextContract
         seqNat contractCanon contractCanon))
    (withContractStepsC rVal canonValid canonValid al rings c.earlier.toList Prod.mk)

/-- Compute `contractCanon` for C-reducibility of `c` using `rVal, mMaxVal`. -/
def computeContractCanon (rVal mMaxVal : Nat) (c : RConf) : Nat :=
  @Prod.rec _ _ (fun _ => _)
    (fun canonValid rings =>
      computeContractCanonWithRings rVal canonValid rings c)
    (withRingColMasks mMaxVal Prod.mk)

/-- Compute `(L2_0, contractCanon)` ($3^{mMax-1}$-bit slices) for C-reducibility of `c`. -/
def computeInitialStateWithRings (rVal canonValid : Nat) (rings : List RingColMasks)
    (swapSteps1 : List SwapStep) (c : RConf) : Nat × Nat :=
  let al := (withBuildAlias c.contractEdges.toList StrictBox.mk).val
  let intStepsD := (withIntStepsD rVal canonValid rings c.earlier.toList StrictBox.mk).val
  let canonLive := dfsInterior intStepsD 0 0 0 0 canonValid canonValid
  seqNat canonLive
    (@Prod.rec _ _ (fun _ => _)
      (fun ringCompat intStepsC =>
        seqNat ringCompat
          (let unextContract := dfsInterior intStepsC 0 0 0 0 ringCompat ringCompat
           let contractCanon := Nat.xor ringCompat unextContract
           let s12 := swapDigits12 swapSteps1 canonLive
           let L2 := Nat.lor canonLive s12
           seqNat L2 (seqNat contractCanon (L2, contractCanon))))
      (withContractStepsC rVal canonValid canonLive al rings c.earlier.toList Prod.mk))

/-- Compute `(L2_0, contractCanon)` for C-reducibility of `c` using `rVal, mMaxVal, swapSteps1`. -/
def computeInitialState (rVal mMaxVal : Nat) (swapSteps1 : List SwapStep) (c : RConf) : Nat × Nat :=
  @Prod.rec _ _ (fun _ => _)
    (fun canonValid rings =>
      computeInitialStateWithRings rVal canonValid rings swapSteps1 c)
    (withRingColMasks mMaxVal Prod.mk)

/-- Perform one full round of Pascal-Catalan Kempe reduction directly on the $3^{mMax-1}$-bit `L2` slice (`d_{mMax-1} = 0`). -/
def kempeRound
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (L2 : Nat) : Nat :=
  let l2_01 := swapDigits01 swapSteps1 L2
  let l2_02 := swapDigits02 swapSteps1 L2
  let d0_1 := Nat.lor l2_01 (Nat.shiftLeft l2_02 pTop)
  let buckets := packToBuckets packLevels (L2 :: d0_1 :: [])
  let covBuckets := evalAllBuckets bucketSpecs buckets
  withUnpackFromBucketsPair unpackRevLevels covBuckets
    (fun u0 u1 =>
      let m0 := Nat.land L2 u0
      selectBool (Nat.beq m0 0) 0
        (let w1 := swapDigits01 swapSteps1 u1
         let m1 := Nat.land m0 w1
         selectBool (Nat.beq m1 0) 0
           (Nat.land m1 (swapDigits12 swapSteps1 m1))))
    0

/-- Advance `L2` by `steps` rounds of `kempeRound`. -/
def stepKempeRounds
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (steps : Nat) : Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat)
    (fun L2 => L2)
    (fun _ ih L2 =>
      let nextL2 := kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2
      seqNat nextL2 (ih nextL2))
    steps

/-- Run up to `fuel` rounds of Kempe reduction for D-reducibility (`contract == 0`) on `L2`. -/
def runDLiveLoop
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (fuel : Nat) : Nat → Bool :=
  @Nat.rec (fun _ => Nat → Bool)
    (fun L2 => Nat.beq L2 0)
    (fun _ ih L2 =>
      selectBool (Nat.beq L2 0)
        true
        (let nextL2 := kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2
         seqNat nextL2 (ih nextL2)))
    fuel

/-- Run up to `fuel` rounds of Kempe reduction for C-reducibility (`contract > 0`) on `L2`. -/
def runCLiveLoop
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (contractCanon : Nat) (fuel : Nat) : Nat → Bool :=
  @Nat.rec (fun _ => Nat → Bool)
    (fun L2 => Nat.beq (Nat.land L2 contractCanon) 0)
    (fun _ ih L2 =>
      selectBool (Nat.beq (Nat.land L2 contractCanon) 0)
        true
        (let nextL2 := kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2
         seqNat nextL2 (ih nextL2)))
    fuel

theorem runDLiveLoop_of_step
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (fuel L2 : Nat)
    (h : runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel
           (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2) = true) :
    runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs (Nat.succ fuel) L2 = true := by
  change selectBool (Nat.beq L2 0) true
    (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
      (runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel
        (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2))) = true
  rw [seqNat_eq]
  cases Nat.beq L2 0
  · exact h
  · rfl

theorem runDLiveLoop_of_steps
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec) :
    ∀ (steps fuel L2 : Nat),
      runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel
        (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps L2) = true →
      runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs (steps + fuel) L2 = true
  | 0, fuel, _, h => by
    rw [Nat.zero_add]
    exact h
  | Nat.succ steps, fuel, L2, h => by
    change runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel
      (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
        (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps
          (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2))) = true at h
    rw [seqNat_eq] at h
    rw [Nat.succ_add]
    exact runDLiveLoop_of_step pTop swapSteps1 packLevels unpackRevLevels bucketSpecs (steps + fuel) L2
      (runDLiveLoop_of_steps pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps fuel _ h)

theorem runCLiveLoop_of_step
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (contractCanon fuel L2 : Nat)
    (h : runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel
           (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2) = true) :
    runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon (Nat.succ fuel) L2 = true := by
  change selectBool (Nat.beq (Nat.land L2 contractCanon) 0) true
    (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
      (runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel
        (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2))) = true
  rw [seqNat_eq]
  cases Nat.beq (Nat.land L2 contractCanon) 0
  · exact h
  · rfl

theorem runCLiveLoop_of_steps
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (contractCanon : Nat) :
    ∀ (steps fuel L2 : Nat),
      runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel
        (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps L2) = true →
      runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon (steps + fuel) L2 = true
  | 0, fuel, _, h => by
    rw [Nat.zero_add]
    exact h
  | Nat.succ steps, fuel, L2, h => by
    change runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel
      (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
        (stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps
          (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2))) = true at h
    rw [seqNat_eq] at h
    rw [Nat.succ_add]
    exact runCLiveLoop_of_step pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon (steps + fuel) L2
      (runCLiveLoop_of_steps pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon steps fuel _ h)

/-- Bundled precomputed Pascal-Catalan Kempe engine for a given ring size `rVal`. -/
inductive KempeEngine where
  | mk (pTop : Nat)
       (swapSteps1 : List SwapStep)
       (packLevels : List (List PackCellSpec))
       (unpackRevLevels : List (List UnpackCellSpec))
       (bucketSpecs : List BucketCatalanSpec) : KempeEngine

def buildKempeEngine (rVal : Nat) : KempeEngine :=
  let mMaxVal := Nat.sub rVal 1
  let mMax1 := Nat.sub mMaxVal 1
  let pTop := pow3 mMax1
  let swapSteps1 := (buildSwapSteps mMax1).val
  @Prod.rec _ _ (fun _ => KempeEngine)
    (fun packLevels unpackRevLevels =>
      let bucketSpecs := (buildAllBucketSpecs rVal mMaxVal).val
      seqNat pTop (KempeEngine.mk pTop swapSteps1 packLevels unpackRevLevels bucketSpecs))
    (buildAllPackUnpackLevels mMaxVal)

def stepEngineRounds (ke : KempeEngine) (steps L2 : Nat) : Nat :=
  @KempeEngine.rec (fun _ => Nat)
    (fun pTop swapSteps1 packLevels unpackRevLevels bucketSpecs =>
      stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps L2)
    ke

def runEngineD (ke : KempeEngine) (fuel L2 : Nat) : Bool :=
  @KempeEngine.rec (fun _ => Bool)
    (fun pTop swapSteps1 packLevels unpackRevLevels bucketSpecs =>
      runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel L2)
    ke

def runEngineC (ke : KempeEngine) (contractCanon fuel L2 : Nat) : Bool :=
  @KempeEngine.rec (fun _ => Bool)
    (fun pTop swapSteps1 packLevels unpackRevLevels bucketSpecs =>
      runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel L2)
    ke

theorem runEngineD_of_step (ke : KempeEngine) (steps fuel L2 midL2 : Nat)
    (hStep : Nat.beq (stepEngineRounds ke steps L2) midL2 = true)
    (hRest : runEngineD ke fuel midL2 = true) :
    runEngineD ke (steps + fuel) L2 = true := by
  cases ke with
  | mk pTop swapSteps1 packLevels unpackRevLevels bucketSpecs =>
    have hEq : stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps L2 = midL2 :=
      Nat.beq_eq.mp hStep
    change runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel midL2 = true at hRest
    rw [← hEq] at hRest
    exact runDLiveLoop_of_steps pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps fuel L2 hRest

theorem runEngineC_of_step (ke : KempeEngine) (contractCanon steps fuel L2 midL2 : Nat)
    (hStep : Nat.beq (stepEngineRounds ke steps L2) midL2 = true)
    (hRest : runEngineC ke contractCanon fuel midL2 = true) :
    runEngineC ke contractCanon (steps + fuel) L2 = true := by
  cases ke with
  | mk pTop swapSteps1 packLevels unpackRevLevels bucketSpecs =>
    have hEq : stepKempeRounds pTop swapSteps1 packLevels unpackRevLevels bucketSpecs steps L2 = midL2 :=
      Nat.beq_eq.mp hStep
    change runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel midL2 = true at hRest
    rw [← hEq] at hRest
    exact runCLiveLoop_of_steps pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon steps fuel L2 hRest

/-- Phase 1 of batch verification: compute `(L2_0, contractCanon)` for each `c` in `cs`
    (with `contractCanon = 0` for D-reducible configurations) in reverse order. -/
def computeBatchInitRev
    (rVal canonValid : Nat) (rings : List RingColMasks) (swapSteps1 : List SwapStep) :
    List RConf → List (Nat × Nat) → StrictBox (List (Nat × Nat)) :=
  @List.rec RConf (fun _ => List (Nat × Nat) → StrictBox (List (Nat × Nat)))
    (fun acc => StrictBox.mk acc)
    (fun c _ ih acc =>
      selectBool (Nat.beq c.contract 0)
        (let live0 := computeInitialLiveDWithRings rVal canonValid rings swapSteps1 c
         selectBool (Nat.beq live0 0)
           (ih acc)
           (ih ((live0, 0) :: acc)))
        (@Prod.rec _ _ (fun _ => _)
          (fun live0 cc =>
            selectBool (Nat.beq (Nat.land live0 cc) 0)
              (ih acc)
              (ih ((live0, cc) :: acc)))
          (computeInitialStateWithRings rVal canonValid rings swapSteps1 c)))

/-- Phase 2 of batch verification: run Kempe reduction on each `(L2_0, contractCanon)` state. -/
def runBatchKempe
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec) :
    List (Nat × Nat) → Bool :=
  @List.rec (Nat × Nat) (fun _ => Bool)
    true
    (fun st _ ih =>
      @Prod.rec Nat Nat (fun _ => Bool)
        (fun live0 cc =>
          let ok :=
            selectBool (Nat.beq cc 0)
              (runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs 120 live0)
              (runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs cc 120 live0)
          andLazy ok ih)
        st)

/-- Verify a batch of configurations `cs` all sharing ring size `r` with a two-phase isolated engine build! -/
def verifyBatchSameR (r : Nat) (cs : List RConf) : Bool :=
  let rVal := r
  let mMaxVal := Nat.sub rVal 1
  let mMax1 := Nat.sub mMaxVal 1
  let pTop := pow3 mMax1
  let swapSteps1 := (buildSwapSteps mMax1).val
  let initStates :=
    (@Prod.rec _ _ (fun _ => _)
      (fun canonValid rings =>
        computeBatchInitRev rVal canonValid rings swapSteps1 cs [])
      (withRingColMasks mMaxVal Prod.mk)).val
  @Prod.rec _ _ (fun _ => _)
    (fun packLevels unpackRevLevels =>
      let bucketSpecs := (buildAllBucketSpecs rVal mMaxVal).val
      runBatchKempe pTop swapSteps1 packLevels unpackRevLevels bucketSpecs initStates)
    (buildAllPackUnpackLevels mMaxVal)

/-- Verify D-reducibility of configuration `c` using `eng`. -/
def verifyRConfD (eng : EngineMasks) (c : RConf) : Bool :=
  let rVal := eng.r
  let mMaxVal := eng.mMax
  let mMax1 := Nat.sub mMaxVal 1
  let swapSteps1 := (buildSwapSteps mMax1).val
  let live0 := computeInitialLiveD rVal mMaxVal swapSteps1 c
  selectBool (Nat.beq live0 0)
    true
    (runEngineD (buildKempeEngine rVal) 120 live0)

/-- Verify C-reducibility of configuration `c` using `eng`. -/
def verifyRConfC (eng : EngineMasks) (c : RConf) : Bool :=
  let rVal := eng.r
  let mMaxVal := eng.mMax
  let mMax1 := Nat.sub mMaxVal 1
  let swapSteps1 := (buildSwapSteps mMax1).val
  let live0 := computeInitialLiveD rVal mMaxVal swapSteps1 c
  let contractCanon := computeContractCanon rVal mMaxVal c
  selectBool (Nat.beq (Nat.land live0 contractCanon) 0)
    true
    (runEngineC (buildKempeEngine rVal) contractCanon 120 live0)

/-- Lookup configuration `idx` in `parsedRConfList` wrapped in `StrictBox` so the list is discarded upon lookup. -/
def getRConfBox (idx : Nat) : StrictBox RConf :=
  let rec go : List RConf → Nat → StrictBox RConf :=
    @List.rec RConf (fun _ => Nat → StrictBox RConf)
      (fun _ => StrictBox.mk rc_0)
      (fun h _ ih i =>
        @Nat.rec (fun _ => StrictBox RConf) (StrictBox.mk h) (fun i' _ => ih i') i)
  go parsedRConfList idx

/-- Lookup configuration `idx` in `parsedRConfList`. -/
def getRConf (idx : Nat) : RConf :=
  (getRConfBox idx).val

/-- Verify D-reducibility of configuration at index `idx` in `parsedRConfList`. -/
def verifyIdxD (idx : Nat) : Bool :=
  let c := (getRConfBox idx).val
  verifyRConfD (buildEngine c.r) c

/-- Verify C-reducibility of configuration at index `idx` in `parsedRConfList`. -/
def verifyIdxC (idx : Nat) : Bool :=
  let c := (getRConfBox idx).val
  verifyRConfC (buildEngine c.r) c

/-- Run up to `fuel` rounds of Kempe reduction for D-reducibility with early fixpoint exit (`nextL2 == L2`). -/
def runDLiveLoopFast
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (fuel : Nat) : Nat → Bool :=
  @Nat.rec (fun _ => Nat → Bool)
    (fun L2 => Nat.beq L2 0)
    (fun _ ih L2 =>
      selectBool (Nat.beq L2 0)
        true
        (let nextL2 := kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2
         seqNat nextL2
           (selectBool (Nat.beq nextL2 L2) false (ih nextL2))))
    fuel

def runEngineDFast (ke : KempeEngine) (fuel L2 : Nat) : Bool :=
  @KempeEngine.rec (fun _ => Bool)
    (fun pTop swapSteps1 packLevels unpackRevLevels bucketSpecs =>
      runDLiveLoopFast pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel L2)
    ke

/-- Verify D-reducibility of configuration at index `idx` with early fixpoint exit on non-D-reducible configs. -/
def verifyIdxDFast (idx : Nat) : Bool :=
  let c := (getRConfBox idx).val
  let rVal := c.r
  let mMaxVal := Nat.sub rVal 1
  let mMax1 := Nat.sub mMaxVal 1
  let swapSteps1 := (buildSwapSteps mMax1).val
  let live0 := computeInitialLiveD rVal mMaxVal swapSteps1 c
  selectBool (Nat.beq live0 0)
    true
    (runEngineDFast (buildKempeEngine rVal) 120 live0)

/-- Compute initial `L2` for configuration `idx`. -/
def initLiveIdx (idx : Nat) : Nat :=
  let c := (getRConfBox idx).val
  let rVal := c.r
  let mMaxVal := Nat.sub rVal 1
  let mMax1 := Nat.sub mMaxVal 1
  let swapSteps1 := (buildSwapSteps mMax1).val
  computeInitialLiveD rVal mMaxVal swapSteps1 c

/-- Compute `contractCanon` for configuration `idx`. -/
def contractCanonIdx (idx : Nat) : Nat :=
  let c := (getRConfBox idx).val
  let rVal := c.r
  let mMaxVal := Nat.sub rVal 1
  computeContractCanon rVal mMaxVal c

theorem land_zero_of_beq_zero {a b : Nat} (h : Nat.beq a 0 = true) :
    Nat.beq (Nat.land a b) 0 = true := by
  have ha : a = 0 := Nat.beq_eq.mp h
  subst ha
  have h0 : Nat.land 0 b = 0 := Nat.zero_and b
  rw [h0]
  rfl

theorem runCLiveLoop_of_D
    (pTop : Nat)
    (swapSteps1 : List SwapStep)
    (packLevels : List (List PackCellSpec))
    (unpackRevLevels : List (List UnpackCellSpec))
    (bucketSpecs : List BucketCatalanSpec)
    (contractCanon : Nat) :
    ∀ (fuel L2 : Nat),
      runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel L2 = true →
      runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel L2 = true
  | 0, _, h => land_zero_of_beq_zero h
  | Nat.succ fuel, L2, h => by
    change selectBool (Nat.beq L2 0) true
      (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
        (runDLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs fuel
          (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2))) = true at h
    rw [seqNat_eq] at h
    change selectBool (Nat.beq (Nat.land L2 contractCanon) 0) true
      (seqNat (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2)
        (runCLiveLoop pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel
          (kempeRound pTop swapSteps1 packLevels unpackRevLevels bucketSpecs L2))) = true
    rw [seqNat_eq]
    cases hZ : Nat.beq L2 0
    · rw [hZ] at h
      cases Nat.beq (Nat.land L2 contractCanon) 0
      · exact runCLiveLoop_of_D pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel _ h
      · rfl
    · rw [land_zero_of_beq_zero hZ]

theorem runEngineC_of_D (ke : KempeEngine) (contractCanon fuel L2 : Nat)
    (h : runEngineD ke fuel L2 = true) :
    runEngineC ke contractCanon fuel L2 = true := by
  cases ke with
  | mk pTop swapSteps1 packLevels unpackRevLevels bucketSpecs =>
    exact runCLiveLoop_of_D pTop swapSteps1 packLevels unpackRevLevels bucketSpecs contractCanon fuel L2 h

theorem verifyIdxC_of_D (idx : Nat) (h : verifyIdxD idx = true) : verifyIdxC idx = true := by
  change selectBool (Nat.beq (initLiveIdx idx) 0) true
    (runEngineD (buildKempeEngine (getRConfBox idx).val.r) 120 (initLiveIdx idx)) = true at h
  change selectBool (Nat.beq (Nat.land (initLiveIdx idx) (contractCanonIdx idx)) 0) true
    (runEngineC (buildKempeEngine (getRConfBox idx).val.r) (contractCanonIdx idx) 120 (initLiveIdx idx)) = true
  cases hZ : Nat.beq (initLiveIdx idx) 0
  · rw [hZ] at h
    cases Nat.beq (Nat.land (initLiveIdx idx) (contractCanonIdx idx)) 0
    · exact runEngineC_of_D (buildKempeEngine (getRConfBox idx).val.r) (contractCanonIdx idx) 120 (initLiveIdx idx) h
    · rfl
  · rw [land_zero_of_beq_zero hZ]

/-- Step 1 of a multi-stage verification: run `steps` Kempe rounds from `initLiveIdx idx` and compare against `l2Mid`. -/
def checkStepInit (idx steps l2Mid : Nat) : Bool :=
  let c := (getRConfBox idx).val
  Nat.beq (stepEngineRounds (buildKempeEngine c.r) steps (initLiveIdx idx)) l2Mid

/-- Middle step of a multi-stage verification: run `steps` Kempe rounds from `l2In` and compare against `l2Out`. -/
def checkStepMid (idx steps l2In l2Out : Nat) : Bool :=
  let c := (getRConfBox idx).val
  Nat.beq (stepEngineRounds (buildKempeEngine c.r) steps l2In) l2Out

/-- Final step of a multi-stage D-reducibility verification. -/
def checkStepFinalD (idx remFuel l2Mid : Nat) : Bool :=
  let c := (getRConfBox idx).val
  runEngineD (buildKempeEngine c.r) remFuel l2Mid

/-- Final step of a multi-stage C-reducibility verification. -/
def checkStepFinalC (idx remFuel l2Mid : Nat) : Bool :=
  let c := (getRConfBox idx).val
  runEngineC (buildKempeEngine c.r) (contractCanonIdx idx) remFuel l2Mid

theorem verifyIdxD_of_split2 (idx s1 remFuel m1 : Nat)
    (hFuel : s1 + remFuel = 120)
    (h1 : checkStepInit idx s1 m1 = true)
    (h2 : checkStepFinalD idx remFuel m1 = true) :
    verifyIdxD idx = true := by
  change @Bool.rec (fun _ => Bool)
    (runEngineD (buildKempeEngine (getRConfBox idx).val.r) 120 (initLiveIdx idx))
    true (Nat.beq (initLiveIdx idx) 0) = true
  cases Nat.beq (initLiveIdx idx) 0
  · rw [← hFuel]
    exact runEngineD_of_step (buildKempeEngine (getRConfBox idx).val.r) s1 remFuel
      (initLiveIdx idx) m1 h1 h2
  · rfl

theorem verifyIdxC_of_split2 (idx s1 remFuel m1 : Nat)
    (hFuel : s1 + remFuel = 120)
    (h1 : checkStepInit idx s1 m1 = true)
    (h2 : checkStepFinalC idx remFuel m1 = true) :
    verifyIdxC idx = true := by
  change @Bool.rec (fun _ => Bool)
    (runEngineC (buildKempeEngine (getRConfBox idx).val.r) (contractCanonIdx idx) 120 (initLiveIdx idx))
    true (Nat.beq (Nat.land (initLiveIdx idx) (contractCanonIdx idx)) 0) = true
  cases Nat.beq (Nat.land (initLiveIdx idx) (contractCanonIdx idx)) 0
  · rw [← hFuel]
    exact runEngineC_of_step (buildKempeEngine (getRConfBox idx).val.r) (contractCanonIdx idx) s1 remFuel
      (initLiveIdx idx) m1 h1 h2
  · rfl

theorem checkStepFinalD_of_mid (idx sMid remFuel mIn mOut : Nat)
    (hMid : checkStepMid idx sMid mIn mOut = true)
    (hFinal : checkStepFinalD idx remFuel mOut = true) :
    checkStepFinalD idx (sMid + remFuel) mIn = true :=
  runEngineD_of_step (buildKempeEngine (getRConfBox idx).val.r) sMid remFuel
    mIn mOut hMid hFinal

theorem checkStepFinalC_of_mid (idx sMid remFuel mIn mOut : Nat)
    (hMid : checkStepMid idx sMid mIn mOut = true)
    (hFinal : checkStepFinalC idx remFuel mOut = true) :
    checkStepFinalC idx (sMid + remFuel) mIn = true :=
  runEngineC_of_step (buildKempeEngine (getRConfBox idx).val.r) (contractCanonIdx idx) sMid remFuel
    mIn mOut hMid hFinal

/-- Map a list of configuration indices to `List RConf` using `@List.rec`. -/
def mapGetRConf : List Nat → List RConf :=
  @List.rec Nat (fun _ => List RConf)
    []
    (fun idx _ ih => getRConf idx :: ih)

/-- Verify a batch of configuration indices sharing ring size `r`. -/
def verifyBatchIndices (r : Nat) (indices : List Nat) : Bool :=
  verifyBatchSameR r (mapGetRConf indices)

def eng6 : EngineMasks := buildEngine 6
def eng7 : EngineMasks := buildEngine 7
def eng8 : EngineMasks := buildEngine 8
def eng9 : EngineMasks := buildEngine 9
def eng10 : EngineMasks := buildEngine 10
def eng11 : EngineMasks := buildEngine 11
def eng12 : EngineMasks := buildEngine 12
def eng13 : EngineMasks := buildEngine 13
def eng14 : EngineMasks := buildEngine 14

end

end KernelReducer
end Math
