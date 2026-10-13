import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# Optimized Batch Verification Runner for In-Kernel Reflection

This module implements an exact, mathematically equivalent optimization of the
RSST D-reducibility greatest-fixed-point reducer (`checkFast`) designed for
fast in-kernel evaluation via `native_decide`:

1. **Active Balanced Signed-Matching Compaction:** Only balanced signed matchings
   (`popcount ((full - 1) - s) % 2 == r % 2`) are generated, and dead signed matchings
   are compacted out of the active array at the end of each iteration rather than
   re-scanned across all iterations.
2. **Active S₃-Orbit Compaction:** `initialLiveFast` records the 6-element `S₃`-orbits
   `(j0, j1, j2, j3, j4, j5)` of non-extendable canonical traces. Each iteration scans
   only the remaining live orbits (checking `cover[j0]`, `cover[j2]`, `cover[j5]`),
   avoiding scanning all `3^r` traces and avoiding all base-3 division/modulo calls
   in `swapImages`.
-/

/-- A balanced signed matching with pre-selected index deltas `a` (bit = 0) and `b` (bit = 1)
    for each of its `p` matched pairs. -/
structure SMData where
  p : Nat
  a : Array Nat
  b : Array Nat

instance : Inhabited SMData := ⟨{ p := 0, a := #[], b := #[] }⟩

/-- Build all balanced signed non-crossing matchings for ring size `r`. -/
def buildSMData (r : Nat) (pow3 : Array Nat) : Array SMData := Id.run do
  let mut res : Array SMData := #[]
  for m in ncMatchings 0 r do
    let p := m.size
    let full := 1 <<< p
    let mut pa := #[]
    let mut pb := #[]
    let mut ma := #[]
    let mut mb := #[]
    for (x, y) in m do
      let px := pow3[x]!
      let py := pow3[y]!
      pa := pa.push (px + py)
      pb := pb.push (2 * px + 2 * py)
      ma := ma.push (px + 2 * py)
      mb := mb.push (2 * px + py)
    for s in [0:full] do
      if popcount ((full - 1) - s) % 2 == r % 2 then
        let mut a := #[]
        let mut b := #[]
        for k in [0:p] do
          if (s >>> k) &&& 1 == 1 then
            a := a.push pa[k]!
            b := b.push pb[k]!
          else
            a := a.push ma[k]!
            b := b.push mb[k]!
        res := res.push { p := p, a := a, b := b }
  return res

/-- Recursive tree check: are all `2^p` traces fitting `sm` currently live in `live`? -/
partial def allFitLive (sm : SMData) (live : ByteArray) (k acc : Nat) : Bool :=
  if k >= sm.p then
    live.get! acc == 1
  else
    allFitLive sm live (k + 1) (acc + sm.a[k]!) && allFitLive sm live (k + 1) (acc + sm.b[k]!)

/-- Recursive tree mark: set `cover := 1` on all `2^p` traces fitting `sm`. -/
partial def markFitCover (sm : SMData) (k acc : Nat) (cov : ByteArray) : ByteArray :=
  if k >= sm.p then
    cov.set! acc 1
  else
    let cov1 := markFitCover sm (k + 1) (acc + sm.a[k]!) cov
    markFitCover sm (k + 1) (acc + sm.b[k]!) cov1

/-- A 6-element `S₃`-orbit of trace codes for a canonical non-extendable colouring.
    `j0` = id, `j2` = swap₁₂, `j5` = swap₁₃. -/
structure Orbit6 where
  j0 : Nat
  j1 : Nat
  j2 : Nat
  j3 : Nat
  j4 : Nat
  j5 : Nat

instance : Inhabited Orbit6 := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

/-- Compute the initial live `ByteArray` and the array of live `S₃`-orbits. -/
def initialLiveFast (c : RConf) (pow3 : Array Nat) : ByteArray × Array Orbit6 := Id.run do
  let r := c.r
  let N := pow3[r]!
  let mut live := zeros N
  let mut orbits : Array Orbit6 := #[]
  let mut col : Array Nat := mkArray c.n 0
  let mut d : Array Nat := mkArray r 0
  for idx in [0:N] do
    let mut t := idx
    let mut x := 0
    for i in [0:r] do
      let di := t % 3
      d := d.set! i di
      x := x ^^^ (di + 1)
      t := t / 3
    if x != 0 then continue
    if d[0]! != 0 then continue
    let mut canon := true
    for i in [0:r] do
      let di := d[i]!
      if di == 1 then
        break
      if di == 2 then
        canon := false
        break
    if !canon then continue
    let mut cv := 0
    for i in [0:r] do
      col := col.set! i cv
      cv := cv ^^^ (d[i]! + 1)
    let (ok, col') := extend c.earlier c.n r col
    col := col'
    if !ok then
      let mut js : Array Nat := #[]
      for p in perms do
        let mut j := 0
        for i in [0:r] do
          j := j + p[d[i]!]! * pow3[i]!
        live := live.set! j 1
        js := js.push j
      orbits := orbits.push ⟨js[0]!, js[1]!, js[2]!, js[3]!, js[4]!, js[5]!⟩
  return (live, orbits)

/-- Fast exact D-reducibility checker using recursive tree traversal and active-set compaction. -/
def checkFast (c : RConf) (sms : Array SMData) (pow3 : Array Nat) : Bool := Id.run do
  let r := c.r
  let N := pow3[r]!
  let (live0, orbits0) := initialLiveFast c pow3
  let mut live := live0
  let mut orbits := orbits0
  let mut activeSM := sms
  let mut changed := true
  while changed && !orbits.isEmpty do
    let mut cover := zeros N
    let mut nextSM : Array SMData := Array.mkEmpty activeSM.size
    for sm in activeSM do
      if allFitLive sm live 0 0 then
        cover := markFitCover sm 0 0 cover
        nextSM := nextSM.push sm
    activeSM := nextSM
    let mut nextOrbits : Array Orbit6 := Array.mkEmpty orbits.size
    for orb in orbits do
      if cover.get! orb.j0 == 1 && cover.get! orb.j2 == 1 && cover.get! orb.j5 == 1 then
        nextOrbits := nextOrbits.push orb
      else
        live := live.set! orb.j0 0
        live := live.set! orb.j1 0
        live := live.set! orb.j2 0
        live := live.set! orb.j3 0
        live := live.set! orb.j4 0
        live := live.set! orb.j5 0
    changed := nextOrbits.size != orbits.size
    orbits := nextOrbits
  return orbits.isEmpty

/-- Precomputed powers of 3 up to 3^15. -/
def sharedPow3 : Array Nat := powers3 15

/-- Precomputed parsed array of all 633 RSST configurations. -/
def sharedCfgs : Array RConf := loadAll ()

/-- Check a single configuration index `idx` using a given signed-matching table `sms`. -/
def checkIdxFast (sms : Array SMData) (idx : Nat) : Bool :=
  checkFast sharedCfgs[idx]! sms sharedPow3

/-- Evaluate D-reducibility for a list of configuration indices sharing the same ring size `r`.
    Precomputes the balanced signed matching table `sms` once for the entire list. -/
def checkRingBatch (r : Nat) (indices : List Nat) : Bool :=
  let sms := buildSMData r sharedPow3
  indices.all (checkIdxFast sms)

/-- Soundness extraction lemma: if `checkRingBatch r indices = true`, then every `idx ∈ indices`
    is certified D-reducible by `checkFast`. -/
theorem certified_of_batch (r : Nat) (indices : List Nat)
    (hBatch : checkRingBatch r indices = true)
    (idx : Nat) (hMem : idx ∈ indices) :
    checkIdxFast (buildSMData r sharedPow3) idx = true :=
  List.all_eq_true.mp hBatch idx hMem

end Batch
end Math
