import FourColorTheorem.Math.U633String

/-!
# Fast native D-reducibility checker (RSST Kempe-chain consistency)

This is the executable checker used by `fourcolortheorem.exe`.

## Representation
A ring colouring is stored as its *edge trace* in the Klein four-group:
`e_i = c_i xor c_{i+1} ∈ {1,2,3}`, with `xor_i e_i = 0`. The trace determines the vertex
colouring up to the choice `c_0 = 0`. A trace is encoded as the base-3 number
`Σ (e_i - 1) * 3^i`, so the live set is a dense `ByteArray` of size `3^r`.

## Algorithm (RSST, "Reducibility in the Four-Color Theorem", §3)
* `C₀` = ring colourings that do **not** extend to the configuration.
* A set `C` is *consistent* if for every `κ ∈ C` and every `θ ∈ {1,2,3}` there is a balanced
  signed non-crossing matching `(M, μ)` such that `κ` θ-fits `(M, μ)` and **every** κ' that
  θ-fits `(M, μ)` lies in `C`.
* The configuration is D-reducible iff the maximal consistent subset of `C₀` is empty.
  We compute it as a greatest fixed point.

## Optimisations (all exact, no heuristics)
1. **Constructive fitting.** Instead of scanning all `3^r` colourings for every matching, the
   `2^p` colourings that θ-fit a signed matching with `p` pairs are generated directly.
2. **S₃ colour symmetry.** `GL(2,2) ≅ S₃` permutes `{1,2,3}` and is induced by a vertex-colour
   permutation fixing 0, so extendability is invariant. Only canonical traces are checked for
   extension, and the result is copied to the whole orbit (about 6× less backtracking).
   The live set therefore stays S₃-invariant throughout, so a signed matching is alive for θ
   iff it is alive for θ = 1, and `κ` is covered for θ = 2 (resp. 3) iff `swap₁₂ κ`
   (resp. `swap₁₃ κ`) is covered for θ = 1. We only enumerate θ = 1 (3× less work).
3. Dead signed matchings are never re-examined. Liveness is a monotone property.
4. The live set is a dense byte map, so membership is O(1).

The result for every configuration is cross-checked against the RSST data: a configuration
with an empty contract must be D-reducible, and the number of extendable colourings must
equal RSST's recorded count `X` (up to colour permutation).
-/

namespace Math
namespace FastReducer

/-- A configuration from `U_633`, parsed together with its RSST metadata. -/
structure RConf where
  n : Nat
  r : Nat
  X : Nat
  contract : Nat
  contractEdges : Array (Nat × Nat)
  earlier : Array (Array Nat)
  adj : Array (Array Nat)

instance : Inhabited RConf := ⟨{ n := 0, r := 0, X := 0, contract := 0, contractEdges := #[], earlier := #[], adj := #[] }⟩

/-- Split on whitespace and parse every natural-number token. -/
def parseNums (s : String) : Array Nat :=
  (s.split (fun ch => ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t')).foldl
    (fun acc w => match w.toNat? with
      | some k => acc.push k
      | none => acc) #[]

/-- Parse one RSST configuration block.
Format: `n r X Y a  e₁ … e_{2a}  (v deg nbr₁ … nbr_deg)ⁿ  coordinates…`. -/
def parseRConf (s : String) : RConf := Id.run do
  let nums := parseNums s
  if nums.size < 5 then return default
  let n := nums[0]!
  let r := nums[1]!
  let X := nums[2]!
  let a := nums[4]!
  let mut contractEdges : Array (Nat × Nat) := #[]
  for i in [0:a] do
    contractEdges := contractEdges.push (nums[5 + 2*i]! - 1, nums[5 + 2*i + 1]! - 1)
  let mut idx := 5 + 2 * a
  let mut adj : Array (Array Nat) := mkArray n #[]
  for _ in [0:n] do
    let v := nums[idx]! - 1
    let d := nums[idx + 1]!
    idx := idx + 2
    for k in [0:d] do
      let u := nums[idx + k]! - 1
      if u < n && v < n then
        adj := adj.modify v (·.push u)
    idx := idx + d
  let mut earlier : Array (Array Nat) := #[]
  for v in [0:n] do
    earlier := earlier.push (adj[v]!.filter (· < v))
  return { n := n, r := r, X := X, contract := a, contractEdges := contractEdges, earlier := earlier, adj := adj }

/-- All 633 configurations, parsed with the correct header offset. -/
def loadAll (_ : Unit) : Array RConf :=
  ((u633_data.split (· == '|')).filter (fun b => b.trim != "")).toArray.map parseRConf

/-- `ByteArray` of `n` zeros. -/
def zeros (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.mkEmpty n
  for _ in [0:n] do
    b := b.push 0
  return b

/-- `ByteArray` of `n` ones. -/
def ones (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.mkEmpty n
  for _ in [0:n] do
    b := b.push 1
  return b

def countOnes (b : ByteArray) : Nat := Id.run do
  let mut c := 0
  for i in [0:b.size] do
    if b.get! i == 1 then c := c + 1
  return c

def popcount (x : Nat) : Nat := Id.run do
  let mut k := x
  let mut c := 0
  while k > 0 do
    c := c + (k &&& 1)
    k := k >>> 1
  return c

/-- Check if color `c` is free among all earlier neighbors of a vertex. -/
def colorFree (nbrs : Array Nat) (col : Array Nat) (c : Nat) : Bool :=
  nbrs.data.all (fun x => col.getD x 0 != c)

/-- Backtracking: can vertices `v … n-1` be 4-coloured, given colours of `0 … v-1` in `col`? -/
def extend (earlier : Array (Array Nat)) (n v : Nat) (col : Array Nat) : Bool × Array Nat :=
  if h : v < n then
    let nbrs := earlier.getD v #[]
    let res0 := if colorFree nbrs col 0 then extend earlier n (v + 1) (col.set! v 0) else (false, col)
    if res0.1 then res0 else
    let res1 := if colorFree nbrs col 1 then extend earlier n (v + 1) (col.set! v 1) else (false, col)
    if res1.1 then res1 else
    let res2 := if colorFree nbrs col 2 then extend earlier n (v + 1) (col.set! v 2) else (false, col)
    if res2.1 then res2 else
    let res3 := if colorFree nbrs col 3 then extend earlier n (v + 1) (col.set! v 3) else (false, col)
    if res3.1 then res3 else
    (false, col)
  else
    (true, col)
termination_by n - v
decreasing_by
  all_goals
    change n - (v + 1) < n - v
    omega

/-- The six permutations of the edge-colour digits `{0,1,2}` (= colours `{1,2,3}`). -/
def perms : Array (Array Nat) :=
  #[#[0,1,2], #[0,2,1], #[1,0,2], #[1,2,0], #[2,0,1], #[2,1,0]]

/-- Live map of the non-extendable ring colourings (indexed by base-3 trace code), together
with the number of S₃-orbits of *extendable* colourings (compared against RSST's `X`). -/
def initialLive (c : RConf) (pow3 : Array Nat) : ByteArray × Nat := Id.run do
  let r := c.r
  let N := pow3[r]!
  let mut live := zeros N
  let mut extOrbits := 0
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
    -- canonical representative of the S₃-orbit: first edge colour 1, first other colour 2
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
    if ok then
      extOrbits := extOrbits + 1
    else
      for p in perms do
        let mut j := 0
        for i in [0:r] do
          j := j + p[d[i]!]! * pow3[i]!
        live := live.set! j 1
  return (live, extOrbits)

/-- All non-crossing partial matchings of the positions `lo … hi-1`. -/
partial def ncMatchings (lo hi : Nat) : Array (Array (Nat × Nat)) :=
  if lo ≥ hi then #[#[]] else Id.run do
    let mut res := ncMatchings (lo + 1) hi
    for k in [lo + 1 : hi] do
      let left := ncMatchings (lo + 1) k
      let right := ncMatchings (k + 1) hi
      for m1 in left do
        for m2 in right do
          res := res.push ((#[(lo, k)] ++ m1) ++ m2)
    return res

/-- Pre-computed index deltas of a matching for θ = 1 (colour digit 0 on unmatched edges).
For pair `k = (x, y)`:
* `pa`/`pb`: sign `+` (equal colours): both 2, or both 3.
* `ma`/`mb`: sign `-` (different colours): (2,3) or (3,2). -/
structure MData where
  p : Nat
  pa : Array Nat
  pb : Array Nat
  ma : Array Nat
  mb : Array Nat
  /-- Offset of this matching's `2^p` sign vectors in the global `alive` map. -/
  offset : Nat

instance : Inhabited MData := ⟨{ p := 0, pa := #[], pb := #[], ma := #[], mb := #[], offset := 0 }⟩

/-- Matching data for ring size `r`, plus the total size of the signed-matching map. -/
def buildMData (r : Nat) (pow3 : Array Nat) : Array MData × Nat := Id.run do
  let mut res : Array MData := #[]
  let mut off := 0
  for m in ncMatchings 0 r do
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
    res := res.push { p := m.size, pa := pa, pb := pb, ma := ma, mb := mb, offset := off }
    off := off + (1 <<< m.size)
  return (res, off)

/-- Code of the `t`-th colouring that θ₁-fits matching `m` with sign vector `s`
(bit `k` of `s` = 1 ↔ pair `k` has sign `+`). -/
@[inline] def fitIndex (m : MData) (s t : Nat) : Nat := Id.run do
  let mut j := 0
  for k in [0:m.p] do
    let plus := (s >>> k) &&& 1 == 1
    let first := (t >>> k) &&& 1 == 0
    j := j + (if plus then (if first then m.pa[k]! else m.pb[k]!)
              else (if first then m.ma[k]! else m.mb[k]!))
  return j

/-- Codes of the images of a trace under the colour swaps 1↔2 and 1↔3. -/
@[inline] def swapImages (idx r : Nat) (pow3 : Array Nat) : Nat × Nat := Id.run do
  let mut t := idx
  let mut a := 0
  let mut b := 0
  for i in [0:r] do
    let d := t % 3
    t := t / 3
    let p := pow3[i]!
    a := a + (if d == 0 then 1 else if d == 1 then 0 else 2) * p
    b := b + (if d == 0 then 2 else if d == 2 then 0 else 1) * p
  return (a, b)



partial def checkCReducible (earlier : Array (Array Nat)) (alias : Array Nat) (n r v : Nat) (col : Array Nat) (pow3 : Array Nat) (live : ByteArray) : Bool :=
  if v == r then Id.run do
    let mut idx := 0
    for i in [0:r] do
      let nxt := if i + 1 == r then 0 else i + 1
      let x := col[i]! ^^^ col[nxt]!
      if x == 0 then return true
      let d_i := x - 1
      idx := idx + d_i * pow3[i]!
    if live.get! idx == 0 then
      return true
    return checkCReducible earlier alias n r (v + 1) col pow3 live
  else if v >= n then
    false
  else Id.run do
    let root_v := alias[v]!
    if root_v < v then
      let c := col[root_v]!
      for u in earlier[v]! do
        if alias[u]! != root_v && col[u]! == c then
          return true
      let col := col.set! v c
      return checkCReducible earlier alias n r (v + 1) col pow3 live
    else
      let mut used : Nat := 0
      for u in earlier[v]! do
        if alias[u]! != root_v then
          used := used ||| (1 <<< col[u]!)
      let mut col := col
      for c in [0:4] do
        if (used >>> c) &&& 1 == 0 then
          col := col.set! v c
          if not (checkCReducible earlier alias n r (v + 1) col pow3 live) then
            return false
      return true

def runCReduction (c : RConf) (pow3 : Array Nat) (live : ByteArray) : Bool := Id.run do

  let mut alias := mkArray c.n 0
  for i in [0:c.n] do alias := alias.set! i i
  for _ in [0:c.n] do
    for (u, v) in c.contractEdges do
      let root_u := alias[u]!
      let root_v := alias[v]!
      let mn := min root_u root_v
      alias := alias.set! u mn
      alias := alias.set! v mn
      alias := alias.set! root_u mn
      alias := alias.set! root_v mn
  
  let col : Array Nat := mkArray c.n 0
  return checkCReducible c.earlier alias c.n c.r 1 col pow3 live

structure Result where
  ringColourings : Nat
  nonExtendable : Nat
  finalLive : Nat
  iterations : Nat
  dReducible : Bool
  xMatches : Bool
  cReducible : Bool


def powers3 (k : Nat) : Array Nat := Id.run do
  let mut a := #[]
  let mut p := 1
  for _ in [0:k+1] do
    a := a.push p
    p := p * 3
  return a

/-- Check that NO proper coloring of the contracted configuration restricts to a trace in `live`.
    Equivalently: every proper coloring of the contracted configuration extends to the original configuration! -/
partial def checkContractExact (earlier : Array (Array Nat)) (alias : Array Nat) (n r v : Nat)
    (col : Array Nat) (pow3 : Array Nat) (live : ByteArray) : Bool :=
  if v >= n then Id.run do
    let mut idx := 0
    for i in [0:r] do
      let nxt := if i + 1 == r then 0 else i + 1
      let x := col[i]! ^^^ col[nxt]!
      if x == 0 then return true
      let d_i := x - 1
      idx := idx + d_i * pow3[i]!
    if live.get! idx == 1 then
      return false
    return true
  else Id.run do
    let root_v := alias[v]!
    if root_v < v then
      let c := col[root_v]!
      for u in earlier[v]! do
        if alias[u]! != root_v && col[u]! == c then
          return true
      let col' := col.set! v c
      return checkContractExact earlier alias n r (v + 1) col' pow3 live
    else
      let mut used : Nat := 0
      for u in earlier[v]! do
        if alias[u]! != root_v then
          used := used ||| (1 <<< col[u]!)
      let mut col' := col
      for c in [0:4] do
        if (used >>> c) &&& 1 == 0 then
          col' := col'.set! v c
          if not (checkContractExact earlier alias n r (v + 1) col' pow3 live) then
            return false
      return true

/-- Test whether a configuration's contraction eliminates all remaining consistent live colorings. -/
def runContractCheck (c : RConf) (pow3 : Array Nat) (live : ByteArray) : Bool := Id.run do
  let mut alias := mkArray c.n 0
  for i in [0:c.n] do alias := alias.set! i i
  for _ in [0:c.n] do
    for (u, v) in c.contractEdges do
      let root_u := alias[u]!
      let root_v := alias[v]!
      let mn := min root_u root_v
      alias := alias.set! u mn
      alias := alias.set! v mn
      alias := alias.set! root_u mn
      alias := alias.set! root_v mn
  let col : Array Nat := mkArray c.n 0
  return checkContractExact c.earlier alias c.n c.r 1 col pow3 live

/-- Full reducibility check (D-reducibility and C-reducibility) of one configuration. -/
def check (c : RConf) (md : Array MData × Nat) (pow3 : Array Nat) : Result := Id.run do
  let r := c.r
  let N := pow3[r]!
  let (ms, totalSigned) := md
  let ringCols := if r % 2 == 0 then (N + 3) / 4 else (N - 3) / 4
  let (live0, extOrbits) := initialLive c pow3
  let mut live := live0
  let mut nlive := countOnes live
  let nonext := nlive
  let mut alive := ones totalSigned
  let mut iters := 0
  let mut changed := true
  while changed && nlive > 0 do
    iters := iters + 1
    let mut cover := zeros N
    for m in ms do
      let full := 1 <<< m.p
      for s in [0:full] do
        -- balanced: number of `-` pairs ≡ r (mod 2)
        if popcount ((full - 1) - s) % 2 == r % 2 then
          if alive.get! (m.offset + s) == 1 then
            let mut ok := true
            for t in [0:full] do
              if live.get! (fitIndex m s t) == 0 then
                ok := false
                break
            if ok then
              for t in [0:full] do
                cover := cover.set! (fitIndex m s t) 1
            else
              alive := alive.set! (m.offset + s) 0
    let mut cnt := 0
    for idx in [0:N] do
      if live.get! idx == 1 then
        let (i12, i13) := swapImages idx r pow3
        if cover.get! idx == 1 && cover.get! i12 == 1 && cover.get! i13 == 1 then
          cnt := cnt + 1
        else
          live := live.set! idx 0
    changed := cnt != nlive
    nlive := cnt
  let cRed := if nlive > 0 && c.contract > 0 then runContractCheck c pow3 live else false
  return { ringColourings := ringCols, nonExtendable := nonext, finalLive := nlive,
           iterations := iters, dReducible := nlive == 0,
           xMatches := extOrbits == c.X, cReducible := cRed }

end FastReducer
end Math
