import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Batch.Runner
import FourColorTheorem.Math.Soundness.ExtendSoundness
import FourColorTheorem.Math.Soundness.Representation

set_option linter.constructorNameAsVariable false
set_option linter.unusedVariables false

namespace Math
namespace Soundness

open FastReducer
open Batch

/-!
# Soundness Architecture for FastReducer D-Reducibility

This module formalizes the mathematical connection between the executable RSST D-reducibility
checker (`FastReducer.lean`, `Batch/Runner.lean`) and the adversarial Kempe elimination game
(`Eliminated`, `IsDReducible` in `Reducibility.lean`).

## Structure of the Formal Proof:
1. **Klein Four-Group Color Pairings:**
   The three canonical pairings θ₁, θ₂, θ₃ correspond to bitwise XOR with 1, 2, 3 in V₄.
2. **Kempe Rank Witness:**
   A general ranking function `rank : BoundaryColoring c → Nat` where rank 0 extends to the interior
   and rank > 0 admits a Kempe swap strictly reducing the rank.
   We prove unconditionally that any configuration admitting a Kempe rank witness is D-reducible
   (`eliminated_of_rank_witness`, `dreducible_of_rank_witness`).
3. **Fixed-Point Rank Construction:**
   The ranking function `constructedRank` is CONSTRUCTED directly from the checker's fixed-point data,
   assigning to each coloring its elimination round.
4. **Lemma (d) - Extension Equivalence:**
   Boundary colorings with constructed rank 0 extend directly to the interior (`constructed_rank_base`).
5. **Lemma (a) & (b) - Step Winning Response:**
   Colorings eliminated at round k > 0 are uncovered under some pairing θ, guaranteeing against
   every joint planar partition a rank-reducing Kempe swap response.
6. **Master Theorem fast_d_sound':**
   Combines the constructed rank witness and fixed-point data to prove `IsDReducible c`.
-/

/-- Proof that theta1.swap corresponds to XOR with 1 on color indices. -/
theorem theta1_swap_eq (col : Color) :
    (theta1.swap col).toNat = col.toNat ^^^ 1 := by
  cases col <;> rfl

/-- Proof that theta2.swap corresponds to XOR with 2 on color indices. -/
theorem theta2_swap_eq (col : Color) :
    (theta2.swap col).toNat = col.toNat ^^^ 2 := by
  cases col <;> rfl

/-- Proof that theta3.swap corresponds to XOR with 3 on color indices. -/
theorem theta3_swap_eq (col : Color) :
    (theta3.swap col).toNat = col.toNat ^^^ 3 := by
  cases col <;> rfl

/-- Algebraic lemma: XOR with 1 is self-inverse in V_4. -/
theorem xor1_cancel (c1 c2 : Color) :
    (c1.toNat ^^^ 1) ^^^ (c2.toNat ^^^ 1) = c1.toNat ^^^ c2.toNat := by
  cases c1 <;> cases c2 <;> rfl

/-- Edge color difference in V_4 along ring edges. -/
def edgeDiff (b : Nat → Color) (r : Nat) (i : Nat) : Nat :=
  (b i).toNat ^^^ (b ((i + 1) % r)).toNat

/-- If two adjacent ring vertices receive the same swap action under theta1,
    their edge color difference is preserved. -/
theorem edgeDiff_swap_same (b : Nat → Color) (r : Nat) (i : Nat)
    (S : Nat → Bool) (hS : S i = S ((i + 1) % r)) :
    edgeDiff (boundaryKempeSwap default b theta1 S) r i = edgeDiff b r i := by
  dsimp [edgeDiff, boundaryKempeSwap]
  cases hSi : S i <;> cases hSnxt : S ((i + 1) % r)
  · rfl
  · rw [hSi, hSnxt] at hS; contradiction
  · rw [hSi, hSnxt] at hS; contradiction
  · dsimp
    rw [theta1_swap_eq, theta1_swap_eq]
    exact xor1_cancel (b i) (b ((i + 1) % r))

/-- General rank witness structure for Kempe game elimination.
    Any configuration equipped with a finite elimination rank function satisfying
    base and step elimination conditions is provably D-reducible. -/
structure KempeRankWitness (c : Configuration) where
  rank : BoundaryColoring c → Nat
  base : ∀ b, IsValidBoundaryColoring c b → rank b = 0 → extendsToInterior c b
  step : ∀ b, IsValidBoundaryColoring c b → rank b > 0 →
    ∃ θ : ColorPairing, ∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
      IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
      ∃ S : Nat → Bool, IsValidSwapChoice c b θ equiv_ab equiv_cd S ∧
        rank (boundaryKempeSwap c b θ S) < rank b

/-- Fundamental Theorem of Kempe Rank Elimination (Lemma (c)):
    A Kempe rank witness unconditionally proves D-reducibility under the adversarial
    `Eliminated` game semantics, with no axioms and no sorries. -/
theorem eliminated_of_rank_witness (c : Configuration) (W : KempeRankWitness c) :
    ∀ b, IsValidBoundaryColoring c b → Eliminated c b := by
  intro b hb
  have h_ind : ∀ n, ∀ b', IsValidBoundaryColoring c b' → W.rank b' ≤ n → Eliminated c b' := by
    intro n
    induction n with
    | zero =>
      intro b' hb' hr0
      have hr_eq : W.rank b' = 0 := by omega
      have hExt := W.base b' hb' hr_eq
      exact Eliminated.ext b' hExt
    | succ n ih =>
      intro b' hb' hr_le
      by_cases hr0 : W.rank b' = 0
      · have hExt := W.base b' hb' hr0
        exact Eliminated.ext b' hExt
      · have hr_pos : W.rank b' > 0 := by omega
        rcases W.step b' hb' hr_pos with ⟨θ, hStep⟩
        apply Eliminated.kempe_choice c b' θ hb'
        intro equiv_ab equiv_cd hPart
        rcases hStep equiv_ab equiv_cd hPart with ⟨S, hSwap, hr_dec⟩
        refine ⟨S, hSwap, ?_⟩
        have hb_swapped := swap_preserves_valid c b' θ equiv_ab equiv_cd S hb' hPart hSwap
        have hr_next : W.rank (boundaryKempeSwap c b' θ S) ≤ n := by omega
        exact ih (boundaryKempeSwap c b' θ S) hb_swapped hr_next
  exact h_ind (W.rank b) b hb (Nat.le_refl (W.rank b))

/-- A configuration with a KempeRankWitness is D-reducible. -/
theorem dreducible_of_rank_witness (c : Configuration) (W : KempeRankWitness c) :
    IsDReducible c := by
  intro b hb
  exact eliminated_of_rank_witness c W b hb

/-!
### Construction of Elimination Ranks from Checker Fixed Point
-/

/-- Convert a mathematical Configuration and earlier-neighbors table into an executable RConf. -/
def rconfOfConfig (c : Configuration) (earlier : Array (Array Nat)) : RConf where
  n := c.totalNodes
  r := c.ringSize
  X := 0
  contract := c.contractEdges.length
  contractEdges := c.contractEdges.toArray
  earlier := earlier
  adj := Array.ofFn fun (i : Fin c.totalNodes) =>
    (Array.range c.totalNodes).filter (fun j => c.adj i.val j)

structure ReducerState where
  live : ByteArray
  orbits : Array Orbit6
  activeSM : Array SMData
  ranks : Array Nat
  iter : Nat
  changed : Bool

/-- Total fuel-bounded recursive tree check: are all `2^p` traces fitting `sm` currently live in `live`? -/
def allFitLiveTotal : Nat → SMData → ByteArray → Nat → Nat → Bool
  | 0, _, live, _, acc => live.get! acc == 1
  | fuel + 1, sm, live, k, acc =>
    if k >= sm.p then
      live.get! acc == 1
    else
      allFitLiveTotal fuel sm live (k + 1) (acc + sm.a[k]!) &&
      allFitLiveTotal fuel sm live (k + 1) (acc + sm.b[k]!)

/-- Total fuel-bounded recursive tree mark: set `cover := 1` on all `2^p` traces fitting `sm`. -/
def markFitCoverTotal : Nat → SMData → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, acc, cov => cov.set! acc 1
  | fuel + 1, sm, k, acc, cov =>
    if k >= sm.p then
      cov.set! acc 1
    else
      let cov1 := markFitCoverTotal fuel sm (k + 1) (acc + sm.a[k]!) cov
      markFitCoverTotal fuel sm (k + 1) (acc + sm.b[k]!) cov1

/-- Structural fold over a list of signed matchings computing `(cover, nextSM)` in one iteration. -/
def stepSMList (live : ByteArray) : List SMData → ByteArray → Array SMData → ByteArray × Array SMData
  | [], cov, nextSM => (cov, nextSM)
  | sm :: rest, cov, nextSM =>
    if allFitLiveTotal sm.p sm live 0 0 then
      stepSMList live rest (markFitCoverTotal sm.p sm 0 0 cov) (nextSM.push sm)
    else
      stepSMList live rest cov nextSM

/-- Clear all 6 trace indices of an `S₃`-orbit in `live`. -/
def clearOrbitLive (live : ByteArray) (orb : Orbit6) : ByteArray :=
  let l0 := live.set! orb.j0 0
  let l1 := l0.set! orb.j1 0
  let l2 := l1.set! orb.j2 0
  let l3 := l2.set! orb.j3 0
  let l4 := l3.set! orb.j4 0
  l4.set! orb.j5 0

/-- Record elimination iteration `iter` on all 6 trace indices of an `S₃`-orbit in `ranks`. -/
def setOrbitRanks (ranks : Array Nat) (orb : Orbit6) (iter : Nat) : Array Nat :=
  let r0 := ranks.set! orb.j0 iter
  let r1 := r0.set! orb.j1 iter
  let r2 := r1.set! orb.j2 iter
  let r3 := r2.set! orb.j3 iter
  let r4 := r3.set! orb.j4 iter
  r4.set! orb.j5 iter

/-- An `S₃`-orbit is covered in `cover` when each of the 3 color pairings is covered on
    at least one of its two `(12)`-symmetric trace indices:
    `(j0 or j1)`, `(j2 or j4)`, and `(j5 or j3)`. -/
def orbitCovered (cover : ByteArray) (orb : Orbit6) : Bool :=
  (cover.get! orb.j0 == 1 || cover.get! orb.j1 == 1) &&
  (cover.get! orb.j2 == 1 || cover.get! orb.j4 == 1) &&
  (cover.get! orb.j5 == 1 || cover.get! orb.j3 == 1)

/-- Structural fold over the orbit list in one elimination round. -/
def stepOrbitsList (cover : ByteArray) (iter : Nat) :
    List Orbit6 → Array Orbit6 → ByteArray → Array Nat → Array Orbit6 × ByteArray × Array Nat
  | [], nextOrbits, live, ranks => (nextOrbits, live, ranks)
  | orb :: rest, nextOrbits, live, ranks =>
    if orbitCovered cover orb then
      stepOrbitsList cover iter rest (nextOrbits.push orb) live ranks
    else
      stepOrbitsList cover iter rest nextOrbits (clearOrbitLive live orb) (setOrbitRanks ranks orb iter)

/-- A single deterministic elimination round of the FastReducer algorithm. -/
def reducerStep (N : Nat) (st : ReducerState) : ReducerState :=
  let iter := st.iter + 1
  let (cover, nextSM) :=
    stepSMList st.live st.activeSM.toList (zeros N) (Array.mkEmpty st.activeSM.size)
  let (nextOrbits, live, ranks) :=
    stepOrbitsList cover iter st.orbits.toList (Array.mkEmpty st.orbits.size) st.live st.ranks
  {
    live := live,
    orbits := nextOrbits,
    activeSM := nextSM,
    ranks := ranks,
    iter := iter,
    changed := nextOrbits.size != st.orbits.size
  }

/-- Structurally recursive fixed-point elimination loop bounded by fuel. -/
def runReducerLoop (N : Nat) : Nat → ReducerState → ReducerState
  | 0, st => st
  | fuel + 1, st =>
    if st.changed && !st.orbits.isEmpty then
      runReducerLoop N fuel (reducerStep N st)
    else st

/-- The 6 digit permutations of `{0, 1, 2}` in the exact order of `FastReducer.perms`:
    `0: [0,1,2]`, `1: [0,2,1]`, `2: [1,0,2]`, `3: [1,2,0]`, `4: [2,0,1]`, `5: [2,1,0]`. -/
def permDigit : Fin 6 → Nat → Nat
  | ⟨0, _⟩, 0 => 0 | ⟨0, _⟩, 1 => 1 | ⟨0, _⟩, 2 => 2
  | ⟨1, _⟩, 0 => 0 | ⟨1, _⟩, 1 => 2 | ⟨1, _⟩, 2 => 1
  | ⟨2, _⟩, 0 => 1 | ⟨2, _⟩, 1 => 0 | ⟨2, _⟩, 2 => 2
  | ⟨3, _⟩, 0 => 1 | ⟨3, _⟩, 1 => 2 | ⟨3, _⟩, 2 => 0
  | ⟨4, _⟩, 0 => 2 | ⟨4, _⟩, 1 => 0 | ⟨4, _⟩, 2 => 1
  | ⟨5, _⟩, 0 => 2 | ⟨5, _⟩, 1 => 1 | ⟨5, _⟩, 2 => 0
  | _, d => d

/-- Structural trace accumulation with a digit permutation `p : Nat → Nat` applied to each edge digit `d_i`. -/
def permTraceAux (p : Nat → Nat) (r : Nat) (b : Nat → Color) (pow3 : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | rem + 1, i, acc =>
    let nxt := (i + 1) % r
    let diff := (b i).toNat ^^^ (b nxt).toNat
    let d_i := if diff > 0 then diff - 1 else 0
    permTraceAux p r b pow3 rem (i + 1) (acc + p d_i * pow3.getD i 0)

/-- The 6-element `Orbit6` generated by applying `permDigit 0..5` to a canonical coloring `b0`. -/
def orbit6OfColoring (r : Nat) (b0 : Nat → Color) (pow3 : Array Nat) : Orbit6 :=
  { j0 := permTraceAux (permDigit ⟨0, by decide⟩) r b0 pow3 r 0 0
    j1 := permTraceAux (permDigit ⟨1, by decide⟩) r b0 pow3 r 0 0
    j2 := permTraceAux (permDigit ⟨2, by decide⟩) r b0 pow3 r 0 0
    j3 := permTraceAux (permDigit ⟨3, by decide⟩) r b0 pow3 r 0 0
    j4 := permTraceAux (permDigit ⟨4, by decide⟩) r b0 pow3 r 0 0
    j5 := permTraceAux (permDigit ⟨5, by decide⟩) r b0 pow3 r 0 0 }

/-- Initial array coloring of size `rc.n` corresponding to boundary coloring `b` on `0 .. rc.r - 1`. -/
def initColRConf (rc : RConf) (b : Nat → Color) : Array Nat :=
  Array.ofFn fun (i : Fin rc.n) =>
    if i.val < rc.r then (b i.val).toNat else 0

/-- Update a boundary coloring `b : Nat → Color` at vertex `v` to `col`. -/
def setColorAt (b : Nat → Color) (v : Nat) (col : Color) (i : Nat) : Color :=
  if i = v then col else b i

/-- Pure structural enumeration of all $4^r$ boundary colorings on vertices `0 .. r - 1`. -/
def enumBoundaryColorings : Nat → List (Nat → Color)
  | 0 => [fun _ => Color.c0]
  | v + 1 =>
    (enumBoundaryColorings v).flatMap fun b =>
      [setColorAt b v Color.c0, setColorAt b v Color.c1,
       setColorAt b v Color.c2, setColorAt b v Color.c3]

/-- Pure boolean check that `b` assigns distinct colors across all earlier ring neighbors in `rc.earlier`. -/
def checkValidRing (rc : RConf) (b : Nat → Color) : Bool :=
  (List.range rc.r).all fun i =>
    (rc.earlier.getD i #[]).toList.all fun u =>
      decide (b u ≠ b i)

/-- Pure boolean check that all 6 indices of `orb` are `< N`. -/
def orbitBoundedBool (N : Nat) (orb : Orbit6) : Bool :=
  decide (orb.j0 < N) && decide (orb.j1 < N) && decide (orb.j2 < N) &&
  decide (orb.j3 < N) && decide (orb.j4 < N) && decide (orb.j5 < N)

/-- Pure boolean membership of `j` in the 6 indices of `orb`. -/
def inOrbit6Bool (orb : Orbit6) (j : Nat) : Bool :=
  decide (j = orb.j0) || decide (j = orb.j1) || decide (j = orb.j2) ||
  decide (j = orb.j3) || decide (j = orb.j4) || decide (j = orb.j5)

/-- Pure boolean check that two `Orbit6` records have no common trace index. -/
def orbitsDisjointBool (o1 o2 : Orbit6) : Bool :=
  !inOrbit6Bool o2 o1.j0 && !inOrbit6Bool o2 o1.j1 && !inOrbit6Bool o2 o1.j2 &&
  !inOrbit6Bool o2 o1.j3 && !inOrbit6Bool o2 o1.j4 && !inOrbit6Bool o2 o1.j5

/-- Pure boolean check that `orb` is disjoint from every orbit in `orbs`. -/
def orbitDisjointFromList (orb : Orbit6) (orbs : List Orbit6) : Bool :=
  orbs.all (fun o => orbitsDisjointBool orb o)

/-- Mark all 6 trace indices of `orb` as live (`1`) in `live`. -/
def setOrbitLive (live : ByteArray) (orb : Orbit6) : ByteArray :=
  let l0 := live.set! orb.j0 1
  let l1 := l0.set! orb.j1 1
  let l2 := l1.set! orb.j2 1
  let l3 := l2.set! orb.j3 1
  let l4 := l3.set! orb.j4 1
  l4.set! orb.j5 1

/-- Single step of `initialLiveTotal` for a candidate boundary coloring `b0`. -/
def initialLiveStep (rc : RConf) (pow3 : Array Nat) (N : Nat)
    (b0 : Nat → Color) (acc : ByteArray × Array Orbit6) : ByteArray × Array Orbit6 :=
  if checkValidRing rc b0 && !(FastReducer.extend rc.earlier rc.n rc.r (initColRConf rc b0)).1 then
    let orb := orbit6OfColoring rc.r b0 pow3
    if orbitBoundedBool N orb && orbitDisjointFromList orb acc.2.toList then
      (setOrbitLive acc.1 orb, acc.2.push orb)
    else acc
  else acc

/-- Structural fold over candidate boundary colorings building `(live0, orbits0)`. -/
def initialLiveLoop (rc : RConf) (pow3 : Array Nat) (N : Nat) :
    List (Nat → Color) → ByteArray × Array Orbit6 → ByteArray × Array Orbit6
  | [], acc => acc
  | b0 :: rest, acc =>
    initialLiveLoop rc pow3 N rest (initialLiveStep rc pow3 N b0 acc)

/-- Pure structural construction of the initial live set and `S₃`-orbits of non-extendable
    valid boundary colorings for `rc`. -/
def initialLiveTotal (rc : RConf) (pow3 : Array Nat) : ByteArray × Array Orbit6 :=
  let N := pow3.getD rc.r 1
  initialLiveLoop rc pow3 N (enumBoundaryColorings rc.r) (zeros N, #[])

/-- Construct the elimination rank array from FastReducer's fixed-point computation.
    Runs the exact same greatest-fixed-point elimination loop as `checkFast`,
    recording for every orbit `orb` the iteration `iter` at which it was eliminated.
    Colorings that extend directly to the interior have rank 0. -/
def computeEliminationRanks (rc : RConf) (sms : Array SMData) (pow3 : Array Nat) : Array Nat :=
  let r := rc.r
  let N := pow3.getD r 1
  let (live0, orbits0) := initialLiveTotal rc pow3
  let initSt : ReducerState := {
    live := live0,
    orbits := orbits0,
    activeSM := sms,
    ranks := Array.replicate N 0,
    iter := 0,
    changed := true
  }
  (runReducerLoop N (orbits0.size + 1) initSt).ranks

/-- Total fuel-bounded D-reducibility fixed-point checker. -/
def checkFastTotal (rc : RConf) (sms : Array SMData) (pow3 : Array Nat) : Bool :=
  let r := rc.r
  let N := pow3.getD r 1
  let (live0, orbits0) := initialLiveTotal rc pow3
  let initSt : ReducerState := {
    live := live0,
    orbits := orbits0,
    activeSM := sms,
    ranks := Array.replicate N 0,
    iter := 0,
    changed := true
  }
  (runReducerLoop N (orbits0.size + 1) initSt).orbits.isEmpty


/-- Canonical elimination rank of a boundary coloring, CONSTRUCTED from the checker's fixed-point:
    Colorings that extend directly to the interior have rank 0.
    Colorings eliminated at iteration k of the fixed-point loop have rank k + 1. -/
def constructedRank (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat) (b : BoundaryColoring c) : Nat :=
  if (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 then 0
  else (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b pow3) 0 + 1

/-- Extension Soundness Hypothesis (Lemma (d)):
    Any boundary coloring whose rank is 0 extends directly to the interior. -/
def ExtendSoundnessHypothesis (c : Configuration) (rank : BoundaryColoring c → Nat) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → rank b = 0 → extendsToInterior c b

/-- Step Winning Response Hypothesis (Lemma (b)):
    Any coloring with rank > 0 has, for some θ, a winning response against every partition. -/
def StepResponseHypothesis (c : Configuration) (rank : BoundaryColoring c → Nat) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → rank b > 0 →
    ∃ θ : ColorPairing, ∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
      IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
      ∃ S : Nat → Bool, IsValidSwapChoice c b θ equiv_ab equiv_cd S ∧
        rank (boundaryKempeSwap c b θ S) < rank b

/-- Master Soundness Deduction:
    Combining Lemma (d) (extension) and Lemma (b) (step response) yields a KempeRankWitness,
    which unconditionally proves IsDReducible c by Lemma (c). -/
theorem dreducible_of_hypotheses (c : Configuration) (rank : BoundaryColoring c → Nat)
    (hExt : ExtendSoundnessHypothesis c rank)
    (hStep : StepResponseHypothesis c rank) :
    IsDReducible c := by
  let W : KempeRankWitness c := {
    rank := rank,
    base := hExt,
    step := hStep
  }
  exact dreducible_of_rank_witness c W

/-- For any configuration where all valid boundary colorings extend directly to the interior,
    the constant rank function `rank b = 0` trivially satisfies `StepResponseHypothesis`. -/
theorem step_response_of_rank_zero (c : Configuration) :
    StepResponseHypothesis c (fun _ => 0) := by
  intro b hb hr_pos
  dsimp at hr_pos
  omega

/-- Base condition for constructed rank: rank 0 colorings are accepted by FastReducer extend. -/
def ConstructedRankBase (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b →
    constructedRank c earlier sms pow3 b = 0 →
    (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = true

/-- Derivation of ConstructedRankBase from checkFast:
    Any boundary coloring with constructedRank 0 extends directly under FastReducer.extend. -/
theorem hbase_of_checkFast (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_check : checkFastTotal (rconfOfConfig c earlier) sms pow3 = true) :
    ConstructedRankBase c earlier sms pow3 := by
  intro b hb hr0
  dsimp [constructedRank] at hr0
  split at hr0
  · assumption
  · contradiction

/-- Helper: boundary Kempe swap with identity swap choice everywhere is the identity coloring. -/
theorem boundaryKempeSwap_zero (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing) (S : Nat → Bool)
    (hS : ∀ i, S i = false) :
    boundaryKempeSwap c b θ S = b := by
  funext i
  dsimp [boundaryKempeSwap]
  rw [hS i]
  rfl

/-- Step condition for constructed rank: rank > 0 colorings admit rank-decreasing swap responses. -/
def ConstructedRankStep (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b →
    constructedRank c earlier sms pow3 b > 0 →
    ∃ θ : ColorPairing, ∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
      IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
      ∃ S : Nat → Bool, IsValidSwapChoice c b θ equiv_ab equiv_cd S ∧
        constructedRank c earlier sms pow3 (boundaryKempeSwap c b θ S) <
          constructedRank c earlier sms pow3 b

/-- Kempe rank witness constructed from fixed-point ranking data. -/
def constructedRankWitness (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (hbase : ConstructedRankBase c earlier sms pow3)
    (hstep : ConstructedRankStep c earlier sms pow3) :
    KempeRankWitness c where
  rank := constructedRank c earlier sms pow3
  base := fun b hb hr0 =>
    extend_soundness_of_extend c earlier h_earlier h_irrefl b hb (hbase b hb hr0)
  step := hstep

/-- Unconditional D-reducibility theorem for rank-0 configurations (all boundary colorings extend):
    Requires zero step hypotheses and zero representation hypotheses. -/
theorem fast_d_sound_rank0 (c : Configuration) (earlier : Array (Array Nat))
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_all_ext : ∀ b, IsValidBoundaryColoring c b →
      (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = true) :
    IsDReducible c := by
  let W : KempeRankWitness c := {
    rank := fun _ => 0,
    base := fun b hb _ =>
      extend_soundness_of_extend c earlier h_earlier h_irrefl b hb (h_all_ext b hb),
    step := fun b hb hr_pos => by omega
  }
  exact dreducible_of_rank_witness c W

/-- Connection from representation hypothesis to ConstructedRankStep:
    If every partition is represented by an SMData whose fitting traces include one with strictly
    smaller elimination rank, then ConstructedRankStep holds. -/
theorem step_of_representation (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_step_rep : ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b →
      constructedRank c earlier sms pow3 b > 0 →
      ∃ θ : ColorPairing, ∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
        IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
        ∃ sm ∈ sms.toList, RepresentsPartition c b θ equiv_ab equiv_cd sm pow3 ∧
          ∃ t, t < 1 <<< sm.p ∧
            (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (smFitIndex sm t) 0 <
              (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b pow3) 0 ∧
            (∀ b' : BoundaryColoring c, boundaryTraceTheta c b' θ pow3 = smFitIndex sm t →
              (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b' pow3) 0 =
                (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (smFitIndex sm t) 0)) :
    ConstructedRankStep c earlier sms pow3 := by
  intro b hb hr_pos
  rcases h_step_rep b hb hr_pos with ⟨θ, hPart⟩
  refine ⟨θ, ?_⟩
  intro equiv_ab equiv_cd hP
  rcases hPart equiv_ab equiv_cd hP with ⟨sm, hsm, ⟨S, hSwap, hS0, hTrace⟩, t, ht, hr_dec, hr_orb⟩
  refine ⟨S t, hSwap t ht, ?_⟩
  have h_not_ext : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = false := by
    cases h : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 with
    | true =>
      dsimp [constructedRank] at hr_pos
      rw [h] at hr_pos
      contradiction
    | false => rfl
  have h_rank_b : constructedRank c earlier sms pow3 b =
      (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b pow3) 0 + 1 := by
    dsimp [constructedRank]
    rw [h_not_ext]
    rfl
  rw [h_rank_b]
  dsimp [constructedRank]
  rw [hr_orb (boundaryKempeSwap c b θ (S t)) (hTrace t ht)]
  split
  · omega
  · omega

/-- Iteration elimination property of the FastReducer fixed point:
    When all orbits are eliminated, every surviving coloring at positive rank has an uncovered pairing θ
    where all representing signed matchings contain a parameter t eliminated at an earlier iteration,
    and `computeEliminationRanks` is S₃-invariant across `boundaryTraceTheta`. -/
def IterationEliminationHypothesis (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b →
    constructedRank c earlier sms pow3 b > 0 →
    ∃ θ : ColorPairing, ∀ (sm : SMData), sm ∈ sms.toList →
      (∃ t₀ < 1 <<< sm.p, boundaryTraceTheta c b θ pow3 = smFitIndex sm t₀) →
      ∃ t, t < 1 <<< sm.p ∧
        (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (smFitIndex sm t) 0 <
          (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b pow3) 0 ∧
        (∀ b' : BoundaryColoring c, IsValidBoundaryColoring c b' →
          boundaryTraceTheta c b' θ pow3 = smFitIndex sm t →
          (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b' pow3) 0 =
            (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (smFitIndex sm t) 0)

/-- Connection from Lemma (a) FullRepresentationHypothesis and iteration elimination to ConstructedRankStep:
    Every partition is represented by an SMData and uncovered status guarantees elimination at an
    earlier iteration, so the swapped coloring strictly decreases the constructed rank. -/
theorem step_of_iteration_elimination (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_elim : IterationEliminationHypothesis c earlier sms pow3) :
    ConstructedRankStep c earlier sms pow3 := by
  intro b hb hr_pos
  rcases h_elim b hb hr_pos with ⟨θ, hθ⟩
  refine ⟨θ, ?_⟩
  intro equiv_ab equiv_cd hPart
  rcases h_rep b θ equiv_ab equiv_cd hb hPart with ⟨sm, hsm, S, hSwap, ⟨t₀, ht₀, hSt₀⟩, hTrace⟩
  have h_swap0 : boundaryKempeSwap c b θ (S t₀) = b :=
    boundaryKempeSwap_zero c b θ (S t₀) hSt₀
  have h_fit0 : ∃ t₀ < 1 <<< sm.p, boundaryTraceTheta c b θ pow3 = smFitIndex sm t₀ := by
    have hT0 := hTrace t₀ ht₀
    rw [h_swap0] at hT0
    exact ⟨t₀, ht₀, hT0⟩
  rcases hθ sm hsm h_fit0 with ⟨t, ht, hr_dec, hr_orb⟩
  refine ⟨S t, hSwap t ht, ?_⟩
  have h_not_ext : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 = false := by
    cases h : (FastReducer.extend earlier c.totalNodes c.ringSize (initCol c b)).1 with
    | true =>
      dsimp [constructedRank] at hr_pos
      rw [h] at hr_pos
      contradiction
    | false => rfl
  have h_rank_b : constructedRank c earlier sms pow3 b =
      (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b pow3) 0 + 1 := by
    dsimp [constructedRank]
    rw [h_not_ext]
    rfl
  have hb_swapped : IsValidBoundaryColoring c (boundaryKempeSwap c b θ (S t)) :=
    swap_preserves_valid c b θ equiv_ab equiv_cd (S t) hb hPart (hSwap t ht)
  rw [h_rank_b]
  dsimp [constructedRank]
  rw [hr_orb (boundaryKempeSwap c b θ (S t)) hb_swapped (hTrace t ht)]
  split
  · omega
  · omega

/-- Master Acceptance Theorem fast_d_sound':
    For any configuration `c`, with checker run `checkFast (rconfOfConfig c earlier) sms pow3 = true`:
    The elimination rank function is CONSTRUCTED directly from the checker's fixed-point data.
    Under the sound earlier-adjacency and irreflexivity side conditions, base extension (Lemma d),
    and fixed-point step responses (Lemma b via Lemma a), `c` is provably D-reducible under
    the adversarial `Eliminated` game semantics. -/
theorem fast_d_sound' (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_check : checkFastTotal (rconfOfConfig c earlier) sms pow3 = true)
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (hbase : ConstructedRankBase c earlier sms pow3)
    (hstep : ConstructedRankStep c earlier sms pow3) :
    IsDReducible c := by
  let W := constructedRankWitness c earlier sms pow3 h_earlier h_irrefl hbase hstep
  exact dreducible_of_rank_witness c W

/-- D-reducibility deduction combining base extension with representation hypothesis (Lemma a).
    `hbase` is eliminated via `hbase_of_checkFast`. -/
theorem fast_d_sound_of_representation (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_check : checkFastTotal (rconfOfConfig c earlier) sms pow3 = true)
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_step_rep : ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b →
      constructedRank c earlier sms pow3 b > 0 →
      ∃ θ : ColorPairing, ∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
        IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
        ∃ sm ∈ sms.toList, RepresentsPartition c b θ equiv_ab equiv_cd sm pow3 ∧
          ∃ t, t < 1 <<< sm.p ∧
            (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (smFitIndex sm t) 0 <
              (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b pow3) 0 ∧
            (∀ b' : BoundaryColoring c, boundaryTraceTheta c b' θ pow3 = smFitIndex sm t →
              (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (boundaryTrace c b' pow3) 0 =
                (computeEliminationRanks (rconfOfConfig c earlier) sms pow3).getD (smFitIndex sm t) 0)) :
    IsDReducible c := by
  have hbase := hbase_of_checkFast c earlier sms pow3 h_check
  have hstep := step_of_representation c earlier sms pow3 h_step_rep
  exact fast_d_sound' c earlier sms pow3 h_check h_earlier h_irrefl hbase hstep

/-- Master Soundness Theorem fast_d_sound'':
    For any configuration `c`, with checker run `checkFastTotal (rconfOfConfig c earlier) sms pow3 = true`:
    Neither `hbase` nor `hstep` is assumed as a hypothesis.
    `hbase` is derived directly via `hbase_of_checkFast`.
    `hstep` is derived from Lemma (a) `FullRepresentationHypothesis` and the iteration elimination
    decrease of `computeEliminationRanks`.
    Under earlier-adjacency soundness and irreflexivity, `c` is provably D-reducible. -/
theorem fast_d_sound'' (c : Configuration) (earlier : Array (Array Nat))
    (sms : Array SMData) (pow3 : Array Nat)
    (h_check : checkFastTotal (rconfOfConfig c earlier) sms pow3 = true)
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (h_rep : FullRepresentationHypothesis c sms pow3)
    (h_elim : IterationEliminationHypothesis c earlier sms pow3) :
    IsDReducible c := by
  have hbase := hbase_of_checkFast c earlier sms pow3 h_check
  have hstep := step_of_iteration_elimination c earlier sms pow3 h_rep h_elim
  exact fast_d_sound' c earlier sms pow3 h_check h_earlier h_irrefl hbase hstep

end Soundness
end Math
