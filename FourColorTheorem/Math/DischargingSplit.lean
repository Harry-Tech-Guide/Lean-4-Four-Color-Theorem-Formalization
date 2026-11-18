module

public import FourColorTheorem.Math.DischargingAlgo
public import FourColorTheorem.Math.KernelRfl

@[expose] public section

namespace Math.Discharging

noncomputable def dropListRec {a : Type} (n : Nat) (l0 : List a) : List a :=
  Nat.rec
    (motive := fun _ => List a → List a)
    (fun l => l)
    (fun _ ih l =>
      List.casesOn l
        []
        (fun _ xs => ih xs))
    n l0

noncomputable def hintStreamAt (chunks : List (List Nat)) (idx : Nat) : HintStream :=
  strictNat (Nat.shiftRight idx 8) fun chunkIdx =>
  strictNat (Nat.land idx 255) fun remIdx =>
  match dropListRec chunkIdx chunks with
  | [] => ([], [])
  | c :: cs =>
    match remIdx with
    | 0 => ([], c :: cs)
    | Nat.succ k => (dropListRec (Nat.succ k) c, cs)

def ptIsHubcapCons : ProofTree → Bool
  | ProofTree.hubcap (_ :: _ :: _) => true
  | _ => false

def ptHubcapHead : ProofTree → ProofTree
  | ProofTree.hubcap (m :: _) => ProofTree.hubcap [m]
  | t => t

def ptHubcapTail : ProofTree → ProofTree
  | ProofTree.hubcap (_ :: ms) => ProofTree.hubcap ms
  | t => t

theorem verifyHubcapMembersRec_cons_eq (deg : Nat) (st : Nat) (shiftedTable : List (List FastPosOut))
    (m : Nat × Nat × Int) (ms : List (Nat × Nat × Int)) (hs : HintStream) :
    verifyHubcapMembersRec deg st shiftedTable (m :: ms) hs =
      (let (ok, hs') := verifyHubcapMembersRec deg st shiftedTable [m] hs
       Bool.rec (false, hs') (verifyHubcapMembersRec deg st shiftedTable ms hs') ok) := by
  unfold verifyHubcapMembersRec
  dsimp only
  simp only [strictNat_eq]
  cases (checkBoundRec deg 20 st 500 []
    (Bool.rec (lookupListRec [] shiftedTable m.1)
      (appendFastPosOut (lookupListRec [] shiftedTable m.1) (lookupListRec [] shiftedTable m.2.1))
      (!Nat.beq m.1 m.2.1))
    [] (m.2.2 + 500).toNat hs) with
  | mk ok hs' =>
    cases ok <;> rfl

theorem verifyTreePureRec_hubcap_eq (deg : Nat) (shiftedTable : List (List FastPosOut))
    (members : List (Nat × Nat × Int)) (st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream) :
    verifyTreePureRec deg shiftedTable (ProofTree.hubcap members) st lineno lev condV condM syms hs =
      (let (ok, hs') := verifyHubcapMembersRec deg st shiftedTable members hs
       strictNat (Nat.add lineno 1) fun lineno' =>
       (ok, lineno', hs')) := rfl

theorem verifyTreePureRec_split_hubcap (deg : Nat) (shiftedTable : List (List FastPosOut))
    (t : ProofTree)
    (st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream)
    (lineno1 : Nat) (hs1 hs2 : HintStream)
    (hIsHub : ptIsHubcapCons t = true)
    (hHead : verifyTreePureRec deg shiftedTable (ptHubcapHead t) st lineno lev condV condM syms hs = (true, lineno1, hs1))
    (hTail : verifyTreePureRec deg shiftedTable (ptHubcapTail t) st lineno lev condV condM syms hs1 = (true, lineno1, hs2)) :
    verifyTreePureRec deg shiftedTable t st lineno lev condV condM syms hs = (true, lineno1, hs2) := by
  cases t with
  | cond _ _ _ _ => contradiction
  | sym _ _ _ _ => contradiction
  | reduce => contradiction
  | hubcap members =>
    cases members with
    | nil => contradiction
    | cons m ms =>
      dsimp [ptHubcapHead] at hHead
      dsimp [ptHubcapTail] at hTail
      rw [verifyTreePureRec_hubcap_eq] at hHead hTail ⊢
      simp only [strictNat_eq] at hHead hTail ⊢
      rw [verifyHubcapMembersRec_cons_eq]
      cases h1 : verifyHubcapMembersRec deg st shiftedTable [m] hs with
      | mk ok1 hs' =>
        rw [h1] at hHead
        dsimp only at hHead ⊢
        injection hHead with hOk1 hRest
        injection hRest with hLineno hHs1
        subst hOk1 hHs1
        exact hTail

structure CBState where
  fuel : Nat
  st : Nat
  forcedch : Nat
  maxch : Nat
  rem : List FastPosOut
  allowed : Nat
  neg : List FastPosOut
  excl : List FastPosOut

noncomputable def evalCBState (deg : Nat) (s : CBState) (hs : HintStream) : Bool × HintStream :=
  checkBoundLoopRec (checkBoundRec deg s.fuel) s.st s.forcedch s.maxch s.rem s.allowed s.neg s.excl hs

noncomputable def advanceCBState (steps : Nat) (s0 : CBState) : CBState :=
  Nat.rec
    (motive := fun _ => CBState → CBState)
    (fun s => s)
    (fun _ ih s =>
      match s.rem with
      | [] => s
      | po :: subRem =>
        Bool.rec
          (ih { s with rem := subRem, neg := po :: s.neg })
          (strictNat (Nat.sub s.allowed 1) fun allowed' =>
           ih { s with rem := subRem, allowed := allowed', excl := po :: s.excl })
          po.isPos)
    steps s0

noncomputable def evalCBPrefix (deg : Nat) (steps : Nat) (s0 : CBState) (hs0 : HintStream) : Bool × HintStream :=
  Nat.rec
    (motive := fun _ => CBState → HintStream → Bool × HintStream)
    (fun _ hs => (true, hs))
    (fun _ ih s hs =>
      match s.rem with
      | [] => (false, hs)
      | po :: subRem =>
        Bool.rec
          (ih { s with rem := subRem, neg := po :: s.neg } hs)
          (strictNat (narrowSWAR s.st po) fun st_next =>
           strictNat (Nat.add s.forcedch 1) fun forced_next =>
           let (okSub, hs') :=
             Bool.rec
               (true, hs)
               (checkBoundRec deg s.fuel st_next forced_next s.neg subRem s.excl s.maxch hs)
               (noExcludedForcedRec st_next s.excl)
           Bool.rec
             (false, hs')
             (strictNat (Nat.sub s.allowed 1) fun allowedch' =>
              Bool.rec
                (ih { s with rem := subRem, allowed := allowedch', excl := po :: s.excl } hs')
                (false, hs')
                (Nat.ble (Nat.add allowedch' s.forcedch) s.maxch))
             okSub)
          po.isPos)
    steps s0 hs0

theorem advanceCBState_zero (s : CBState) :
    advanceCBState 0 s = s := rfl

theorem advanceCBState_succ (k : Nat) (s : CBState) :
    advanceCBState (Nat.succ k) s =
      match s.rem with
      | [] => s
      | po :: subRem =>
        Bool.rec
          (advanceCBState k { s with rem := subRem, neg := po :: s.neg })
          (strictNat (Nat.sub s.allowed 1) fun allowed' =>
           advanceCBState k { s with rem := subRem, allowed := allowed', excl := po :: s.excl })
          po.isPos := rfl

theorem evalCBPrefix_zero (deg : Nat) (s : CBState) (hs : HintStream) :
    evalCBPrefix deg 0 s hs = (true, hs) := rfl

theorem evalCBPrefix_succ (deg k : Nat) (s : CBState) (hs : HintStream) :
    evalCBPrefix deg (Nat.succ k) s hs =
      match s.rem with
      | [] => (false, hs)
      | po :: subRem =>
        Bool.rec
          (evalCBPrefix deg k { s with rem := subRem, neg := po :: s.neg } hs)
          (strictNat (narrowSWAR s.st po) fun st_next =>
           strictNat (Nat.add s.forcedch 1) fun forced_next =>
           let (okSub, hs') :=
             Bool.rec
               (true, hs)
               (checkBoundRec deg s.fuel st_next forced_next s.neg subRem s.excl s.maxch hs)
               (noExcludedForcedRec st_next s.excl)
           Bool.rec
             (false, hs')
             (strictNat (Nat.sub s.allowed 1) fun allowedch' =>
              Bool.rec
                (evalCBPrefix deg k { s with rem := subRem, allowed := allowedch', excl := po :: s.excl } hs')
                (false, hs')
                (Nat.ble (Nat.add allowedch' s.forcedch) s.maxch))
             okSub)
          po.isPos := rfl

theorem checkBoundLoopRec_cons
    (cb : Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (st forcedch maxch : Nat) (po : FastPosOut) (subRem : List FastPosOut)
    (allowedch : Nat) (negBefore curExcluded : List FastPosOut) (hs : HintStream) :
    checkBoundLoopRec cb st forcedch maxch (po :: subRem) allowedch negBefore curExcluded hs =
      Bool.rec
        (checkBoundLoopRec cb st forcedch maxch subRem allowedch (po :: negBefore) curExcluded hs)
        (strictNat (narrowSWAR st po) fun st_next =>
         strictNat (Nat.add forcedch 1) fun forced_next =>
         let (okSub, hs') :=
           Bool.rec
             (true, hs)
             (cb st_next forced_next negBefore subRem curExcluded maxch hs)
             (noExcludedForcedRec st_next curExcluded)
         Bool.rec
           (false, hs')
           (strictNat (Nat.sub allowedch 1) fun allowedch' =>
            Bool.rec
              (checkBoundLoopRec cb st forcedch maxch subRem allowedch' negBefore (po :: curExcluded) hs')
              (true, hs')
              (Nat.ble (Nat.add allowedch' forcedch) maxch))
           okSub)
        po.isPos := rfl

theorem evalCBState_split_prefix (deg : Nat) (steps : Nat) (s : CBState) (hs hs1 hs2 : HintStream)
    (hPref : evalCBPrefix deg steps s hs = (true, hs1))
    (hRest : evalCBState deg (advanceCBState steps s) hs1 = (true, hs2)) :
    evalCBState deg s hs = (true, hs2) := by
  induction steps generalizing s hs with
  | zero =>
    rw [evalCBPrefix_zero] at hPref
    rw [advanceCBState_zero] at hRest
    injection hPref with _ hHs
    subst hHs
    exact hRest
  | succ k ih =>
    rw [evalCBPrefix_succ] at hPref
    rw [advanceCBState_succ] at hRest
    cases s with
    | mk fuel st forcedch maxch rem allowed neg excl =>
      cases rem with
      | nil =>
        dsimp only at hPref
        injection hPref with hFalse _
        cases hFalse
      | cons po subRem =>
        unfold evalCBState
        dsimp only at hPref hRest ⊢
        rw [checkBoundLoopRec_cons]
        cases hPos : po.isPos with
        | false =>
          rw [hPos] at hPref hRest
          dsimp only at hPref hRest ⊢
          exact ih { fuel := fuel, st := st, forcedch := forcedch, maxch := maxch, rem := subRem, allowed := allowed, neg := po :: neg, excl := excl } hs hPref hRest
        | true =>
          rw [hPos] at hPref hRest
          dsimp only at hPref hRest ⊢
          simp only [strictNat_eq] at hPref hRest ⊢
          cases hSub : Bool.rec (motive := fun _ => Bool × HintStream) (true, hs)
            (checkBoundRec deg fuel (narrowSWAR st po) (forcedch.add 1) neg subRem excl maxch hs)
            (noExcludedForcedRec (narrowSWAR st po) excl) with
          | mk okSub hs' =>
            rw [hSub] at hPref
            dsimp only at hPref ⊢
            cases okSub with
            | false =>
              dsimp only at hPref
              injection hPref with hFalse _
              cases hFalse
            | true =>
              dsimp only at hPref ⊢
              cases hBle : Nat.ble ((allowed.sub 1).add forcedch) maxch with
              | true =>
                rw [hBle] at hPref
                dsimp only at hPref
                injection hPref with hFalse _
                cases hFalse
              | false =>
                rw [hBle] at hPref
                dsimp only at hPref ⊢
                exact ih { fuel := fuel, st := st, forcedch := forcedch, maxch := maxch, rem := subRem, allowed := allowed.sub 1, neg := neg, excl := po :: excl } hs' hPref hRest

def ptIsSingleHubcap : ProofTree → Bool
  | ProofTree.hubcap [_] => true
  | _ => false

noncomputable def initCBState (shiftedTable : List (List FastPosOut)) (t : ProofTree) (st : Nat) : CBState :=
  match t with
  | ProofTree.hubcap (m :: _) =>
    let (x, y, v) := m
    let outsX := lookupListRec [] shiftedTable x
    let initRem :=
      Bool.rec
        outsX
        (appendFastPosOut outsX (lookupListRec [] shiftedTable y))
        (!Nat.beq x y)
    let maxchStrict := (v + 500).toNat
    let (forced1, nextNegBefore) := filterNegAPS st [] 500
    let (forcedch, allowedch, nextRem) := filterRemAPS st initRem forced1
    { fuel := 19
      st := st
      forcedch := forcedch
      maxch := maxchStrict
      rem := nextRem
      allowed := allowedch
      neg := nextNegBefore
      excl := [] }
  | _ =>
    { fuel := 0, st := 0, forcedch := 0, maxch := 0, rem := [], allowed := 0, neg := [], excl := [] }

theorem checkBoundRec_succ (deg fuel st forcedIn : Nat) (negBefore rem excluded : List FastPosOut)
    (maxch : Nat) (hs : HintStream) :
    checkBoundRec deg (Nat.succ fuel) st forcedIn negBefore rem excluded maxch hs =
      (let (forced1, nextNegBefore) := filterNegAPS st negBefore forcedIn
       let (forcedch, allowedch, nextRem) := filterRemAPS st rem forced1
       Bool.rec
         (Bool.rec
           (checkBoundLoopRec (checkBoundRec deg fuel) st forcedch maxch nextRem allowedch nextNegBefore excluded hs)
           (reduceAxleRec deg 64 [st] hs)
           (Nat.ble (Nat.add maxch 1) forcedch))
         (true, hs)
         (Nat.ble (Nat.add forcedch allowedch) maxch)) := rfl

theorem verifyTreePureRec_of_initCBState (deg : Nat) (shiftedTable : List (List FastPosOut))
    (t : ProofTree) (st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream)
    (lineno1 : Nat) (hs' : HintStream)
    (hSingle : ptIsSingleHubcap t = true)
    (hB1 : Nat.ble (Nat.add (initCBState shiftedTable t st).forcedch (initCBState shiftedTable t st).allowed) (initCBState shiftedTable t st).maxch = false)
    (hB2 : Nat.ble (Nat.add (initCBState shiftedTable t st).maxch 1) (initCBState shiftedTable t st).forcedch = false)
    (hLineno : Nat.add lineno 1 = lineno1)
    (hEval : evalCBState deg (initCBState shiftedTable t st) hs = (true, hs')) :
    verifyTreePureRec deg shiftedTable t st lineno lev condV condM syms hs = (true, lineno1, hs') := by
  cases t with
  | cond _ _ _ _ => contradiction
  | sym _ _ _ _ => contradiction
  | reduce => contradiction
  | hubcap members =>
    cases members with
    | nil => contradiction
    | cons m ms =>
      cases ms with
      | cons _ _ => contradiction
      | nil =>
        rw [verifyTreePureRec_hubcap_eq]
        unfold verifyHubcapMembersRec
        dsimp only
        simp only [strictNat_eq]
        rw [checkBoundRec_succ]
        dsimp only [initCBState] at hB1 hB2 hEval
        unfold evalCBState at hEval
        dsimp only at hB1 hB2 hEval ⊢
        rw [hB1, hB2]
        dsimp only
        rw [hEval, hLineno]

noncomputable def childCBState (s : CBState) : CBState :=
  match s.rem with
  | [] => s
  | po :: subRem =>
    strictNat (narrowSWAR s.st po) fun st_next =>
    strictNat (Nat.add s.forcedch 1) fun forced_next =>
    let (forced1, nextNegBefore) := filterNegAPS st_next s.neg forced_next
    let (forcedch, allowedch, nextRem) := filterRemAPS st_next subRem forced1
    { fuel := Nat.sub s.fuel 1
      st := st_next
      forcedch := forcedch
      maxch := s.maxch
      rem := nextRem
      allowed := allowedch
      neg := nextNegBefore
      excl := s.excl }

noncomputable def evalCBAfterChild (deg : Nat) (s : CBState) (hs1 : HintStream) : Bool × HintStream :=
  match s.rem with
  | [] => (false, hs1)
  | po :: subRem =>
    strictNat (Nat.sub s.allowed 1) fun allowedch' =>
    Bool.rec
      (evalCBState deg { s with rem := subRem, allowed := allowedch', excl := po :: s.excl } hs1)
      (true, hs1)
      (Nat.ble (Nat.add allowedch' s.forcedch) s.maxch)

theorem evalCBState_split_child (deg : Nat) (s : CBState) (hs hs1 hs2 : HintStream)
    (fuel' : Nat)
    (hFuel : s.fuel = Nat.succ fuel')
    (hPos : (match s.rem with | [] => false | po :: _ => po.isPos) = true)
    (hNoExcl : (match s.rem with | [] => false | po :: _ => noExcludedForcedRec (narrowSWAR s.st po) s.excl) = true)
    (hB1 : Nat.ble (Nat.add (childCBState s).forcedch (childCBState s).allowed) (childCBState s).maxch = false)
    (hB2 : Nat.ble (Nat.add (childCBState s).maxch 1) (childCBState s).forcedch = false)
    (hChild : evalCBState deg (childCBState s) hs = (true, hs1))
    (hAfter : evalCBAfterChild deg s hs1 = (true, hs2)) :
    evalCBState deg s hs = (true, hs2) := by
  cases s with
  | mk fuel st forcedch maxch rem allowed neg excl =>
    dsimp only at hFuel
    subst hFuel
    cases rem with
    | nil =>
      dsimp only at hPos
      cases hPos
    | cons po subRem =>
      dsimp only at hPos hNoExcl
      unfold evalCBState
      dsimp only
      rw [checkBoundLoopRec_cons]
      rw [hPos]
      dsimp only
      simp only [strictNat_eq]
      rw [hNoExcl]
      dsimp only
      rw [checkBoundRec_succ]
      dsimp only [childCBState] at hB1 hB2 hChild
      simp only [strictNat_eq] at hB1 hB2 hChild
      unfold evalCBState at hChild
      dsimp only at hB1 hB2 hChild ⊢
      have hSub1 : fuel'.succ.sub 1 = fuel' := rfl
      rw [hSub1] at hChild
      rw [hB1, hB2]
      dsimp only
      rw [hChild]
      dsimp only
      unfold evalCBAfterChild at hAfter
      dsimp only at hAfter
      simp only [strictNat_eq] at hAfter
      exact hAfter

theorem evalCBState_split_child_done (deg : Nat) (s : CBState) (hs hs1 : HintStream)
    (fuel' : Nat)
    (hFuel : s.fuel = Nat.succ fuel')
    (hPos : (match s.rem with | [] => false | po :: _ => po.isPos) = true)
    (hNoExcl : (match s.rem with | [] => false | po :: _ => noExcludedForcedRec (narrowSWAR s.st po) s.excl) = true)
    (hB1 : Nat.ble (Nat.add (childCBState s).forcedch (childCBState s).allowed) (childCBState s).maxch = false)
    (hB2 : Nat.ble (Nat.add (childCBState s).maxch 1) (childCBState s).forcedch = false)
    (hBle : Nat.ble (Nat.add (Nat.sub s.allowed 1) s.forcedch) s.maxch = true)
    (hChild : evalCBState deg (childCBState s) hs = (true, hs1)) :
    evalCBState deg s hs = (true, hs1) := by
  cases s with
  | mk fuel st forcedch maxch rem allowed neg excl =>
    dsimp only at hFuel hBle
    subst hFuel
    cases rem with
    | nil =>
      dsimp only at hPos
      cases hPos
    | cons po subRem =>
      dsimp only at hPos hNoExcl
      unfold evalCBState
      dsimp only
      rw [checkBoundLoopRec_cons]
      rw [hPos]
      dsimp only
      simp only [strictNat_eq]
      rw [hNoExcl]
      dsimp only
      rw [checkBoundRec_succ]
      dsimp only [childCBState] at hB1 hB2 hChild
      simp only [strictNat_eq] at hB1 hB2 hChild
      unfold evalCBState at hChild
      dsimp only at hB1 hB2 hChild ⊢
      have hSub1 : fuel'.succ.sub 1 = fuel' := rfl
      rw [hSub1] at hChild
      rw [hB1, hB2]
      dsimp only
      rw [hChild]
      dsimp only
      rw [hBle]

theorem evalCBState_split_child_cont (deg : Nat) (s : CBState) (hs hs1 hs2 : HintStream)
    (fuel' : Nat)
    (hFuel : s.fuel = Nat.succ fuel')
    (hPos : (match s.rem with | [] => false | po :: _ => po.isPos) = true)
    (hNoExcl : (match s.rem with | [] => false | po :: _ => noExcludedForcedRec (narrowSWAR s.st po) s.excl) = true)
    (hB1 : Nat.ble (Nat.add (childCBState s).forcedch (childCBState s).allowed) (childCBState s).maxch = false)
    (hB2 : Nat.ble (Nat.add (childCBState s).maxch 1) (childCBState s).forcedch = false)
    (hBle : Nat.ble (Nat.add (Nat.sub s.allowed 1) s.forcedch) s.maxch = false)
    (hChild : evalCBState deg (childCBState s) hs = (true, hs1))
    (hAfter : evalCBState deg (advanceCBState 1 s) hs1 = (true, hs2)) :
    evalCBState deg s hs = (true, hs2) := by
  cases s with
  | mk fuel st forcedch maxch rem allowed neg excl =>
    dsimp only at hFuel hBle
    subst hFuel
    cases rem with
    | nil =>
      dsimp only at hPos
      cases hPos
    | cons po subRem =>
      dsimp only at hPos hNoExcl
      unfold evalCBState
      dsimp only
      rw [checkBoundLoopRec_cons]
      rw [hPos]
      dsimp only
      simp only [strictNat_eq]
      rw [hNoExcl]
      dsimp only
      rw [checkBoundRec_succ]
      dsimp only [childCBState] at hB1 hB2 hChild
      simp only [strictNat_eq] at hB1 hB2 hChild
      unfold evalCBState at hChild
      dsimp only at hB1 hB2 hChild ⊢
      have hSub1 : fuel'.succ.sub 1 = fuel' := rfl
      rw [hSub1] at hChild
      rw [hB1, hB2]
      dsimp only
      rw [hChild]
      dsimp only
      rw [hBle]
      dsimp only
      rw [advanceCBState_succ] at hAfter
      dsimp only at hAfter
      rw [hPos] at hAfter
      dsimp only at hAfter
      simp only [strictNat_eq, advanceCBState_zero] at hAfter
      exact hAfter

end Math.Discharging
