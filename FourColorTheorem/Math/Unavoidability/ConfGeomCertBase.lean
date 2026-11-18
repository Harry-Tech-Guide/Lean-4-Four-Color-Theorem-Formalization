module

public import FourColorTheorem.Math.Unavoidability.FastConfEquiv

@[expose] public section

/-!
# Certified Configuration Geometric Checkers & Unpacking Lemmas (Stage R.1 Base)

Provides the executable boolean predicates (`checkPairGeom`, `checkListZipGeom`) and all
unpacking soundness theorems mapping `checkPairGeom (lookupFastConfRec h) parsedRConfList[h] = true`
to `IntRunShape`, `QStep` consistency, half-edge reciprocity, ring fans, facial-triangle
cliques, and RSST `(3.6)` `|X| = 4` triad witnesses.
-/

namespace Math.Unavoidability

open Math Math.Discharging Math.FastReducer

namespace GeomCert

def natContains (xs : List Nat) (v : Nat) : Bool :=
  match xs with
  | [] => false
  | x :: rest => if Nat.beq x v then true else natContains rest v

def natNodup : List Nat → Bool
  | [] => true
  | x :: xs => if natContains xs x then false else natNodup xs

def spanWhileGe (r : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
    if r ≤ x then
      let (p, rest) := spanWhileGe r xs
      (x :: p, rest)
    else ([], x :: xs)

def spanWhileLt (r : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
    if x < r then
      let (p, rest) := spanWhileLt r xs
      (x :: p, rest)
    else ([], x :: xs)

def cycHas (cps : List CycPair) (v w : Nat) : Bool :=
  match cps with
  | [] => false
  | cp :: rest => (Nat.beq cp.v v && Nat.beq cp.w w) || cycHas rest v w

def hasGapQStep (iv : IntVert) (x a : Nat) : List QStep → Bool
  | [] => false
  | q :: rest =>
    (Nat.beq q.v iv.u && Nat.beq q.z (x + 1) && Nat.beq q.u (a + 1) && cycHas iv.cyc (x + 1) (a + 1)) ||
    hasGapQStep iv x a rest

def checkRotShape (r : Nat) (adjL : List (List Nat)) (qs : List QStep) (iv : IntVert) (rot : List Nat) : Bool :=
  let (p1, rest1) := spanWhileGe r rot
  match rest1 with
  | [] => Nat.ble 5 p1.length
  | _ :: _ =>
    let (g1, rest2) := spanWhileLt r rest1
    match rest2 with
    | [] => Nat.ble 2 p1.length && Nat.ble 1 g1.length
    | _ :: _ =>
      let (p2, g2) := spanWhileGe r rest2
      match g1, g2, p1, p2 with
      | [x1], [x2], a1 :: _, a2 :: _ =>
        Nat.ble 2 p1.length && Nat.ble 2 p2.length &&
        !Nat.beq x1 x2 &&
        !natContains (Internal.listGetD [] adjL x1) x2 &&
        !natContains (Internal.listGetD [] adjL (Internal.listLastD 0 p1)) a2 &&
        !natContains (Internal.listGetD [] adjL (Internal.listLastD 0 p2)) a1 &&
        (hasGapQStep iv x1 a2 qs || hasGapQStep iv x2 a1 qs)
      | _, _, _, _ => false

def existsRot (r : Nat) (adjL : List (List Nat)) (qs : List QStep) (iv : IntVert) (nbrs : List Nat) : Nat → Bool
  | 0 => false
  | k + 1 =>
    let rot := nbrs.drop k ++ nbrs.take k
    if checkRotShape r adjL qs iv rot then true else existsRot r adjL qs iv nbrs k

def checkIntRunsList (r : Nat) (adjL : List (List Nat)) (qs : List QStep) : List IntVert → Bool
  | [] => true
  | iv :: rest =>
    let nbrs := Internal.listGetD [] adjL (iv.u - 1)
    existsRot r adjL qs iv nbrs nbrs.length && checkIntRunsList r adjL qs rest

def findIntVert? (u : Nat) : List IntVert → Option IntVert
  | [] => none
  | iv :: rest => if Nat.beq iv.u u then some iv else findIntVert? u rest

def checkQStepsAll (r : Nat) (ivs : List IntVert) : List QStep → Bool
  | [] => true
  | qs :: rest =>
    let okStep :=
      if Nat.blt r qs.v then
        match findIntVert? qs.v ivs with
        | none => false
        | some iv => cycHas iv.cyc qs.z qs.u
      else
        Nat.blt r qs.u &&
        match findIntVert? qs.u ivs with
        | none => false
        | some iv => cycHas iv.cyc qs.v qs.z
    okStep && checkQStepsAll r ivs rest

def checkIntCovered (cov : List Nat) : List IntVert → Bool
  | [] => true
  | iv :: rest => natContains cov iv.u && checkIntCovered cov rest

def checkQStepsGeom (fc : FastConf) : Bool :=
  let cov := fc.z0 :: fc.z1 :: fc.qSteps.map (·.z)
  natNodup cov && checkIntCovered cov fc.intVerts && checkQStepsAll fc.ring fc.intVerts fc.qSteps

def checkCycEntries (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) (iv : IntVert) : List CycPair → Bool
  | [] => true
  | cp :: rest =>
    let okV :=
      if Nat.blt r cp.v then
        match findIntVert? cp.v ivs with
        | none => false
        | some iv2 => cycHas iv2.cyc cp.w iv.u
      else true
    let okW :=
      if Nat.blt r cp.w then
        match findIntVert? cp.w ivs with
        | none => false
        | some iv2 => cycHas iv2.cyc iv.u cp.v
      else true
    let okTwoRing :=
      if Nat.ble cp.v r && Nat.ble cp.w r then
        let x := cp.v - 1
        let fans := ((Internal.listGetD [] adjL x).drop 1).dropLast
        Nat.beq (cp.w - 1) ((x + 1) % r) && fans.head? == some (iv.u - 1)
      else true
    okV && okW && okTwoRing && checkCycEntries r adjL ivs iv rest

def checkAllCycEntries (r : Nat) (adjL : List (List Nat)) (allIvs : List IntVert) : List IntVert → Bool
  | [] => true
  | iv :: rest => checkCycEntries r adjL allIvs iv iv.cyc && checkAllCycEntries r adjL allIvs rest

def checkConsecFans (x : Nat) (ivs : List IntVert) : List Nat → Bool
  | [] => true
  | [_] => true
  | uk :: uk1 :: rest =>
    let ok :=
      match findIntVert? (uk + 1) ivs, findIntVert? (uk1 + 1) ivs with
      | some ivk, some ivk1 =>
        cycHas ivk.cyc (uk1 + 1) (x + 1) &&
        cycHas ivk1.cyc (x + 1) (uk + 1)
      | _, _ => false
    ok && checkConsecFans x ivs (uk1 :: rest)

def checkFansForRing (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) : Nat → Bool
  | 0 => true
  | x + 1 =>
    let fans := ((Internal.listGetD [] adjL x).drop 1).dropLast
    let nextR := (x + 1) % r
    let prevR := (x + r - 1) % r
    let nextFans := ((Internal.listGetD [] adjL nextR).drop 1).dropLast
    let okEnd :=
      match fans with
      | [] => false
      | u1 :: _ =>
        let um := Internal.listLastD 0 fans
        nextFans.getLast? == some u1 &&
        (match findIntVert? (u1 + 1) ivs, findIntVert? (um + 1) ivs with
         | some iv1, some ivm =>
           cycHas iv1.cyc (x + 1) (nextR + 1) &&
           cycHas ivm.cyc (prevR + 1) (x + 1)
         | _, _ => false)
    okEnd && checkConsecFans x ivs fans && checkFansForRing r adjL ivs x

def cycUnord (cps : List CycPair) (x y : Nat) : Bool :=
  cycHas cps x y || cycHas cps y x

def checkTriForPair (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) (a b : Nat) : List Nat → Bool
  | [] => true
  | d :: rest =>
    let ok :=
      if Nat.blt b d && natContains (Internal.listGetD [] adjL b) d then
        (Nat.ble r a && match findIntVert? (a + 1) ivs with | some iv => cycUnord iv.cyc (b + 1) (d + 1) | none => false) ||
        (Nat.ble r b && match findIntVert? (b + 1) ivs with | some iv => cycUnord iv.cyc (a + 1) (d + 1) | none => false) ||
        (Nat.ble r d && match findIntVert? (d + 1) ivs with | some iv => cycUnord iv.cyc (a + 1) (b + 1) | none => false)
      else true
    ok && checkTriForPair r adjL ivs a b rest

def checkTriForVert (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) (a : Nat) (adjA : List Nat) : List Nat → Bool
  | [] => true
  | b :: rest =>
    (if Nat.blt a b then checkTriForPair r adjL ivs a b adjA else true) &&
    checkTriForVert r adjL ivs a adjA rest

def checkAllTriGo (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) : Nat → Bool
  | 0 => true
  | a + 1 =>
    let adjA := Internal.listGetD [] adjL a
    checkTriForVert r adjL ivs a adjA adjA && checkAllTriGo r adjL ivs a

def countNonCEIn (ce : List (Nat × Nat)) (vx : List Nat) (u : Nat) : List Nat → Nat
  | [] => 0
  | w :: rest =>
    (if natContains vx w && !isContractPair ce u w then 1 else 0) + countNonCEIn ce vx u rest

def existsTriad4Go (r : Nat) (adjL : List (List Nat)) (ce : List (Nat × Nat)) (vx : List Nat) : Nat → Bool
  | 0 => false
  | u + 1 =>
    let adjU := Internal.listGetD [] adjL u
    if Nat.ble r u && Nat.ble 3 (countNonCEIn ce vx u adjU) then true
    else existsTriad4Go r adjL ce vx u

def checkTriad4 (r n : Nat) (adjL : List (List Nat)) (ce : List (Nat × Nat)) : Bool :=
  if Nat.beq ce.length 4 then
    let vx := ce.flatMap (fun p => [p.1, p.2])
    existsTriad4Go r adjL ce vx n
  else true

def checkPairGeom (fc : FastConf) (rc : RConf) : Bool :=
  let r := rc.r
  let n := rc.n
  let ce := rc.contractEdges.toList
  let adjL := rc.adj.toList.map Array.toList
  Nat.beq fc.ring r && Nat.beq fc.nverts n && Nat.beq adjL.length n &&
  checkIntRunsList r adjL fc.qSteps fc.intVerts &&
  checkQStepsGeom fc &&
  checkAllCycEntries r adjL fc.intVerts fc.intVerts &&
  checkFansForRing r adjL fc.intVerts r &&
  checkAllTriGo r adjL fc.intVerts n &&
  checkTriad4 r n adjL ce

def checkListZipGeom : List FastConf → List RConf → Bool
  | [], _ => true
  | _, [] => true
  | fc :: fcs, rc :: rcs => checkPairGeom fc rc && checkListZipGeom fcs rcs

theorem checkListZipGeom_getElem :
    ∀ (fcs : List FastConf) (rcs : List RConf),
      checkListZipGeom fcs rcs = true →
      ∀ (k : Nat) (hk1 : k < fcs.length) (hk2 : k < rcs.length),
        checkPairGeom (fcs[k]'hk1) (rcs[k]'hk2) = true := by
  intro fcs
  induction fcs with
  | nil =>
    intro _ _ k hk1 _
    cases hk1
  | cons fc fcs ih =>
    intro rcs hz k hk1 hk2
    cases rcs with
    | nil => cases hk2
    | cons rc rcs =>
      unfold checkListZipGeom at hz
      obtain ⟨hhead, htail⟩ := Bool.and_eq_true _ _ |>.mp hz
      cases k with
      | zero => exact hhead
      | succ k' =>
        exact ih rcs htail k' (Nat.lt_of_succ_lt_succ hk1) (Nat.lt_of_succ_lt_succ hk2)

private theorem natContains_iff (xs : List Nat) (v : Nat) :
    natContains xs v = true ↔ v ∈ xs := by
  induction xs with
  | nil => simp [natContains]
  | cons x rest ih =>
    unfold natContains
    cases h : Nat.beq x v with
    | true =>
      have hxv : x = v := Nat.beq_eq.mp h
      subst hxv
      simp
    | false =>
      have hxv : x ≠ v := fun he => by subst he; simp at h
      have hvx : v ≠ x := fun he => hxv he.symm
      simp [ih, hvx]

private theorem natNodup_iff (xs : List Nat) :
    natNodup xs = true → xs.Nodup := by
  induction xs with
  | nil => intro _; exact List.nodup_nil
  | cons x xs ih =>
    unfold natNodup
    intro h
    cases hc : natContains xs x with
    | true => simp [hc] at h
    | false =>
      simp [hc] at h
      refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih h⟩
      have hct : natContains xs x = true := (natContains_iff xs x).mpr hmem
      rw [hc] at hct
      contradiction

private theorem cycHas_iff (cps : List CycPair) (v w : Nat) :
    cycHas cps v w = true ↔ { v := v, w := w : CycPair } ∈ cps := by
  induction cps with
  | nil => simp [cycHas]
  | cons cp rest ih =>
    unfold cycHas
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.mem_cons]
    constructor
    · intro h
      rcases h with ⟨hv, hw⟩ | hrest
      · left
        have hv' : cp.v = v := Nat.beq_eq.mp hv
        have hw' : cp.w = w := Nat.beq_eq.mp hw
        cases cp; simp_all
      · right; exact ih.mp hrest
    · intro h
      rcases h with rfl | hrest
      · left; simp
      · right; exact ih.mpr hrest

private theorem cycUnord_iff (cps : List CycPair) (v w : Nat) :
    cycUnord cps v w = true ↔
      ({ v := v, w := w : CycPair } ∈ cps ∨ { v := w, w := v : CycPair } ∈ cps) := by
  unfold cycUnord
  simp only [Bool.or_eq_true, cycHas_iff]

private theorem findIntVert?_spec (u : Nat) (ivs : List IntVert) {iv : IntVert}
    (h : findIntVert? u ivs = some iv) : iv ∈ ivs ∧ iv.u = u := by
  induction ivs with
  | nil => simp [findIntVert?] at h
  | cons a rest ih =>
    unfold findIntVert? at h
    cases hbeq : Nat.beq a.u u with
    | true =>
      simp only [hbeq] at h
      injection h with ha
      subst ha
      exact ⟨List.mem_cons_self, Nat.beq_eq.mp hbeq⟩
    | false =>
      simp only [hbeq] at h
      obtain ⟨hm, hu⟩ := ih h
      exact ⟨List.mem_cons_of_mem a hm, hu⟩

private theorem hasGapQStep_spec (iv : IntVert) (x a : Nat) (qs : List QStep)
    (h : hasGapQStep iv x a qs = true) :
    ∃ q ∈ qs, q.v = iv.u ∧ q.z = x + 1 ∧ q.u = a + 1 ∧ { v := x + 1, w := a + 1 : CycPair } ∈ iv.cyc := by
  induction qs with
  | nil => simp [hasGapQStep] at h
  | cons q rest ih =>
    unfold hasGapQStep at h
    rcases Bool.or_eq_true _ _ |>.mp h with hq | hrest
    · simp only [Bool.and_eq_true] at hq
      obtain ⟨⟨⟨hv, hz⟩, hu⟩, hcyc⟩ := hq
      exact ⟨q, List.mem_cons_self, Nat.beq_eq.mp hv, Nat.beq_eq.mp hz, Nat.beq_eq.mp hu, (cycHas_iff _ _ _).mp hcyc⟩
    · obtain ⟨q', hm, rest'⟩ := ih hrest
      exact ⟨q', List.mem_cons_of_mem q hm, rest'⟩

private theorem spanWhileGe_spec (r : Nat) (xs : List Nat) :
    (spanWhileGe r xs).1 ++ (spanWhileGe r xs).2 = xs ∧
    (∀ v ∈ (spanWhileGe r xs).1, r ≤ v) ∧
    (∀ v rest', (spanWhileGe r xs).2 = v :: rest' → v < r) := by
  induction xs with
  | nil =>
    simp [spanWhileGe]
  | cons x xs ih =>
    unfold spanWhileGe
    by_cases hr : r ≤ x
    · simp only [hr, ite_true]
      obtain ⟨happ, hge, hhead⟩ := ih
      refine ⟨?_, ?_, hhead⟩
      · simpa [List.cons_append] using congrArg (x :: ·) happ
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hmem
        · exact hr
        · exact hge v hmem
    · simp only [hr, ite_false]
      refine ⟨rfl, ?_, ?_⟩
      · intro _ hv; cases hv
      · intro v rest' heq
        injection heq with hv _
        subst hv
        omega

private theorem spanWhileLt_spec (r : Nat) (xs : List Nat) :
    (spanWhileLt r xs).1 ++ (spanWhileLt r xs).2 = xs ∧
    (∀ v ∈ (spanWhileLt r xs).1, v < r) ∧
    (∀ v rest', (spanWhileLt r xs).2 = v :: rest' → r ≤ v) := by
  induction xs with
  | nil =>
    simp [spanWhileLt]
  | cons x xs ih =>
    unfold spanWhileLt
    by_cases hr : x < r
    · simp only [hr, ite_true]
      obtain ⟨happ, hlt, hhead⟩ := ih
      refine ⟨?_, ?_, hhead⟩
      · simpa [List.cons_append] using congrArg (x :: ·) happ
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hmem
        · exact hr
        · exact hlt v hmem
    · simp only [hr, ite_false]
      refine ⟨rfl, ?_, ?_⟩
      · intro _ hv; cases hv
      · intro v rest' heq
        injection heq with hv _
        subst hv
        omega

private theorem listLastD_eq_getLast?_some {α : Type} (d : α) :
    ∀ (xs : List α) {b : α}, xs.getLast? = some b → Internal.listLastD d xs = b := by
  intro xs
  induction xs with
  | nil =>
    intro _ h; simp at h
  | cons x rest ih =>
    intro b h
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h
      rfl
    | cons y ys =>
      change Internal.listLastD d (y :: ys) = b
      have hsub : (y :: ys).getLast? = some b := by simpa using h
      exact ih hsub

private theorem list_nonempty_ends {α : Type} :
    ∀ (xs : List α), xs ≠ [] → ∃ a b, xs.head? = some a ∧ xs.getLast? = some b ∧ a ∈ xs ∧ b ∈ xs := by
  intro xs
  induction xs with
  | nil => intro h; exact absurd rfl h
  | cons x rest ih =>
    intro _
    cases rest with
    | nil => exact ⟨x, x, rfl, rfl, List.mem_cons_self, List.mem_cons_self⟩
    | cons y ys =>
      obtain ⟨_, b', _, hl, _, hb⟩ := ih (by simp)
      refine ⟨x, b', rfl, ?_, List.mem_cons_self, List.mem_cons_of_mem x hb⟩
      simpa using hl

private theorem existsRot_spec (r : Nat) (adjL : List (List Nat)) (qs : List QStep)
    (iv : IntVert) (nbrs : List Nat) :
    ∀ k : Nat, existsRot r adjL qs iv nbrs k = true →
      ∃ j < k, checkRotShape r adjL qs iv (nbrs.drop j ++ nbrs.take j) = true := by
  intro k
  induction k with
  | zero => intro h; simp [existsRot] at h
  | succ k ih =>
    intro h
    unfold existsRot at h
    cases hc : checkRotShape r adjL qs iv (nbrs.drop k ++ nbrs.take k) with
    | true => exact ⟨k, Nat.lt_succ_self k, hc⟩
    | false =>
      simp only [hc] at h
      obtain ⟨j, hj, hrot⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hrot⟩

private theorem checkIntRunsList_spec (r : Nat) (adjL : List (List Nat)) (qs : List QStep) :
    ∀ ivs : List IntVert, checkIntRunsList r adjL qs ivs = true →
      ∀ iv ∈ ivs,
        let nbrs := Internal.listGetD [] adjL (iv.u - 1)
        existsRot r adjL qs iv nbrs nbrs.length = true := by
  intro ivs
  induction ivs with
  | nil => intro _ iv hm; cases hm
  | cons a rest ih =>
    intro h iv hm
    unfold checkIntRunsList at h
    obtain ⟨ha, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
    rcases List.mem_cons.mp hm with rfl | htail
    · exact ha
    · exact ih hrest iv htail

private theorem checkIntCovered_spec (cov : List Nat) :
    ∀ ivs : List IntVert, checkIntCovered cov ivs = true →
      ∀ iv ∈ ivs, iv.u ∈ cov := by
  intro ivs
  induction ivs with
  | nil => intro _ iv hm; cases hm
  | cons a rest ih =>
    intro h iv hm
    unfold checkIntCovered at h
    obtain ⟨ha, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
    rcases List.mem_cons.mp hm with rfl | htail
    · exact (natContains_iff cov iv.u).mp ha
    · exact ih hrest iv htail

private theorem blt_eq_false (a b : Nat) (h : b ≤ a) : Nat.blt a b = false := by
  unfold Nat.blt
  cases hb : Nat.ble (a + 1) b with
  | false => rfl
  | true => have := Nat.ble_eq.mp hb; omega

private theorem checkQStepsAll_spec (r : Nat) (ivs : List IntVert) :
    ∀ qs : List QStep, checkQStepsAll r ivs qs = true →
      ∀ q ∈ qs,
        (r < q.v → ∃ iv ∈ ivs, iv.u = q.v ∧ { v := q.z, w := q.u : CycPair } ∈ iv.cyc) ∧
        (q.v ≤ r → r < q.u ∧ ∃ iv ∈ ivs, iv.u = q.u ∧ { v := q.v, w := q.z : CycPair } ∈ iv.cyc) := by
  intro qs
  induction qs with
  | nil => intro _ q hm; cases hm
  | cons q0 rest ih =>
    intro h q hm
    unfold checkQStepsAll at h
    obtain ⟨hq0, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
    rcases List.mem_cons.mp hm with rfl | htail
    · constructor
      · intro hlt
        rw [if_pos (Nat.blt_eq.mpr hlt)] at hq0
        cases hfind : findIntVert? q.v ivs with
        | none => rw [hfind] at hq0; contradiction
        | some iv =>
          rw [hfind] at hq0
          obtain ⟨hmem, hu⟩ := findIntVert?_spec q.v ivs hfind
          exact ⟨iv, hmem, hu, (cycHas_iff _ _ _).mp hq0⟩
      · intro hle
        rw [blt_eq_false r q.v hle] at hq0
        simp only [Bool.false_eq_true, ite_false] at hq0
        obtain ⟨hru, hmid⟩ := Bool.and_eq_true _ _ |>.mp hq0
        refine ⟨Nat.blt_eq.mp hru, ?_⟩
        cases hfind : findIntVert? q.u ivs with
        | none => rw [hfind] at hmid; contradiction
        | some iv =>
          rw [hfind] at hmid
          obtain ⟨hmem, hu⟩ := findIntVert?_spec q.u ivs hfind
          exact ⟨iv, hmem, hu, (cycHas_iff _ _ _).mp hmid⟩
    · exact ih hrest q htail

private theorem checkCycEntries_spec (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) (iv : IntVert) :
    ∀ cps : List CycPair, checkCycEntries r adjL ivs iv cps = true →
      ∀ cp ∈ cps,
        (r < cp.v → ∃ iv2 ∈ ivs, iv2.u = cp.v ∧ { v := cp.w, w := iv.u : CycPair } ∈ iv2.cyc) ∧
        (r < cp.w → ∃ iv2 ∈ ivs, iv2.u = cp.w ∧ { v := iv.u, w := cp.v : CycPair } ∈ iv2.cyc) ∧
        (cp.v ≤ r → cp.w ≤ r →
          cp.w - 1 = (cp.v - 1 + 1) % r ∧
          ((Internal.listGetD [] adjL (cp.v - 1)).drop 1).dropLast.head? = some (iv.u - 1)) := by
  intro cps
  induction cps with
  | nil => intro _ cp hm; cases hm
  | cons cp0 rest ih =>
    intro h cp hm
    unfold checkCycEntries at h
    have h1 := Bool.and_eq_true _ _ |>.mp h
    have h2 := Bool.and_eq_true _ _ |>.mp h1.1
    have h3 := Bool.and_eq_true _ _ |>.mp h2.1
    have hv := h3.1
    have hw := h3.2
    have h2r := h2.2
    have hrest := h1.2
    rcases List.mem_cons.mp hm with rfl | htail
    · refine ⟨?_, ?_, ?_⟩
      · intro hlt
        rw [if_pos (Nat.blt_eq.mpr hlt)] at hv
        cases hfind : findIntVert? cp.v ivs with
        | none => rw [hfind] at hv; contradiction
        | some iv2 =>
          rw [hfind] at hv
          obtain ⟨hmem, hu⟩ := findIntVert?_spec cp.v ivs hfind
          exact ⟨iv2, hmem, hu, (cycHas_iff _ _ _).mp hv⟩
      · intro hlt
        rw [if_pos (Nat.blt_eq.mpr hlt)] at hw
        cases hfind : findIntVert? cp.w ivs with
        | none => rw [hfind] at hw; contradiction
        | some iv2 =>
          rw [hfind] at hw
          obtain ⟨hmem, hu⟩ := findIntVert?_spec cp.w ivs hfind
          exact ⟨iv2, hmem, hu, (cycHas_iff _ _ _).mp hw⟩
      · intro hvle hwle
        have hbv : Nat.ble cp.v r = true := Nat.ble_eq.mpr hvle
        have hbw : Nat.ble cp.w r = true := Nat.ble_eq.mpr hwle
        rw [if_pos (Bool.and_eq_true _ _ |>.mpr ⟨hbv, hbw⟩)] at h2r
        obtain ⟨heqw, hhead⟩ := Bool.and_eq_true _ _ |>.mp h2r
        exact ⟨Nat.beq_eq.mp heqw, beq_iff_eq.mp hhead⟩
    · exact ih hrest cp htail

private theorem checkAllCycEntries_spec (r : Nat) (adjL : List (List Nat)) (allIvs : List IntVert) :
    ∀ ivs : List IntVert, checkAllCycEntries r adjL allIvs ivs = true →
      ∀ iv ∈ ivs, checkCycEntries r adjL allIvs iv iv.cyc = true := by
  intro ivs
  induction ivs with
  | nil => intro _ iv hm; cases hm
  | cons iv0 rest ih =>
    intro h iv hm
    unfold checkAllCycEntries at h
    obtain ⟨h0, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
    rcases List.mem_cons.mp hm with rfl | htail
    · exact h0
    · exact ih hrest iv htail

private theorem checkConsecFans_spec (x : Nat) (ivs : List IntVert) :
    ∀ fans : List Nat, checkConsecFans x ivs fans = true →
      ∀ k (hk : k + 1 < fans.length),
        ∃ ivk ∈ ivs, ∃ ivk1 ∈ ivs,
          ivk.u = fans[k] + 1 ∧ ivk1.u = fans[k + 1] + 1 ∧
          { v := fans[k + 1] + 1, w := x + 1 : CycPair } ∈ ivk.cyc ∧
          { v := x + 1, w := fans[k] + 1 : CycPair } ∈ ivk1.cyc := by
  intro fans
  induction fans with
  | nil => intro _ k hk; cases hk
  | cons uk tail ih =>
    intro h k hk
    cases tail with
    | nil => simp at hk
    | cons uk1 rest =>
      unfold checkConsecFans at h
      obtain ⟨hok, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
      cases k with
      | zero =>
        cases hf1 : findIntVert? (uk + 1) ivs with
        | none => rw [hf1] at hok; contradiction
        | some ivk =>
          cases hf2 : findIntVert? (uk1 + 1) ivs with
          | none => rw [hf1, hf2] at hok; contradiction
          | some ivk1 =>
            rw [hf1, hf2] at hok
            dsimp only at hok
            obtain ⟨h1, h2⟩ := Bool.and_eq_true _ _ |>.mp hok
            obtain ⟨hm1, hu1⟩ := findIntVert?_spec (uk + 1) ivs hf1
            obtain ⟨hm2, hu2⟩ := findIntVert?_spec (uk1 + 1) ivs hf2
            exact ⟨ivk, hm1, ivk1, hm2, hu1, hu2, (cycHas_iff _ _ _).mp h1, (cycHas_iff _ _ _).mp h2⟩
      | succ k' =>
        have hk' : k' + 1 < (uk1 :: rest).length := Nat.lt_of_succ_lt_succ hk
        exact ih hrest k' hk'

private theorem checkFansForRing_spec (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) :
    ∀ m : Nat, checkFansForRing r adjL ivs m = true →
      ∀ x, x < m →
        let fans := ((Internal.listGetD [] adjL x).drop 1).dropLast
        let nextR := (x + 1) % r
        let prevR := (x + r - 1) % r
        let nextFans := ((Internal.listGetD [] adjL nextR).drop 1).dropLast
        fans ≠ [] ∧
        nextFans.getLast? = fans.head? ∧
        (∀ u1, fans.head? = some u1 →
          ∃ iv1 ∈ ivs, iv1.u = u1 + 1 ∧ { v := x + 1, w := nextR + 1 : CycPair } ∈ iv1.cyc) ∧
        (∀ um, fans.getLast? = some um →
          ∃ ivm ∈ ivs, ivm.u = um + 1 ∧ { v := prevR + 1, w := x + 1 : CycPair } ∈ ivm.cyc) ∧
        (∀ k (hk : k + 1 < fans.length),
          ∃ ivk ∈ ivs, ∃ ivk1 ∈ ivs,
            ivk.u = fans[k] + 1 ∧ ivk1.u = fans[k + 1] + 1 ∧
            { v := fans[k + 1] + 1, w := x + 1 : CycPair } ∈ ivk.cyc ∧
            { v := x + 1, w := fans[k] + 1 : CycPair } ∈ ivk1.cyc) := by
  intro m
  induction m with
  | zero => intro _ x hx; cases hx
  | succ m ih =>
    intro h x hx
    unfold checkFansForRing at h
    have h1 := Bool.and_eq_true _ _ |>.mp h
    have h2 := Bool.and_eq_true _ _ |>.mp h1.1
    have hend := h2.1
    have hconsec := h2.2
    have hprev := h1.2
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hlt | rfl
    · exact ih hprev x hlt
    · dsimp only
      let fans := ((Internal.listGetD [] adjL x).drop 1).dropLast
      cases hfans : fans with
      | nil =>
        have hsub : (List.drop 1 (Internal.listGetD [] adjL x)).dropLast = [] := hfans
        rw [hsub] at hend
        contradiction
      | cons u1 fs =>
        have hsub : (List.drop 1 (Internal.listGetD [] adjL x)).dropLast = u1 :: fs := hfans
        rw [hsub] at hend
        obtain ⟨hnext, hmid⟩ := Bool.and_eq_true _ _ |>.mp hend
        have hne : (List.drop 1 (Internal.listGetD [] adjL x)).dropLast ≠ [] := fun he => by
          rw [hsub] at he; cases he
        refine ⟨hne, ?_, ?_, ?_, ?_⟩
        · rw [hsub, List.head?_cons]
          exact beq_iff_eq.mp hnext
        · intro u1' hu1'
          rw [hsub] at hu1'
          simp only [List.head?_cons, Option.some.injEq] at hu1'
          subst hu1'
          cases hf1 : findIntVert? (u1 + 1) ivs with
          | none => rw [hf1] at hmid; contradiction
          | some iv1 =>
            cases hfm : findIntVert? (Internal.listLastD 0 (u1 :: fs) + 1) ivs with
            | none => rw [hf1, hfm] at hmid; contradiction
            | some ivm =>
              rw [hf1, hfm] at hmid
              dsimp only at hmid
              obtain ⟨hc1, _⟩ := Bool.and_eq_true _ _ |>.mp hmid
              obtain ⟨hm1, hv1⟩ := findIntVert?_spec (u1 + 1) ivs hf1
              exact ⟨iv1, hm1, hv1, (cycHas_iff _ _ _).mp hc1⟩
        · intro um hum
          rw [hsub] at hum
          have hlast : Internal.listLastD 0 (u1 :: fs) = um := listLastD_eq_getLast?_some 0 (u1 :: fs) hum
          rw [hlast] at hmid
          cases hf1 : findIntVert? (u1 + 1) ivs with
          | none => rw [hf1] at hmid; contradiction
          | some iv1 =>
            cases hfm : findIntVert? (um + 1) ivs with
            | none => rw [hf1, hfm] at hmid; contradiction
            | some ivm =>
              rw [hf1, hfm] at hmid
              dsimp only at hmid
              obtain ⟨_, hcm⟩ := Bool.and_eq_true _ _ |>.mp hmid
              obtain ⟨hmm, hvm⟩ := findIntVert?_spec (um + 1) ivs hfm
              exact ⟨ivm, hmm, hvm, (cycHas_iff _ _ _).mp hcm⟩
        · have hf_consec : checkConsecFans x ivs (List.drop 1 (Internal.listGetD [] adjL x)).dropLast = true := hconsec
          exact checkConsecFans_spec x ivs _ hf_consec

private theorem checkTriForPair_spec (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) (a b : Nat) :
    ∀ ds : List Nat, checkTriForPair r adjL ivs a b ds = true →
      ∀ d ∈ ds, b < d → d ∈ Internal.listGetD [] adjL b →
        (∃ iv ∈ ivs,
          (iv.u = a + 1 ∧ ({ v := b + 1, w := d + 1 : CycPair } ∈ iv.cyc ∨ { v := d + 1, w := b + 1 : CycPair } ∈ iv.cyc)) ∨
          (iv.u = b + 1 ∧ ({ v := a + 1, w := d + 1 : CycPair } ∈ iv.cyc ∨ { v := d + 1, w := a + 1 : CycPair } ∈ iv.cyc)) ∨
          (iv.u = d + 1 ∧ ({ v := a + 1, w := b + 1 : CycPair } ∈ iv.cyc ∨ { v := b + 1, w := a + 1 : CycPair } ∈ iv.cyc))) := by
  intro ds
  induction ds with
  | nil => intro _ d hm _ _; cases hm
  | cons d0 rest ih =>
    intro h d hm hbd hnb
    unfold checkTriForPair at h
    obtain ⟨hd0, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
    rcases List.mem_cons.mp hm with rfl | htail
    · have hblt : Nat.blt b d = true := Nat.blt_eq.mpr hbd
      have hct : natContains (Internal.listGetD [] adjL b) d = true := (natContains_iff _ _).mpr hnb
      rw [if_pos (Bool.and_eq_true _ _ |>.mpr ⟨hblt, hct⟩)] at hd0
      rcases Bool.or_eq_true _ _ |>.mp hd0 with hab | hc
      · rcases Bool.or_eq_true _ _ |>.mp hab with ha | hb
        · obtain ⟨_, hfa⟩ := Bool.and_eq_true _ _ |>.mp ha
          cases hfind : findIntVert? (a + 1) ivs with
          | none => rw [hfind] at hfa; contradiction
          | some iv =>
            rw [hfind] at hfa
            obtain ⟨hmem, hu⟩ := findIntVert?_spec (a + 1) ivs hfind
            exact ⟨iv, hmem, Or.inl ⟨hu, (cycUnord_iff _ _ _).mp hfa⟩⟩
        · obtain ⟨_, hfb⟩ := Bool.and_eq_true _ _ |>.mp hb
          cases hfind : findIntVert? (b + 1) ivs with
          | none => rw [hfind] at hfb; contradiction
          | some iv =>
            rw [hfind] at hfb
            obtain ⟨hmem, hu⟩ := findIntVert?_spec (b + 1) ivs hfind
            exact ⟨iv, hmem, Or.inr (Or.inl ⟨hu, (cycUnord_iff _ _ _).mp hfb⟩)⟩
      · obtain ⟨_, hfd⟩ := Bool.and_eq_true _ _ |>.mp hc
        cases hfind : findIntVert? (d + 1) ivs with
        | none => rw [hfind] at hfd; contradiction
        | some iv =>
          rw [hfind] at hfd
          obtain ⟨hmem, hu⟩ := findIntVert?_spec (d + 1) ivs hfind
          exact ⟨iv, hmem, Or.inr (Or.inr ⟨hu, (cycUnord_iff _ _ _).mp hfd⟩)⟩
    · exact ih hrest d htail hbd hnb

private theorem checkTriForVert_spec (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) (a : Nat) (adjA : List Nat) :
    ∀ bs : List Nat, checkTriForVert r adjL ivs a adjA bs = true →
      ∀ b ∈ bs, a < b → checkTriForPair r adjL ivs a b adjA = true := by
  intro bs
  induction bs with
  | nil => intro _ b hm _; cases hm
  | cons b0 rest ih =>
    intro h b hm hab
    unfold checkTriForVert at h
    obtain ⟨hb0, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
    rcases List.mem_cons.mp hm with rfl | htail
    · rw [if_pos (Nat.blt_eq.mpr hab)] at hb0
      exact hb0
    · exact ih hrest b htail hab

private theorem checkAllTriGo_spec (r : Nat) (adjL : List (List Nat)) (ivs : List IntVert) :
    ∀ m : Nat, checkAllTriGo r adjL ivs m = true →
      ∀ a, a < m → checkTriForVert r adjL ivs a (Internal.listGetD [] adjL a) (Internal.listGetD [] adjL a) = true := by
  intro m
  induction m with
  | zero => intro _ a ha; cases ha
  | succ m ih =>
    intro h a ha
    unfold checkAllTriGo at h
    obtain ⟨hm, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with hlt | rfl
    · exact ih hrest a hlt
    · exact hm

private theorem countNonCEIn_eq_filter_length (ce : List (Nat × Nat)) (vx : List Nat) (u : Nat)
    (hvx : ∀ w, natContains vx w = true ↔ ∃ p ∈ ce, w = p.1 ∨ w = p.2) :
    ∀ ws : List Nat,
      countNonCEIn ce vx u ws =
        (ws.filter (fun w => (decide (∃ p ∈ ce, w = p.1 ∨ w = p.2)) && !isContractPair ce u w)).length := by
  intro ws
  induction ws with
  | nil => rfl
  | cons w rest ih =>
    unfold countNonCEIn
    rw [ih]
    have hdec : natContains vx w = decide (∃ p ∈ ce, w = p.1 ∨ w = p.2) := by
      cases hc : natContains vx w with
      | true =>
        symm; exact decide_eq_true ((hvx w).mp hc)
      | false =>
        symm; exact decide_eq_false (fun h => by have := (hvx w).mpr h; rw [hc] at this; contradiction)
    rw [hdec]
    cases hb : decide (∃ p ∈ ce, w = p.1 ∨ w = p.2) && !isContractPair ce u w
    · simp [hb]
    · simp [hb, Nat.add_comm]

private theorem existsTriad4Go_spec (r : Nat) (adjL : List (List Nat)) (ce : List (Nat × Nat)) (vx : List Nat) :
    ∀ m : Nat, existsTriad4Go r adjL ce vx m = true →
      ∃ u < m, r ≤ u ∧ 3 ≤ countNonCEIn ce vx u (Internal.listGetD [] adjL u) := by
  intro m
  induction m with
  | zero => intro h; simp [existsTriad4Go] at h
  | succ m ih =>
    intro h
    unfold existsTriad4Go at h
    by_cases hcond : Nat.ble r m = true ∧ Nat.ble 3 (countNonCEIn ce vx m (Internal.listGetD [] adjL m)) = true
    · exact ⟨m, Nat.lt_succ_self m, Nat.ble_eq.mp hcond.1, Nat.ble_eq.mp hcond.2⟩
    · have hfalse : (Nat.ble r m && Nat.ble 3 (countNonCEIn ce vx m (Internal.listGetD [] adjL m))) = false := by
        cases hb : Nat.ble r m && Nat.ble 3 (countNonCEIn ce vx m (Internal.listGetD [] adjL m)) with
        | false => rfl
        | true =>
          exfalso
          exact hcond (Bool.and_eq_true _ _ |>.mp hb)
      dsimp only at h
      rw [hfalse] at h
      simp only [Bool.false_eq_true, ite_false] at h
      obtain ⟨u, hu, hru, hcnt⟩ := ih h
      exact ⟨u, Nat.lt_succ_of_lt hu, hru, hcnt⟩

end GeomCert

open GeomCert

/-- Inductive witness describing the cyclic interior/ring run decomposition around an interior
    vertex of one of the configurations. -/
inductive IntRunShape (r : Nat) (c : Configuration) (fc : FastConf) (iv : IntVert) : List Nat → Prop where
  | allInterior {rot : List Nat} :
      (∀ v ∈ rot, r ≤ v) →
      5 ≤ rot.length →
      IntRunShape r c fc iv rot
  | oneRingRun {rot p1 g1 : List Nat} :
      rot = p1 ++ g1 →
      2 ≤ p1.length →
      1 ≤ g1.length →
      (∀ v ∈ p1, r ≤ v) →
      (∀ v ∈ g1, v < r) →
      IntRunShape r c fc iv rot
  | twoRingGaps {rot p1 p2 : List Nat} {x1 x2 : Nat} :
      rot = p1 ++ [x1] ++ p2 ++ [x2] →
      2 ≤ p1.length →
      2 ≤ p2.length →
      x1 < r →
      x2 < r →
      x1 ≠ x2 →
      c.adj x1 x2 = false →
      (∀ v ∈ p1, r ≤ v) →
      (∀ v ∈ p2, r ≤ v) →
      (∃ a1 b1 a2 b2,
        p1.head? = some a1 ∧ p1.getLast? = some b1 ∧
        p2.head? = some a2 ∧ p2.getLast? = some b2 ∧
        c.adj b1 a2 = false ∧ c.adj b2 a1 = false) →
      (∃ q ∈ fc.qSteps,
        q.v = iv.u ∧ q.z ≤ r ∧ r < q.u ∧
        { v := q.z, w := q.u : CycPair } ∈ iv.cyc ∧
        ((q.z = x1 + 1 ∧ p2.head? = some (q.u - 1)) ∨
         (q.z = x2 + 1 ∧ p1.head? = some (q.u - 1)))) →
      IntRunShape r c fc iv rot

private theorem natListContains_iff (xs : List Nat) (a : Nat) :
    xs.contains a = true ↔ a ∈ xs := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    unfold List.contains List.elem
    cases hax : (a == x) with
    | true =>
      have heq : a = x := beq_iff_eq.mp hax
      subst heq
      simp
    | false =>
      have hne : a ≠ x := fun h => by subst h; simp at hax
      have ih' : List.elem a rest = true ↔ a ∈ rest := ih
      dsimp only
      rw [ih', List.mem_cons]
      exact ⟨Or.inr, fun hm => hm.elim (fun h => absurd h hne) id⟩

theorem rc_adj_size_eq_n (h : Nat) (hh : h < 633) :
    (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.size =
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n := by
  rcases fastConf_equiv_header h hh with ⟨_, _, _, _, hn, _, _, _, _, _, _, hrcadj, _⟩
  dsimp [configOfRConf, Configuration.totalNodes] at hn hrcadj
  omega

theorem rc_r_pos (h : Nat) (hh : h < 633) :
    0 < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r := by
  rcases fastConf_equiv_header h hh with ⟨_, _, hr, _, _, hr6, _⟩
  omega

theorem rc_r_add_int_eq_n (h : Nat) (hh : h < 633) :
    (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r +
      (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).interiorSize =
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n := by
  rcases fastConf_equiv_header h hh with ⟨_, _, hr, _, hn, _⟩
  dsimp [configOfRConf, Configuration.totalNodes] at hr hn
  omega

theorem fc_intVerts_len_eq (h : Nat) (hh : h < 633) :
    (lookupFastConfRec h).intVerts.length =
      (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).interiorSize := by
  rcases fastConf_equiv_header h hh with ⟨_, _, _, _, _, _, _, _, _, _, hlen, _⟩
  exact hlen

theorem rc_int_idx_lt_adj_size (h : Nat) (hh : h < 633) {iu : Nat}
    (hiu : iu < (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).interiorSize) :
    (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu <
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.size := by
  have hsz := rc_adj_size_eq_n h hh
  have hsum := rc_r_add_int_eq_n h hh
  have hr : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize =
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r := rfl
  omega

theorem rc_ring_idx_lt_adj_size (h : Nat) (hh : h < 633) {x : Nat}
    (hx : x < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r) :
    x < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.size := by
  have hsz := rc_adj_size_eq_n h hh
  have hsum := rc_r_add_int_eq_n h hh
  omega

private theorem checkPairGeom_unpack {fc : FastConf} {rc : RConf}
    (h : checkPairGeom fc rc = true) :
    let adjL := rc.adj.toList.map Array.toList
    Nat.beq fc.ring rc.r = true ∧
    Nat.beq fc.nverts rc.n = true ∧
    Nat.beq adjL.length rc.n = true ∧
    checkIntRunsList rc.r adjL fc.qSteps fc.intVerts = true ∧
    checkQStepsGeom fc = true ∧
    checkAllCycEntries rc.r adjL fc.intVerts fc.intVerts = true ∧
    checkFansForRing rc.r adjL fc.intVerts rc.r = true ∧
    checkAllTriGo rc.r adjL fc.intVerts rc.n = true ∧
    checkTriad4 rc.r rc.n adjL rc.contractEdges.toList = true := by
  unfold checkPairGeom at h
  have h8 := Bool.and_eq_true _ _ |>.mp h
  have h7 := Bool.and_eq_true _ _ |>.mp h8.1
  have h6 := Bool.and_eq_true _ _ |>.mp h7.1
  have h5 := Bool.and_eq_true _ _ |>.mp h6.1
  have h4 := Bool.and_eq_true _ _ |>.mp h5.1
  have h3 := Bool.and_eq_true _ _ |>.mp h4.1
  have h2 := Bool.and_eq_true _ _ |>.mp h3.1
  have h1 := Bool.and_eq_true _ _ |>.mp h2.1
  exact ⟨h1.1, h1.2, h2.2, h3.2, h4.2, h5.2, h6.2, h7.2, h8.2⟩

private theorem geom_adjL_spec (h : Nat) (hh : h < 633) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let c := configOfRConf rc
    let adjL := rc.adj.toList.map Array.toList
    adjL.length = rc.n ∧
    rc.adj.size = c.totalNodes ∧
    c.totalNodes = rc.n ∧
    c.ringSize = rc.r ∧
    rc.r + c.interiorSize = rc.n ∧
    (∀ x (hx : x < rc.n),
      Internal.listGetD [] adjL x =
        (rc.adj[x]'(Nat.lt_of_lt_of_eq hx (rc_adj_size_eq_n h hh).symm)).toList) ∧
    (∀ x y, x < rc.n → y < rc.n → (c.adj x y = true ↔ y ∈ Internal.listGetD [] adjL x)) := by
  rcases fastConf_equiv_header h hh with ⟨_, _, hr, _, hn, _, _, _, _, _, _, hrcadj, _⟩
  obtain ⟨_, hadj_eq, _⟩ := fastConf_equiv_adj h hh
  have hsum := rc_r_add_int_eq_n h hh
  have hsz := rc_adj_size_eq_n h hh
  have hadjlen : ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.toList.map Array.toList).length =
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n := by
    rw [List.length_map, Array.length_toList]
    exact hsz
  refine ⟨hadjlen, hrcadj, hn, hr, hsum, ?_, ?_⟩
  · intro x hx
    have hi : x < ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.toList.map Array.toList).length := by
      rw [hadjlen]; exact hx
    rw [Internal.listGetD_eq_getElem _ _ hi, List.getElem_map]
    exact congrArg Array.toList (Array.getElem_toList (by rw [Array.length_toList, hsz]; exact hx))
  · intro x y hx hy
    have hx' : x < (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).totalNodes := by
      rw [hn]; exact hx
    have hy' : y < (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).totalNodes := by
      rw [hn]; exact hy
    have hi : x < ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.toList.map Array.toList).length := by
      rw [hadjlen]; exact hx
    rw [Internal.listGetD_eq_getElem _ _ hi, List.getElem_map]
    have hceq := hadj_eq x hx' y hy'
    have hlst : ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.toList[x]'
        (by rw [Array.length_toList, hsz]; exact hx)) =
        (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj[x]'(Nat.lt_of_lt_of_eq hx hsz.symm) :=
      Array.getElem_toList (by rw [Array.length_toList, hsz]; exact hx)
    rw [hlst, hceq]
    exact natListContains_iff _ y

private theorem checkRotShape_sound_aux (rc : RConf) (fc : FastConf) (iv : IntVert) (rot : List Nat)
    (hrot_lt : ∀ v ∈ rot, v < rc.n)
    (hadjiff : ∀ x y, x < rc.n → y < rc.n →
      ((configOfRConf rc).adj x y = true ↔ y ∈ Internal.listGetD [] (rc.adj.toList.map Array.toList) x))
    (hrot : checkRotShape rc.r (rc.adj.toList.map Array.toList) fc.qSteps iv rot = true) :
    IntRunShape rc.r (configOfRConf rc) fc iv rot := by
  unfold checkRotShape at hrot
  have hsp1 := spanWhileGe_spec rc.r rot
  cases hpair1 : spanWhileGe rc.r rot with
  | mk p1 rest1 =>
    rw [hpair1] at hsp1 hrot
    rcases hsp1 with ⟨happ1, hp1ge, _⟩
    dsimp only at hrot
    cases rest1 with
    | nil =>
      simp only [List.append_nil] at happ1
      rw [← happ1]
      exact IntRunShape.allInterior hp1ge (Nat.ble_eq.mp hrot)
    | cons r1 rs1 =>
      dsimp only at hrot
      have hsp2 := spanWhileLt_spec rc.r (r1 :: rs1)
      cases hpair2 : spanWhileLt rc.r (r1 :: rs1) with
      | mk g1 rest2 =>
        rw [hpair2] at hsp2 hrot
        rcases hsp2 with ⟨happ2, hg1lt, _⟩
        dsimp only at hrot
        cases rest2 with
        | nil =>
          simp only [List.append_nil] at happ2
          rw [← happ2] at happ1
          obtain ⟨hp1len, hg1len⟩ := Bool.and_eq_true _ _ |>.mp hrot
          exact IntRunShape.oneRingRun happ1.symm (Nat.ble_eq.mp hp1len) (Nat.ble_eq.mp hg1len) hp1ge hg1lt
        | cons r2 rs2 =>
          dsimp only at hrot
          have hsp3 := spanWhileGe_spec rc.r (r2 :: rs2)
          cases hpair3 : spanWhileGe rc.r (r2 :: rs2) with
          | mk p2 g2 =>
            rw [hpair3] at hsp3 hrot
            rcases hsp3 with ⟨happ3, hp2ge, hhead3⟩
            dsimp only at hrot
            cases g1 with
            | nil => simp at hrot
            | cons x1 xs1 =>
              cases xs1 with
              | cons _ _ => simp at hrot
              | nil =>
                cases g2 with
                | nil => simp at hrot
                | cons x2 xs2 =>
                  cases xs2 with
                  | cons _ _ => simp at hrot
                  | nil =>
                    cases p1 with
                    | nil => simp at hrot
                    | cons a1 as1 =>
                      cases p2 with
                      | nil => simp at hrot
                      | cons a2 as2 =>
                        dsimp only at hrot
                        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hrot
                        obtain ⟨⟨⟨⟨⟨⟨hp1l, hp2l⟩, hneq⟩, hx12⟩, hpa⟩, hqa⟩, hgap⟩ := hrot
                        have hrotEq : rot = (a1 :: as1) ++ [x1] ++ (a2 :: as2) ++ [x2] := by
                          rw [← happ1, ← happ2, ← happ3]
                          simp [List.append_assoc]
                        have hmem_of : ∀ v, v ∈ (a1 :: as1) ++ [x1] ++ (a2 :: as2) ++ [x2] → v < rc.n :=
                          fun v hv => hrot_lt v (hrotEq.symm ▸ hv)
                        have hx1n : x1 < rc.n := hmem_of x1 (by simp)
                        have hx2n : x2 < rc.n := hmem_of x2 (by simp)
                        have hx1r : x1 < rc.r := hg1lt x1 List.mem_cons_self
                        have hx2r : x2 < rc.r := hhead3 x2 [] rfl
                        have hneq' : x1 ≠ x2 := fun heq => by subst heq; simp at hneq
                        have hx12f : (configOfRConf rc).adj x1 x2 = false := by
                          cases hc : (configOfRConf rc).adj x1 x2 with
                          | false => rfl
                          | true =>
                            exfalso
                            have hmem := (hadjiff x1 x2 hx1n hx2n).mp hc
                            have hct := (natContains_iff _ _).mpr hmem
                            rw [hx12] at hct
                            contradiction
                        obtain ⟨a1', b1, ha1', hb1, _, hm_b1⟩ :=
                          list_nonempty_ends (a1 :: as1) (by simp)
                        obtain ⟨a2', b2, ha2', hb2, _, hm_b2⟩ :=
                          list_nonempty_ends (a2 :: as2) (by simp)
                        have ha1eq : a1' = a1 := by simp at ha1'; exact ha1'.symm
                        have ha2eq : a2' = a2 := by simp at ha2'; exact ha2'.symm
                        subst a1'; subst a2'
                        have hblast1 : Internal.listLastD 0 (a1 :: as1) = b1 :=
                          listLastD_eq_getLast?_some 0 (a1 :: as1) hb1
                        have hblast2 : Internal.listLastD 0 (a2 :: as2) = b2 :=
                          listLastD_eq_getLast?_some 0 (a2 :: as2) hb2
                        have hb1n : b1 < rc.n :=
                          hmem_of b1 (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hm_b1)))
                        have hb2n : b2 < rc.n :=
                          hmem_of b2 (List.mem_append_left _ (List.mem_append_right _ hm_b2))
                        have ha1n : a1 < rc.n := hmem_of a1 (by simp)
                        have ha2n : a2 < rc.n := hmem_of a2 (by simp)
                        have hb1a2f : (configOfRConf rc).adj b1 a2 = false := by
                          cases hc : (configOfRConf rc).adj b1 a2 with
                          | false => rfl
                          | true =>
                            exfalso
                            have hmem := (hadjiff b1 a2 hb1n ha2n).mp hc
                            have hct := (natContains_iff _ _).mpr hmem
                            rw [hblast1] at hpa
                            rw [hpa] at hct
                            contradiction
                        have hb2a1f : (configOfRConf rc).adj b2 a1 = false := by
                          cases hc : (configOfRConf rc).adj b2 a1 with
                          | false => rfl
                          | true =>
                            exfalso
                            have hmem := (hadjiff b2 a1 hb2n ha1n).mp hc
                            have hct := (natContains_iff _ _).mpr hmem
                            rw [hblast2] at hqa
                            rw [hqa] at hct
                            contradiction
                        refine IntRunShape.twoRingGaps hrotEq (Nat.ble_eq.mp hp1l) (Nat.ble_eq.mp hp2l)
                          hx1r hx2r hneq' hx12f hp1ge hp2ge
                          ⟨a1, b1, a2, b2, rfl, hb1, rfl, hb2, hb1a2f, hb2a1f⟩ ?_
                        rcases Bool.or_eq_true _ _ |>.mp hgap with hg1 | hg2
                        · obtain ⟨q, hqm, hqv, hqz, hqu, hcyc⟩ := hasGapQStep_spec iv x1 a2 _ hg1
                          have ha2r : rc.r < a2 + 1 := by
                            have := hp2ge a2 List.mem_cons_self
                            omega
                          exact ⟨q, hqm, hqv, by omega, by omega, by rw [hqz, hqu]; exact hcyc,
                            Or.inl ⟨hqz, by simp [hqu]⟩⟩
                        · obtain ⟨q, hqm, hqv, hqz, hqu, hcyc⟩ := hasGapQStep_spec iv x2 a1 _ hg2
                          have ha1r : rc.r < a1 + 1 := by
                            have := hp1ge a1 List.mem_cons_self
                            omega
                          exact ⟨q, hqm, hqv, by omega, by omega, by rw [hqz, hqu]; exact hcyc,
                            Or.inr ⟨hqz, by simp [hqu]⟩⟩

private theorem checkRotShape_sound (h : Nat) (hh : h < 633) (iv : IntVert) (rot : List Nat)
    (hrot_lt : ∀ v ∈ rot, v < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hrot : checkRotShape (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r
      ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.toList.map Array.toList)
      (lookupFastConfRec h).qSteps iv rot = true) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    IntRunShape rc.r (configOfRConf rc) (lookupFastConfRec h) iv rot :=
  checkRotShape_sound_aux _ _ iv rot hrot_lt (geom_adjL_spec h hh).2.2.2.2.2.2 hrot

/-- Unpack `IntRunShape` from `checkPairGeom = true`. -/
theorem geom_int_runs_of (h : Nat) (hh : h < 633)
    (hgeom : checkPairGeom (lookupFastConfRec h) (parsedRConfList[h]'(parsedRConfList_length ▸ hh)) = true)
    (iu : Nat) (hiu : iu < (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).interiorSize) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    let c := configOfRConf rc
    have hiu' : iu < fc.intVerts.length := Nat.lt_of_lt_of_eq hiu (fc_intVerts_len_eq h hh).symm
    have hu0 : c.ringSize + iu < rc.adj.size := rc_int_idx_lt_adj_size h hh hiu
    let iv := fc.intVerts[iu]'hiu'
    let nbrs := (rc.adj[c.ringSize + iu]'hu0).toList
    ∃ k < nbrs.length, IntRunShape rc.r c fc iv (nbrs.drop k ++ nbrs.take k) := by
  obtain ⟨_, _, _, hint, _, _, _, _, _⟩ := checkPairGeom_unpack hgeom
  rcases fastConf_equiv_header h hh with ⟨_, _, hr, _, hn, _, _, _, _, _, hlen, _, _⟩
  obtain ⟨hadj_nodup, _, _, _⟩ := fastConf_equiv_adj h hh
  have hiu' : iu < (lookupFastConfRec h).intVerts.length := Nat.lt_of_lt_of_eq hiu hlen.symm
  have hivu_eq' : ((lookupFastConfRec h).intVerts[iu]'hiu').u =
      (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu + 1 :=
    (fastConf_equiv_intVerts h hh iu hiu).1
  rcases geom_adjL_spec h hh with ⟨_, _, _, _, _, hgetadj, _⟩
  let iv := (lookupFastConfRec h).intVerts[iu]'hiu'
  have hiv_mem : iv ∈ (lookupFastConfRec h).intVerts := List.getElem_mem hiu'
  have herot := checkIntRunsList_spec _ _ _ _ hint iv hiv_mem
  have hu0_sz : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu <
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.size := rc_int_idx_lt_adj_size h hh hiu
  have hu0_n : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu <
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n := (rc_adj_size_eq_n h hh) ▸ hu0_sz
  have hivu : iv.u - 1 = (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu := by
    have hsub : ((lookupFastConfRec h).intVerts[iu]'hiu').u - 1 =
        (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu := by
      rw [hivu_eq']
      exact Nat.add_sub_cancel _ 1
    exact hsub
  have hgetu0 : Internal.listGetD [] ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.toList.map Array.toList) (iv.u - 1) =
      ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj[
        (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu]'hu0_sz).toList := by
    rw [hivu]
    exact hgetadj _ hu0_n
  rw [hgetu0] at herot
  obtain ⟨k, hk, hrot⟩ := existsRot_spec _ _ _ _ _ _ herot
  refine ⟨k, hk, ?_⟩
  exact checkRotShape_sound h hh iv _ (fun v hv => by
    have hv_nbr : v ∈ ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj[
        (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu]'hu0_sz).toList := by
      rcases List.mem_append.mp hv with hv1 | hv2
      · exact List.mem_of_mem_drop hv1
      · exact List.mem_of_mem_take hv2
    have hu0tot : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).ringSize + iu <
        (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).totalNodes := by
      rw [hn]; exact hu0_n
    have hvlt := (hadj_nodup _ hu0tot).2 v hv_nbr
    rw [hn] at hvlt
    exact hvlt.1) hrot

/-- Unpack `QStep` consistency from `checkPairGeom = true`. -/
theorem geom_qSteps_of (h : Nat) (hh : h < 633)
    (hgeom : checkPairGeom (lookupFastConfRec h) (parsedRConfList[h]'(parsedRConfList_length ▸ hh)) = true) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    let cov := fc.z0 :: fc.z1 :: fc.qSteps.map (·.z)
    cov.Nodup ∧
    (∀ iv ∈ fc.intVerts, iv.u ∈ cov) ∧
    (∀ q ∈ fc.qSteps,
      (rc.r < q.v → ∃ iv ∈ fc.intVerts, iv.u = q.v ∧ { v := q.z, w := q.u : CycPair } ∈ iv.cyc) ∧
      (q.v ≤ rc.r → rc.r < q.u ∧ ∃ iv ∈ fc.intVerts, iv.u = q.u ∧ { v := q.v, w := q.z : CycPair } ∈ iv.cyc)) := by
  obtain ⟨_, _, _, _, hqs, _, _, _, _⟩ := checkPairGeom_unpack hgeom
  unfold checkQStepsGeom at hqs
  have hqs1 := Bool.and_eq_true _ _ |>.mp hqs
  have hqs2 := Bool.and_eq_true _ _ |>.mp hqs1.1
  have hnod := hqs2.1
  have hcov := hqs2.2
  have hall := hqs1.2
  rcases fastConf_equiv_header h hh with ⟨hfr0, _, hr, _⟩
  have hfr : (lookupFastConfRec h).ring = (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r := by
    rw [hfr0, hr]
  rw [hfr] at hall
  exact ⟨natNodup_iff _ hnod, checkIntCovered_spec _ _ hcov, checkQStepsAll_spec _ _ _ hall⟩

/-- Unpack half-edge reciprocity from `checkPairGeom = true`. -/
theorem geom_halfEdge_recip_of (h : Nat) (_hh : h < 633)
    (hgeom : checkPairGeom (lookupFastConfRec h) (parsedRConfList[h]'(parsedRConfList_length ▸ _hh)) = true) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ _hh)
    let fc := lookupFastConfRec h
    ∀ iv ∈ fc.intVerts, ∀ cp ∈ iv.cyc,
      (rc.r < cp.v → ∃ iv2 ∈ fc.intVerts, iv2.u = cp.v ∧ { v := cp.w, w := iv.u : CycPair } ∈ iv2.cyc) ∧
      (rc.r < cp.w → ∃ iv2 ∈ fc.intVerts, iv2.u = cp.w ∧ { v := iv.u, w := cp.v : CycPair } ∈ iv2.cyc) := by
  obtain ⟨_, _, _, _, _, hcyc, _, _, _⟩ := checkPairGeom_unpack hgeom
  intro rc fc iv hiv cp hcp
  have hsp := checkCycEntries_spec _ _ _ iv _ (checkAllCycEntries_spec _ _ _ _ hcyc iv hiv) cp hcp
  exact ⟨hsp.1, hsp.2.1⟩

/-- Unpack two-ring cyclic pair invariant from `checkPairGeom = true`. -/
theorem geom_cyc_ring_pairs_of (h : Nat) (hh : h < 633)
    (hgeom : checkPairGeom (lookupFastConfRec h) (parsedRConfList[h]'(parsedRConfList_length ▸ hh)) = true) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    ∀ iv ∈ fc.intVerts, ∀ cp ∈ iv.cyc,
      cp.v ≤ rc.r → cp.w ≤ rc.r →
        cp.w - 1 = (cp.v - 1 + 1) % rc.r ∧
        ∃ hx : cp.v - 1 < rc.adj.size,
          ((rc.adj[cp.v - 1]'hx).toList.drop 1).dropLast.head? = some (iv.u - 1) := by
  obtain ⟨_, _, _, _, _, hcyc, _, _, _⟩ := checkPairGeom_unpack hgeom
  rcases geom_adjL_spec h hh with ⟨_, _, _, _, hsum, hgetadj, _⟩
  intro rc fc iv hiv cp hcp hvle hwle
  have hsp := (checkCycEntries_spec _ _ _ iv _ (checkAllCycEntries_spec _ _ _ _ hcyc iv hiv) cp hcp).2.2 hvle hwle
  have hpos := rc_r_pos h hh
  have hvle' : cp.v ≤ (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r := hvle
  have hx_lt_n : cp.v - 1 < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n := by omega
  have hx_sz : cp.v - 1 < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.size :=
    (rc_adj_size_eq_n h hh).symm ▸ hx_lt_n
  refine ⟨hsp.1, hx_sz, ?_⟩
  rw [← hgetadj (cp.v - 1) hx_lt_n]
  exact hsp.2

private theorem fans_spec_rw {ivs : List IntVert} {x : Nat}
    {xs ys xsNext ysNext : List Nat} (hxs : xs = ys) (hnext : xsNext = ysNext)
    {nextR prevR : Nat}
    (h : let fans := xs; let nextFans := xsNext
      fans ≠ [] ∧ nextFans.getLast? = fans.head? ∧
      (∀ u1, fans.head? = some u1 → ∃ iv1 ∈ ivs, iv1.u = u1 + 1 ∧ { v := x + 1, w := nextR + 1 : CycPair } ∈ iv1.cyc) ∧
      (∀ um, fans.getLast? = some um → ∃ ivm ∈ ivs, ivm.u = um + 1 ∧ { v := prevR + 1, w := x + 1 : CycPair } ∈ ivm.cyc) ∧
      (∀ k (hk : k + 1 < fans.length), ∃ ivk ∈ ivs, ∃ ivk1 ∈ ivs,
        ivk.u = fans[k] + 1 ∧ ivk1.u = fans[k + 1] + 1 ∧
        { v := fans[k + 1] + 1, w := x + 1 : CycPair } ∈ ivk.cyc ∧
        { v := x + 1, w := fans[k] + 1 : CycPair } ∈ ivk1.cyc)) :
    let fans := ys; let nextFans := ysNext
    fans ≠ [] ∧ nextFans.getLast? = fans.head? ∧
    (∀ u1, fans.head? = some u1 → ∃ iv1 ∈ ivs, iv1.u = u1 + 1 ∧ { v := x + 1, w := nextR + 1 : CycPair } ∈ iv1.cyc) ∧
    (∀ um, fans.getLast? = some um → ∃ ivm ∈ ivs, ivm.u = um + 1 ∧ { v := prevR + 1, w := x + 1 : CycPair } ∈ ivm.cyc) ∧
    (∀ k (hk : k + 1 < fans.length), ∃ ivk ∈ ivs, ∃ ivk1 ∈ ivs,
      ivk.u = fans[k]'(Nat.lt_of_succ_lt hk) + 1 ∧ ivk1.u = fans[k + 1]'hk + 1 ∧
      { v := fans[k + 1]'hk + 1, w := x + 1 : CycPair } ∈ ivk.cyc ∧
      { v := x + 1, w := fans[k]'(Nat.lt_of_succ_lt hk) + 1 : CycPair } ∈ ivk1.cyc) := by
  subst hxs; subst hnext; exact h

/-- Unpack ring fan consistency from `checkPairGeom = true`. -/
theorem geom_ring_fans_of (h : Nat) (hh : h < 633)
    (hgeom : checkPairGeom (lookupFastConfRec h) (parsedRConfList[h]'(parsedRConfList_length ▸ hh)) = true)
    (x : Nat) (hx : x < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    let nextR := (x + 1) % rc.r
    let prevR := (x + rc.r - 1) % rc.r
    have hxn : x < rc.adj.size := rc_ring_idx_lt_adj_size h hh hx
    have hnextn : nextR < rc.adj.size :=
      rc_ring_idx_lt_adj_size h hh (Nat.mod_lt _ (rc_r_pos h hh))
    let fans := ((rc.adj[x]'hxn).toList.drop 1).dropLast
    let nextFans := ((rc.adj[nextR]'hnextn).toList.drop 1).dropLast
    fans ≠ [] ∧
    nextFans.getLast? = fans.head? ∧
    (∀ u1, fans.head? = some u1 →
      ∃ iv1 ∈ fc.intVerts, iv1.u = u1 + 1 ∧ { v := x + 1, w := nextR + 1 : CycPair } ∈ iv1.cyc) ∧
    (∀ um, fans.getLast? = some um →
      ∃ ivm ∈ fc.intVerts, ivm.u = um + 1 ∧ { v := prevR + 1, w := x + 1 : CycPair } ∈ ivm.cyc) ∧
    (∀ k (hk : k + 1 < fans.length),
      ∃ ivk ∈ fc.intVerts, ∃ ivk1 ∈ fc.intVerts,
        ivk.u = fans[k]'(Nat.lt_of_succ_lt hk) + 1 ∧
        ivk1.u = fans[k + 1]'hk + 1 ∧
        { v := fans[k + 1]'hk + 1, w := x + 1 : CycPair } ∈ ivk.cyc ∧
        { v := x + 1, w := fans[k]'(Nat.lt_of_succ_lt hk) + 1 : CycPair } ∈ ivk1.cyc) := by
  obtain ⟨_, _, _, _, _, _, hfans, _, _⟩ := checkPairGeom_unpack hgeom
  rcases geom_adjL_spec h hh with ⟨_, _, _, _, _, hgetadj, _⟩
  have hsp := checkFansForRing_spec _ _ _ _ hfans x hx
  have hxn_sz : x < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.size := rc_ring_idx_lt_adj_size h hh hx
  have hnextn_sz : (x + 1) % (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r <
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.size :=
    rc_ring_idx_lt_adj_size h hh (Nat.mod_lt _ (rc_r_pos h hh))
  have hxn : x < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n :=
    (rc_adj_size_eq_n h hh) ▸ hxn_sz
  have hnextn : (x + 1) % (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r <
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n :=
    (rc_adj_size_eq_n h hh) ▸ hnextn_sz
  exact fans_spec_rw
    (congrArg (fun l => (l.drop 1).dropLast) (hgetadj x hxn))
    (congrArg (fun l => (l.drop 1).dropLast) (hgetadj _ hnextn))
    hsp

private theorem tri_sorted {h : Nat} (hh : h < 633) {r : Nat} {adjL : List (List Nat)} {ivs : List IntVert}
    {x y z : Nat} (hxy : x < y) (hyz : y < z)
    (hx : x < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hy : y < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hz : z < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (h1 : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj x y = true)
    (h2 : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj y z = true)
    (h3 : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj x z = true)
    (htri : checkAllTriGo r adjL ivs (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n = true)
    (hadjL : ∀ a, a < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n →
      ∀ b, b < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n →
        ((configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj a b = true ↔ b ∈ Internal.listGetD [] adjL a)) :
    ∃ iv ∈ ivs,
      (iv.u = x + 1 ∧ ({ v := y + 1, w := z + 1 : CycPair } ∈ iv.cyc ∨ { v := z + 1, w := y + 1 : CycPair } ∈ iv.cyc)) ∨
      (iv.u = y + 1 ∧ ({ v := x + 1, w := z + 1 : CycPair } ∈ iv.cyc ∨ { v := z + 1, w := x + 1 : CycPair } ∈ iv.cyc)) ∨
      (iv.u = z + 1 ∧ ({ v := x + 1, w := y + 1 : CycPair } ∈ iv.cyc ∨ { v := y + 1, w := x + 1 : CycPair } ∈ iv.cyc)) := by
  have hy_mem := (hadjL x hx y hy).mp h1
  have hz_mem_x := (hadjL x hx z hz).mp h3
  have hz_mem_y := (hadjL y hy z hz).mp h2
  have hv := checkAllTriGo_spec r adjL ivs _ htri x hx
  have hp := checkTriForVert_spec r adjL ivs x _ _ hv y hy_mem hxy
  exact checkTriForPair_spec r adjL ivs x y _ hp z hz_mem_x hyz hz_mem_y

/-- Unpack facial 3-clique completeness from `checkPairGeom = true`. -/
theorem geom_tri_clique_in_cyc_of (h : Nat) (hh : h < 633)
    (hgeom : checkPairGeom (lookupFastConfRec h) (parsedRConfList[h]'(parsedRConfList_length ▸ hh)) = true)
    {a b d : Nat}
    (ha : a < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hb : b < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hd : d < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hab : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj a b = true)
    (hbd : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj b d = true)
    (had : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj a d = true) :
    ∃ iv ∈ (lookupFastConfRec h).intVerts,
      (iv.u = a + 1 ∧ ({ v := b + 1, w := d + 1 : CycPair } ∈ iv.cyc ∨ { v := d + 1, w := b + 1 : CycPair } ∈ iv.cyc)) ∨
      (iv.u = b + 1 ∧ ({ v := a + 1, w := d + 1 : CycPair } ∈ iv.cyc ∨ { v := d + 1, w := a + 1 : CycPair } ∈ iv.cyc)) ∨
      (iv.u = d + 1 ∧ ({ v := a + 1, w := b + 1 : CycPair } ∈ iv.cyc ∨ { v := b + 1, w := a + 1 : CycPair } ∈ iv.cyc)) := by
  obtain ⟨_, _, _, _, _, _, _, htri, _⟩ := checkPairGeom_unpack hgeom
  rcases geom_adjL_spec h hh with ⟨_, _, hn, _, _, _, hadjL⟩
  obtain ⟨_, _, hsym, _⟩ := fastConf_equiv_adj h hh
  have ha' : a < (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).totalNodes := by
    rw [hn]; exact ha
  have hb' : b < (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).totalNodes := by
    rw [hn]; exact hb
  have hd' : d < (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).totalNodes := by
    rw [hn]; exact hd
  have hnab : a ≠ b := fun he => by subst he; rw [(hsym a ha' a ha').2] at hab; contradiction
  have hnbd : b ≠ d := fun he => by subst he; rw [(hsym b hb' b hb').2] at hbd; contradiction
  have hnad : a ≠ d := fun he => by subst he; rw [(hsym a ha' a ha').2] at had; contradiction
  have hba : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj b a = true := by
    rw [← (hsym a ha' b hb').1]; exact hab
  have hdb : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj d b = true := by
    rw [← (hsym b hb' d hd').1]; exact hbd
  have hda : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj d a = true := by
    rw [← (hsym a ha' d hd').1]; exact had
  have hhadj : ∀ x, x < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n →
      ∀ y, y < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n →
        ((configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj x y = true ↔
          y ∈ Internal.listGetD [] ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.toList.map Array.toList) x) :=
    fun x hx y hy => hadjL x y hx hy
  rcases Nat.lt_or_gt_of_ne hnab with hlt_ab | hlt_ba
  · rcases Nat.lt_or_gt_of_ne hnbd with hlt_bd | hlt_db
    · exact tri_sorted hh hlt_ab hlt_bd ha hb hd hab hbd had htri hhadj
    · rcases Nat.lt_or_gt_of_ne hnad with hlt_ad | hlt_da
      · obtain ⟨iv, hm, hres⟩ := tri_sorted hh hlt_ad hlt_db ha hd hb had hdb hab htri hhadj
        refine ⟨iv, hm, ?_⟩
        rcases hres with ⟨u, c⟩ | ⟨u, c⟩ | ⟨u, c⟩
        · exact Or.inl ⟨u, c.elim Or.inr Or.inl⟩
        · exact Or.inr (Or.inr ⟨u, c⟩)
        · exact Or.inr (Or.inl ⟨u, c⟩)
      · obtain ⟨iv, hm, hres⟩ := tri_sorted hh hlt_da hlt_ab hd ha hb hda hab hdb htri hhadj
        refine ⟨iv, hm, ?_⟩
        rcases hres with ⟨u, c⟩ | ⟨u, c⟩ | ⟨u, c⟩
        · exact Or.inr (Or.inr ⟨u, c⟩)
        · exact Or.inl ⟨u, c.elim Or.inr Or.inl⟩
        · exact Or.inr (Or.inl ⟨u, c.elim Or.inr Or.inl⟩)
  · rcases Nat.lt_or_gt_of_ne hnad with hlt_ad | hlt_da
    · obtain ⟨iv, hm, hres⟩ := tri_sorted hh hlt_ba hlt_ad hb ha hd hba had hbd htri hhadj
      refine ⟨iv, hm, ?_⟩
      rcases hres with ⟨u, c⟩ | ⟨u, c⟩ | ⟨u, c⟩
      · exact Or.inr (Or.inl ⟨u, c⟩)
      · exact Or.inl ⟨u, c⟩
      · exact Or.inr (Or.inr ⟨u, c.elim Or.inr Or.inl⟩)
    · rcases Nat.lt_or_gt_of_ne hnbd with hlt_bd | hlt_db
      · obtain ⟨iv, hm, hres⟩ := tri_sorted hh hlt_bd hlt_da hb hd ha hbd hda hba htri hhadj
        refine ⟨iv, hm, ?_⟩
        rcases hres with ⟨u, c⟩ | ⟨u, c⟩ | ⟨u, c⟩
        · exact Or.inr (Or.inl ⟨u, c.elim Or.inr Or.inl⟩)
        · exact Or.inr (Or.inr ⟨u, c.elim Or.inr Or.inl⟩)
        · exact Or.inl ⟨u, c⟩
      · obtain ⟨iv, hm, hres⟩ := tri_sorted hh hlt_db hlt_ba hd hb ha hdb hba hda htri hhadj
        refine ⟨iv, hm, ?_⟩
        rcases hres with ⟨u, c⟩ | ⟨u, c⟩ | ⟨u, c⟩
        · exact Or.inr (Or.inr ⟨u, c.elim Or.inr Or.inl⟩)
        · exact Or.inr (Or.inl ⟨u, c.elim Or.inr Or.inl⟩)
        · exact Or.inl ⟨u, c.elim Or.inr Or.inl⟩

/-- Unpack RSST `(3.6)` `|X| = 4` triad witness from `checkPairGeom = true`. -/
theorem geom_triad4_of (h : Nat) (hh : h < 633)
    (hgeom : checkPairGeom (lookupFastConfRec h) (parsedRConfList[h]'(parsedRConfList_length ▸ hh)) = true)
    (hce : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).contractEdges.length = 4) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let c := configOfRConf rc
    ∃ v_tri : Nat, ∃ hv : v_tri < rc.adj.size,
      rc.r ≤ v_tri ∧ v_tri < rc.n ∧
      3 ≤ ((rc.adj[v_tri]'hv).toList.filter
        (fun w => decide (∃ p ∈ c.contractEdges, w = p.1 ∨ w = p.2) && !isContractPair c.contractEdges v_tri w)).length := by
  obtain ⟨_, _, _, _, _, _, _, _, htriad⟩ := checkPairGeom_unpack hgeom
  unfold checkTriad4 at htriad
  have hce_rc : (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).contractEdges.toList.length = 4 := hce
  rw [if_pos (Nat.beq_eq.mpr hce_rc)] at htriad
  obtain ⟨u, hun, hru, hcnt⟩ := existsTriad4Go_spec _ _ _ _ _ htriad
  rcases geom_adjL_spec h hh with ⟨_, _, _, _, _, hgetadj, _⟩
  have hvx : ∀ w, natContains ((parsedRConfList[h]'(parsedRConfList_length ▸ hh)).contractEdges.toList.flatMap fun p => [p.1, p.2]) w = true ↔
      ∃ p ∈ (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).contractEdges.toList, w = p.1 ∨ w = p.2 := by
    intro w
    rw [natContains_iff, List.mem_flatMap]
    constructor
    · rintro ⟨p, hp, hmem⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      exact ⟨p, hp, hmem⟩
    · rintro ⟨p, hp, hmem⟩
      exact ⟨p, hp, by simp [hmem]⟩
  rw [countNonCEIn_eq_filter_length _ _ u hvx, hgetadj u hun] at hcnt
  have husz : u < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).adj.size :=
    (rc_adj_size_eq_n h hh).symm ▸ hun
  exact ⟨u, husz, hru, hun, hcnt⟩

end Math.Unavoidability
