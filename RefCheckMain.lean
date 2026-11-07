import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.Soundness.CReduce

open Math
open Math.FastReducer
open Math.Batch
open Math.Soundness

/-!
Differential checker (Stage K0.7):
Compares the proof-target checker (`checkFastTotal` + `runContractCheckTotal` on
`rconfOfConfig (theUnavoidableSet[i]!) (sharedCfgs[i]!.earlier)` with `buildSMData r sharedPow3`)
against `FastReducer.check` and RSST ground truth (`c.contract == 0` vs `c.contract > 0`).

Usage:
  `refcheck [maxRing] [minRing]`              -- runs both proof-target checker and `FastReducer.check`
  `refcheck [maxRing] [minRing] --proof-only` -- runs proof-target checker and compares against RSST verdicts
-/

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

def main (args : List String) : IO UInt32 := do
  let posArgs := args.filter (fun s => !s.startsWith "--")
  let maxRing := (posArgs[0]? >>= String.toNat?).getD 14
  let minRing := (posArgs[1]? >>= String.toNat?).getD 2
  let proofOnly := args.contains "--proof-only"
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
