import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.Planarity
import FourColorTheorem.Math.FastReducer

open Math.FastReducer

/-!
Runs the D-reducibility check on all 633 RSST configurations in parallel. The largest
rings are scheduled first, and each result is compared with the RSST ground truth.

Usage: `fourcolortheorem [maxRing]`. For example, `fourcolortheorem 10` checks only rings ≤ 10.
-/

def main (args : List String) : IO UInt32 := do
  let maxRing := (args.head? >>= String.toNat?).getD 14
  let out ← IO.getStdout
  IO.println "--- Four Color Theorem: native D-reducibility checker (RSST) ---"
  let configs := loadAll ()
  IO.println s!"Loaded {configs.size} configurations. Checking rings ≤ {maxRing}."
  let pow3 := powers3 15
  let t0 ← IO.monoMsNow
  -- matching tables are shared (read-only) by all tasks of the same ring size
  let mut mdata : Array (Array MData × Nat) := #[]
  for r in [0:15] do
    mdata := mdata.push (if r < 2 || r > maxRing then (#[], 0) else buildMData r pow3)
  IO.println s!"Matching tables built in {(← IO.monoMsNow) - t0} ms."
  out.flush

  -- longest-first scheduling: biggest rings first
  let order := ((List.range configs.size).toArray.filter (fun i => configs[i]!.r ≤ maxRing)).qsort
    (fun i j => configs[i]!.r > configs[j]!.r || (configs[i]!.r == configs[j]!.r && i < j))
  let total := order.size
  let done ← IO.mkRef 0
  let mut tasks : Array (Nat × Task (Except IO.Error Result)) := #[]
  for i in order do
    let c := configs[i]!
    let md := mdata[c.r]!
    let t ← IO.asTask do
      let ts ← IO.monoMsNow
      let res := check c md pow3
      let te ← IO.monoMsNow
      let k ← done.modifyGet (fun k => (k + 1, k + 1))
      let expected := c.contract == 0
      let verdict := if res.dReducible then "D-REDUCIBLE" else if res.cReducible then "C-REDUCIBLE" else "FAILED"
      let agree := if res.dReducible == expected then "agrees with RSST" else if res.cReducible == (!expected) then "agrees with RSST (C-reduced)" else "*** DISAGREES WITH RSST ***"
      let xs := if res.xMatches then "" else " [X-count mismatch!]"
      IO.println s!"[{k}/{total}] Config {i} (ring {c.r}): {verdict}, {agree}{xs} | colourings {res.ringColourings}, non-extendable {res.nonExtendable}, final live {res.finalLive}, {res.iterations} iters, {te - ts} ms | elapsed {(te - t0) / 1000}s"
      (← IO.getStdout).flush
      return res
    tasks := tasks.push (i, t)

  let mut dred := 0
  let mut cred := 0
  let mut disagree : Array Nat := #[]
  let mut xbad : Array Nat := #[]
  let mut errors := 0
  for (i, t) in tasks do
    match ← IO.wait t with
    | .ok res =>
      if res.dReducible then dred := dred + 1
      else if res.cReducible then cred := cred + 1
      if res.dReducible != (configs[i]!.contract == 0) then disagree := disagree.push i
      if !res.xMatches then xbad := xbad.push i
    | .error e =>
      errors := errors + 1
      IO.println s!"Error on config {i}: {e}"
  let expectedD := (order.filter (fun i => configs[i]!.contract == 0)).size
  IO.println "\n--- Summary ---"
  IO.println s!"Configurations checked: {total}"
  IO.println s!"D-reducible: {dred} (RSST data says {expectedD})"
  IO.println s!"C-reducible: {cred} (Successfully verified by backtracking)"
  IO.println s!"Disagreements with RSST: {disagree.size} {if disagree.isEmpty then "" else toString disagree.toList}"
  IO.println s!"X-count mismatches: {xbad.size} {if xbad.isEmpty then "" else toString xbad.toList}"
  IO.println s!"Errors: {errors}"
  IO.println s!"Total wall time: {((← IO.monoMsNow) - t0) / 1000}s"
  return (if disagree.isEmpty && xbad.isEmpty && errors == 0 then 0 else 1)
