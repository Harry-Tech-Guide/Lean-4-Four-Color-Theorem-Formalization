import FourColorTheorem.Math.ComputableReducer
import FourColorTheorem.Math.U633Parser

open Math.ComputableReducer

def main : IO Unit := do
  IO.println s!"--- Four Color Theorem: Native Lean 4 Computable Reducer ---"
  let configs := Math.parseAllConfigs
  IO.println s!"Loaded {configs.size} configurations from string parser!"
  
  let mut reducibleCount := 0
  let mut failedCount := 0
  
  let mut tasks : Array (Task (Except IO.Error (Nat × Bool))) := #[]
  
  for i in [0:configs.size] do
    let c := configs[i]!
    let t <- IO.asTask (do
      let reducible := isComputablyDReducible c
      if reducible then
        IO.println s!"SUCCESS: Config {i} (ringSize={c.ringSize}) is D-REDUCIBLE!"
      else
        IO.println s!"FAILURE: Config {i} (ringSize={c.ringSize}) failed D-reduction."
      (IO.getStdout >>= fun s => s.flush)
      return (i, reducible)
    )
    tasks := tasks.push t
      
  for t in tasks do
    let res := t.get
    match res with
    | Except.ok (i, reducible) =>
      if reducible then reducibleCount := reducibleCount + 1 else failedCount := failedCount + 1
    | Except.error e => IO.println s!"Error: {e}"
      
  IO.println s!"\n--- Summary ---"
  IO.println s!"Reducible: {reducibleCount}"
  IO.println s!"Failed: {failedCount}"
