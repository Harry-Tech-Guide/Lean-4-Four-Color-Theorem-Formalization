import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser

def main : IO Unit := do
  IO.println "--- STARTING ---"
  (<- IO.getStdout).flush
  IO.println "--- Four Color Theorem: Discharging Verifier ---"
  (<- IO.getStdout).flush
  
  let configs := (Math.parseAllConfigs ()).toList
  
  let tests : List (Nat × (List Math.Configuration → Unit → Bool)) := [
    (7, Math.Discharging.test7),
    (8, Math.Discharging.test8),
    (9, Math.Discharging.test9),
    (10, Math.Discharging.test10),
    (11, Math.Discharging.test11)
  ]
  
  let mut all_success := true
  
  for (deg, test_fn) in tests do
    IO.println s!"\nEvaluating Unavoidability for Degree {deg} Cartwheels..."
    (<- IO.getStdout).flush
    let test_val := test_fn configs ()
    if test_val then
      IO.println s!"  SUCCESS: Degree {deg} proof tree fully verified! All branches drain to <= 0 or reduce."
      (<- IO.getStdout).flush
    else
      IO.println s!"  FAILURE: Degree {deg} tree failed bounds verification!"
      (<- IO.getStdout).flush
      all_success := false
      
  if all_success then
    IO.println "\n*** ALL DISCHARGING RULES VERIFIED! Unavoidability holds! ***"
  else
    IO.println "\n*** PROOF FAILED! ***"
