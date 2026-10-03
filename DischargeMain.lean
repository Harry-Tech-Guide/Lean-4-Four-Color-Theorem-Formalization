import FourColorTheorem.Math.TestDischarging

def main : IO Unit := do
  IO.println "--- Four Color Theorem: Discharging Verifier ---"
  
  let tests : List (Nat × (Unit → Bool)) := [
    (7, fun () => Math.Discharging.test7),
    (8, fun () => Math.Discharging.test8),
    (9, fun () => Math.Discharging.test9),
    (10, fun () => Math.Discharging.test10),
    (11, fun () => Math.Discharging.test11)
  ]
  
  let mut all_success := true
  
  for (deg, test_fn) in tests do
    IO.println s!"\nEvaluating Unavoidability for Degree {deg} Cartwheels..."
    (<- IO.getStdout).flush
    let test_val := test_fn ()
    if test_val then
      IO.println s!"  SUCCESS: Degree {deg} proof tree fully verified! All branches drain to <= 0 or reduce."
    else
      IO.println s!"  FAILURE: Degree {deg} tree failed bounds verification!"
      all_success := false
      
  if all_success then
    IO.println "\n*** ALL DISCHARGING RULES VERIFIED! Unavoidability holds! ***"
  else
    IO.println "\n*** PROOF FAILED! ***"
