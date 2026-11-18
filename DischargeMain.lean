module

public import FourColorTheorem.Math.TestDischarging
public import FourColorTheorem.Math.U633Parser

@[expose] public section

def main : IO Unit := do
  IO.println "--- STARTING ---"
  (<- IO.getStdout).flush
  IO.println "--- Four Color Theorem: Discharging Verifier ---"
  (<- IO.getStdout).flush
  
  let configs := (Math.parseAllConfigs ()).toList
  
  let runTest (deg : Nat) (t : Math.Discharging.ProofTree) (configs : List Math.Configuration) (_ : Unit) : Bool :=
    let outs := Math.Discharging.readOutlets deg Math.Discharging.theRules
    Math.Discharging.verifyTreeFull configs deg (Math.Discharging.trivial_A_low deg) (Math.Discharging.trivial_A_upp deg) t outs

  let tests : List (Nat × (List Math.Configuration → Unit → Bool)) := [
    (7, runTest 7 (Math.Discharging.present7 ())),
    (8, runTest 8 (Math.Discharging.present8 ())),
    (9, runTest 9 (Math.Discharging.present9 ())),
    (10, runTest 10 (Math.Discharging.present10 ())),
    (11, runTest 11 (Math.Discharging.present11 ()))
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
