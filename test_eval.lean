import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.Present7
import FourColorTheorem.Math.U633Parser

def main : IO Unit := do
  let configs := parseU633String u633_data
  IO.println s!"test7 evaluates to {test7 configs.toList ()}"
