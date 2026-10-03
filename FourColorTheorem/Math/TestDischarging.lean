import FourColorTheorem.Math.DischargingAlgo
import FourColorTheorem.Math.Present7
import FourColorTheorem.Math.Present8
import FourColorTheorem.Math.Present9
import FourColorTheorem.Math.Present10
import FourColorTheorem.Math.Present11
import FourColorTheorem.Math.Rules

namespace Math.Discharging

def trivial_A_low (deg : Nat) : Array Nat := mkArray (5 * deg + 2) 5 |>.set! 0 deg
def trivial_A_upp (deg : Nat) : Array Nat := mkArray (5 * deg + 2) 12 |>.set! 0 deg

def test7 : Bool :=
  let deg := 7
  let outs := readOutlets deg theRules
  verifyTree deg (trivial_A_low deg) (trivial_A_upp deg) present7 outs

def test8 : Bool :=
  let deg := 8
  let outs := readOutlets deg theRules
  verifyTree deg (trivial_A_low deg) (trivial_A_upp deg) present8 outs

def test9 : Bool :=
  let deg := 9
  let outs := readOutlets deg theRules
  verifyTree deg (trivial_A_low deg) (trivial_A_upp deg) present9 outs

def test10 : Bool :=
  let deg := 10
  let outs := readOutlets deg theRules
  verifyTree deg (trivial_A_low deg) (trivial_A_upp deg) present10 outs

def test11 : Bool :=
  let deg := 11
  let outs := readOutlets deg theRules
  verifyTree deg (trivial_A_low deg) (trivial_A_upp deg) present11 outs

end Math.Discharging
