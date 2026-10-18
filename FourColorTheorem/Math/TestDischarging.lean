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

def test7 (configs : List Configuration) (_ : Unit) : Bool :=
  let deg := 7
  let outs := readOutlets deg theRules
  verifyTree configs deg (trivial_A_low deg) (trivial_A_upp deg) (present7 ()) outs

def test8 (configs : List Configuration) (_ : Unit) : Bool :=
  let deg := 8
  let outs := readOutlets deg theRules
  verifyTree configs deg (trivial_A_low deg) (trivial_A_upp deg) (present8 ()) outs

def test9 (configs : List Configuration) (_ : Unit) : Bool :=
  let deg := 9
  let outs := readOutlets deg theRules
  verifyTree configs deg (trivial_A_low deg) (trivial_A_upp deg) (present9 ()) outs

def test10 (configs : List Configuration) (_ : Unit) : Bool :=
  let deg := 10
  let outs := readOutlets deg theRules
  verifyTree configs deg (trivial_A_low deg) (trivial_A_upp deg) (present10 ()) outs

def test11 (configs : List Configuration) (_ : Unit) : Bool :=
  let deg := 11
  let outs := readOutlets deg theRules
  verifyTree configs deg (trivial_A_low deg) (trivial_A_upp deg) (present11 ()) outs

/-- The Discharging Trees Verification Predicate:
    Asserts that the RSST proof presentation trees for cartwheel degrees 7 through 11
    are verified by verifyTree against the unavoidable configurations and discharging rules. -/
def DischargingTreesVerified (configs : List Configuration) : Prop :=
  test7 configs () = true ∧
  test8 configs () = true ∧
  test9 configs () = true ∧
  test10 configs () = true ∧
  test11 configs () = true

end Math.Discharging
