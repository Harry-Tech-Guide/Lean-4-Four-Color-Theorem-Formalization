import FourColorTheorem.Math.ComputableReducer

namespace Math
namespace ComputableReducer

def mkAdjFromFlat (n : Nat) (data : Array Bool) : Nat -> Nat -> Bool :=
  fun i j => if h : i * n + j < data.size then data[i * n + j]! else false

/-- The Birkhoff Diamond is config 0 in the unavoidable set. -/
def birkhoff : Configuration := {
  ringSize := 6,
  interiorSize := 4,
  adj := mkAdjFromFlat 10 #[false, true, false, false, false, true, true, false, false, true, true, false, true, false, false, false, true, true, false, false, false, true, false, true, false, false, false, true, false, false, false, false, true, false, true, false, false, true, true, false, false, false, false, true, false, true, false, false, true, true, true, false, false, false, true, false, false, false, false, true, true, true, false, false, false, false, false, true, true, true, false, true, true, true, false, false, true, false, true, false, false, false, false, true, true, false, true, true, false, true, true, false, false, false, true, true, true, false, true, false]
}

/-- Evaluate the number of valid boundary colorings for the Birkhoff Diamond (ring size 6). -/
def totalColorings := (generateRingColorings birkhoff.ringSize).size

/-- Evaluate the number of NON-extending colorings (the live set). -/
def nonExtending := (getNonExtendingColorings birkhoff).size

/-- Evaluate the number of balanced signed matchings for ring size 6. -/
def totalMatchings := (generateBalancedSignedMatchings birkhoff.ringSize).size

-- Check if it is D-reducible!
-- To keep the evaluation from timing out in `#eval`, we just define a boolean.
def birkhoff_is_reducible : Bool := isComputablyDReducible birkhoff

end ComputableReducer
end Math
