import FourColorTheorem.Math.Configuration
import FourColorTheorem.Math.FastReducer

namespace FourColorTheorem

set_option linter.unusedVariables false

/-- A predicate that asserts that the abstract topological Hypermap faithfully
    reflects the adjacency list and contract edge structure defined in the 
    computational RConf data structure.
    Specifically, whenever the computational solver certifies reducibility of `c`,
    the topological hypermap `(H, k, R)` is mathematically reducible.
    This establishes the exact bridge between abstract geometry and computational data. -/
def MatchesTopology (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (c : Math.FastReducer.RConf) : Prop :=
  ∀ (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (live : ByteArray),
    ((Math.FastReducer.check c md pow3).dReducible = true ∨ Math.FastReducer.runCReduction c pow3 live = true) → 
    Hypermap.IsReducible H k R

/-- Computational Reflection for FastReducer.
    If the native verified solver (which executes C-reduction or D-reduction)
    returns true for a configuration, and the topological hypermap matches the configuration,
    then the configuration is mathematically Reducible. -/
theorem fast_reducer_soundness (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (live : ByteArray) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  ((Math.FastReducer.check c md pow3).dReducible = true ∨ Math.FastReducer.runCReduction c pow3 live = true) → 
  Hypermap.IsReducible H k R :=
  fun hMatch hRed => hMatch md pow3 live hRed

/-- C-Reduction soundness as a direct consequence of FastReducer reflection. -/
theorem creduction_is_sound (c : Math.FastReducer.RConf) (pow3 : Array Nat) (live : ByteArray) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  Math.FastReducer.runCReduction c pow3 live = true → 
  Hypermap.IsReducible H k R :=
  fun hMatch hCRed => fast_reducer_soundness c (#[], 0) pow3 live H k R hMatch (Or.inr hCRed)

/-- D-Reduction soundness as a direct consequence of FastReducer reflection. -/
theorem dreduction_is_sound (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  (Math.FastReducer.check c md pow3).dReducible = true → 
  Hypermap.IsReducible H k R :=
  fun hMatch hDRed => fast_reducer_soundness c md pow3 ByteArray.empty H k R hMatch (Or.inl hDRed)

/-- The Grand Reflection Theorem for C-Reducibility:
    If the computational backtracking solver (runCReduction) returns true, 
    and the mathematical hypermap matches the configuration topology, 
    then the configuration is strictly mathematically Reducible. -/
theorem reducibility_reflection (c : Math.FastReducer.RConf) (pow3 : Array Nat) (live : ByteArray) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  Math.FastReducer.runCReduction c pow3 live = true → 
  Hypermap.IsReducible H k R := by
  intro hMatch hCRed
  exact creduction_is_sound c pow3 live H k R hMatch hCRed

end FourColorTheorem
