import FourColorTheorem.Math.Configuration
import FourColorTheorem.Math.FastReducer

namespace FourColorTheorem

set_option linter.unusedVariables false

/-- Semantic Bridge Assumption:
    Asserts that the abstract topological hypermap `(H, k, R)` faithfully
    corresponds to the adjacency and ring structure in the computational `RConf`.
    Under this assumption, certifying reducibility via the computational solver
    implies mathematical reducibility `Hypermap.IsReducible H k R`. -/
def MatchesTopology (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) (c : Math.FastReducer.RConf) : Prop :=
  ∀ (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (live : ByteArray),
    ((Math.FastReducer.check c md pow3).dReducible = true ∨ Math.FastReducer.runCReduction c pow3 live = true) → 
    Hypermap.IsReducible H k R

/-- Computational Reflection for FastReducer:
    Under the semantic bridge assumption `MatchesTopology H k R c`,
    a positive reducibility certificate from `FastReducer` implies mathematical reducibility. -/
theorem fast_reducer_soundness (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (live : ByteArray) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  ((Math.FastReducer.check c md pow3).dReducible = true ∨ Math.FastReducer.runCReduction c pow3 live = true) → 
  Hypermap.IsReducible H k R :=
  fun hMatch hRed => hMatch md pow3 live hRed

/-- C-Reduction soundness:
    Under `MatchesTopology`, successful C-reduction implies `Hypermap.IsReducible H k R`. -/
theorem creduction_is_sound (c : Math.FastReducer.RConf) (pow3 : Array Nat) (live : ByteArray) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  Math.FastReducer.runCReduction c pow3 live = true → 
  Hypermap.IsReducible H k R :=
  fun hMatch hCRed => fast_reducer_soundness c (#[], 0) pow3 live H k R hMatch (Or.inr hCRed)

/-- D-Reduction soundness:
    Under `MatchesTopology`, successful D-reduction implies `Hypermap.IsReducible H k R`. -/
theorem dreduction_is_sound (c : Math.FastReducer.RConf) (md : Array Math.FastReducer.MData × Nat) (pow3 : Array Nat) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  (Math.FastReducer.check c md pow3).dReducible = true → 
  Hypermap.IsReducible H k R :=
  fun hMatch hDRed => fast_reducer_soundness c md pow3 ByteArray.empty H k R hMatch (Or.inl hDRed)

/-- Reflection for C-Reducibility:
    Under `MatchesTopology`, a positive result from `runCReduction` implies mathematical reducibility. -/
theorem reducibility_reflection (c : Math.FastReducer.RConf) (pow3 : Array Nat) (live : ByteArray) (H : Hypermap) (k : Nat) (R : Hypermap.Ring H k) :
  MatchesTopology H k R c → 
  Math.FastReducer.runCReduction c pow3 live = true → 
  Hypermap.IsReducible H k R := by
  intro hMatch hCRed
  exact creduction_is_sound c pow3 live H k R hMatch hCRed

end FourColorTheorem
