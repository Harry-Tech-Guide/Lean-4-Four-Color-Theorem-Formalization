import Lean

namespace Math
namespace Discharging

inductive ProofTree where
  | cond (v : Nat) (m : Int) (trueBranch : ProofTree) (falseBranch : ProofTree) : ProofTree
  | sym (symNum : Nat) (lev : Nat) (a : Nat) (b : Nat) : ProofTree
  | reduce : ProofTree
  | hubcap (hubcap : List (Nat × Nat × Int)) : ProofTree
  deriving Repr, Inhabited, BEq

end Discharging
end Math
