import Lean

open Lean Elab Tactic Meta

/-- Assigns `@Eq.refl ty lhs` directly to an equality goal `lhs = rhs`,
    bypassing redundant `Meta.isDefEq` reduction in the elaborator so that
    definitional equality `lhs ≡ rhs` is checked once directly by the Lean 4 C++ kernel. -/
elab "kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  match goalType.eq? with
  | some (ty, lhs, _rhs) =>
    let u ← getLevel ty
    goal.assign (mkApp2 (mkConst ``Eq.refl [u]) ty lhs)
    replaceMainGoal []
  | none => throwTacticEx `kernel_rfl goal "goal is not an equality"
