/-- Kernel reflexivity tactic (`rfl`) with zero `import Lean` dependency. -/
macro "kernel_rfl" : tactic => `(tactic| rfl)
