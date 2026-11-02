# Lean 4 Formalization & MCP Proving Rules

Follow these rules for all theorem-proving and verification work in `c:\Four Color Theorem`.

## 1. MCP-First Interactive Proving (`lean-lsp`)

- **Always use the `lean-lsp` MCP server** for inspecting proof states, checking diagnostics, and testing tactics before running any CLI build commands:
  - `lean_goal`: Query the exact proof state (`⊢` goal and local hypotheses) at `(file_path, line, column)`.
  - `lean_diagnostic_messages`: Retrieve live compiler errors, warnings, and unsolved goals for a modified `.lean` file in under a second.
  - `lean_multi_attempt`: Test an array of candidate tactic snippets at a proof point in a single call without modifying the file on disk.
  - `lean_hover_info`: Inspect the type signature and documentation of any definition or lemma at `(file_path, line, column)`.
  - `lean_local_search`: Search for declarations across the repository.
- **Do NOT spawn cold `lake env lean` or `lake build` processes** to inspect proof goals or iterate on broken tactics.

## 2. Targeted Module Building & Cache Protection

- **Never run concurrent `lake build` commands.** Overlapping builds corrupt the `.lake` build cache.
- **Never run full `lake build FourColorTheorem`** (all 204 targets including 138 `native_decide` batch certificates) during iterative proof development.
- For fast verification of soundness, discharging, and topology modules (< 3 seconds), run:
  ```powershell
  powershell -ExecutionPolicy Bypass -File "c:\Four Color Theorem\.agents\skills\lean-mcp-proving\scripts\verify_fast.ps1"
  ```
- Only run full `lake build FourColorTheorem` when `Batch/` files or `FastReducer.lean` execution behavior is modified.

## 3. Subagent Configuration & Token Economy

- When defining a custom proving subagent via `define_subagent`, always set `EnableMCPTools: true` and `EnableWriteTools: true`.
- When invoking any subagent via `invoke_subagent`, **always set `Model: 'flash'`** to conserve credits.
- Read only narrow line ranges (`StartLine` / `EndLine` of 40–80 lines) around the target declaration. Never dump full files or repeat long build logs.

## 4. Mathematical & Proof Integrity

- **Zero `sorry`**: Never commit or report completion with any `sorry` in the codebase.
- **Zero Unapproved Axioms**: Never introduce new `axiom` declarations to bypass proof obligations.
- **Zero Constant-`true` Stubs or Weakened Definitions**: Never weaken a theorem statement or replace an executable check with a constant `true`.
