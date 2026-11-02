---
name: lean-mcp-proving
description: >-
  Interactive Lean 4 theorem proving workflow using the lean-lsp MCP server
  and fast targeted verification scripts. Use whenever proving lemmas, eliminating
  axioms, debugging Lean compiler errors, or verifying soundness modules in
  FourColorTheorem.
---

# Interactive Lean 4 Proving with `lean-lsp` MCP

Use this workflow to prove theorems in `FourColorTheorem` with sub-second feedback and minimal token usage.

## 1. The 4-Step Interactive Proof Loop

1. **Inspect the Goal (`lean_goal`)**:
   - Read the target theorem lines with `read_file` (`StartLine` / `EndLine` within 50 lines).
   - Call `lean_goal` (via `call_mcp_tool` on `lean-lsp`) at the exact `(file_path, line, column)` inside the `by` block to view all hypotheses and the `⊢` target.
2. **Test Candidate Tactics (`lean_multi_attempt`)**:
   - When the next tactic is non-obvious, call `lean_multi_attempt` at the proof position with 2–5 candidate tactic strings (e.g., `["omega", "simp [constructedRank]", "rcases h with ⟨a, b⟩"]`).
   - Pick the tactic that closes the goal or cleanly simplifies the state without touching disk.
3. **Apply the Edit (`edit_file`)**:
   - Write the verified tactic block into the `.lean` file using `edit_file`.
4. **Verify Diagnostics Instantly (`lean_diagnostic_messages`)**:
   - Call `lean_diagnostic_messages` on the edited file to confirm zero compiler errors and zero warnings.

## 2. Fast Verification & Axiom Audit (`verify_fast.ps1`)

After `lean_diagnostic_messages` reports zero errors on your modified file, run the fast verification script (completes in ~2–3 seconds using cached batch `.olean` files):

```powershell
powershell -ExecutionPolicy Bypass -File "c:\Four Color Theorem\.agents\skills\lean-mcp-proving\scripts\verify_fast.ps1"
```

What [verify_fast.ps1](./scripts/verify_fast.ps1) checks:
1. Scans `FourColorTheorem/` for any `\bsorry\b` occurrence.
2. Runs `lake build` on the core mathematical & soundness modules (`ExtendSoundness`, `Representation`, `DReduce`, `CReduce`, `StructuralVerification`, `MainTheorem`, `MasterCertificate`).
3. Prints `#print axioms Math.four_color_theorem` to verify the exact axiom footprint.
