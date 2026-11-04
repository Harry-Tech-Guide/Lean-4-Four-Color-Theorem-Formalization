import Lean
import Lean.Replay

open Lean

/-!
# Fresh Kernel Replay Verifier (`FreshReplay.lean`)

Note on Lean `v4.11.0`'s built-in `Lean.Environment.Replay.addDecl`:
In Lean `v4.11.0`, `Replay.addDecl` calls `env.addDecl {} d`, which passes empty `Options` (`{}`)
and therefore enforces the default `maxHeartbeats = 200000` (`200,000,000` cumulative C++ kernel
heartbeats across the thread, since `g_heartbeat` is never reset inside `Environment.replay`).
In Lean `v4.28.0+` (`leanchecker`), the Lean FRO fixed `Replay.addDecl` to call
`env.addDeclCore 0 0 d (cancelTk? := none)` (`maxHeartbeats = 0`, unlimited) and to replay `Eq`
prior to `Declaration.quotDecl`.

This file backports that exact `addDeclCore 0` fix to `v4.11.0` and replays the complete
transitive dependency cone of `Solution.four_color_theorem` into a fresh `mkEmptyEnvironment`.
-/

namespace FreshKernelReplay

structure Context where
  newConstants : HashMap Name ConstantInfo

structure State where
  env : Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  replayedCount : Nat := 0

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def throwKernelException (ex : KernelException) : M Unit := do
  let ctx := { fileName := "", options := Options.empty, fileMap := default }
  let state := { env := (← get).env }
  Prod.fst <$> (Lean.Core.CoreM.toIO · ctx state) do Lean.throwKernelException ex

/-- Backport of Lean v4.28.0+ `Replay.addDecl`: uses `addDeclCore 0` (unlimited heartbeats). -/
def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 d none with
  | .ok env =>
    let c := (← get).replayedCount + 1
    modify fun s => { s with env := env, replayedCount := c }
    if c % 2000 == 0 then
      IO.println s!"  [FreshReplay] Replayed {c} declarations into fresh kernel..."
  | .error ex => throwKernelException ex

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants.find? name | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      match ci with
      | .defnInfo   info => addDecl (Declaration.defnDecl   info)
      | .thmInfo    info => addDecl (Declaration.thmDecl    info)
      | .axiomInfo  info => addDecl (Declaration.axiomDecl  info)
      | .opaqueInfo info => addDecl (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| ((← read).newConstants.find! n)
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure ((← read).newConstants.find! n))
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDecl (Declaration.inductDecl lparams nparams types false)
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        replayConstant `Eq
        addDecl (Declaration.quotDecl)
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.constants.find? ctor, (← read).newConstants.find? ctor with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.constants.find? ctor, (← read).newConstants.find? ctor with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

def replay (newConstants : HashMap Name ConstantInfo) (env : Environment) : IO Environment := do
  let mut remaining : NameSet := {}
  for (n, ci) in newConstants.toList do
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := { newConstants }) do
      for n in remaining do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  return s.env

end FreshKernelReplay

/-- Collect the complete transitive dependency cone of `root` in `env`
    (including inductive types, constructors, and recursors of all used constants). -/
partial def collectCone (env : Environment) (root : Name) : HashMap Name ConstantInfo := Id.run do
  let mut map : HashMap Name ConstantInfo := {}
  let mut visited : NameSet := {}
  let mut queue : Array Name := #[root]
  while !queue.isEmpty do
    let n := queue.back
    queue := queue.pop
    if !visited.contains n then
      visited := visited.insert n
      if let some ci := env.constants.map₁.find? n then
        map := map.insert n ci
        for dep in ci.getUsedConstantsAsSet do
          if !visited.contains dep then
            queue := queue.push dep
        match ci with
        | .inductInfo info =>
          for indName in info.all do
            if !visited.contains indName then queue := queue.push indName
            if let some indCi := env.constants.map₁.find? indName then
              for ctor in indCi.inductiveVal!.ctors do
                if !visited.contains ctor then queue := queue.push ctor
          let recName := mkRecName n
          if !visited.contains recName then queue := queue.push recName
        | .ctorInfo info =>
          if !visited.contains info.induct then queue := queue.push info.induct
        | .recInfo info =>
          for indName in info.all do
            if !visited.contains indName then queue := queue.push indName
        | _ => pure ()
  return map

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  for mod in #[`Spec, `Challenge, `SanityChecks] do
    withImportModules #[{ module := mod }] {} (trustLevel := 0) fun env => do
      let numConsts := env.constants.map₁.size
      IO.println s!"Replaying all {numConsts} constants in {mod} (env.constants.map₁) into mkEmptyEnvironment..."
      discard <| FreshKernelReplay.replay env.constants.map₁ (← mkEmptyEnvironment)
      IO.println s!"SUCCESS: All {numConsts} constants in {mod} verified from scratch by a fresh kernel!"
  let mod : Name := `Solution
  IO.println s!"Loading compiled .olean environment for {mod}..."
  withImportModules #[{ module := mod }] {} (trustLevel := 0) fun env => do
    let cone := collectCone env `four_color_theorem
    IO.println s!"Replaying {cone.size} transitive constants in {mod}.four_color_theorem into mkEmptyEnvironment..."
    discard <| FreshKernelReplay.replay cone (← mkEmptyEnvironment)
    IO.println s!"SUCCESS: All {cone.size} declarations in {mod}.four_color_theorem verified from scratch by a fresh kernel!"
