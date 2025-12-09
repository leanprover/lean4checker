/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.CoreM
import Lean.Replay
import Lean4Checker.Lean
import Lean4Checker.Replay
import Lake.Load.Manifest

open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s #[{module}] {} 0 false false
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay' newConstants
  env'.freeRegions
  region.free

unsafe def replayFromFresh (module : Name) : IO Unit := do
  Lean.withImportModules #[{module}] {} fun env => do
    discard <| (← mkEmptyEnvironment).replay' env.constants.map₁

/-- Read the name of the main module from the `lake-manifest`. -/
-- This has been copied from `ImportGraph.getCurrentModule` in the
-- https://github.com/leanprover-community/import-graph repository.
def getCurrentModule : IO Name := do
  match (← Lake.Manifest.load? ⟨"lake-manifest.json"⟩) with
  | none =>
    -- TODO: should this be caught?
    pure .anonymous
  | some manifest =>
    -- TODO: This assumes that the `package` and the default `lean_lib`
    -- have the same name up to capitalisation.
    -- Would be better to read the `.defaultTargets` from the
    -- `← getRootPackage` from `Lake`, but I can't make that work with the monads involved.
    return manifest.name.capitalize

/-- Default number of worker tasks for parallel checking. -/
def defaultNumWorkers : Nat := 32

/-- Parse `--num-workers=N` flag, returning the number of workers. -/
def parseNumWorkers (flags : List String) : IO Nat := do
  for flag in flags do
    if flag.startsWith "--num-workers=" then
      let numStr := flag.drop "--num-workers=".length
      match numStr.toNat? with
      | some n => return n
      | none => throw <| IO.userError s!"Invalid --num-workers value: {numStr}"
  return defaultNumWorkers

/--
Run as e.g. `lake exe lean4checker` to check everything in the current project.
or e.g. `lake exe lean4checker Mathlib.Data.Nat` to check everything with module name
starting with `Mathlib.Data.Nat`.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4checker --fresh Mathlib.Data.Nat.Prime.Basic`
to replay all the constants (both imported and defined in that file) into a fresh environment.
This can only be used on a single file.

Use `--num-workers=N` to control parallelism (default: 32).

This is not an external verifier, simply a tool to detect "environment hacking".
-/
unsafe def main (args : List String) : IO UInt32 := do
  -- Contributor's note: lean4lean is intended to have a CLI interface matching lean4checker,
  -- so if you want to make a change here please either make a sibling PR to
  -- https://github.com/digama0/lean4lean or ping @digama0 (Mario Carneiro) to go fix it.
  initSearchPath (← findSysroot)
  let (flags, args) := args.partition fun s => s.startsWith "-"
  let verbose := "-v" ∈ flags || "--verbose" ∈ flags
  let numWorkers ← parseNumWorkers flags
  let targets ← do
    match args with
    | [] => pure [← getCurrentModule]
    | args => args.mapM fun arg => do
      let mod := arg.toName
      if mod.isAnonymous then
        throw <| IO.userError s!"Could not resolve module: {arg}"
      else
        pure mod
  let mut targetModules := []
  let sp ← searchPathRef.get
  IO.println s!"Searching for modules matching: {targets}"
  (← IO.getStdout).flush
  for target in targets do
    let mut found := false
    for path in (← SearchPath.findAllWithExt sp "olean") do
      if let some m := (← searchModuleNameOfFileName path sp) then
        if target.isPrefixOf m then
          targetModules := targetModules.insert m
          found := true
    if not found then
      throw <| IO.userError s!"Could not find any oleans for: {target}"
  IO.println s!"Found {targetModules.length} modules to check"
  (← IO.getStdout).flush
  if "--fresh" ∈ flags then
    if targetModules.length != 1 then
      throw <| IO.userError s!"--fresh flag is only valid when specifying a single module:\n\
        {targetModules}"
    for m in targetModules do
      if verbose then IO.println s!"replaying {m} with --fresh"
      replayFromFresh m
  else
    -- Use a sliding window of tasks to limit memory usage while maximizing parallelism
    let modules := targetModules.toArray
    let mut pending : Array (Name × Task (Except IO.Error Unit)) := #[]
    let mut nextIdx := 0
    -- Keep the pool filled with up to numWorkers tasks
    while nextIdx < modules.size || !pending.isEmpty do
      -- Fill the pool up to numWorkers
      while pending.size < numWorkers && nextIdx < modules.size do
        let m := modules[nextIdx]!
        pending := pending.push (m, ← IO.asTask (replayFromImports m))
        nextIdx := nextIdx + 1
      -- Wait for at least one task to complete
      if pending.size > 0 then
        let (m, t) := pending[0]!
        match t.get with
        | .error e =>
          IO.eprintln s!"lean4checker found a problem in {m}"
          if verbose then IO.println s!"replaying {m}"
          throw e
        | .ok _ =>
          if verbose then IO.println s!"replaying {m}"
        pending := pending.eraseIdx! 0
  return 0
