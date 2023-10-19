/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean.Replay
import Lean4Checker.Lean

open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← importModulesCore mod.imports
    |>.run (s := { moduleNameSet := ({} : NameHashSet).insert module })
  let env ← finalizeImport s #[{module}] {} 0
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions
  region.free

unsafe def replayFromFresh (module : Name) : IO Unit := do
  Lean.withImportModules #[{module}] {} 0 fun env => do
    discard <| (← mkEmptyEnvironment).replay env.constants.map₁

/--
Run as e.g. `lake exe lean4checker` to check everything on the Lean search path,
or `lake exe lean4checker Mathlib.Data.Nat.Basic` to check a single file.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4checker --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment.

This is not an external verifier, simply a tool to detect "environment hacking".
-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (flags, args) := args.partition fun s => s.startsWith "--"
  match flags, args with
    | flags, [mod] => match mod.toName with
      | .anonymous => throw <| IO.userError s!"Could not resolve module: {mod}"
      | m =>
        if "--fresh" ∈ flags then
          replayFromFresh m
        else
          replayFromImports m
    | [], _ => do
      let sp ← searchPathRef.get
      let mut tasks := #[]
      for path in (← SearchPath.findAllWithExt sp "olean") do
        if let some m := (← searchModuleNameOfFileName path sp) then
          tasks := tasks.push (m, ← IO.asTask (replayFromImports m))
      for (m, t) in tasks do
        if let .error e := t.get then
          IO.eprintln s!"lean4checker found a problem in {m}"
          throw e
    | _, _ => throw <| IO.userError "--fresh flag is only valid when specifying a single module"
  return 0
