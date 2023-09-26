/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean4Checker.Lean

open Lean

structure Context where
  newConstants : HashMap Name ConstantInfo

structure State where
  env : Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

/-- Use the current `Environment` to throw a `KernelException`. -/
def throwKernelException (ex : KernelException) : M Unit := do
    let ctx := { fileName := "", options := ({} : KVMap), fileMap := default }
    let state := { env := (← get).env }
    Prod.fst <$> (Lean.Core.CoreM.toIO · ctx state) do Lean.throwKernelException ex

/-- Add a declaration, possibly throwing a `KernelException`. -/
def addDecl (d : Declaration) : M Unit := do
  match (← get).env.addDecl d with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throwKernelException ex

deriving instance BEq for ConstantVal
deriving instance BEq for ConstructorVal
deriving instance BEq for RecursorRule
deriving instance BEq for RecursorVal

mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants.find? name | unreachable!
    replayConstants ci.getUsedConstants
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      match ci with
      | .defnInfo   info =>
        addDecl (Declaration.defnDecl   info)
      | .thmInfo    info =>
        addDecl (Declaration.thmDecl    info)
      | .axiomInfo  info =>
        addDecl (Declaration.axiomDecl  info)
      | .opaqueInfo info =>
        addDecl (Declaration.opaqueDecl info)
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
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstants
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDecl (Declaration.inductDecl lparams nparams types false)
      -- We postpone checking constructors,
      -- and at the end make sure they are identical
      -- to the constructors generated when we replay the inductives.
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      -- Similarly we postpone checking recursors.
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        addDecl (Declaration.quotDecl)
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
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


unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let (mod, region) ← readModuleData mFile
  let (_, s) ← importModulesCore mod.imports
    |>.run (s := { moduleNameSet := ({} : NameHashSet).insert module })
  let env ← finalizeImport s #[{module}] {} 0
  let mut remaining := {}
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      newConstants := newConstants.insert name ci
      remaining := remaining.insert name
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := { newConstants }) do
      for n in mod.constNames do
        replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
  s.env.freeRegions
  region.free

unsafe def replayFromFresh (module : Name) : IO Unit := do
  Lean.withImportModules #[{module}] {} 0 fun env => do
    let fresh ← mkEmptyEnvironment
    let mut remaining : NameSet := {}
    for (n, ci) in env.constants.map₁.toList do
      -- We skip unsafe constants, and also partial constants.
      -- Later we may want to handle partial constants.
      if !ci.isUnsafe && !ci.isPartial then
        remaining := remaining.insert n
    discard <| StateRefT'.run (s := { env := fresh, remaining }) do
      ReaderT.run (r := { newConstants := env.constants.map₁ }) do
        for n in remaining do
          replayConstant n
        checkPostponedConstructors
        checkPostponedRecursors

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
