/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Util.FoldConsts

/-!
# Additional useful definitions in the `Lean` namespace.

These could be moved to the Lean repository.
-/

namespace Lean

namespace NameSet

/-- The union of two `NameSet`s. -/
def append (s t : NameSet) : NameSet :=
  s.mergeBy (fun _ _ _ => .unit) t

instance : Append NameSet where
  append := NameSet.append

def ofList (names : List Name) : NameSet :=
  names.foldl (fun s n => s.insert n) {}

end NameSet

def HashMap.keyNameSet (m : HashMap Name α) : NameSet :=
  m.fold (fun s n _ => s.insert n) {}

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def Expr.getUsedConstants' (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

namespace ConstantInfo

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstants (c : ConstantInfo) : NameSet :=
  c.type.getUsedConstants' ++ match c.value? with
  | some v => v.getUsedConstants'
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .opaqueInfo val => val.value.getUsedConstants'
    | _ => {}

def inductiveVal! : ConstantInfo → InductiveVal
  | .inductInfo val => val
  | _ => panic! "Expected a `ConstantInfo.inductInfo`."

end ConstantInfo

namespace Environment

def importsOf (env : Environment) (n : Name) : Array Import :=
  if n = env.header.mainModule then
    env.header.imports
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports
    | .none => #[]

end Environment

end Lean
