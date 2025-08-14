/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Util.FoldConsts
import Lean.Environment

/-!
# Additional useful definitions in the `Lean` namespace.

These could be moved to the Lean repository.
-/

namespace Lean

def HashMap.keyNameSet (m : Std.HashMap Name α) : NameSet :=
  m.fold (fun s n _ => s.insert n) {}
namespace Environment

def importsOf (env : Environment) (n : Name) : Array Import :=
  if n = env.header.mainModule then
    env.header.imports
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports
    | .none => #[]

end Environment

end Lean
