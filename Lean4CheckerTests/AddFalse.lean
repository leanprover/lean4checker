import Lean4CheckerTests.OpenPrivate

open private Lean.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.extensions from Lean.Environment
open private Lean.Kernel.Environment.extraConstNames from Lean.Environment

open Lean in
elab "add_false" : command => do
  modifyEnv fun env =>
    let constants := env.constants.insert `false $ ConstantInfo.thmInfo
      { name := `false, levelParams := [], type := .const ``False [], value := .const ``False [] }
    -- Before `Environment.mk` became private, we could just use
    -- `{ env with constants }`
    let kenv := Lean.Kernel.Environment.mk constants
      env.toKernelEnv.quotInit
      env.toKernelEnv.diagnostics
      env.toKernelEnv.const2ModIdx
      (Lean.Kernel.Environment.extensions env.toKernelEnv)
      (Lean.Kernel.Environment.extraConstNames env.toKernelEnv)
      env.header
    Lean.Environment.mk kenv (.pure kenv) {} none

add_false

example : False :=
   false
