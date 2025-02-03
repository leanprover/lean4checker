import Lean4CheckerTests.OpenPrivate

open private Lean.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.mk from Lean.Environment
open private Lean.Kernel.Environment.extensions from Lean.Environment
open private Lean.Kernel.Environment.extraConstNames from Lean.Environment

open Lean in
elab "add_false_constructor" : command => do
  modifyEnv fun env =>
    let constants := env.constants.insert `False.intro $ ConstantInfo.ctorInfo
      { name := `False.intro
        levelParams := []
        type := .const ``False []
        induct := `False
        cidx := 0
        numParams := 0
        numFields := 0
        isUnsafe := false }
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

add_false_constructor

example : False :=
  False.intro
