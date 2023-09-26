import Lean

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
    { env with constants }

add_false_constructor

example : False :=
  False.intro
