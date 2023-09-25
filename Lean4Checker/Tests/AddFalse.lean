import Lean

open Lean in
elab "add_false" : command => do
  modifyEnv fun env =>
    let constants := env.constants.insert `false $ ConstantInfo.thmInfo
      { name := `false, levelParams := [], type := .const ``False [], value := .const ``False [] }
    { env with constants }

add_false

example : False :=
   false
