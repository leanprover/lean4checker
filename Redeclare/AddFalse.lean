import Lean

def hello := "world"

def f := 2

def g := f

def h := g

open Lean in
elab "add_false1" : command => do
  modifyEnv fun env =>
    let constants := env.constants.insert `false1 $ ConstantInfo.thmInfo
      { name := `false1, levelParams := [], type := .const ``False [], value := .const ``False [] }
    { env with constants }

add_false1

example : False :=
   false1
