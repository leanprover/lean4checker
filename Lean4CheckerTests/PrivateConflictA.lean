module

prelude
public import Init.Core

def foo : Nat := 42

public theorem thm1 : True := if foo = 42 then trivial else trivial
