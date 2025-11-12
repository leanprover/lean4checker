module

prelude
public import Init.Core
import Lean4CheckerTests.PrivateConflictA2
import Lean4CheckerTests.PrivateConflictB2

public theorem all  : True ∧ True := .intro thm1' thm2'
