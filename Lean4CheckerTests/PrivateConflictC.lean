module

prelude
public import Init.Core
import Lean4CheckerTests.PrivateConflictA
import Lean4CheckerTests.PrivateConflictB

public theorem all  : True ∧ True := .intro @thm1 @thm2
