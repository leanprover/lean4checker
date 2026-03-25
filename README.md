# ⚠️ Deprecated: lean4checker is now built into Lean

**This repository is deprecated and will be archived.**

`lean4checker` has been merged into the Lean 4 repository itself, and is now distributed as
`leanchecker` with every Lean toolchain (starting from v4.28.0). You no longer need this
separate repository.

## Using the built-in `leanchecker`

To check your project's `.olean` files using the built-in checker, run:
```
lake env leanchecker
```
or to check a single module:
```
lake env leanchecker Mathlib.Data.Nat.Basic
```
or to replay all constants into a fresh environment:
```
lake env leanchecker --fresh Mathlib
```

Because `leanchecker` is part of the toolchain, `lake env` will find it automatically —
no need to build or point to a separate binary.

---

## Original README

Recheck a compiled Lean `olean` file using the Lean kernel.

`lake exe lean4checker <module>` will replay the environment in `<module>`,
starting from the environment provided by its imports,
ensuring that the kernel accepts all declarations.

`lake exe lean4checker` without an argument will run `lean4checker` in parallel on every `.olean`
file on the search path (note that this include Lean 4 and all dependencies of your project).

You can also use `lake exe lean4checker --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment.
This is single threaded, and may be much slower.

This is not an external verifier, as it uses the Lean kernel itself.
However it is useful as a tool to detect "environment hacking",
i.e. using metaprogramming facilities to build an inconsistent Lean `Environment`.
