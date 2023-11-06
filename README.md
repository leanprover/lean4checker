# Recheck a compiled Lean `olean` file using the Lean kernel.

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

## Usage

To run this in another Lean project, use:
```
lake env path/to/lean4checker
```
or
```
lake env path/to/lean4checker Mathlib.Data.Nat.Basic
```
to check a single file.


## Caveats

Despite `.olean` files being "fairly cross-platform",
`lean4checker` will reject `.olean`s that were compiled on a system
that  does not use the same bignum library as your system,
so it advisable to not rely on cached `.olean`s.
