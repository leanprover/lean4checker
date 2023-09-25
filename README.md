# Recheck a compiled Lean `olean` file using the Lean kernel.

`lake exe lean4checker <module>` will replay the environment in `<module>`,
starting from the environment provided by its imports,
ensuring that the kernel accepts all declarations.

This is not an external verifier, as it uses the Lean kernel itself.
However it is useful as a tool to detect "environment hacking",
i.e. using metaprogramming facilities to build an inconsistent Lean `Environment`.

## Usage

To run this in another Lean project, use for example:
```
lake env path/to/lean4checker Mathlib.Data.Nat.Basic
```

In Mathlib CI we run `lean4checker` in parallel over every file, using:
```
git clone https://github.com/leanprover/lean4checker
cd lean4checker
lake build
cd ..
grep '^import Mathlib.' Mathlib.lean | sed 's/import //' | parallel --halt now,fail=1 'lake env lean4checker/build/bin/lean4checker {}'
```

## Variants

It would be easy to adapt this code to replay the entire environment up to some set of declarations,
starting from an empty environment
(rather than the current implementation, which starts from the environment provided by the imports).
If this would be useful to you, please ask.
