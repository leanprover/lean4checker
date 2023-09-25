# Replay a Lean environment

`lake exe redeclare <module>` will replay the environment in `<module>`,
ensuring that the kernel accepts all declarations.

This is not an external verifier, but rather a tool to detect "environment hacking",
i.e. using metaprogramming facilities to build an inconsistent Lean `Environment`.
