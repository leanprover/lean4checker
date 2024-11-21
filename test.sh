#!/usr/bin/env bash

lake build

check_command() {
    local cmd="$1"
    local expected="$2"

    output=$($cmd 2>&1)

    if [ $? -eq 0 ]; then
        echo "Error: The command '$cmd' succeeded but was expected to fail."
        exit 1
    fi

    if [[ "$output" != "$expected" ]]; then
        echo "Error: The command '$cmd' did not produce the expected error."
        echo "Expected:"
        echo "$expected"
        echo "Got:"
        echo "$output"
        exit 1
    fi
}

check_command "lake -q exe lean4checker Lean4CheckerTests.AddFalse" "lean4checker found a problem in Lean4CheckerTests.AddFalse
uncaught exception: (kernel) declaration type mismatch, 'false' has type
  Prop
but it is expected to have type
  False"

check_command "lake -q exe lean4checker Lean4CheckerTests.AddFalseConstructor" "lean4checker found a problem in Lean4CheckerTests.AddFalseConstructor
uncaught exception: No such constructor False.intro"

check_command "lake -q exe lean4checker Lean4CheckerTests.ReplaceAxiom" "lean4checker found a problem in Lean4CheckerTests.ReplaceAxiom
uncaught exception: application type mismatch
  False.elim @propext
argument has type
  ∀ {a b : Prop}, (a ↔ b) → a = b
but function has type
  False → ∀ (x y z n : Nat), 0 < x → 0 < y → 0 < z → 2 < n → x ^ n + y ^ n ≠ z ^ n"

check_command "lake -q exe lean4checker --fresh Lean4CheckerTests.UseFalseConstructor" "uncaught exception: (kernel) unknown constant 'False.intro'"

# The 'ReduceBool' test writes to a temporary file.
# We clean up before and afterwards for consistency, although neither should be required.
rm -f .lean4checker.tmp
check_command "lake -q exe lean4checker Lean4CheckerTests.ReduceBool" "lean4checker found a problem in Lean4CheckerTests.ReduceBool
uncaught exception: (kernel) unknown declaration 'foo'"
rm -f .lean4checker.tmp

check_command "lake exe lean4checker Lean4CheckerTests.OverridenPrelude" "TODO"

echo "All commands produced the expected errors."
