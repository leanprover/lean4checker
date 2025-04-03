#!/usr/bin/env bash
set -euo pipefail

echo "Building lean4checker..."
lake build

echo "Running lean4checker on itself..."
lake -q exe lean4checker Lean4Checker

echo "Begining self-checks..."

check_command() {
    (
        set +e
        local cmd="$1"
        local expected="$2"

        echo "Running $cmd..."
        output=$($cmd 2>&1)

        if [ $? -eq 0 ]; then
            echo "Error: The command '$cmd' succeeded but was expected to fail."
            exit 2
        fi

        if [[ "$output" != "$expected" ]]; then
            echo "Error: The command '$cmd' did not produce the expected error."
            echo "Expected:"
            echo "$expected"
            echo "Got:"
            echo "$output"
            exit 3
        fi
    )
    return 0
}

check_command "lake -q exe lean4checker Lean4CheckerTests.AddFalse" "lean4checker found a problem in Lean4CheckerTests.AddFalse
uncaught exception: (kernel) declaration type mismatch, 'false' has type
  Prop
but it is expected to have type
  False"

check_command "lake -q exe lean4checker Lean4CheckerTests.AddFalseConstructor" "lean4checker found a problem in Lean4CheckerTests.AddFalseConstructor
uncaught exception: No such constructor False.intro"

check_command "lake -q exe lean4checker Lean4CheckerTests.ReplaceAxiom" "lean4checker found a problem in Lean4CheckerTests.ReplaceAxiom
uncaught exception: (kernel) application type mismatch
  False.elim @propext
argument has type
  ∀ {a b : Prop}, Iff a b → Eq a b
but function has type
  False →
    ∀ (x y z n : Nat),
      LT.lt 0 x → LT.lt 0 y → LT.lt 0 z → LT.lt 2 n → Ne (HAdd.hAdd (HPow.hPow x n) (HPow.hPow y n)) (HPow.hPow z n)"

# The 'ReduceBool' test writes to a temporary file.
# We clean up before and afterwards for consistency, although neither should be required.
rm -f .lean4checker.tmp || true
check_command "lake -q exe lean4checker Lean4CheckerTests.ReduceBool" "lean4checker found a problem in Lean4CheckerTests.ReduceBool
uncaught exception: (kernel) (interpreter) unknown declaration 'foo'"
rm -f .lean4checker.tmp || true

check_command "lake -q exe lean4checker --fresh Lean4CheckerTests.UseFalseConstructor" "uncaught exception: (kernel) unknown constant 'False.intro'"

echo "All commands produced the expected errors."
