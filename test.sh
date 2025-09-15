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

check_command "lake -q exe lean4checker Lean4CheckerTests.ReplaceAxiom" "lean4checker found a problem in Lean4CheckerTests.ReplaceAxiom
uncaught exception: (kernel) application type mismatch
  False.elim @propext
argument has type
  ∀ {a b : Prop}, Iff a b → Eq a b
but function has type
  False →
    ∀ (x y z n : Nat),
      instLTNat.lt 0 x →
        instLTNat.lt 0 y →
          instLTNat.lt 0 z →
            instLTNat.lt 2 n → Ne (instHAdd.hAdd (instHPow.hPow x n) (instHPow.hPow y n)) (instHPow.hPow z n)"

echo "All commands produced the expected errors."
