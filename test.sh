#!/bin/bash

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

check_command "lake exe lean4checker Lean4Checker.Tests.AddFalse" "uncaught exception: (kernel) declaration type mismatch, 'false' has type
  Prop
but it is expected to have type
  False"

check_command "lake exe lean4checker Lean4Checker.Tests.AddFalseConstructor" "uncaught exception: No such constructor False.intro"

check_command "lake exe lean4checker --fresh Lean4Checker.Tests.UseFalseConstructor" "uncaught exception: (kernel) unknown constant 'False.intro'"

echo "All commands produced the expected errors."
