/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

def runLean4Checker (module : String) : IO (UInt32 × String) := do
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["-q", "exe", "lean4checker", module]
  }
  let combined := output.stdout ++ output.stderr
  return (output.exitCode, combined.trimAsciiEnd.toString)

def main : IO UInt32 := do
  IO.println "Building..."
  let buildResult ← IO.Process.output { cmd := "lake", args := #["build"] }
  if buildResult.exitCode != 0 then
    IO.eprintln s!"Build failed:\n{buildResult.stderr}"
    return 1

  IO.println "Running lean4checker on itself..."
  let (exitCode, output) ← runLean4Checker "Lean4Checker"
  if exitCode != 0 then
    IO.eprintln s!"lean4checker failed on Lean4Checker:\n{output}"
    return 1

  IO.println "Running self-checks..."
  let testDir := System.FilePath.mk "Lean4CheckerTests"
  let entries ← testDir.readDir
  let expectedFiles := entries.filter fun e => e.fileName.endsWith ".expected.out"

  let mut failed := false
  for entry in expectedFiles do
    let base := entry.fileName.dropEnd ".expected.out".length |>.toString
    let module := s!"Lean4CheckerTests.{base}"
    IO.println s!"Checking {module}..."

    let expected ← IO.FS.readFile entry.path
    let (exitCode, output) ← runLean4Checker module

    if exitCode == 0 then
      IO.eprintln s!"Error: lean4checker succeeded but was expected to fail for {module}"
      failed := true
      continue

    if output != expected.trimAsciiEnd.toString then
      IO.eprintln s!"Error: Output mismatch for {module}"
      IO.eprintln "Expected:"
      IO.eprintln expected.trimAsciiEnd.toString
      IO.eprintln "Got:"
      IO.eprintln output
      failed := true
      continue

  if failed then
    return 1
  IO.println "All tests passed."
  return 0
