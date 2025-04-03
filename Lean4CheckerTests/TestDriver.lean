import Lean.Elab.Command
import Lean.Elab.Frontend
import Lean.Environment

def main : IO UInt32 := do
  let proc ← IO.Process.spawn {
    cmd := "bash"
    args := #["test.sh"]
    stdout := IO.Process.Stdio.inherit
    stderr := IO.Process.Stdio.inherit
  }
  let exitCode ← proc.wait
  return exitCode
