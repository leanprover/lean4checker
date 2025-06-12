open System IO.FS

def t : FilePath := ".lean4checker.tmp"

def exists_or_touch (f : FilePath) : IO Bool := do
  match ← f.pathExists with
  | false => writeFile f "0"; return true
  | true => match ← readFile f with
    | "0" => writeFile f "1"; return true
    | "1" => writeFile f "2"; return true
    | "2" => writeFile f "3"; return false
    | "3" => writeFile f "4"; return false
    | "4" => removeFile f; return false
    | _ => throw <| IO.userError ""

def foo : Bool :=
  match exists_or_touch t () with
  | .ok b _ => b
  | _ => false

/--
Adaptation note: after https://github.com/leanprover/lean4/pull/8419
this exploit requires that we write `by rfl` instead of `rfl` here.
What is going on!?
-/
theorem T1 : true = Lean.reduceBool foo := by rfl
theorem T2 : Lean.reduceBool foo = false := rfl
theorem contradiction : False := nomatch T1.trans T2
