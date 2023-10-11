def foo : Bool :=
  match IO.getRandomBytes 1 () with
  | .ok bs _ => bs[0]! >= 128
  | _ => false
theorem T1 : false = Lean.reduceBool foo := rfl
theorem T2 : Lean.reduceBool foo = true := rfl
theorem contradiction : False := nomatch T1.trans T2
