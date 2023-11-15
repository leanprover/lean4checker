prelude

set_option autoImplicit false

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

-- The kernel has a hard-coded interpretation for this function
-- which differs from the one we give here
def Nat.add : (@& Nat) → (@& Nat) → Nat := fun _ _ => .succ .zero

inductive Empty : Type
structure Unit : Type

def T (n : Nat) : Type :=
  Nat.rec Empty (fun _ _ => Unit) n

def test (n : Nat) : T (Nat.add n .zero) := Unit.mk
def test0 : T (Nat.add .zero .zero) := test .zero
def empty : Empty := test0

theorem boom (P : Prop) : P := Empty.rec empty
