prelude

set_option autoImplicit false

universe u
variable {α : Type u}

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

-- The kernel has a hard-coded interpretation for this function
def Nat.add : (@& Nat) → (@& Nat) → Nat := fun _ _ => .succ .zero
-- But not this function
def Nat.add2 : (@& Nat) → (@& Nat) → Nat := fun _ _ => .succ .zero

theorem eq1 (x : Nat ): Eq (Nat.add x Nat.zero) (Nat.add2 x Nat.zero) := Eq.refl _
theorem eq2 : Eq (Nat.add .zero .zero) (Nat.add2 .zero .zero) := eq1 _
theorem eq3 : Eq (Nat.zero) (.succ .zero) := eq2
