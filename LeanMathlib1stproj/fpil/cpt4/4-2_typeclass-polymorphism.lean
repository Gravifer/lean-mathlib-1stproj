-- #【Typeclass Polymorphism](https://leanprover.github.io/functional_programming_in_lean/type-classes/polymorphism.html)

set_option autoImplicit true
set_option eval.pp true
set_option eval.type true
set_option eval.derive.repr true
-- set_option pp.all true
-- set_option pp.explicit true
-- set_option pp.universes true
set_option pp.numericTypes true
set_option pp.notation true

#check @IO.println
#check @List.length
#check @List.sum
#print Zero
#check Zero Nat
#print Add

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr
variable (α : Type) in
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

#check Add.add
#check @OfNat.ofNat
variable (α : Type) in
#check Add (PPoint α)
#print OfNat

#eval Nat.zero
