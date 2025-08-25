#check Unit -> Type
#check (n : Nat) → n = n + 0
#check Type → 2 + 2 = 4
variable (u v : Nat)
#check (Type 0 -> Type 1)
#print List
def myListOfList : List (Type → Type) :=
  .cons List .nil
set_option pp.all true in
  #print myListOfList
#print ite

example : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
