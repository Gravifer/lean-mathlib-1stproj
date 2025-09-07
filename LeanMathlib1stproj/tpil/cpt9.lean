namespace tpil
section cpt9 -- # Structures and Records
set_option autoImplicit true
set_option relaxedAutoImplicit true
/- A non-recursive inductive type that contains only one constructor
    is called a *structure* or *record*. -/

section sect1 -- ## Defining Structures
/- The `structure` command is essentially a _front end_ for defining inductive data types.
  Every `structure` declaration introduces a namespace with the same name.-/
  structure Point (α : Type u) where
    mk ::
    x : α
    y : α
  deriving Repr
  #check Point      -- a Type
  #check @Point.rec -- the eliminator
  #check @Point.mk  -- the constructor
  #check @Point.x   -- a projection
  #check @Point.y   -- a projection
end sect1

-- ## §9.2 Objects
/- Fields can be marked as implicit using curly braces;
    implicit fields become implicit parameters to the constructor.
  If the value of a field is not specified, Lean tries to infer it.
    If the unspecified fields cannot be inferred, Lean flags an error
    indicating the corresponding placeholder could not be synthesized. -/
structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β
#check { a := 10, b := true : MyStruct }

def p : Point Nat :=  { x := 1, y := 2 }
#eval { p with y := 3 }
#eval { p with x := 4 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α
def q : Point3 Nat :=  { x := 5, y := 5, z := 5 }
def r : Point3 Nat :=  { p, q with x := 6 }
example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl

-- ## §9.3 Inheritance
inductive Color where  | red | green | blue
structure ColorPoint (α : Type u) extends Point α where
  c : Color


end cpt9
