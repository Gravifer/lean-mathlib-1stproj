-- # [1.6 Polymorphism](https://leanprover.github.io/functional_programming_in_lean/getting-to-know/polymorphism.html)

/-
def id (x : α) : α := x

def const (x : α) (y : β) : α := x

def compose (f : β → γ) (g : α → β) : α → γ := f ∘ g
-/

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
#check  replaceX
#check (replaceX)
#check  replaceX Nat

-- ## Linked lists
/-
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)
-/
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length α ys)

-- ## Implicit arguments
-- * Arguments can be declared implicit by wrapping them in curly braces
def replaceX1 {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check  List.length
#check (List.length)
#check  List.length (α := Int)

/-
* A Lean naming convention is to define operations
* that might fail in groups using the suffixes
*   `?` for a version that returns an Option,
*   `!` for a version that crashes when provided with invalid input, and
*   `D` for a version that returns a default value when the operation would otherwise fail.
* For instance,
*   `head`  requires the caller to provide mathematical evidence that the list is not empty,
*   `head?` returns an Option, head! crashes the program when passed an empty list, and
*   `headD` takes a default value to return in case the list is empty.
* The question mark and exclamation mark are part of the name, not special syntax,
* as Lean's naming rules are more liberal than many languages.
-/
#eval ([] : List Int).head?
#eval [].head? (α := Int)
