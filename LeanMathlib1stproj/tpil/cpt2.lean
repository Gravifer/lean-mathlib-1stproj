-- # Dependent types

-- ## §2.6 Variables and Sections
/- Sections are local scopes
    - A `section … end` block introduces local definitions
        (constants, variables, notation, attributes, etc.).
    - Anything declared inside the section can be used inside it.
    - When the section ends, Lean closes over those declarations,
      turning free variables into parameters of the outside definitions. -/

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful

/-  You do not have to indent the lines within a section.
    Nor do you have to name a section, which is to say,
    you can use an anonymous section / end pair.
    If you do name a section, however, you have to close it using the same name.
    Sections can also be nested,
    which allows you to declare new variables incrementally. -/

-- ## §2.8 Dependent typing, explained

-- ### Polymorphism via dependent arrow type

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat
#check cons Bool
#check cons
/-  you can use the command `#check` to inspect the type of
    the following List functions.  The `@` symbol and the difference
    between the round and curly braces will be explained momentarily. -/
#check @List.cons
#check @List.nil
#check @List.length
#check @List.append


section sigma_types -- ### Sigma types
/-  Just as dependent function types `(a : α) → β a` generalize the notion of
 .  a function type `α → β` by allowing `β` to depend on `α`,
 .  **dependent Cartesian product types** `(a : α) × β a` generalize
 .  the Cartesian product α × β in the same way.
 .  Dependent products are also called **sigma types**. -/

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5

-- The functions f and g above denote the same function.
end sigma_types

section implicit_args -- ## §2.9 Implicit Arguments
universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append

#check Lst.cons Nat 0 (Lst.nil Nat)
def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)
#check Lst.append Nat as bs

/- A central feature of dependent type theory:
    terms carry a lot of information,
    and often some of that information can be inferred from the context.
    In Lean, one uses an underscore, `_`, to specify that
    the system should fill in the information automatically.
    This is known as an _implicit argument_. -/
#check Lst.cons _ 0 (Lst.nil _)
def as' : Lst Nat := Lst.nil _
def bs' : Lst Nat := Lst.cons _ 5 (Lst.nil _)
#check Lst.append _ as' bs'

/-  When a function takes an argument that can generally be inferred from context,
    Lean allows you to specify that this argument should, by default, be left implicit.
    This is done by putting the arguments in curly braces. -/
def Lst' (α : Type u) : Type u := List α
def Lst'.cons {α : Type u} (a : α) (as : Lst' α) : Lst' α := List.cons a as
def Lst'.nil {α : Type u} : Lst' α := List.nil
def Lst'.append {α : Type u} (as bs : Lst' α) : Lst' α := List.append as bs

#check Lst'.cons 0 Lst'.nil
def as'' : Lst' Nat := Lst'.nil
def bs'' : Lst' Nat := Lst'.cons 5 Lst'.nil
#check Lst'.append as'' bs''

-- We can also use this device in function definitions:
def ident {α : Type u} (x : α) := x
-- Checking the type of ident requires wrapping it in parentheses to avoid having its signature shown:
#check ident
#check (ident)
/-  Sometimes, however, we may find ourselves in a situation
    where we have declared an argument to a function to be implicit,
    but now want to provide the argument explicitly.
    If foo is such a function, the notation `@foo` denotes
    the same function with all the arguments made explicit. -/
#check @ident

end implicit_args
