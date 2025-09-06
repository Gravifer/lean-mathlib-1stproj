namespace tpil
section cpt6 -- # Lean System Interactions
set_option autoImplicit true
set_option relaxedAutoImplicit true

-- ## §6.1 Messages
/- up till now I've been using `#check_failure` to test that certain expressions do not typecheck.
  There is actually a `#guard_msgs` instead, which checks that certain error messages are produced,
  but allows the file to compile if they are not.
-/

/--
error: Type mismatch
  "Not a number"
has type
  String
but is expected to have type
  Nat
-/#guard_msgs in
def x : Nat := "Not a number"

/--
error: aborting evaluation since the expression depends on the
'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!'
command.
-/#guard_msgs(error) in
#eval (sorry : Nat)

-- ## §6.2 Imports
/- The `import` command can be used to import other files.
  It must be used at the very top of the file, before any other commands.
  Importing is **transitive**. In other words,
    if you import `Foo` and `Foo` imports `Bar`,
    then you also have access to the contents of `Bar`,
    and do not need to import it explicitly. -/

-- ## §6.3 Sections
-- ## §6.4 Namespaces
/- the `protected` keyword makes a name require qualification,
    even if the namespace is opened. -/
protected def Foo.bar : Nat := 1
open Foo
/-- error: Unknown identifier `bar`
-/#guard_msgs in #check bar -- error
#check Foo.bar
/- `open` variants:
  - `open NS (a b c)` only introduce unqual-aliases for `NS.a, NS.b, NS.c`.
  - `open NS hiding (d)` introduces unqual-aliases for all but `NS.d`.
  - `open NS renaming (a → x)` introduces _only_ unqual-aliases `x` for `NS.a`;
                                unmentioned names in `NS` are not introduced.
  // `open NS as P` introduces unqual-aliases `P.a` for `NS.a`. ! Not a thing
  `export ⋯` is like `open ⋯` but also re-exports the names.
-/
open Nat renaming mul → times, add → plus in #eval plus (times 2 2) 3
-- // open Nat as ℕ in #eval ℕ.mul 2 3

-- ## §6.5 Attributes
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

@[local simp] theorem List.isPrefix_self (as : List α) : isPrefix as as := ⟨[], by simp⟩
attribute [simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

/- the `instance` command works by assigning an [instance] attribute to the associated definition. -/
instance : LE (List α) where
  le := isPrefix
variable {α : Type} in #synth LE (List α)
-- is the same as
def instLEList : LE (List α) :=
  { le := isPrefix }
attribute [local instance] instLEList
variable {α : Type} in #synth LE (List α)

theorem List.isPrefix_self' (as : List α) : as ≤ as := ⟨[], by simp⟩

-- ## §6.6 More on Implicit Arguments
/- If Lean displays the type of a term `t` as `{x : α} → β x`, it indicates that
    `x` has been marked as an implicit argument to `t`.
  This means that whenever you write `t`, a placeholder ("hole") is inserted,
    so that `t` is replaced by `@t _`.
  If this is not what's desired, write `@t` instead.

  Notice that implicit arguments are inserted **eagerly**.
  Suppose we define a function `f : (x : Nat) → {y : Nat} → (z : Nat) → Nat`;
    expression `f 7` without further arguments is parsed as `@f 7 _`.
  Double braces `{{}}`(`⦃⦄`) specifies a placeholder only to be added
    before a subsequent explicit argument.
  The expression`f : (x : Nat) → ⦃y : Nat⦄ → (z : Nat) → Nat`
    have `f 7` parsed as-is, while `f 7 3` would be parsed as `@f 7 _ 3`.
-/
variable {α : Type u}
def reflexive   (r : α → α → Prop) : Prop :=  ∀ ( a     : α ), r a a

def symmetric'  (r : α → α → Prop) : Prop :=  ∀ { a b   : α }, r a b → r b a
def transitive' (r : α → α → Prop) : Prop :=  ∀ { a b c : α }, r a b → r b c → r a c
def Euclidean'  (r : α → α → Prop) : Prop :=  ∀ { a b c : α }, r a b → r a c → r b c

theorem th1' {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean' r)
            : symmetric' r :=
              fun {a b : α} =>
              fun (h : r a b) =>
              show r b a from euclr h (reflr _)

theorem th2' {r : α → α → Prop}
            (symmr : symmetric' r) (euclr : Euclidean' r)
            : transitive' r :=
              fun {a b c : α} =>
              fun (rab : r a b) (rbc : r b c) =>
              euclr (symmr rab) rbc

theorem th3' {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean' r)
            : transitive' r :=  th2' (th1' reflr @euclr) @euclr

variable (r : α → α → Prop) (euclr : Euclidean' r) in
#check euclr

-- compare with the below using weak implicits

def symmetric   (r : α → α → Prop) : Prop :=  ∀ {{a b   : α}}, r a b → r b a
def transitive  (r : α → α → Prop) : Prop :=  ∀ {{a b c : α}}, r a b → r b c → r a c
def Euclidean   (r : α → α → Prop) : Prop :=  ∀ {{a b c : α}}, r a b → r a c → r b c

theorem th1 {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : symmetric r :=
            fun {a b : α} =>
            fun (h : r a b) =>
            show r b a from euclr h (reflr _)

theorem th2 {α : Type u} {r : α → α → Prop}
            (symmr : symmetric r) (euclr : Euclidean r)
            : transitive r :=
            fun {a b c : α} =>
            fun (rab : r a b) (rbc : r b c) =>
            euclr (symmr rab) rbc

theorem th3 {α : Type u} {r : α → α → Prop}
            (reflr : reflexive r) (euclr : Euclidean r)
            : transitive r :=  th2 (th1 reflr euclr) euclr

variable (r : α → α → Prop) (euclr : Euclidean r) in
#check euclr

/- * `[]` implicits are used for typeclasses -/


-- ## §6.7 Notation
-- ### §6.7.1 precedence
/-
infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.neg
postfix:max "⁻¹"  => Inv.inv
-- these are macros; unfolds to
notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
 -- `max` is a shorthand for precedence 1024:
notation:1024 arg:1024 "⁻¹" => Inv.inv arg
-/
-- ## §6.8 Coercions
/- Coercions can be explicitly requested using the overloaded `↑` operator. -/

-- ## §6.9 Print debugging
-- examples with equality
#check Eq
#check @Eq
#check Eq.symm
#check @Eq.symm
#print Eq.symm
-- examples with And
#check And
#check And.intro
#check @And.intro-- a user-defined function
universe u in def foo {α : Type u} (x : α) : α := x
#check foo
#check @foo
#print foo

-- ## §6.10 Setting options
set_option pp.explicit true
set_option pp.universes true
set_option pp.notation false
-- `set_option pp.all false` only reverts the options set by `set_option pp.all true`; i.e., explicitly set options wouldn't be toggled.
#check 2 + 2 = 4
#reduce (fun x => x + 2) = (fun x => x + 3)
#check (fun x => x + 1) 1

-- ## §6.11 Lib using
-- ## §6.12 Auto-bound Implicit Arguments
universe u v w in
def compose {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)
-- verbose universe decls can be shortened as
set_option autoImplicit false in
def compose'.{u, v, w}
    {α : Type u} {β : Type v} {γ : Type w}
    (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

-- ## §6.13 Implicit Lambdas
variable {ρ : Type u} {m : Type u → Type v} [Monad m] in
#synth Monad (ReaderT ρ m)

-- ## §6.14 Stub function sugar
#check (· + 1)
#check (2 - ·)
#eval [1, 2, 3, 4, 5].foldl (· * ·) 1
variable (f : Nat → Nat → Nat → Nat := fun x y z => x + y + z) in
#check (f · 1 ·)
#eval [(1, 2), (3, 4), (5, 6)].map (·.1)
#check (Prod.mk · (· + 1))

-- ## §6.16 Named arguments
def sum (xs : List Nat) :=  xs.foldl (init := 0) (·+·)
#eval sum [1, 2, 3, 4]
example {a b : Nat} {p : Nat → Nat → Nat → Prop}
    (h₁ : p a b b) (h₂ : b = a) :  p a a b :=
  Eq.subst (motive := fun x => p a x b) h₂ h₁
def f (x : Nat) (y : Nat := 1) (w : Nat := 2) (z : Nat) :=
  x + y + w - z

-- interaction between named and default arguments

example (x z : Nat) : f (z := z) x = x + 1 + 2 - z := rfl

example (x z : Nat) : f x (z := z) = x + 1 + 2 - z := rfl

example (x y : Nat) : f x y = fun z => x + y + 2 - z := rfl

example : f = (fun x z => x + 1 + 2 - z) := rfl

example (x : Nat) : f x = fun z => x + 1 + 2 - z := rfl

example (y : Nat) : f (y := 5) = fun x z => x + 5 + 2 - z := rfl

def g {α} [Add α] (a : α) (b? : Option α := none) (c : α) : α :=
  match b? with
  | none   => a + c
  | some b => a + b + c

variable [Add α]

example : g = fun (a c : α) => a + c := rfl

example (x : α) : g (c := x) = fun (a : α) => a + x := rfl

example (x : α) : g (b? := some x) = fun (a c : α) => a + x + c := rfl

example (x : α) : g x = fun (c : α) => x + c := rfl

example (x y : α) : g x y = fun (c : α) => x + y + c := rfl

/- You can use `..` to provide missing explicit arguments as `_`.
    This feature combined with named arguments is useful for writing patterns.
  Here is an example: -/
inductive Term where
  | var    (name : String)
  | num    (val : Nat)
  | app    (fn : Term) (arg : Term)
  | lambda (name : String) (type : Term) (body : Term)

def getBinderName : Term → Option String
  | Term.lambda (name := n) .. => some n
  | _ => none

def getBinderType : Term → Option Term
  | Term.lambda (type := t) .. => some t
  | _ => none

/- Ellipses are also useful when explicit args can be automatically inferred,
    and we want to avoid a sequence of `_`s. -/
example (f : Nat → Nat) (a b c : Nat) : f (a + b + c) = f (a + (b + c)) :=
  congrArg f (Nat.add_assoc ..)


end cpt6
end tpil
