import LeanMathlib1stproj.fpil
-- open FPIL

set_option autoImplicit true
set_option relaxedAutoImplicit true
-- set_option trace.Meta.synthInstance.answer true


#print Function.const
#print Applicative
#synth Applicative Option
#print instAlternativeOption
variable {ε : Type} in
#synth Applicative (Except ε)
#print Except.instMonad

-- ## Subtypes
structure RawInput where
  name : String
  birthYear : String
#print Subtype
/- * Lean has special syntax for Subtype.
    If `p` has type `α → Prop`,
    then the type `Subtype p` can also be written `{x : α // p x}`,
    or even `{x // p x}` when the type can be inferred automatically.
-/
def FastPos : Type := {x : Nat // x > 0}
#print FastPos
namespace FastPos
  def one : FastPos := ⟨1, by simp⟩
  #print one
end FastPos
-- variable {n : Nat} in
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp +arith⟩
#check (3 : FastPos)
#check_failure (0 : FastPos) -- ! error
/-  Subtypes allow efficient representation of validation rules,
    but transfer the burden of maintaining these rules to the user,
    who have to prove the invariants.

    Generally, **use subtypes internally** to a library,
    providing an API automatically ensuring all invariants satisfied,
    with any necessary proofs being internal to the library.

    Checking whether a value of type `α` is in the subtype `{x : α // p x}`
    usually requires that the proposition p x be decidable.
-/

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then -- * when `if` is used with a decidable proposition, a name can be provided.
    some ⟨n, h⟩
  else none

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}

open FPIL in
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
instance : Functor (Validate ε) where
  map f
   | .ok x => .ok (f x)
   | .errors errs => .errors errs
instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩
def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with -- * While this function's type signature makes it suitable to be used as bind in a Monad instance, there are good reasons not to do so.
  | .errors errs => .errors errs
  | .ok x => next x
