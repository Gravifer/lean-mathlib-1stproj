import LeanMathlib1stproj.fpil.cpt6.«6-2_applicative»

set_option autoImplicit true
set_option relaxedAutoImplicit true

#print Monad

abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr

#print OrElse

def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }
#print Alternative
instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse
variable {f : Type → Type} {α : Type} in
-- #synth (OrElse (f α)) (Alternative f)

#synth Alternative Option
#print Applicative
-- variable {f : Type → Type} {α : Type} in
-- #synth (Applicative.{0, 0} f) (Alternative.{0, 0} f)
#print guard
