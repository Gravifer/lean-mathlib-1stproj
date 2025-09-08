namespace tpil
section cpt10 -- # Typeclass
set_option autoImplicit true
set_option relaxedAutoImplicit true

/- With dependent typing, manually simulating typeclasses can be done as follows -/
namespace Ex
  variable {α : Type} [s : Add α] (x y : α)
  structure Add' (α : Type) where
    add : α → α → α
  #check Add'
  #check Add' α
  #check @Add'.add
  def double (s : Add' α) (x : α) : α :=  s.add x x
  #eval double { add := Nat.add } 10
  #eval double { add := Nat.mul } 10
  #eval double { add := Int.add } 10
/- manually passing the instance is tedious;
  typeclasses make arguments such as `Add α` implicit,
  and use a database of user-defined instances
  to synthesize the desired instances automatically
  through a process known as typeclass resolution. -/
  class Add (α : Type) where
    add : α → α → α
  #check Add
  #check Add α
  #check @Add.add
  /- the square brackets indicate that the argument of type `Add α` is
    __instance implicit__, i.e. that it should be synthesized using typeclass resolution.
    This mechanism is kind of like that of constraints in Haskell
        `Add a => a -> a -> a`
  -/
end Ex

#check default

-- ## §10.1 Chaining Instances
/- What makes typeclass inference powerful is that one can chain instances.
  An instance declaration can in turn depend on an implicit instance of a typeclass.
  This causes typeclass inference to chain through instances recursively,
    backtracking when necessary, in a Prolog-like search. -/
#eval (default : List Empty)
#eval (default : List Unit)
#eval (default : List Nat)
instance : Inhabited (List α) := ⟨[]⟩
#eval (default : List Empty)
#eval (default : List Unit)
#eval (default : List Nat)
instance [Inhabited α]: Inhabited (List α) := ⟨[default]⟩
#eval (default : List Empty)
#eval (default : List Unit)
#eval (default : List Nat)

#print inferInstance
#print inferInstanceAs
#check (inferInstance : Inhabited Nat)
def foo : Inhabited (Nat × Nat) :=  inferInstance
theorem ex : foo.default = (default, default) :=  rfl

-- ## §10.2 toString
structure Person where
  name : String
  age  : Nat
instance : ToString Person where  toString p := p.name ++ "@" ++ toString p.age
#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")

-- ## §10.3 Numerals
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0
instance : OfNat Rational n where  ofNat := { num := n, den := 1, inv := by decide }
instance  : ToString Rational   where  toString r := s!"{r.num}/{r.den}"
#eval (2 : Rational)
#check (2 : Rational)
#check (2 : Nat)
-- ! `nat_lit` is not a function, but a builtin that is handled specially by the parser
#check nat_lit 2

class Monoid (α : Type u) where
  unit : α
  op   : α → α → α
instance [s : Monoid α] : OfNat α (nat_lit 1) where  ofNat := s.unit
def getUnit  [Monoid α] : α :=  1

-- ## §10.4 Outparams
/--error: typeclass instance problem is stuck, it is often due to metavariables
  Inhabited (Nat × ?m.2) -/ #guard_msgs (error) in
#eval (inferInstance : Inhabited (Nat × _))
/- The parameter of the typeclass is an input for the typeclass synthesizer.
  __Outparams__ are a way to guide typeclass resolution by indicating that
  certain parameters of a typeclass can be inferred from the other parameters.
  This is useful when a typeclass has multiple parameters, and some of them
  can be determined from the others. -/
namespace Ex
  class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
    hMul : α → β → γ
  export HMul (hMul)
  instance : HMul Nat Nat Nat where  hMul := Nat.mul
  instance : HMul Nat (Array Nat) (Array Nat) where
    hMul a bs := bs.map (fun b => hMul a b)
  #eval hMul 4 3
  #eval hMul 4 #[2, 3, 4]
end Ex

/- Output parameters are ignored during instance synthesis.  Even when synthesis
    occurs in a context where their values are already determined, the values are ignored.
  Once an instance is found using its input parameters, Lean ensures that
    the already-known values of the output parameters match those which were found.

  Lean also features semi-output parameters, which have
    some features of input parameters and some of output parameters.
  Like input parameters, semi-output parameters are considered when selecting instances.
  Like output parameters, they can be used to instantiate unknown values. However,
    they do not do so uniquely. Instance synthesis with semi-output parameters
    can be more difficult to predict, because the order in which instances
    are considered can determine which is selected, but it is also more flexible. -/

section sect5-- ## Default Instances
/- the `[default_instance]` attribute supports a priority parameter; the default is 100 -/
  @[default_instance 200] -- ! default instance cannot actually be local
  local instance : OfNat Rational n where  ofNat := { num := n, den := 1, inv := by decide }
  instance  : ToString Rational   where  toString r := s!"{r.num}/{r.den}"
  #check 2
end sect5
  #check 2

-- ## §10.6 Local Instances
structure Point where
  x : Nat
  y : Nat
section
  local instance : Add Point where  add a b := { x := a.x + b.x, y := a.y + b.y }
  def double (p : Point) :=  p + p
end -- instance `Add Point` is not active anymore
/--error: failed to synthesize
  HAdd Point Point ?m.5

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command. -/#guard_msgs in
def triple (p : Point) :=  p + p + p
/- `attribute [-instance]` temporarily disables an instance
  * only recommended for debugging purposes
-/

-- ## §10.7 Scoped Instances
/- `scoped` is the persistent version of `local`; a tagged instance
    is only active when you are inside of the namespace or open the namespace.

  `open scoped ⋯` is actually working with this tag -/

-- ## §10.8 Decidable Propositions
/- Classically, every proposition is decidable. But using classical logic, say,
    to define a function by cases, that function will not be computable.
  Thus in Lean, **using the law of the excluded middle to define functions
    can prevent them from being used computationally**.  Thus,
    the standard library assigns a low priority to the `propDecidable` instance.
  Algorithmically speaking, the `Decidable` typeclass can be used
    to infer a procedure that effectively determines
      whether or not the proposition is true.  As a result,
    the typeclass supports such computational definitions when they are possible
    while at the same time allowing a smooth transition
      to the use of classical definitions and classical reasoning. -/
#print Decidable -- * an inductive typeclass!
#print decide
#print of_decide_eq_true
#print  ite
#print dite
#print if_pos
#print if_neg
#check @Decidable.byCases
#check @Decidable.byContradiction
#check @instDecidableAnd
#check @instDecidableOr
#check @instDecidableNot

def step (a b x : Nat) : Nat :=  if x < a ∨ x > b then 0 else 1
set_option pp.explicit true in  #print step

#print Classical.propDecidable

#print Classical.choice
#print Classical.choose
#print Classical.axiomOfChoice
#print Classical.skolem
#print Classical.byCases
#print Classical.byContradiction
#print Classical.not_not
#print Classical.decidable_of_decidable_not
#print Classical.not_forall
#print Classical.not_forall_not
#print Classical.not_exists_not
#print Classical.forall_or_exists_not
#print Classical.exists_or_forall_not

namespace Hidden
open Classical
#print Classical.dite_not
#print Classical.ite_not
#print Classical.decide_not
noncomputable scoped
  instance (priority := low) propDecidable (a : Prop) : Decidable a :=
    choice <| match em a with
      | Or.inl h => ⟨isTrue h⟩
      | Or.inr h => ⟨isFalse h⟩
end Hidden

-- ## §10.9 Managing Type Class Inference
def Set (α : Type u) := α → Prop

/--error: failed to synthesize
  Inhabited (Set α)

Hint: Additional diagnostic information may be available using
the `set_option diagnostics true` command. -/#guard_msgs in
example : Inhabited (Set α) :=  inferInstance -- need the below

example : Inhabited (Set α) :=  inferInstanceAs (Inhabited (α → Prop))

section
set_option trace.Meta.synthInstance true
set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400
variable (α : Type) in
#check_failure (inferInstance : Inhabited (Set α))
end

/- As said, instances in a given context represent a Prolog-like program,
  which gives rise to a backtracking search. Both the efficiency of the program
    and the solutions that are found can depend on the order
      in which the system tries the instance.
    Instances which are declared last are tried first.
    Moreover, if instances are declared in other modules,
      the order in which they are tried depends on
        the order in which namespaces are opened.
      Instances declared in namespaces which are opened later are tried earlier.

  You can change the order that type class instances are tried
    by assigning them a priority. When an instance is declared,
    it is assigned a default priority value.
  You can assign other priorities when defining an instance. -/
class Foo where
  a : Nat
  b : Nat

instance (priority := default + 1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=  rfl

instance (priority := default + 2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=  rfl

-- ## §10.10 Coercion
/- Lean allows us to declare three kinds of coercions:
    - from a family of types to another family of types
        (term to term)
    - from a family of types to the class of sorts
        (term to type)
    - from a family of types to the class of function types
        (term to function)
-/
#synth Coe Bool Prop
#print boolToProp
#print Equivalence
#check HEq

def Set.empty {α : Type u} : Set α := fun _ => False
def Set.mem (a : α) (s : Set α) : Prop := s a
def Set.singleton (a : α) : Set α := fun x => x = a
def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x
notation "{ " a " }" => Set.singleton a
infix:55 " ∪ " => Set.union

def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ List.toSet as
instance : Coe (List α) (Set α) where  coe a := List.toSet a
def s : Set Rational := {1}
#check s ∪ [2, 3]

#print CoeDep
#print CoeSort
#print CoeFun
#print CoeT



end cpt10
