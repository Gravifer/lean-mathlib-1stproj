set_option autoImplicit true
set_option relaxedAutoImplicit true

variable (u : Nat) in
example : Sort (u + 1) := Sort u -- * _universes à la Russell_

/- * the term _universe_ is also used for a design pattern in which
   * a datatype is used to represent a subset of types,
   * and a function converts the datatype's constructors into actual types.
   * The values of this datatype are called _codes_ for their types.
-/

inductive NatOrBool where  -- * _universes à la Tarski_
  | nat | bool

abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool

def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat => input.toNat?
  | .bool =>
    match input with
    | "true" => some true
    | "false" => some false
    | _ => none


inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2

def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
/-  Even though every type in the `NestedPairs` universe already has a `BEq` instance,
    type class search **does not** automatically check
    every possible case of a datatype in an instance declaration,
    because there might be infinitely many such cases, as with `NestedPairs`. -/
instance {t : NestedPairs} : BEq t.asType where
  beq x y := x == y
-- * The `t` in the error message stands for an unknown value of type `NestedPairs`.

/- explain to Lean how to find them by recursion on the codes -/
instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y

-- ## typeclasses v universes
-- * typeclass ≅ interfaces universe _à la_ Tarski ≅ sealed class

-- ## Universe of finite types

inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite -- constructor `arr` stands for function type, which is written with an `arr`ow.

abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2 => asType t1 → asType t2

def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse

mutual
  def Finite.enumerate (t : Finite) : List t.asType :=
    match t with
    | .unit => [()]
    | .bool => [true, false]
    | .pair t1 t2 => t1.enumerate.product t2.enumerate
    | .arr t1 t2 => t1.functions t2.enumerate

  def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) :=
    match t with
      | .unit =>
        results.map fun r =>
          fun () => r
      | .bool =>
        (results.product results).map fun (r1, r2) =>
          fun
            | true => r1
            | false => r2
      | .pair t1 t2 =>
        let f1s := t1.functions <| t2.functions results
        f1s.map fun f =>
          fun (x, y) =>
            f x y
      | .arr t1 t2 =>
        let args := t1.enumerate
        let base :=
          results.map fun r =>
            fun _ => r
        args.foldr
          (fun arg rest =>
            (t2.functions rest).map fun more =>
              fun f => more (f arg) f)
          base
end

def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr t1 t2 =>
      t1.enumerate.all fun arg => beq t2 (x arg) (y arg)

--
