import Lean
/-! # Expressions -/
#print Lean.Expr
/- inductive Lean.Expr : Type
    number of parameters: 0
  constructors:
    Lean.Expr.bvar    : Nat          → Lean.Expr
    Lean.Expr.fvar    : Lean.FVarId  → Lean.Expr
    Lean.Expr.mvar    : Lean.MVarId  → Lean.Expr
    Lean.Expr.sort    : Lean.Level   → Lean.Expr
    Lean.Expr.const   : Lean.Name    → List Lean.Level → Lean.Expr
    Lean.Expr.app     : Lean.Expr    → Lean.Expr → Lean.Expr
    Lean.Expr.lam     : Lean.Name    → Lean.Expr → Lean.Expr → Lean.BinderInfo → Lean.Expr
    Lean.Expr.forallE : Lean.Name    → Lean.Expr → Lean.Expr → Lean.BinderInfo → Lean.Expr
    Lean.Expr.letE    : Lean.Name    → Lean.Expr → Lean.Expr → Lean.Expr → Bool → Lean.Expr
    Lean.Expr.lit     : Lean.Literal → Lean.Expr
    Lean.Expr.mdata   : Lean.MData   → Lean.Expr → Lean.Expr
    Lean.Expr.proj    : Lean.Name    → Nat → Lean.Expr → Lean.Expr
-/
namespace Playground
open Lean
inductive Expr where
  | bvar    : Nat /- de Bruijn index -/→ Expr         -- bound variables
  | fvar    : FVarId → Expr                           -- free variables ("local constants" or "locals" in Lean 3)
  | mvar    : MVarId → Expr                           -- meta variables (placeholder / hole)
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
    /- Multiple arguments are done using _partial application_: `f x y ↝ app (app f x) y`. -/
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (dependent) arrow (Π-type)
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection
    /- Suppose you have a structure such as `p : α × β`,
        rather than storing the projection `π₁ p` as `app π₁ p`,
        it is expressed as `proj Prod 0 p`. This is for efficiency reasons.
      ([todo] find link to docstring explaining this) -/
end Playground
/- At the `Expr` level, constants are always applied to **all** their arguments, implicit or not. -/

/-! ## De Bruijn Indices -//-
  Lean's "bvars" are usually called just "variables";
  Lean's "loose" is usually called "free";
  and Lean's "fvars" might be called "local hypotheses".
-/

/-! ## Universe Levels -//-
  A universe level is a natural number,
  a universe parameter (introduced with a `universe` declaration),
  a universe metavariable or the maximum of two universes.
-/
#print Lean.Level

/-! ## Constructing Expressions -/
/-! ### Constants -/
open Lean
def z' := Expr.const `Nat.zero []
#eval z' -- Lean.Expr.const `Nat.zero []
def z := Expr.const ``Nat.zero []
#eval z  -- Lean.Expr.const `Nat.zero []
/-
The double-backtick variant checks that the name in fact refers to a defined constant.
It also resolves the given name, making it fully-qualified.
The first expression, `z₁`, is unsafe:
  if we use it in a context where the `Nat` namespace is not open,
  Lean will complain that there is no constant called `zero` in the environment.
In contrast, the second expression, `z₂`,
  contains the fully-qualified name `Nat.zero` and does not have this problem.
-/

/-! ### Function Applications -/
/-! ### Lambda Abstractions -/

/-! ## Exercises -/
namespace mpil
-- 1. Create expression `1 + 2` with `Expr.app`.
def zero:= Expr.const ``Nat.zero []
def one := Expr.app (.const ``Nat.succ []) (.const ``zero [])
def two := Expr.app (.const ``Nat.succ []) (.const ``one [])
def add_1_2 := Expr.app (Expr.app (.const ``Nat.add []) one) two
#eval add_1_2

-- 2. Create expression `1 + 2` with `Lean.mkAppN`.
def add_1_2' := Lean.mkAppN (Expr.const ``Nat.add []) #[one, two]
-- 3. Create expression `fun x => 1 + x`.
def nat : Expr := .const ``Nat []
def oneAdd : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default
def mapOneAddNil : Expr :=
  mkAppN (.const ``List.map [levelZero, levelZero])
    #[nat, nat, oneAdd, .app (.const ``List.nil [levelZero]) nat]
-- 4. [**De Bruijn Indexes**] Create expression `fun a, fun b, fun c, (b * a) + c`.
def mulAdd : Expr :=
  .lam `a nat
    (.lam `b nat
      (.lam `c nat
        (mkAppN (.const ``Nat.add [])
          #[mkAppN (.const ``Nat.mul []) #[.bvar 1, .bvar 2], .bvar 0])
        BinderInfo.default)
      BinderInfo.default)
    BinderInfo.default
-- 5. Create expression `fun x y => x + y`.
def addXY : Expr :=
  .lam `x nat
    (.lam `y nat
      (mkAppN (.const ``Nat.add []) #[.bvar 1, .bvar 0])
      BinderInfo.default)
    BinderInfo.default
-- 6. Create expression `fun x, String.append "hello, " x`.
-- open Lean in
def appendHello : Expr :=
  .lam `x (.const ``String [])
    (mkAppN (.const ``String.append []) #[mkStrLit "hello, ", .bvar 0])
    BinderInfo.default
-- 7. Create expression `∀ x : Prop, x ∧ x`.
def forallProp : Expr :=
  .lam `x (Expr.sort Lean.Level.zero)
    (mkAppN (.const ``And.intro []) #[.bvar 0, .bvar 0])
    BinderInfo.default
-- 8. Create expression `Nat → String`.
def natToString : Expr :=
  Expr.forallE `notUsed
    (Expr.const `Nat []) (Expr.const `String [])
    BinderInfo.default
-- 9. Create expression `fun (p : Prop) => (λ hP : p => hP)`.
def lambdaInLambda : Expr :=
  Expr.lam `p (Expr.sort Lean.Level.zero)
  (
    Expr.lam `hP (Expr.bvar 0)
    (Expr.bvar 0)
    BinderInfo.default
  )
  BinderInfo.default
-- 10. [**Universe levels**] Create expression `Type 6`.
def type6 : Expr := Expr.sort (Level.succ (Level.succ (Level.succ (Level.succ (Level.succ (Level.succ Level.zero))))))
example   : Expr := Expr.sort (Nat.toLevel 7)
end mpil
