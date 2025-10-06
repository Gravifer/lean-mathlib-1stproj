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
