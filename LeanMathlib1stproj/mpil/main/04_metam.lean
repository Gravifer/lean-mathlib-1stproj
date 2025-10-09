import Lean
import Batteries
/-! # `MetaM` -/
/- * Lean 4 metaprogramming monad zoo
- `CoreM` gives access to the *environment*, i.e. the set of things that
  have been declared or imported at the current point in the program.
- `MetaM` gives access to the *metavariable context*, i.e. the set of
  metavariables that are currently declared and the values assigned to them (if
  any).
- `TermElabM` gives access to various information used during elaboration.
- `TacticM` gives access to the list of current goals.

- `CommandElabM` extends `MetaM` but is incomparable with `TermElabM`.
-/
open Lean Lean.Expr Lean.Meta

/-! ## Metavariables -/
/-! ### Tactic Communication via Metavariables -/
/-! ### Basic Operations -/
#print Lean.Meta.mkFreshExprMVar
#print Lean.Meta.mkFreshExprMVarAt
#print Lean.MVarId.assign
#print Lean.MVarId.getDecl
#print Lean.MVarId.getType
#print Lean.getExprMVarAssignment?
#print Lean.MVarId.isAssigned
#print Lean.instantiateMVars
#print Lean.MVarId.instantiateMVars -- in Batteries

#eval show MetaM Unit from do
  -- Create two fresh metavariables of type `Nat`.
  let mvar1 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar1)
  let mvar2 ← mkFreshExprMVar (Expr.const ``Nat []) (userName := `mvar2)
  -- Create a fresh metavariable of type `Nat → Nat`. The `mkArrow` function
  -- creates a function type.
  let mvar3 ← mkFreshExprMVar (← mkArrow (.const ``Nat []) (.const ``Nat []))
    (userName := `mvar3)

  -- Define a helper function that prints each metavariable.
  let printMVars : MetaM Unit := do
    IO.println s!"  meta1: {← instantiateMVars mvar1}"
    IO.println s!"  meta2: {← instantiateMVars mvar2}"
    IO.println s!"  meta3: {← instantiateMVars mvar3}"

  IO.println "Initially, all metavariables are unassigned:"
  printMVars

  -- Assign `mvar1 : Nat := ?mvar3 ?mvar2`.
  mvar1.mvarId!.assign (.app mvar3 mvar2)
  IO.println "After assigning mvar1:"
  printMVars

  -- Assign `mvar2 : Nat := 0`.
  mvar2.mvarId!.assign (.const ``Nat.zero [])
  IO.println "After assigning mvar2:"
  printMVars

  -- Assign `mvar3 : Nat → Nat := Nat.succ`.
  mvar3.mvarId!.assign (.const ``Nat.succ [])
  IO.println "After assigning mvar3:"
  printMVars
-- Initially, all metavariables are unassigned:
--   meta1: ?_uniq.1
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar1:
--   meta1: ?_uniq.3 ?_uniq.2
--   meta2: ?_uniq.2
--   meta3: ?_uniq.3
-- After assigning mvar2:
--   meta1: ?_uniq.3 Nat.zero
--   meta2: Nat.zero
--   meta3: ?_uniq.3
-- After assigning mvar3:
--   meta1: Nat.succ Nat.zero
--   meta2: Nat.zero
--   meta3: Nat.succ

/-! ### Local Contexts -/
#print Lean.getLCtx
#print Lean.MVarId.withContext
#print Lean.FVarId.getDecl
#print Lean.Meta.getLocalDeclFromUserName
#print ForIn

def myAssumption (mvarId : MVarId) : MetaM Bool := do
  -- Check that `mvarId` is not already assigned.
  mvarId.checkNotAssigned `myAssumption
  -- Use the local context of `mvarId`.
  mvarId.withContext do
    -- The target is the type of `mvarId`.
    let target ← mvarId.getType
    -- For each hypothesis in the local context:
    for ldecl in ← getLCtx do
      -- If the hypothesis is an implementation detail, skip it.
      if ldecl.isImplementationDetail then
        continue
      -- If the type of the hypothesis is definitionally equal to the target
      -- type:
      if ← isDefEq ldecl.type target then
        -- Use the local hypothesis to prove the goal.
        mvarId.assign ldecl.toExpr
        -- Stop and return true.
        return true
    -- If we have not found any suitable local hypothesis, return false.
    return false
#print Lean.MVarId.checkNotAssigned
#print Lean.Meta.isDefEq
#print Lean.LocalDecl.toExpr

/-! ### Metavariable Depth-/
#print Lean.Meta.withNewMCtxDepth

/-! ## Computation -/
/-! ### Full Normalisation -/
#print Lean.Meta.reduce
#print Lean.Expr
#print Lean.Literal
/- Optional arguments of reduce allow us to skip certain parts of an expression.
  E.g. `reduce e (explicitOnly := true)` does not normalise any implicit arguments in the expression `e`.
  This yields better performance. -/
#reduce (· + 2) $ 3

/-! ### Transparency -/
/- An ugly but important detail of Lean 4 metaprogramming is that
  any given expression does not have a single normal form.
  Rather, it has a normal form up to a given *transparency*. -/
#print Lean.Meta.TransparencyMode
#print Lean.Meta.getTransparency
/- The four settings unfold progressively more constants:
  - `reducible`: unfold only constants tagged with the `@[reducible]` attribute.
      Note that `abbrev` is a shorthand for `@[reducible] def`.
  - `instances`: unfold reducible constants and constants tagged with the `@[instance]` attribute.
      Again, the `instance` command is a shorthand for `@[instance] def`.
  - `default`: unfold all constants except those tagged as `@[irreducible]`.
  - `all`: unfold all constants, even those tagged as `@[irreducible]`. -/
#print Lean.Meta.withTransparency
#print Lean.Meta.withReducible
#print Lean.Meta.ppExpr
def traceConstWithTransparency (md : TransparencyMode) (c : Name) :
    MetaM Format := do
  ppExpr (← withTransparency md $ reduce (.const c []))

@[irreducible] def irreducibleDef : Nat      := 1
def                defaultDef     : Nat      := irreducibleDef + 1
abbrev             reducibleDef   : Nat      := defaultDef + 1
#eval traceConstWithTransparency .reducible ``reducibleDef
set_option pp.explicit true in
#eval traceConstWithTransparency .reducible ``reducibleDef
#eval traceConstWithTransparency .instances ``reducibleDef
#eval traceConstWithTransparency .default   ``reducibleDef
#eval traceConstWithTransparency .all       ``reducibleDef

/-! ### Weak Head Normalisation -/
#print whnf
#print Lean.Meta.whnfImp
open Lean.Elab.Term in
def whnf' (e : TermElabM Syntax) : TermElabM Format := do
  let e ← elabTermAndSynthesize (← e) none
  ppExpr (← whnf e)
#eval whnf' `(List.cons 1 [])
#eval whnf' `(List.cons (1 + 1) [])
#eval withTransparency .reducible $ whnf' `(List.append [1] [2])
#eval whnf' `(λ x : Nat => x)
#eval whnf' `(∀ x, x > 0)
#eval whnf' `(Type 3)
#eval whnf' `((15 : Nat))
/- Some more expressions in WHNF which are a bit tricky to test:
    ```lean
      ?x 0 1  -- Assuming the metavariable `?x` is unassigned, it is in WHNF.
      h  0 1  -- Assuming `h` is a local hypothesis, it is in WHNF.
    ```
  Some tricky examples *not* in WHNF:
    ```lean
      ?x 0 1 -- Assuming `?x` is assigned (e.g. to `Nat.add`),
                  its application is not in WHNF.
      h 0 1  -- Assuming `h` is a local definition (e.g. with value `Nat.add`),
                  its application is not in WHNF.
    ```
-/
def matchAndReducing (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) Q) => return some (P, Q)
  | _ => return none
def matchAndReducing₂ (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match ← whnf e with
  | (.app (.app (.const ``And _) P) e') =>
    match ← whnf e' with
    | (.app (.app (.const ``And _) Q) R) => return some (P, Q, R)
    | _ => return none
  | _ => return none

/-! ### Definitional Equality -/
#print Lean.Meta.isDefEq
#print Lean.Meta.isExprDefEq
#print MetavarKind

/-! ## Constructing Expressions -/
/-! ### Applications -/
set_option autoImplicit true in
def appendAppend (xs ys : List α) := (xs.append ys).append xs
set_option pp.all true in
set_option pp.explicit true in
#print appendAppend

#print Lean.Meta.mkAppM --
#print Lean.Meta.mkAppM'--
#print Lean.Meta.mkAppOptM
#print Lean.Meta.mkAppOptM'

/-! ### Lambdas and Foralls -/
/- Instead of using `bvar`s directly, the Lean way
    is to construct expressions with bound variables in two steps:
1. Construct the body of the expression (in our example: the body of the lambda),
    using temporary local hypotheses (`fvar`s) to stand in for the bound variables.
2. Replace these `fvar`s with `bvar`s and, at the same time,
    add the corresponding lambda binders.
-/
#print Lean.Meta.withLocalDecl
#print Lean.Meta.mkLambdaFVars
#print Lean.Meta.mkForallFVars
#print Lean.Meta.mkForallFVars'
#print Lean.mkArrow

/-! ### Deconstructing Expressions -/
#print Lean.Meta.forallTelescope
#print Lean.Meta.forallTelescopeReducing
#print Lean.Meta.forallBoundedTelescope
#print Lean.Meta.forallMetaTelescope
#print Lean.Meta.forallMetaTelescopeReducing
#print Lean.Meta.forallMetaBoundedTelescope
#print Lean.Meta.lambdaTelescope
--// #print Lean.Meta.lambdaTelescopeReducing --? No longer athing?
#print Lean.Meta.lambdaBoundedTelescope
#print Lean.Meta.lambdaMetaTelescope

/-! ## Backtracking -/
