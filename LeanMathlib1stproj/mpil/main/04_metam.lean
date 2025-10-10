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
--// #print Lean.Meta.lambdaTelescopeReducing --? No longer a thing?
#print Lean.Meta.lambdaBoundedTelescope
#print Lean.Meta.lambdaMetaTelescope

/-! ## Backtracking -/
#print Lean.MonadBacktrack
#print Lean.saveState
#print Lean.Meta.SavedState
#print Lean.Meta.SavedState.restore
#print Lean.restoreState
--// #print Lean.Core.restore
#print Lean.withoutModifyingState
#print Lean.observing?
#print Lean.commitIfNoEx

/-! ## Exercises -/
/- 1. [**Metavariables**] Create a metavariable with type `Nat`, and assign to it value `3`.
        Notice that changing the type of the metavariable from `Nat` to, for example,
        `String`, doesn't raise any errors - that's why, as was mentioned, we must make sure
        > (a) that `val` must have the target type of `mvarId` and
        > (b) that `val` must only contain `fvars` from the local context of `mvarId`. -/
  #eval show MetaM Unit from do
    let hi ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `hi)
    IO.println s!"value in hi: {← instantiateMVars hi}" -- ?_uniq.1
    hi.mvarId!.assign (
      Expr.app (Expr.const `Nat.succ []) (
        Expr.app (Expr.const `Nat.succ []) (
          Expr.app (Expr.const `Nat.succ []) (
            Expr.const ``Nat.zero []))))
    IO.println s!"value in hi: {← instantiateMVars hi}" -- Nat.succ Nat.zero
/- 2. [**Metavariables**] What would
      `instantiateMVars (Lean.mkAppN (Expr.const 'Nat.add []) #[mkNatLit 1, mkNatLit 2])`
    output? -/
  #eval show MetaM Unit from do -- identity; no mvar to instantiate
    let instantiatedExpr ← instantiateMVars (Expr.lam `x (Expr.const `Nat []) (Expr.bvar 0) BinderInfo.default)
    IO.println instantiatedExpr -- fun (x : Nat) => x
-- 3. [**Metavariables**] Fill in the missing lines in the following code.
  #eval show MetaM Unit from do
    let oneExpr := Expr.app (Expr.const `Nat.succ []) (Expr.const ``Nat.zero [])
    let twoExpr := Expr.app (Expr.const `Nat.succ []) oneExpr

    -- Create `mvar1` with type `Nat`
    let mvar1 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar1)
    -- Create `mvar2` with type `Nat`
    let mvar2 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar2)
    -- Create `mvar3` with type `Nat`
    let mvar3 ← Lean.Meta.mkFreshExprMVar (Expr.const `Nat []) (userName := `mvar3)

    -- Assign `mvar1` to `2 + ?mvar2 + ?mvar3`
    mvar1.mvarId!.assign (Lean.mkAppN (Expr.const `Nat.add []) #[(Lean.mkAppN (Expr.const `Nat.add []) #[twoExpr, mvar2]), mvar3])

    -- Assign `mvar3` to `1`
    mvar3.mvarId!.assign oneExpr

    -- Instantiate `mvar1`, which should result in expression `2 + ?mvar2 + 1`
    let instantiatedMvar1 ← instantiateMVars mvar1
    IO.println instantiatedMvar1 -- Nat.add (Nat.add 2 ?_uniq.2) 1

/- 4. [**Metavariables**] Consider the theorem `red`, and tactic `explore` below.
    a) What would be the `type`  and `userName`  of metavariable `mvarId`?
    b) What would be the `type`s and `userName`s of all local declarations in this metavariable's local context?
  Print them all out. -/
  elab "explore" : tactic => do
    let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
    let metavarDecl : MetavarDecl ← mvarId.getDecl

    IO.println "Our metavariable"
    IO.println s!"\n{metavarDecl.userName} : {metavarDecl.type}"

    IO.println "All of its local declarations"
    let localContext : LocalContext := metavarDecl.lctx
    for (localDecl : LocalDecl) in localContext do
      if localDecl.isImplementationDetail then
        -- (implementation detail) red : 1 = 1 → 2 = 2 → 2 = 2
        IO.println s!"\n(implementation detail) {localDecl.userName} : {localDecl.type}"
      else
        -- hA : 1 = 1
        -- hB : 2 = 2
        IO.println s!"\n{localDecl.userName} : {localDecl.type}"

  theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
    explore
    sorry

-- 5. [**Metavariables**] Write a tactic `solve` that proves the theorem `red`.
-- 6. [**Computation**] What is the normal form of the following expressions:
--   **a)** `fun x => x` of type `Bool → Bool`
--   **b)** `(fun x => x) ((true && false) || true)` of type `Bool`
--   **c)** `800 + 2` of type `Nat`
-- 7. [**Computation**] Show that `1` created with `Expr.lit (Lean.Literal.natVal 1)` is definitionally equal to an expression created with `Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])`.
-- 8. [**Computation**] Determine whether the following expressions are definitionally equal. If `Lean.Meta.isDefEq` succeeds, and it leads to metavariable assignment, write down the assignments.
--   **a)** `5 =?= (fun x => 5) ((fun y : Nat → Nat => y) (fun z : Nat => z))`
--   **b)** `2 + 1 =?= 1 + 2`
--   **c)** `?a =?= 2`, where `?a` has a type `String`
--   **d)** `?a + Int =?= "hi" + ?b`, where `?a` and `?b` don't have a type
--   **e)** `2 + ?a =?= 3`
--   **f)** `2 + ?a =?= 2 + 1`
-- 9. [**Computation**] Write down what you expect the following code to output.

--     ```lean
--     @[reducible] def reducibleDef     : Nat := 1 -- same as `abbrev`
--     @[instance] def instanceDef       : Nat := 2 -- same as `instance`
--     def defaultDef                    : Nat := 3
--     @[irreducible] def irreducibleDef : Nat := 4

--     @[reducible] def sum := [reducibleDef, instanceDef, defaultDef, irreducibleDef]

--     #eval show MetaM Unit from do
--       let constantExpr := Expr.const `sum []

--       Meta.withTransparency Meta.TransparencyMode.reducible do
--         let reducedExpr ← Meta.reduce constantExpr
--         dbg_trace (← ppExpr reducedExpr) -- ...

--       Meta.withTransparency Meta.TransparencyMode.instances do
--         let reducedExpr ← Meta.reduce constantExpr
--         dbg_trace (← ppExpr reducedExpr) -- ...

--       Meta.withTransparency Meta.TransparencyMode.default do
--         let reducedExpr ← Meta.reduce constantExpr
--         dbg_trace (← ppExpr reducedExpr) -- ...

--       Meta.withTransparency Meta.TransparencyMode.all do
--         let reducedExpr ← Meta.reduce constantExpr
--         dbg_trace (← ppExpr reducedExpr) -- ...

--       let reducedExpr ← Meta.reduce constantExpr
--       dbg_trace (← ppExpr reducedExpr) -- ...
--     ```
-- 10. [**Constructing Expressions**] Create expression `fun x => 1 + x` in two ways:
--   **a)** not idiomatically, with loose bound variables
--   **b)** idiomatically.
--   In what version can you use `Lean.mkAppN`? In what version can you use `Lean.Meta.mkAppM`?
-- 11. [**Constructing Expressions**] Create expression `∀ (yellow: Nat), yellow`.
-- 12. [**Constructing Expressions**] Create expression `∀ (n : Nat), n = n + 1` in two ways:
--   **a)** not idiomatically, with loose bound variables
--   **b)** idiomatically.
--   In what version can you use `Lean.mkApp3`? In what version can you use `Lean.Meta.mkEq`?
-- 13. [**Constructing Expressions**] Create expression `fun (f : Nat → Nat), ∀ (n : Nat), f n = f (n + 1)` idiomatically.
-- 14. [**Constructing Expressions**] What would you expect the output of the following code to be?

--     ```lean
--     #eval show Lean.Elab.Term.TermElabM _ from do
--       let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
--       let expr ← Elab.Term.elabTermAndSynthesize stx none

--       let (_, _, conclusion) ← forallMetaTelescope expr
--       dbg_trace conclusion -- ...

--       let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
--       dbg_trace conclusion -- ...

--       let (_, _, conclusion) ← lambdaMetaTelescope expr
--       dbg_trace conclusion -- ...
--     ```
-- 15. [**Backtracking**] Check that the expressions `?a + Int` and `"hi" + ?b` are definitionally equal with `isDefEq` (make sure to use the proper types or `Option.none` for the types of your metavariables!).
-- Use `saveState` and `restoreState` to revert metavariable assignments.
