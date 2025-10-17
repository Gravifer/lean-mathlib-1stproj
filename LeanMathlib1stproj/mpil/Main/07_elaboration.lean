import Lean
import Batteries
open Lean Elab Command Term Meta
/-! # Elaboration -/
-- * see <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/>
/-! ## Command elaboration
  A command is the highest level of `Syntax`, a Lean file is made
  up of a list of commands. The most commonly used commands are declarations,
  for example:
  - `def`
  - `inductive`
  - `structure`
  but there are also other ones, most notably `#check`, `#eval` and friends.

  All commands live in the `command` syntax category so in order to declare
  custom commands, their syntax has to be registered in that category. -/
/-! ### Semantics -/
#print CommandElabM
#print CommandElab
/- The `CommandElabM` monad has 4 main kinds of side effects:
  1. Logging messages to the user via the `Monad` extensions
    `MonadLog` and `AddMessageContext`, like `#check`. This is done via
    functions that can be found in `Lean.Elab.Log`, the most notable ones
    being: `logInfo`, `logWarning` and `logError`.
  2. Interacting with the `Environment` via the `Monad` extension `MonadEnv`.
    This is the place where all of the relevant information for the compiler
    is stored, all known declarations, their types, doc-strings, values etc.
    The current environment can be obtained via `getEnv` and set via `setEnv`
    once it has been modified. Note that quite often wrappers around `setEnv`
    like `addDecl` are the correct way to add information to the `Environment`.
  3. Performing `IO`, `CommandElabM` is capable of running any `IO` operation.
    For example reading from files and based on their contents perform
    declarations.
  4. Throwing errors, since it can run any kind of `IO`, it is only natural
    that it can throw errors via `throwError`.
-/
#print MonadLog
#print addMessageContext
#print MonadEnv
#print getEnv
#print setEnv
#print addDecl
#print IO
#print Macro.throwError

/-! ### Mechanism
  1. Check whether any macros can be applied to the current `Syntax`.
    If there is a macro that does apply and does not throw an error
    the resulting `Syntax` is recursively elaborated as a command again.
  2. If no macro can be applied, we search for all `CommandElab`s that have been
    registered for the `SyntaxKind` of the `Syntax` we are elaborating,
    using the `command_elab` attribute.
  3. All of these `CommandElab` are then tried in order
    until one of them does not throw an `unsupportedSyntaxException`,
    Lean's way of indicating that the elaborator "feels responsible"
    for this specific `Syntax` construct. Note that it can still throw a regular
    error to indicate to the user that something is wrong.
    If no responsible elaborator is found, then
    the command elaboration is aborted with an `unexpected syntax` error message.

  The general idea behind the procedure is quite similar to ordinary macro expansion.
-/
/-! ### Procedure
  1. Declaring the syntax
  2. Declaring the elaborator
  3. Registering the elaborator as responsible for the syntax
      via the `command_elab` attribute. -/
syntax (name := mycommand1) "#mycommand1" : command -- declare the syntax
@[command_elab mycommand1]
def mycommand1Impl : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo "Hello World"
#mycommand1 -- Hello World

-- equivalent to the macroed:
elab "#mycommand2" : command =>  logInfo "Hello World"
#mycommand2 -- Hello World

/-
In the following example, we are not extending the original `#check` syntax,
but adding a new `SyntaxKind` for this specific syntax construct.
However, from the point of view of the user, the effect is basically the same.
-/
elab "#check" "mycheck" : command => do
  logInfo "Got ya!"
#check mycheck
-- actually extending the original `#check`
@[command_elab Lean.Parser.Command.check] def mySpecialCheck : CommandElab := fun stx => do
  if let some str := stx[1].isStrLit? then
    logInfo s!"Specially elaborated string literal!: {str} : String"
  else
    throwUnsupportedSyntax
#check "Hello" -- Specially elaborated string literal!: Hello : String
#check Nat.add -- Nat.add : Nat → Nat → Nat

/- * Convention:
  - A declaration changes Lean’s environment, which survives past that line
      (it creates or mutates constants, attributes, options, etc.).
  - A `#`-command is purely local:
      it’s a request to the elaborator to evaluate something now or show information,
      but the result is not recorded into the environment.
TODO: Maybe we should also add a mini project that demonstrates a
  non # style command aka a declaration, although nothing comes to mind right now.
TODO:  Define a `conjecture` declaration, similar to `lemma/theorem`, except that
  it is automatically sorried.  The `sorry` could be a custom one, to reflect that
  the "conjecture" might be expected to be true.
-/

/-! ## Term elaboration -/
/-! ### Semantics
  As with command elaboration, the next step is giving some semantics to the syntax.
  With terms, this is done by registering a so called term elaborator. -/
#print TermElabM
#print TermElab
/- Term elaborators have type `TermElab`. This type is already
  quite different from command elaboration:
  - As with command elaboration the `Syntax` is whatever the user used
    to create this term
  - The `Option Expr` is the expected type of the term, since this cannot
    always be known it is only an `Option` argument
  - Unlike command elaboration, term elaboration is not only executed
    because of its side effects -- the `TermElabM Expr` return value does
    actually contain something of interest, namely, the `Expr` that represents
    the `Syntax` object.

  `TermElabM` is basically an upgrade of `CommandElabM` in every regard:
  it supports all the capabilities we mentioned above, plus two more.
  The first one is quite simple: On top of running `IO` code it is also
  capable of running `MetaM` code, so `Expr`s can be constructed nicely.
  The second one is very specific to the term elaboration loop.
-/
/-! ### Mechanics
  The basic idea of term elaboration is the same as command elaboration:
  expand macros and recurse or run term elaborators that have been registered
  for the `Syntax` via the `term_elab` attribute (they might in turn run term elaboration)
  until we are done. There is, however, one special action that a term elaborator
  can do during its execution. -/
#print Except
#print Exception
#print Elab.throwPostpone
#print Term.synthesizeSyntheticMVars
#print Elab.Term.SyntheticMVarKind

/-! ### Procedure -/
syntax (name := myterm1) "myterm_1" : term
def mytermValues := [1, 2]
@[term_elab myterm1]
def myTerm1Impl : TermElab := fun stx type? => do
  mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 0] -- `MetaM` code
#eval myterm_1 -- 1
-- Also works with `elab`
elab "myterm_2" : term => do
  mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 1] -- `MetaM` code
#eval myterm_2 -- 2

/-! ### Example: recreate `⟨⋯⟩` notation -/
-- slightly different notation so no ambiguity happens
syntax (name := myanon) "⟨⟨" term,* "⟩⟩" : term

def getCtors (typ : Name) : MetaM (List Name) := do
  let env ← getEnv
  match env.find? typ with
  | some (ConstantInfo.inductInfo val) =>
    pure val.ctors
  | _ => pure []

@[term_elab myanon]
def myanonImpl : TermElab := fun stx typ? => do
  -- Attempt to postpone execution if the type is not known or is a metavariable.
  -- Metavariables are used by things like the function elaborator to fill
  -- out the values of implicit parameters when they haven't gained enough
  -- information to figure them out yet.
  -- Term elaborators can only postpone execution once, so the elaborator
  -- doesn't end up in an infinite loop. Hence, we only try to postpone it,
  -- otherwise we may cause an error.
  tryPostponeIfNoneOrMVar typ?
  -- If we haven't found the type after postponing just error
  let some typ := typ? | throwError "expected type must be known"
  if typ.isMVar then
    throwError "expected type must be known"
  let Expr.const base .. := typ.getAppFn | throwError s!"type is not of the expected form: {typ}"
  let [ctor] ← getCtors base | throwError "type doesn't have exactly one constructor"
  let args := TSyntaxArray.mk stx[1].getSepArgs
  let stx ← `($(mkIdent ctor) $args*) -- syntax quotations
  elabTerm stx typ -- call term elaboration recursively

#check (⟨⟨1, sorry⟩⟩ : Fin 12) -- { val := 1, isLt := (_ : 1 < 12) } : Fin 12
#check_failure ⟨⟨1, sorry⟩⟩ -- expected type must be known
#check_failure (⟨⟨0⟩⟩ : Nat) -- type doesn't have exactly one constructor
#check_failure (⟨⟨⟩⟩ : Nat → Nat) -- type is not of the expected form: Nat -> Nat

/-!
As a final note, we can shorten the postponing act by using an additional
syntax sugar of the `elab` syntax instead:
-/

-- This `t` syntax will effectively perform the first two lines of `myanonImpl`
elab "⟨⟨" args:term,* "⟩⟩" : term <= t => do
  sorry

/-! ## Exercises -/
