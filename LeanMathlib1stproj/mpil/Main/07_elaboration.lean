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
/-! ### Giving meaning to commands -/
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

/-! ### Command elaboration
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
/-! ### Steps
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
