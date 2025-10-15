import Lean
import Batteries
/-! # Macros -/
open Lean
#print Macro.throwUnsupported
#print Macro.throwError

/-! ## Simplifying macro declaration -/
/- There is `macro_rules` which basically desugars to functions;
    it figures out lot's of things on its own for us:
  - the name of the syntax declaration
  - the `macro` attribute registration
  - the `throwUnsupported` wildcard
  apart from which it just works like a function that is using pattern
  matching syntax, we can in theory encode arbitrarily complex macro
  functions on the right hand side.

  There is also the `macro` macro quite close to `notation`:
  - it performs syntax declaration for us
  - it automatically writes a `macro_rules` style function to match on it
  There are of course differences as well:
  - `notation` is limited to the `term` syntax category
  - `notation` cannot have arbitrary macro code on the right hand side
-/

/-! ## `Syntax` Quotations -/
/- we call the `` `() `` syntax a `Syntax` quotation.
  When we plug variables into a syntax quotation like this: `` `($x) ``
    we call the `$x` part an anti-quotation.
  When we insert `x` like this it is required that
    `x` is of type `TSyntax y` where `y` is some `Name` of a syntax category.
  The Lean compiler is smart enough to figure out
    the syntax categories that are allowed in this place. -/
#print TSyntax.getNat
/- If we wish to insert a literal `$x` into the `Syntax` for some reason,
    for example macro creating macros,
    we can escape the anti quotation using: `` `($$x) ``.

  To specify the syntax kind we wish `x` to be interpreted as, we can
    make this explicit using: `` `($x:term) `` where `term` can be replaced with
    any other valid syntax category (e.g. `command`) or parser (e.g. `ident`). -/

/-! ### Advanced anti-quotations -/
/- we can also use anti-quotations in a way similar to format strings:
        `` `($(mkIdent `c)) `` is the same as: `` let x := mkIdent `c; `($x) ``.

  Furthermore there are sometimes situations in which we are not working
  with basic `Syntax` but `Syntax` wrapped in more complex datastructures,
  most notably `Array (TSyntax c)` or `TSepArray c s`. Where `TSepArray c s`,
  is a `Syntax` specific type, it is what we get if we pattern match on some
  `Syntax` that uses a separator `s` to separate things from the category `c`.
  For example if we match using: `$xs,*`, `xs` will have type `TSepArray c ","`,.
  With the special case of matching on no specific separator (i.e. whitespace):
  `$xs*` in which we will receive an `Array (TSyntax c)`.

  If we are dealing with `xs : Array (TSyntax c)` and want to insert it into
  a quotation we have two main ways to achieve this:
  1. Insert it using a separator, most commonly `,`: `` `($xs,*) ``.
    This is also the way to insert a `TSepArray c ",""`
  2. Insert it point blank without a separator (TODO): `` `() ``
-/
/-! #### anti-quotation splices -/
-- * optional slicing `$[...]?`
  syntax "mylet " ident (" : " term)? " := " term " in " term : term
  macro_rules
    | `(mylet $x $[: $ty]? := $val in $body) => `(let $x $[: $ty]? := $val; $body)
-- * list comprehension `$[...],*`
  syntax "foreach " "[" term,* "]" term : term
  macro_rules
    | `(foreach [ $[$x:term],* ] $func:term) => `(let f := $func; [ $[f $x],* ])
  /- unlike regular separator matching it does not give us an Array or SepArray,
    instead it allows us to write another splice on the right hand side
    that gets evaluated for each time the pattern we specified matched,
    with the specific values from the match per iteration. -/

/-! ## Hygiene -/ -- see [Beyond Notations](https://lmcs.episciences.org/9362/pdf)
/- The idea described in the paper comes down to the concept of "macro scopes".
  Whenever a new macro is invoked, a new macro scope (basically a unique number)
    is added to a list of all the macro scopes that are active right now.
  When the current macro introduces a new identifier,
    what is actually getting added is an identifier of the form:
  ```lean4
    <actual name>._@.(<module_name>.<scopes>)*.<module_name>._hyg.<scopes>
  ```
  For example, if the module name is `Init.Data.List.Basic`, the name is
  `foo.bla`, and macros scopes are [2, 5] we get:
  ```lean4
    foo.bla._@.Init.Data.List.Basic._hyg.2.5
  ```
  Since macro scopes are unique numbers, the list of macro scopes
    appended in the end of the name will always be unique
    across all macro invocations,
    hence macro hygiene issues are not possible.

  There is more than just the macro scopes to this name generation,
    because we may have to combine scopes from different files/modules.
  The main module being processed is always the right most one.
  This situation may happen when we execute a macro
    generated in a file imported in the current file.
  ```lean4
    foo.bla._@.Init.Data.List.Basic.2.1.Init.Lean.Expr_hyg.4
  ```
  The delimiter `_hyg` at the end is used just to improve performance of
  the function `Lean.Name.hasMacroScopes` -- the format could also work without it.
-/
#print Lean.Name.hasMacroScopes

/-! ## `MonadQuotation` and `MonadRef` -/
/- Instead of bookkeeping for only a single monad `MacroM`
    the general concept of keeping track of macro scopes in monadic way
    is abstracted away using a type class called `MonadQuotation`.
  This allows any other monad to also easily provide this hygienic `Syntax`
    creation mechanism by simply implementing this type class. -/
#print MonadRef
#print MonadQuotation
/- How `MonadRef` comes into play here is that Lean requires a way to indicate
errors at certain positions to the user. One thing that wasn't introduced
in the `Syntax` chapter is that values of type `Syntax` actually carry their
position in the file around as well. When an error is detected, it is usually
bound to a `Syntax` value which tells Lean where to indicate the error in the file.
What Lean will do when using `withFreshMacroScope` is to apply the position of
the result of `getRef` to each introduced symbol, which then results in better
error positions than not applying any position. -/
syntax "error_position" ident : term
macro_rules
  | `(error_position all) => Macro.throwError "Ahhh"
  -- the `%$tk` syntax gives us the Syntax of the thing before the %,
  -- in this case `error_position`, giving it the name `tk`
  | `(error_position%$tk first) => withRef tk (Macro.throwError "Ahhh")
#check_failure error_position all -- the error is indicated at `error_position all`
#check_failure error_position first -- the error is only indicated at `error_position`

/-! ## Reading further -/
-- See <https://github.com/leanprover/lean4/blob/45df6fcd376e7e66bf179b16e2d6f182a60d3b93/src/Init/Prelude.lean#L5656-L5870>
