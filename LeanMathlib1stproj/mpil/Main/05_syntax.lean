import Lean
import Lean.Parser.Syntax
import Batteries
import Batteries.Util.ExtendedBinder
namespace mpil
/-! # Syntax -/
/-! ## Declaring Syntax -/
/-! ### Free form syntax declarations -/
namespace temp
  scoped syntax "⊥" : term -- ⊥ for false
  scoped syntax "⊤" : term -- ⊤ for true
  scoped syntax:40 term " OR " term : term
  scoped syntax:50 term " AND " term : term
  #check_failure ⊥ OR (⊤ AND ⊥)
end temp /- While this does work, it allows arbitrary terms
  to the left and right of our `AND` and `OR` operation.
  If we want to write a mini language that only accepts our boolean language
    on a syntax level we will have to declare our own syntax category on top.

This is done using the `declare_syntax_cat` command: -/
declare_syntax_cat boolean_expr
syntax "⊥" : boolean_expr -- ⊥ for false
syntax "⊤" : boolean_expr -- ⊤ for true
syntax:40 boolean_expr " OR " boolean_expr : boolean_expr
syntax:50 boolean_expr " AND " boolean_expr : boolean_expr
/- In order to integrate our syntax category into the rest of the system
  we will have to extend an already existing one with new syntax,
  in this case we will re-embed it into the `term` category: -/
syntax "[Bool|" boolean_expr "]" : term
#check_failure [Bool| ⊥ AND ⊤]

/-! ### Syntax combinators
  - helper parsers without syntax categories (i.e. not extendable)
  - alternatives       `⋯<|>⋯`
  - repetitive parts   [`⋯*`, `⋯+`]
  - optional parts     `(⋯)?`
There does also exist a number of built-in named parsers that are generally useful,
  most notably:
  - `str`   for string literals
  - `num`   for number literals
  - `ident` for identifiers
  - ...
-/

/-! ## Operating on Syntax -/
#print Lean.Syntax
#print Lean.SourceInfo
#print Lean.SyntaxNodeKind

/-! ### Constructing new `Syntax` -/ open Lean
#eval Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"] -- is the syntax of `Nat.add 1 1`
#eval mkNode `«term_+_» #[Syntax.mkNumLit "1", mkAtom "+", Syntax.mkNumLit "1"] -- is the syntax for `1 + 1`
-- note that the `«term_+_» is the auto-generated SyntaxNodeKind for the + syntax

/-! ### Matching on `Syntax` -/
def isAdd11 : Syntax → Bool
  | `(Nat.add 1 1) => true
  | _ => false
def isAdd : Syntax → Option (Syntax × Syntax)
  | `(Nat.add $x $y) => some (x, y)
  | _ => none

/-! ### Typed Syntax -/
-- Note that `x` and `y` in this example are of type `` TSyntax `term ``, not `Syntax`.
#print TSyntax
/- note about the matching on syntax:
  In this basic form it only works on syntax from the `term` category.
  If you want to use it to match on your own syntax categories
    you will have to use `` `(category| ...)``. -/

/-! ### Example: arith -/
declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith

partial def denoteArith : TSyntax `arith → Nat
  | `(arith| $x:num) => x.getNat
  | `(arith| $x:arith + $y:arith) => denoteArith x + denoteArith y
  | `(arith| $x:arith - $y:arith) => denoteArith x - denoteArith y
  | `(arith| ($x:arith)) => denoteArith x
  | _ => 0

/-! ## Exercises -/ open Lean Elab Command Term
-- 1. Create an "urgent minus 💀" notation such that `5 * 8 💀 4` returns `20`, and `8 💀 6 💀 1` returns `3`.
  -- **a)** Using `notation` command.
    namespace a
      scoped notation:72 lhs:50 " 💀 " rhs:72 => lhs - rhs
    end a
  -- **b)** Using `infix` command.
    namespace b
      set_option quotPrecheck false
      scoped infixl:71 " 💀 " => fun lhs rhs => lhs - rhs
    end b
  -- **c)** Using `syntax` command.
    namespace c
      scoped syntax:71 term:50 " 💀 " term:72 : term
      scoped macro_rules | `($l:term 💀 $r:term) => `($l - $r)
    end c

-- 2. Consider the following syntax categories: `term`, `command`, `tactic`; and 3 syntax rules given below. Make use of each of these newly defined syntaxes.
  syntax "good" "morning" : term
  syntax "hello" : command
  syntax "yellow" : tactic

-- 3. Create a `syntax` rule that would accept the following commands:
  --   - `red red red 4`
  --   - `blue 7`
  --   - `blue blue blue blue blue 18`
  --   (So, either all `red`s followed by a number; or all `blue`s followed by a number; `red blue blue 5` - shouldn't work.)
syntax (name := colors) (("blue"+) <|> ("red"+)) num : command
@[command_elab colors]
def elabColors : CommandElab := fun stx => Lean.logInfo "success!"
blue blue 443
red red red 4

-- 4. Mathlib has a `#help option` command that displays all options available in the current environment, and their descriptions. `#help option pp.r` will display all options starting with a "pp.r" substring.
  --   Create a `syntax` rule that would accept the following commands:
  --   - `#better_help option`
  --   - `#better_help option pp.r`
  --   - `#better_help option some.other.name`
syntax (name := help) "#better_help" "option" (ident)? : command
@[command_elab help]
def elabHelp : CommandElab := fun stx => Lean.logInfo "success!"
#better_help option
#better_help option pp.r
#better_help option some.other.name

-- 5. Mathlib has a ∑ operator. Create a `syntax` rule that would accept the following terms:
  --   - `∑ x in { 1, 2, 3 }, x^2`
  --   - `∑ x in { "apple", "banana", "cherry" }, x.length`
syntax (name := bigsumin) "∑ " Batteries.ExtendedBinder.extBinder "in " term "," term : term
@[term_elab bigsumin]
def elabSum : TermElab := fun stx tp => return mkNatLit 42
#eval ∑ x in { 1, 2, 3 }, x^2
def hi := (∑ x in { "apple", "banana", "cherry" }, x.length) + 1
#eval hi
