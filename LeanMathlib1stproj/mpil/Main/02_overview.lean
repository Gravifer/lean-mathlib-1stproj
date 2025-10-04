import Lean
/-! # Overview -/
/-! ## Three essential commands and their syntax sugars -/
/-! ## Order of execution: syntax rule, macro, elab -/
namespace mpil
open Lean Elab Command

syntax (name := xxx) "red" : command
syntax (name := yyy) "green" : command
syntax (name := zzz) "blue" : command

@[macro xxx] def redMacro : Macro := λ stx =>
  match stx with
  | _ => `(green)

@[macro yyy] def greenMacro : Macro := λ stx =>
  match stx with
  | _ => `(blue)

@[command_elab zzz] def blueElab : CommandElab := λ stx =>
  Lean.logInfo "finally, blue!"

red -- finally, blue!

/-! ## Manual conversions between `Syntax`/`Expr`/executable-code -/
/-
  * all functions that let us turn Syntax into Expr
  *   start with "elab", short for "elaboration";
  * all functions that let us turn Expr (or Syntax) into actual code
  *   start with "eval", short for "evaluation".
-/
