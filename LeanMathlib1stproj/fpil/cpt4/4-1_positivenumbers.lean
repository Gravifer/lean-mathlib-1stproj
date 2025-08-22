import Lean

set_option eval.pp true
set_option eval.type true
set_option eval.derive.repr true
-- set_option pp.explicit true
set_option pp.universes true
set_option pp.notation true
-- set_option pp.numerals false

class Plus.{u} (α : Type u) where
  plus : α → α → α

#check (Plus)
#check Plus
#check Nat       -- Nat : Type
#check Plus Nat  -- Plus Nat : Type 1
#print Plus
#check Nat.zero_le

#check fun x => [x]
#check Sort 1
#check Sort 2

#check (Plus.{0})
#check (Type->Type)
#check Prop
#check (Sort 0)
#check Decidable
#check (Decidable)
#check (Nat.zero_le 0)
#check (LE.le.{0} 0 0)
#check Decidable (LE.le.{0} 0 0)
#check `(Nat.succ 0)

open Lean Lean.Expr Lean.Meta Lean.Elab.Term Lean.Core in
#eval show MetaM Unit from do
  let e ← elabTerm (← `(Nat.succ 0)) none
  let ty ← inferType e
  IO.println s!"Expression: {e}"
  IO.println s!"Its type: {ty}"

open Lean Lean.Expr Lean.Meta Lean.Elab.Term Lean.Core in
#eval show MetaM Unit from do
  let stx ← `(Nat.succ 0)
  let e ← elabTerm stx none
  let ty ← inferType e
  IO.println s!"Expression: {e}"
  IO.println s!"Its type: {ty}"
