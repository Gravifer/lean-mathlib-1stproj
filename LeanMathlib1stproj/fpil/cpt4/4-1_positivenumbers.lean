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

open Lean.Meta Lean.Elab.Term in
#eval show TermElabM Unit from do -- * extends `MetaM`: ```abbrev TermElabM := ReaderT Context $ StateRefT State MetaM```
  let stx ← `(Nat.succ 0)
  let e ← elabTerm stx none
  let ty ← inferType e
  IO.println s!"Expression: {e}"
  IO.println s!"Its type: {ty}"

open Lean.Meta Lean.Elab.Term in
def myCheck stx := do
  let e ← elabTerm (<- stx) none
  let ty ← inferType e
  IO.println s!"{e} : {ty}"

open Lean.Meta Lean.Elab.Term in
def getType stx := do
  let e ← elabTerm (<- stx) none
  let ty ← inferType e
  -- IO.println s!"{e} : {ty}"
  return ty

#eval myCheck `(Nat.succ 0)

#eval (getType `(Nat.zero_le 0))  -- ! doesn't work

inductive Pos' : Type where
  | one : Pos'
  | succ : Pos' → Pos'

#print OfNat
instance {n : Nat} : OfNat Pos' (n+1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos'
      | 0 => Pos'.one
      | k + 1 => Pos'.succ (natPlusOne k)
    natPlusOne n


def Pos'.OfNat' (n : Nat) (ok : n > 0) : Pos' :=
  if h : n = 1 then Pos'.one else Pos'.succ (Pos'.OfNat' (n - 1) (by
    have : n ≥ 1 := ok
    have : n ≠ 1 := h
    omega))
def seven : Pos' := Pos'.OfNat' 7 (by simp)

class Plus' (α : Type) where
  plus : α → α → α

def Pos'.plus : Pos' → Pos' → Pos'
  | Pos'.one, k => Pos'.succ k
  | Pos'.succ n, k => Pos'.succ (n.plus k)

instance : Plus' Pos' where
  plus := Pos'.plus

instance : Add Pos' where
  add := Pos'.plus

def fourteen : Pos' := seven + seven

def Pos'.toNat : Pos' → Nat
  | Pos'.one => 1
  | Pos'.succ n => n.toNat + 1

instance : ToString Pos' where
  toString x := toString (x.toNat)

#eval Pos'.OfNat' 1 (by simp)
def eight : Pos' := 8
#eval eight
#eval Pos'.OfNat' 14 (by simp)
#eval Pos'.toNat fourteen
-- theorem foo : fourteen = Pos'.OfNat 14 (by simp) := by
--   unfold fourteen
--   rw [seven]
--   simp -- ! `simp` made no progress

def Pos'.mul : Pos' → Pos' → Pos'
  | Pos'.one, k => k
  | Pos'.succ n, k => n.mul k + k

instance : Mul Pos' where
  mul := Pos'.mul
#eval [seven * Pos'.one,
       seven * seven,
       Pos'.succ Pos'.one * seven]
