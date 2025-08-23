set_option autoImplicit true
inductive Pos' : Type where
  | one : Pos'
  | succ : Pos' → Pos'
def Pos'.toNat : Pos' → Nat
  | Pos'.one => 1
  | Pos'.succ n => n.toNat + 1
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

#print BEq
#print BEq.beq

#eval 1 + 1

set_option diagnostics true in
#eval (fun (x : Nat) => 1 + x) == (Nat.succ ·)

#check (fun (x : Nat) => 1 + x) = (Nat.succ ·)

#print decide
#eval decide (1 + 1 = 2)
#eval (2 < 4)
#check (2 < 4)
#eval decide (2 < 4)

#eval decide $ (fun (x : Nat) => 1 + x) = (Nat.succ ·)
#print LT
#print Ordering

inductive foo where | a | b | c -- * turns out you can write this inline
#print Hashable
-- #print BinTree
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

-- ## Instance derivation
deriving instance BEq, Hashable for Pos'
deriving instance BEq, Hashable, Repr for NonEmptyList
#print Inhabited
#print List.append
#print List.concat -- ! somehow the APIs are swapped. see [this PR](https://github.com/leanprover-community/lean/pull/771) and [this discussion](https://leanprover-community.github.io/archive/stream/113488-general/topic/append.20and.20concat.html)
#print Functor
#print Functor.mapConst

-- deriving instance ToString for NonEmptyList -- ! rejected
