set_option autoImplicit true

def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1

def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1

theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  -- induction k with
  -- | zero => rfl
  -- | succ n ih => unfold Nat.plusR; rw [<-ih]
  induction k <;> simp [Nat.plusR] <;> assumption
/- *`<;>` operator: two tactics -> tactic.
    `T1 <;> T2` applies `T1` to the current goal,
    and then applies `T2` in all goals created by `T1`. -/

inductive BinTree (α : Type) : Type
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r =>
    .branch (r.mirror) x (l.mirror)

theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
  induction t <;> simp +arith [BinTree.mirror, BinTree.count, *]
