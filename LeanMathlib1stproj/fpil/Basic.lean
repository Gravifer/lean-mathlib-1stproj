set_option autoImplicit true
set_option relaxedAutoImplicit true

namespace FPIL
inductive Pos : Type where
  | one : Pos
  | succ : Pos  → Pos
deriving instance BEq, Hashable for Pos
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : OfNat Pos (n+1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving instance BEq, Hashable, Repr for NonEmptyList
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  -- | {head := _, tail := []}, _ + 1 => none
  -- | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
  | xs, n + 1 => xs.tail[n]?

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos ) ok := xs[i.toNat]

instance : Append (NonEmptyList α) where
  append xs ys := ⟨xs.head, xs.tail ++ (ys.head :: ys.tail)⟩

def FastPos : Type := {x : Nat // x > 0}
namespace FastPos
  def one : FastPos := ⟨1, by simp⟩
end FastPos
-- variable {n : Nat} in
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp +arith⟩

end FPIL
