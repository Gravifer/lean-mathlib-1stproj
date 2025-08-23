-- # [Arrays and Indexing](https://leanprover.github.io/functional_programming_in_lean/type-classes/indexing.html)

set_option autoImplicit true

-- * arrays are written similarly to lists, but with a leading `#`
def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  -- | {head := _, tail := []}, _ + 1 => none
  -- | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
  | xs, n + 1 => xs.tail.get? n -- ! deprecated syntax; equivalent to `xs.tail[n]?`

/- * The definition of what it means for an index to be in bounds
   * should be written as an abbrev
   * because the tactics used to find evidence that indices are acceptable
   * are able to solve inequalities of numbers, but don't know anything
   * about the specific name of types like `NonEmptyList`
-/
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

#print GetElem
instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

inductive Pos' : Type where
  | one : Pos'
  | succ : Pos' → Pos'
def Pos'.toNat : Pos' → Nat
  | Pos'.one => 1
  | Pos'.succ n => n.toNat + 1
instance : GetElem (List α) Pos' α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos') ok := xs[i.toNat]
