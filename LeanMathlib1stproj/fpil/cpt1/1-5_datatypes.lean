-- # [1.5 Datatypes](https://leanprover.github.io/functional_programming_in_lean/getting-to-know/datatypes-and-patterns.html)

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

#check (Nat.zero)
#check (Nat.succ) -- projection function?

#eval (0 : Nat) == Nat.zero
#check Nat.pred

/- import Mathlib.Data.PNat.Basic -- positive integers
structure PNat :=
  (val : Nat)
  (property : val > 0)
-/

--
