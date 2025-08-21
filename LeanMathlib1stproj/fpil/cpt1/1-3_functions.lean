-- # [1.3 Functions](https://leanprover.github.io/functional_programming_in_lean/getting-to-know/functions-and-definitions.html)

-- ## symbols
def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)

-- ## functions
def add1 (n : Nat) : Nat := n + 1
#eval add1 7
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n
#eval maximum (5 + 8) (2 * 7)
#check maximum
#check (maximum)

-- ### exercises

def joinStringsWith sep fst snd := String.append fst (String.append sep snd)
#check  joinStringsWith
#check (joinStringsWith)
#check joinStringsWith ": "

def volume (height width depth : Nat) := height * width * depth
#check (volume)

-- ## types
def Str : Type := String
def aStr : Str := "This is a string."

-- ## messages
def NaturalNumber : Type := Nat
-- def thirtyEight : NaturalNumber := 38 -- ! fails
def thirtyEight : NaturalNumber := (38 : Nat) -- todo: overload `NatualNumber` so the previous line type checks
abbrev N : Type := Nat -- * Definitions written using abbrev are always unfolded
def thirtyNine : N := 39
