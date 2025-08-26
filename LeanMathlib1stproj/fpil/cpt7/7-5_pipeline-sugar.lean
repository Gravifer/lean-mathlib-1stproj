-- Examples where `partial` is REQUIRED

-- Example 1: Try uncommenting this to see the error Lean gives you:
-- def infiniteLoop : IO Unit := infiniteLoop
-- Error: "fail to show termination for infiniteLoop"

-- With partial, it compiles:
partial def infiniteLoop : IO Unit := infiniteLoop

-- Example 2: Try uncommenting this to see the termination error:
-- def countDown (n : Nat) : IO Unit :=
--   if n = 0 then
--     IO.println "Done!"
--   else do
--     IO.println s!"Count: {n}"
--     countDown (n - 1)
-- Error: Lean can't prove that `n - 1` is smaller than `n` for all `n`

-- With partial, it works:
partial def countDown (n : Nat) : IO Unit :=
  if n = 0 then
    IO.println "Done!"
  else do
    IO.println s!"Count: {n}"
    countDown (n - 1)

-- Example 3: Collatz conjecture - termination unknown mathematically
partial def collatz (n : Nat) : Nat :=
  if n = 1 then 1
  else if n % 2 = 0 then collatz (n / 2)
  else collatz (3 * n + 1)

-- Example 4: Mutual recursion that Lean can't prove terminates
mutual
  partial def isEven : Nat → Bool
    | 0 => true
    | n + 1 => isOdd n

  partial def isOdd : Nat → Bool
    | 0 => false
    | n + 1 => isEven n
end

-- CONTRAST: These examples DON'T need partial

def spam : IO Unit := do
  repeat IO.println "Spam!"  -- `repeat` is syntax, not a recursive function; found in `Lean.Init.Conv` `Lean.Init.While`, and `repeat'` in `Lean.Init.Tactics`

-- This recursive function DOESN'T need partial because Lean can prove termination
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n  -- Pattern matching on `n + 1` proves termination

-- This also doesn't need partial - Lean recognizes structural recursion on lists
def listLength {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + listLength xs

-- Test the functions (uncomment to try):
-- #eval factorial 5
-- #eval countDown 5
-- #eval collatz 7
