-- N.B. the anonymous bind does not exist in Haskell
def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5

def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7

def test1 : IO Unit := do
  let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
  (← IO.getStdout).putStrLn s!"The answer is {a}"

def test1_desugared : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"


def test_correct : IO Unit := do
  let x ← getNumA
  let a : Nat ← if x == 5 then
                  pure 0
                else
                  getNumB
  (← IO.getStdout).putStrLn s!"The answer is {a}"


def test_do : IO Unit := do
  let a ← (do
    if (← getNumA) == 5 then
      pure 0
    else
      getNumB)
  (← IO.getStdout).putStrLn s!"The answer is {a}"

def test_inline : IO Unit := do
  let a ← if (← getNumA) == 5 then pure 0 else getNumB
  (← IO.getStdout).putStrLn s!"The answer is {a}"
