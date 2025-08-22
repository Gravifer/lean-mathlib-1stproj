import Greeting

-- def main : IO Unit :=
--   IO.println s!"Hello, {hello}!"


import Greeting.Smile

def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {expression}!"
