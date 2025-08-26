set_option autoImplicit true
set_option relaxedAutoImplicit true

def List.count' (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found

def List.count'' (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  let rec go : List α → Id Unit
    | [] => pure ()
    | y :: ys => do -- * another layer of `do`
      -- // if p y then found := found + 1 -- ! now `found` is not in the generated StateT
      go ys
  return found
