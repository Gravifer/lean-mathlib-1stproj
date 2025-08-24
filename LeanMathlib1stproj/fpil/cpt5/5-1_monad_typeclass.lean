
set_option autoImplicit true

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x
infixl:55 " ~~> " => andThen

#print Monad
