set_option autoImplicit true
set_option relaxedAutoImplicit true

inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)

-- // example : Vect String n := Vect.nil
variable (n : Nat) in
#check_failure (Vect.nil : Vect String n)
-- // example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)
variable (n : Nat) in
#check_failure (Vect.cons "Hello" (Vect.cons "world" Vect.nil) : Vect String n)

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

def Vect.replicate' (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (.cons x (replicate' k x)) -- ! error

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

def Vect.zip' : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip' k xs ys)

-- ## Exercises
def oregonianPeaks  : Vect String 3 := .cons "Mount Hood"    (.cons "Mount Adams" (.cons "Mount St. Helens" .nil))
def washingtonPeaks : Vect String 3 := .cons "Mount Rainier" (.cons "Mount Baker" (.cons "Glacier Peak"     .nil))
def danishPeaks     : Vect String 3 := .cons "Møns Klint"    (.cons "Kullen"      (.cons "Hälsingland"      .nil))
def zipPeaks : Vect (String × String) 3 :=
  Vect.zip oregonianPeaks washingtonPeaks
#eval zipPeaks

def Vect.map (f : α → β) (v : Vect α n) : Vect β n :=
  match v with
  | .nil => .nil
  | .cons x xs => .cons (f x) (.map f xs)

def Vect.zipWith (f : α → β → γ) (v1 : Vect α n) (v2 : Vect β n) : Vect γ n :=
  match v1, v2 with
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

def Vect.unzip : Vect (α × β) n → (Vect α n × Vect β n)
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
      let (xs, ys) := unzip xys
      (.cons x xs, .cons y ys)

def Vect.snoc (v : Vect α n) (x : α) : Vect α (n + 1) :=
  match v with
  | .nil => .cons x .nil
  | .cons y ys => .cons y (snoc ys x)

#eval Vect.snoc (.cons "snowy" .nil) "peaks"
example : Vect.snoc (.cons "snowy" .nil) "peaks" = Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil)) := rfl

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => .snoc (reverse xs) x

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, v => v
  | k + 1, .cons _ xs => drop k xs

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | k + 1, .cons x xs => .cons x (take k xs)

#eval danishPeaks.drop 2
#eval danishPeaks.take 2

--
