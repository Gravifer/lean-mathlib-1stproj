-- # [1.4 Structures](https://leanprover.github.io/functional_programming_in_lean/getting-to-know/structures.html)

#check 1.2
#check -454.2123215
#check 0.0
-- #check (.3 : Float) -- ! must have the prefix `0`
#check (0 : Float)

structure Point where -- syntactic sugar for a dependent record type
  x : Float
  y : Float
deriving Repr -- Haskell-style deriving
#check Point

def origin : Point := { x := 0, y := 0.0 }
#check origin
#eval origin
#eval origin.x

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))
#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

#check ({ x := 0.0, y := 0.0 } : Point) -- * equivalent to:
#check { x := 0.0, y := 0.0 : Point}

-- ## no in-place mutation
def zeroX (p : Point) : Point :=
  { p with x := 0 } -- * equivalent to `{ x := 0, y := p.y }`
def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }
#eval fourAndThree
#eval zeroX fourAndThree
#eval fourAndThree -- * not mutated

-- ## constuctors
#check Point.mk 1.5 2.8
#check Point.mk

structure Point1 where
  point1 ::
  x : Float
  y : Float
deriving Repr
#check Point1.point1

-- TARGET.f ARG1 ARG2 .... ===> If (TARGET : T) then T.f TARGET ARG1 ARG2 ...
#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor

-- ## exercises
structure RectangularPrism where
  height : Float
  width : Float
  depth : Float
deriving Repr

def RectangularPrism.volume (p : RectangularPrism) : Float :=
  p.height * p.width * p.depth / 3

#eval RectangularPrism.volume { height := 2.0, width := 3.0, depth := 4.0 }

structure Segment where
  s : Point
  e : Point
deriving Repr
def Segment.length (s : Segment) : Float :=
  distance s.s s.e
#eval Segment.length { s := { x := 1.0, y := 2.0 }, e := { x := 5.0, y := -1.0 } }
