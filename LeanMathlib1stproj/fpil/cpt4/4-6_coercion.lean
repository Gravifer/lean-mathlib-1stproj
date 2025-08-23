import Lean.Data.Json
set_option autoImplicit true

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
inductive Pos' : Type where
  | one : Pos'
  | succ : Pos' → Pos'
instance {n : Nat} : OfNat Pos' (n+1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos'
      | 0 => Pos'.one
      | k + 1 => Pos'.succ (natPlusOne k)
    natPlusOne n
def Pos'.toNat : Pos' → Nat
  | Pos'.one => 1
  | Pos'.succ n => n.toNat + 1

instance : Coe Pos' Nat where
  coe x := x.toNat

#check [1, 2, 3, 4].drop (2 : Pos')
#print CoeDep
set_option relaxedAutoImplicit true
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }
#check @Coe.coe
#check @CoeDep.coe
#check @CoeSort.coe

-- Find and check the CoeSort instance for Bool
#synth CoeSort Bool Prop
#check (inferInstance : CoeSort Bool Prop)
#print boolToSort

-- ## JSON as a String
inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
deriving Repr
structure Serializer where
  Contents : Type
  serialize : Contents → JSON
def Str : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }
instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize
def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]
#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"

def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString
def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))

open Lean.Data in
partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"
#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString
