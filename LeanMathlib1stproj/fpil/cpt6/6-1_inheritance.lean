structure MythicalCreature where
  large : Bool
  deriving Repr
#check MythicalCreature.mk
#check MythicalCreature.large

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr
#check Monster.mk
#check_failure Monster.large
def troll : Monster where
  large := true
  vulnerability := "sunlight"
#eval troll
#eval troll.toMythicalCreature -- * auto generated!
#eval troll.large
/- * Just like the where syntax, curly-brace notation with field names also works with structure inheritance -/
def troll' : Monster := {large := true, vulnerability := "sunlight"}
#eval troll'
def troll'' : Monster := ⟨true, "sunlight"⟩
def troll'1 : Monster := ⟨⟨true⟩, "sunlight"⟩
#eval troll'1
/- * auto-upcast only works with dot attributor -/
def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
#check_failure MythicalCreature.large troll -- ! error - this should fail
#eval troll.small
#check_failure MythicalCreature.small troll -- ! error - this should also fail
def MythicalCreature.foo : MythicalCreature -> Nat := fun _ => 42
instance : Coe Monster MythicalCreature where coe m := m.toMythicalCreature
#eval MythicalCreature.foo (troll : Monster)
#eval troll.foo
#eval MythicalCreature.large troll -- * now calls can auto-upcast

-- ## Multiple Inheritance

structure Helper extends MythicalCreature where
  assistance : String
  payment : String
  deriving Repr
def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"
/- * diamond resolution in Lean
   **the first specified path to the grandparent structure is taken**
    and the additional parent structures' fields are copied
    rather than having the new structure include both parents directly. -/
structure MonstrousAssistant extends Monster, Helper where deriving Repr
def domesticatedTroll : MonstrousAssistant where
  large := false
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"
#check MonstrousAssistant.mk
#print MonstrousAssistant.toHelper

inductive Size where
  | small
  | medium
  | large
deriving BEq

structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large

def nonsenseCreature : SizedCreature where
  large := false
  size := .large

/- * If the child structure should not deviate from the parent structure, there are a few options:
   * - Documenting the relationship, as is done for BEq and Hashable
   * - Defining a proposition that the fields are related appropriately,
   *   and designing the API to require evidence that the proposition is true where it matters
   * - Not using inheritance at all
-/
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)
def huldre : SizedCreature where
  size := .medium
example : SizesMatch huldre := by decide
