-- # Interlude: Propositions and Proofs
def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

#check (1 + 2 = 3)

-- def onePlusOneIsTwo : 1 + 1 = 2 := rfl -- short for _reflexivity_

def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl

theorem onePlusOneIsTwo1 : 1 + 1 = 2 := by
  simp

-- Option 1: Use rfl (reflexivity) for the full proof
/-
  theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
    constructor
    · simp  -- proves 1 + 1 = 2
    · rfl   -- proves "Str".append "ing" = "String"
-/

-- Option 2: Fully explicit with rfl
theorem addAndAppend' : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := ⟨rfl, rfl⟩

-- Option 3: Using decide for computational proofs
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by decide

variable (A B : Prop) -- * nowadays required
-- // #check (fun a : A => b : B) -- term-level proof of A → B

open Classical
theorem impl_to_disj (A B : Prop) : (A → B) ↔ (¬A ∨ B) :=
⟨ λ f => if h : A then Or.inr (f h) else Or.inl h,
  λ d a => d.elim (λ na => False.elim (na a)) id ⟩

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _/-b-/ => Or.inl a

-- the `simp` tactic can simplify basic connectives
theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp
theorem trueIsTrue : True := True.intro
theorem trueOrFalse : True ∨ False := by simp
theorem falseImpliesTrue : False → True := by simp

-- ## Evidence as Arguments
def third {α : Type} (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- Lean CAN infer the type parameter when using implicit arguments correctly:
def third' {α : Type} (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- We can also let Lean infer the universe level:
def third'' {α} (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- ### Auto-Implicit Mode Demonstration

-- Turn ON auto-implicit (allows undeclared variables to be auto-implicit)
set_option autoImplicit true

-- Now we can use α without explicitly declaring it!
def third_auto (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- This also works for multiple type variables
def combine (x : α) (y : β) : α × β := (x, y)

-- Turn OFF auto-implicit (back to default behavior)
set_option autoImplicit false

-- Now this would give an error if uncommented:
-- def third_error (xs : List α) (ok : xs.length > 2) : α := xs[2]  -- Error: unknown identifier 'α'

-- Let's test that they work the same way:
#check third
#check third'
#check third''
#check third_auto

-- Example usage - Lean infers α automatically:
#eval third woodlandCritters (by decide)

-- ### Term Mode vs Tactic Mode Examples

-- Term mode: direct proof construction
theorem directProof1 : 2 + 3 = 5 := rfl
theorem directProof2 : "hello".length = 5 := rfl
theorem directProof3 : [1, 2, 3].length = 3 := rfl

-- Tactic mode: proof by instructions
theorem tacticProof1 : 2 + 3 = 5 := by simp
theorem tacticProof2 : "hello".length = 5 := by rfl  -- simp doesn't work here, but rfl does
theorem tacticProof3 : [1, 2, 3].length = 3 := by simp

-- You can mix them - tactics ultimately produce terms
theorem mixedProof : 1 + 1 = 2 ∧ 3 + 3 = 6 := ⟨rfl, rfl⟩  -- term mode with constructor
theorem mixedProof2 : 1 + 1 = 2 ∧ 3 + 3 = 6 := by constructor <;> rfl  -- tactic mode

-- More complex: when rfl alone isn't enough, tactics can help
theorem complexTactic : (1 + 1) * 2 = 4 := by simp
theorem complexTerm : (1 + 1) * 2 = 4 := rfl  -- this also works!

-- When rfl fails, you need tactics or more complex terms
-- Example: proving something that requires unfolding definitions
def double (n : Nat) : Nat := n + n
theorem aboutDouble : double 2 = 4 := rfl  -- works because double 2 unfolds to 2 + 2 = 4

-- Check what these proofs actually look like
#check @rfl  -- the actual proof term
#print directProof1  -- see the proof term Lean generated
#print tacticProof1  -- see what tactic mode produced (should be similar to rfl)

-- ## Exercises
theorem eq_2Plus3Is5 : 2 + 3 = 5 := by rfl
theorem eq_15Minus8Is7 : 15 - 8 = 7 := by rfl
theorem eq_HelloWorld : "Hello, ".append "world" = "Hello, world" := by rfl
-- theorem lt_8_15 : 8 < 15 := by rfl
/- ! output
! Tactic `rfl` failed: The left-hand side
!   8
! is not definitionally equal to the right-hand side
!   15
! ⊢ 8 < 15Lean 4
-/
theorem lt_8_15 : 8 < 15 := by simp
def fifth {α} (xs : List α) (ok : xs.length > 4) : α := xs[4]
-- #eval fifth woodlandCritters (by decide)
/- ! output
! Tactic `decide` proved that the proposition
!   woodlandCritters.length > 4
! is falseLean 4
-/
