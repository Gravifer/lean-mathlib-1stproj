namespace tpil
section cpt8
set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Lean provides natural ways of defining recursive functions,
    performing pattern matching, and writing inductive proofs.
  It allows you to define a function by specifying equations that it should satisfy,
    and it allows you to prove a theorem by specifying how to handle various cases that can arise.
  Behind the scenes, these descriptions are "compiled" down to primitive recursors,
    using a procedure that we refer to as the **equation compiler**.
  The equation compiler is **not part of the trusted code base**;
    its output consists of terms that are checked independently by the kernel. -/

-- ## §8.1 pattern matching
/- `Nat.casesOn` is a convenience wrapper around `Nat.rec` for simple case analysis.
  Unlike `Nat.rec`, it doesn't provide the inductive hypothesis in the successor case.

  It's defined as: `Nat.rec zero (fun n n_ih ↦ succ n) t`
  Notice how it discards the inductive hypothesis `n_ih` and only passes `n` to the successor function.

  Use `casesOn` when you only need to distinguish between zero and successor cases,
  but don't need to recurse or access the result for smaller values.

  See `Lean.Meta.Match.MatchPatternAttr`, for the `@[match_pattern]` attribute
    which allows all the pattern matching capabilities.
  Patterns with multiple branches are actually dealing with nested constructors.
-/
#print Nat.casesOn
#print Nat.rec
#print Nat.recOn
#print Nat.strongRecOn -- requires well-founded recursion

def sub2 : Nat → Nat
  | 0     => 0
  | 1     => 0
  | x + 2 => x

#reduce sub2 5

/- Ways to discover auxiliary functions without knowing their names in advance: -/

-- 1. Print the main function to see what auxiliaries it references
#print sub2
set_option pp.all true in
#print sub2

-- 2. Use #check to see the type and get hints about the structure
#check sub2

-- 3. Get all declarations in the current namespace that start with "sub2"
#print axioms sub2  -- Shows what axioms/definitions this depends on

-- 4. For match expressions, Lean typically generates `.match_n` auxiliaries
-- Let's check the pattern:
#print sub2.match_1

-- 5. General pattern: Lean generates auxiliary functions with predictable names
-- For pattern matching: functionName.match_1, functionName.match_2, etc.
-- For mutual recursion: functionName._mutual, etc.
-- For well-founded recursion: functionName._unsafe_rec, etc.

-- You can also use tactics to explore:
example : sub2 3 = 1 := by
  unfold sub2  -- This will show you the underlying definition
  simp

section _temp_
variable {α : Type} {p : α → Bool} {a : α}
#check ¬p a = true
variable {α : Type} {p : α → Prop} {a : α}
#check p a = false
end _temp_

set_option linter.unusedVariables false
def tail1 {α : Type u} : List α → List α
  | []      => []
  | a :: as => as
def tail2 : {α : Type u} → List α → List α
  | α, []      => []
  | α, a :: as => as


-- ## §8.2 Wildcards and Overlapping Patterns


/- Generally speaking, the equation compiler processes input of the following form:
  ```lean
  def foo (a : α) : (b : β) → γ
    | [patterns₁] => t₁
    ...
    | [patternsₙ] => tₙ
  ```
  - `(a : α)` is a sequence of parameters
  - `(b : β)` is the sequence of arguments on which pattern matching takes place
  - `γ` is any type, which can depend on `a` and `b`.
Each line should contain the same number of patterns, one for each element of `β`.
A pattern is either
  - a variable,
  - a constructor applied to other patterns, or
  - an expression that normalizes to something of that form
    (where the non-constructors are marked with the `[match_pattern]` attribute).
The appearances of constructors prompt case splits,
  with the arguments to the constructors represented by the given variables. -/
-- ## §8.3 Structural Recursion and Induction
/- the terms `t₁, ..., tₙ` can make use of any of the parameters `a`,
  as well as any of the variables that are introduced in the corresponding patterns.
  What makes recursion and induction possible is that they can also involve recursive calls to `foo`.

  __Structural recursion__ is when the arguments to `foo`
    occurring on RHS of `=>` are subterms of the patterns on the left-hand side.
  The idea is that they are **structurally smaller**,
    and hence appear in the inductive type at an earlier stage.
  The equation compiler ensures the structural order
    compared to the original arguments `b`.
  This guarantees that the recursion will eventually terminate,
    and that any inductive proofs will eventually reach the base case.

  In some situations, reductions hold only _propositionally_, i.e.,
    they are equational theorems that must be applied explicitly.
  The equation compiler generates such theorems internally:
    they are not meant to be used directly by the user; rather,
    the `simp` tactic is configured to use them when necessary.
-/
def fib : Nat → Nat
    | 0 | 1  => 1
    | n+2 => fib (n+1) + fib n
  example : fib 0 = 1 := rfl
  example : fib 1 = 1 := rfl
  example : fib (n + 2) = fib (n + 1) + fib n := rfl
  example : fib 7 = 21 := rfl
def fibFast (n : Nat) : Nat :=  (loop n).2 where  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  #eval fibFast 100
  #print fibFast.loop
def fibFast' (n : Nat) : Nat :=  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2
  #eval fibFast' 100
  #print fibFast'.loop

/- For structural recursion, the equampiler uses _course-of-values_ recursion,
  using the constants `below` and `brecOn` autogened with each inductively defined type.
  This is one of the techniques the equampiler uses
    to justify to the Lean kernel that a function terminates.
  It does not affect codegen, which compiles recursive functions,
    as in other functional programming language compilers. -/
variable (C : Nat → Type u)
#check (@Nat.below  C)
#reduce @Nat.below  C (3 : Nat)
#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)
set_option pp.auxDecls true in #print fib

-- ## §8.4 Local recursive declarations
/- Lean uses `let rec` and `where` for local recursion,
    mixing OCaml and Haskell styles -/

-- ## §8.5 Well-Founded Recursion and Induction
/- When structural recursion cannot be used, well-founded recursion can prove termination.
  We need a well-founded relation and a proof that
    each recursive application is decreasing with respect to this relation.
  Dependent type theory is powerful enough to encode and justify well-founded recursion. -/
#print Acc  -- (Acc r x)  ↔  (∀y:α, r y x → Acc r y)
#print Acc.casesOn
#print Acc.rec
#print Acc.recOn
#print Acc.inv
#print WellFounded  -- (WellFounded r) ↔ (∀a:α, Acc r a)
#print WellFounded.fix
#print WellFounded.fixF
#print Nat.strongRecOn
/- The equation compiler uses `WellFounded.fix` to justify well-founded recursion.
  This is a generalization of `Nat.strongRecOn` to arbitrary well-founded relations.
  The user can also use `WellFounded.fix` directly to define functions by well-founded recursion. -/
section _wf_
variable (α : Sort u) (r : α → α → Prop)
  #check Acc r
  #check WellFounded r
  noncomputable -- because the code generator currently does not support `WellFounded.fix`
    def f {α : Sort u} (r : α → α → Prop) (h : WellFounded r)
      (C : α → Sort v)  -- motive of the recursive definition
      (F :  -- inductive recipe for constructing an element of `C x`, `∀x`,
        (x : α) → ((y : α) → r y x → C y) → C x)  --  given elements of `C y` for each predecessor `y` of `x`.
      : (x : α) → C x :=  WellFounded.fix h F
end _wf_
#print measure

#print Nat.div
#print Nat.div.go

section _wf_
namespace Hidden
  open Nat -- mockup of Nat.div using WellFounded.fix
  -- We use the standard `<` relation on `Nat`, which is well-founded.
  theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
    fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left
  def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
    if h : 0 < y ∧ y ≤ x then
      f (x - y) (div_lemma h) y + 1
    else  zero
  noncomputable def div' := WellFounded.fix (measure id).wf div.F
  -- The elaborator is designed to make such definitions more convenient and accepts the following
  def div (x y : Nat) : Nat :=
    if h : 0 < y ∧ y ≤ x then
      have : x - y < x := div_lemma h
      div (x - y) y + 1
    else  0
  /- When Lean encounters a recursive definition, it first tries structural recursion,
      and only when that fails, does it fall back on well-founded recursion.
    Lean uses the tactic `decreasing_tactic` to show that
      the recursive applications are smaller.
    The auxiliary proposition `x - y < x` in the example above
      should be viewed as a hint for this tactic.

    The defining equation for `div` does _not_ hold definitionally,
      but we can unfold `div` using the `unfold` tactic.
    We use `conv` to select which `div` application we want to unfold.-/
  example (x y : Nat)
    : div x y = if 0 < y ∧ y ≤ x
        then  div (x - y) y + 1
        else 0 := by
    -- unfold occurrence in the left-hand-side of the equation:
    conv => lhs; unfold div
    rfl

  example (x y : Nat) (h : 0 < y ∧ y ≤ x)
    : div x y = div (x - y) y + 1 := by
    conv => lhs; unfold div
    simp [h]

  /- As a final example, observe that Ackermann's function can be defined directly
      because it is justified by the well-foundedness
        of the lexicographic order on the natural numbers.
    The `termination_by` clause instructs Lean to use a lexicographic order.
    This clause is actually mapping the function arguments to elements of type `Nat × Nat`.
    Then, Lean uses typeclass resolution to synthesize
      an element of type `WellFoundedRelation (Nat × Nat)`. -/
  def ack : Nat → Nat → Nat
    | 0,   y   => y+1
    | x+1, 0   => ack x 1
    | x+1, y+1 => ack x (ack (x+1) y)
    termination_by x y => (x, y) /- Lean can auto determine an appropriate lexicographical order in many cases,
                                    and this clause here is actually optional -/

  #print SizeOf
  variable [SizeOf α]
  #synth WellFoundedRelation α
  #synth WellFoundedRelation (α × α)
  #print sizeOfWFRel

  #print Array
  #print Array.size

  /- Lean defaults to `decreasing_tactic` to prove recursive applications are decreasing.
      The modifier `decreasing_by` allows us to provide our own tactic.-/
  theorem div_lemma' {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
    fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos
  def div'' (x y : Nat) : Nat :=  if h : 0 < y ∧ y ≤ x
      then  div'' (x - y) y + 1
      else  0
    decreasing_by apply div_lemma'; assumption

  -- using `termination_by` and `decreasing_by` together:
  def ack' : Nat → Nat → Nat
    | 0,   y   => y+1
    | x+1, 0   => ack' x 1
    | x+1, y+1 => ack' x (ack' (x+1) y)
    termination_by x y => (x, y)
    decreasing_by -- unfolds well-founded recursion auxiliary definitions:
      all_goals simp_wf
      · apply Prod.Lex.left; simp +arith
      · apply Prod.Lex.right; simp +arith
      · apply Prod.Lex.left; simp +arith
end Hidden
end _wf_


-- ## §8.6 Functional Induction
/-
- tactic `fun_induction` is a convenience wrapper around tactic `induction` to use the the functional induction principle.
      `fun_induction f x₁ ... xₙ y₁ ... yₘ`
  where `f` is a function defined by non-mutual structural or well-founded recursion, is equivalent to
      `induction y₁, ... yₘ using f.induct_unfolding x₁ ... xₙ`
  where the arguments of `f` are used as arguments to `f.induct_unfolding` or targets of the induction, as appropriate.
- tactic `fun_cases` tactic wraps tactic `cases` when using a functional cases principle.
      `fun_cases f x ... y ...`
  is equivalent to
      `cases y, ... using f.fun_cases_unfolding x ...`

  tactic `simp_all` is a stronger version of `simp [*] at *`
    where the hypotheses and target are simplified multiple times
      until no simplification is applicable.
    Only non-dependent propositional hypotheses are considered.
-/

-- ## §8.7 Mutual Recursion
mutual
  def even : Nat → Bool
    | 0   => true
    | n+1 => odd n

  def odd : Nat → Bool
    | 0   => false
    | n+1 => even n
end

example : even (a + 1) = odd a := by
  simp [even]

example : odd (a + 1) = even a := by
  simp [odd]

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a; induction a
  . simp [even, odd]
  . simp [even, odd, *]


-- ## §8.8 Dependent Pattern Matching
/- the above approach relying on `casesOn` and `recOn` struggles with
    indexed inductive families such as `Vect α n`,
    since case splits impose constraints on the values of the indices.-/
#print Nat.noConfusion

section sect9 -- ## Inaccessible Patterns
/- Sometimes an argument in a dependent matching pattern is not essential to the definition,
  but nonetheless has to be included to specialize the type of the expression appropriately.
  Lean allows users to mark such subterms as inaccessible for pattern matching.
  These annotations are essential, for example,
    when a term occurring in the left-hand side is neither a variable nor a constructor application,
    because these are not suitable targets for pattern matching.
  We can view such inaccessible patterns as "don't care" components of the patterns.
  You can declare a subterm inaccessible by writing `.(t)`.
  If the inaccessible pattern can be inferred, you can also write `_`,
    which is actually a shorthand for `.(_)` in this case. -/
  inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
    | imf : (a : α) → ImageOf f (f a)
  open ImageOf
  def inverse {f : α → β} : (b : β) → ImageOf f b → α
    | .(f a), imf a => a  /- The typing rules forces us to write `f a` for the first argument,
        but this term is neither a variable nor a constructor application,
        and plays no role in the pattern-matching definition; we thus mark `f a` inaccessible.
        The inaccessible annotation makes it clear that `f` is **not** a pattern matching variable. -/
  def inverse' {f : α → β} : (b : β) → ImageOf f b → α
    | _, imf a => a

end sect9


-- ## §8.10 Match Expressions
/- Lean uses the `match ⋯ with` expr construct internally
    to implement pattern-matching in all parts of the system.
  Thus, all four of these definitions have the same net effect: -/
def bar₁ : Nat × Nat → Nat
  | (m, n) => m + n
def bar₂ (p : Nat × Nat) : Nat :=  match p with
  | (m, n) => m + n
def bar₃ : Nat × Nat → Nat :=  fun (m, n) => m + n
def bar₄ (p : Nat × Nat) : Nat :=
  let (m, n) := p; m + n

-- all four definitions are equivalent:
variable (p q : Nat → Prop)

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y
  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
  : ∃ x y, p x ∧ q y :=
  match h₀, h₁ with  | ⟨x, px⟩, ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example : (∃ x, p x) → (∃ y, q y) → ∃ x y, p x ∧ q y :=
  fun ⟨x, px⟩ ⟨y, qy⟩ => ⟨x, y, px, qy⟩

example (h₀ : ∃ x, p x) (h₁ : ∃ y, q y)
  : ∃ x y, p x ∧ q y :=
  let ⟨x, px⟩ := h₀
  let ⟨y, qy⟩ := h₁
  ⟨x, y, px, qy⟩

-- ## §8.11 Exercises
/- 4. Define a function that will append two vectors. -/
variable {α : Type u}
inductive Vect (α : Type u) : Nat → Type u
  | nil  : Vect α 0
  | cons : α → {n : Nat} → Vect α n → Vect α (n + 1)
/- def Vect.append ⦃m n : Nat⦄ (v₁ : Vect α m) (v₂ : Vect α n) : Vect α (m + n) :=
  go m n v₁ v₂ where
    go : (m n : Nat) → Vect α m → Vect α n → Vect α (m + n)
    | 0   , n, Vect.nil,        v₂ => by rw [<-Nat.zero_add n] at v₂; exact v₂
    | m'+1, n, Vect.cons a v₁', v₂ => by
        have v : Vect α (m' + n + 1) := .cons a $ go m' n v₁' v₂
        rw [Nat.add_right_comm]; exact v -/
def Vect.append ⦃m n : Nat⦄ (v₁ : Vect α m) (v₂ : Vect α n) : Vect α (m + n) :=
  match m, v₁ with
    | 0   , .nil        => by rw [<-Nat.zero_add n] at v₂; exact v₂
    | m'+1, .cons a v₁' => by
        rw [Nat.add_right_comm]; exact .cons a $ @Vect.append m' n v₁' v₂

end cpt8
