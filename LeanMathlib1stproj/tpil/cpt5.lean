namespace tpil
section cpt5 -- # Tactics
set_option autoImplicit true
set_option relaxedAutoImplicit true

-- ## §5.1 Entrance
/-
  - Commands:
    1. Use `#check`  to check the type of an expression.
    2. Use `#eval`   to evaluate an expression.
    3. Use `#print`  to print the definition of a term.
        -  `#print axioms <theorem>` lists the axioms used in the proof of `<theorem>`.
    4. Use `#synth`  to synthesize an instance of a type class.
    5. Use `#find`   to search for declarations matching a pattern.
    6. Use `#guard`  to assert that an expression has a certain type.
        -  `#guard_msg`    to assert that a command produces a certain message.
        -  `#guard_hyp`    to assert that a hypothesis has a certain type.
        -  `#guard_expr`   to assert that an expression is equal to another expression.
        -  `#guard_prefix` to assert that a declaration has a certain prefix.
    7. Use `#lint`   to check for common issues in the code.
    8. Use `#reduce` to reduce an expression to its simplest form.
    9. Use `#exit`   to exit Lean.
  - Symbols:
    - `⊢` (turnstile) separates hypotheses from the conclusion in a sequent.
    - `⊤` (top) and `⊥` (bottom) for true and false.
    - `∧` (and), `∨` (or), `¬` (not), `→` (implies), `↔` (if and only if).
    - `∀` (for all) and `∃` (there exists).
    - `∈` (element of) for set membership.
    - `∅` (empty set) for the empty set.
    - `ℕ`, `ℤ`, `ℚ`, `ℝ`, and `ℂ` for the common number sets, respectively.
  - Unsound:
    - `_`     is a hole for the typechecker to infer a term.
    - `sorry` is a placeholder for an incomplete proof, both a term and a tactic.
    - `admit` is used to assume a statement without proof.
    - `axiom` introduces an unproven assumption.
    * `Classical` module provides classical logic axioms.
  - Unhygienics:
    - Combinator `unhygienic` let autogen make exposed names.
    - `expose_names` expose names already autogened.
    - Tactic `rename_i` renames the most recent inaccessible names.
-/

-- ## §5.2 Basics
/- Enter tactic mode with the combinator `by`. Common tactics
  - `exact` closes the main goal if its target type matches.
  - `apply` unifies the conclusion with the expression in the current goal.
    - `case «tag» =>` focuses on a specific case of an inductive type.
    - `.`/`·`` «tactics»` select the first subgoal.
  - `intro` introduces a hypothesis (and generally a variable of any type)
            allows implicit destructuring match.
    - `intros` introduces multiple hypotheses/variables, but **inaccessibly**.
            * write pointly first, then revise it to a pointless style.
  - `revert` inverts what `intro` does; for a variable, this amounts to quantifying it universally.
             > `revert` is clever; it revert not only an element of the context
                but also all subsequent elements of the context depending on it.
  - `generalize` replaces an arbitrary expression in the goal by a fresh variable,
                 adding an equality hypothesis to the context.
    - `generalize'` is like `generalize`, but does not add an equality hypothesis.
  - `rfl` (`reflexivity`) solves goals that are reflexive relations
          applied to definitionally equal arguments.
    - `symmetry` changes a goal of the form `a = b` to `b = a`.
    - `transitivity` changes a goal of the form `a = c` to `a = b` and `b = c`.
  - `repeat` combinator repeatedly applies a tactic until it fails.
-/

-- ## §5.3 More
/-
  - `constructor` applies a constructor of an inductive if unique.
    - `exists` provides a witness for an existential quantifier
              (`constructor` would make it a metavar).
  - `cases` splits an inductive, and close unreachables automatically
            can decompose a disjunction goal / conjunction hypothesis.
    - `with` (optionally) runs a tactic on all branches; then follows a list of alternatives.
    - unstructured `cases` (i.e., no `with`) can optionally be combined with `case` and `·`.
    - ultimately a companion for the `induction` tactic. See later chapters.
  - `contradiction` searches for a contradiction among the hypotheses of the current goal.
-/

-- ## §5.4 Structuring
/- it is possible to mix term-style and tactic-style proofs, and pass between the two freely. -/

-- ## §5.5 Combinators
/-
  - `«t1»; «t2»` applies `t1` to the main goal, then `t2` to the main goal. (syntax, not combinator)
  - `«t1» <;> «t2»` combinator apply `t2` to **all** subgoals produced by `t1`. (flatmap)
                    > a _parallel_ version of sequencing
  - `«t1» <|> «t2»` combinator tries `t1`, and if it fails, tries `t2`. (alternative monad)
  - `first | t₁ | t₂ | ... | tₙ` applies each `tᵢ` until one succeeds, or else fails
  - `try «t»` combinator applies `t`, but does not fail if `t` fails:
                `try t` is equivalent to `first| t |skip`
      ! Be careful: `repeat (try t)` loops forever, because the inner tactic never fails.
  - `all_goals «t»` applies `t` to all current goals, succeed only if all succeeds.
  - `any_goals «t»` applies `t` to all, but succeed if any.
  - `focus t`  ensures that `t` only effects the current goal, temporarily hiding the others from the scope.
-/

-- ## §5.6 Rewriting
/- already familiar -/

-- ## §5.7 Simplifier
/- Whereas `rw` is designed as a surgical tool for manipulating a goal,
    the simplifier offers a more powerful form of automation.
  Some identities in library have been tagged with the `[simp]` attribute,
    and the `simp` tactic uses them to iteratively rewrite subterms in an expression.

  You can use a wildcard `*` to simplify all the hypotheses and the goal.-/
attribute [local simp] Nat.mul_comm Nat.mul_assoc Nat.mul_left_comm -- modifier `local` makes `simp` only use it in current scope
attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

example (w x y z : Nat) (p : Nat → Prop)
        (h : p (x * y + z * w * x)) : p (x * w * z + y * x) := by
  simp at *; assumption

example (x y z : Nat) (p : Nat → Prop)
        (h₁ : p (1 * x + y)) (h₂ : p (x * z * 1))
        : p (y + 0 + x) ∧ p (z * x) := by
  simp at * <;> constructor <;> assumption

/- It may seem that commutativity and left-commutativity are problematic,
    in that repeated application of either causes looping.
  But the simplifier detects identities that permute their arguments,
    and uses a technique known as ordered rewriting.
  This means that the system maintains an internal ordering of terms,
    and only applies the identity if doing so decreases the order.

  To use all the hypotheses present in the local context when simplifying, use `[*]`-/
variable (k : Nat) (f : Nat → Nat) in
example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]

/- using `@[simp]` is equivalent to `attribute [simp]`

Additional useful modifiers:
  `simp only` excludes defaults, allowing a more explicit-crafted list of rules.
  In the examples below, `-` and `only` are used to block the application of `reverse_mk_symm`.-/
def mk_symm (xs : List α) :=
  xs ++ xs.reverse
@[simp] theorem reverse_mk_symm (xs : List α)
        : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p (mk_symm ys ++ xs.reverse) := by
  simp at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp [-reverse_mk_symm] at h; assumption

example (xs ys : List Nat) (p : List Nat → Prop)
        (h : p (xs ++ mk_symm ys).reverse)
        : p ((mk_symm ys).reverse ++ xs.reverse) := by
  simp only [List.reverse_append] at h; assumption
/- The simp tactic has many configuration options.
    For example, we can enable contextual simplifications as follows: -/
example : if x = 0 then y + x = y else x ≠ 0 := by
  simp +contextual
-- option `+arith` which enables arithmetical simplifications.
example : 0 < 1 + x ∧ x + y + 2 ≥ y + 1 := by
  simp +arith

-- ## §5.8 Split
def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

-- ## §5.9 Extensible tactics
-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv


-- ## §5.10 Exercises
set_option trace.split.failure true
/- Use tactic combinators to obtain a one-line proof of the following: -/
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  apply And.intro <;> (try apply And.intro) <;> repeat (first | left; assumption | right | assumption)


/- # AI Junk #-/

-- Define tactic sequences for handling multiple conjunctions and disjunctions

-- Tactic to break multiple conjunctions into subgoals
-- This version tries to apply And.intro as much as possible
syntax "split_conjs" : tactic
macro_rules
  | `(tactic| split_conjs) => `(tactic| repeat (first | apply And.intro | constructor))

-- Alternative version that handles the last goal differently (for the one-liner style)
syntax "split_all_conjs" : tactic
macro_rules
  | `(tactic| split_all_conjs) => `(tactic| apply And.intro <;> try apply And.intro)

-- More advanced version that fully decomposes nested conjunctions
syntax "split_all_nested_conjs" : tactic
macro_rules
  | `(tactic| split_all_nested_conjs) => `(tactic| repeat (any_goals (first | apply And.intro | constructor)))

-- Tactic to select a specific disjunct (0-indexed from left)
syntax "pick_left" : tactic
macro_rules
  | `(tactic| pick_left) => `(tactic| left)

syntax "pick_middle" : tactic
macro_rules
  | `(tactic| pick_middle) => `(tactic| right; left)

syntax "pick_right" : tactic
macro_rules
  | `(tactic| pick_right) => `(tactic| right; right)

-- General tactic to try finding a disjunct that can be solved by assumption
syntax "pick_assumption" : tactic
macro_rules
  | `(tactic| pick_assumption) => `(tactic| first | left; assumption | right; left; assumption | right; right; assumption)

-- More flexible disjunction picker - tries all positions automatically
syntax "pick_any" : tactic
macro_rules
  | `(tactic| pick_any) => `(tactic| repeat (first | assumption | left | right))

-- Parameterized disjunction picker (picks the nth disjunct, 0-indexed)
-- Note: A ∨ B ∨ C is parsed as A ∨ (B ∨ C), so we navigate accordingly
syntax "pick" num : tactic
macro_rules
  | `(tactic| pick 0) => `(tactic| left)
  | `(tactic| pick 1) => `(tactic| right; left)
  | `(tactic| pick 2) => `(tactic| right; right)

-- Examples using the new tactics:

-- Basic conjunction splitting (works for simple cases)
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  split_conjs
  · exact hp
  · exact hq

-- For nested conjunctions, use the advanced version or manual approach
example (p q r s : Prop) (hp : p) (hq : q) (hr : r) (hs : s) : p ∧ q ∧ r ∧ s := by
  constructor
  · exact hp
  · constructor
    · exact hq
    · constructor
      · exact hr
      · exact hs

-- Disjunction examples demonstrating the pick tactics
example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  pick_left
  exact hp

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  pick_middle
  exact hq

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  pick_right
  exact hr

-- The pick_assumption tactic automatically finds the right disjunct
example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by pick_assumption
example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by pick_assumption
example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by pick_assumption

-- More complex example: multiple disjunctions with different variables available
example (p q r s : Prop) (hq : q) (hs : s) : (p ∨ q ∨ r) ∧ (r ∨ s ∨ p) := by
  constructor
  · pick_assumption  -- finds q in first disjunction
  · right; left; exact hs  -- manually pick s in second disjunction

-- Examples using the numbered pick tactic
example (p q r s : Prop) (hr : r) : p ∨ q ∨ r := by
  pick 2
  exact hr

-- The original problem now has a much cleaner solution:
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  split_all_conjs <;> pick_assumption

-- Alternative solution using the basic building blocks:
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor
  · pick_left; exact hp
  · constructor
    · pick_middle; exact hp
    · pick_right; exact hp

example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  pick_left
  exact hp

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  pick_middle
  exact hq

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  pick_right
  exact hr

-- The original example now becomes much cleaner:
example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  split_all_conjs <;> pick_assumption



----

/-
  - `;;` combinator applies the following tactic to all goals.
  - `|>` combinator pipes the result of a tactic to another tactic.
  - `>>=` combinator pipes the result of a tactic to another tactic, passing the result as an argument.
  - `>>` combinator pipes the result of a tactic to another tactic, ignoring the result.
  - `!` combinator applies a tactic repeatedly until it fails.
  - `?` combinator tries a tactic, but does not fail if the tactic fails.
  - `⟨ ... ⟩` combinator applies a tactic to each goal in sequence.
  - `⊢` (turnstile) separates hypotheses from the conclusion in a sequent.
  - `·` (dot) selects the first subgoal.
  - `.` (period) selects the first subgoal.
-/

/-
  - `by_cases h : P` performs case analysis on a proposition `P`, creating two subgoals.
    - In the first subgoal, `h : P` is added to the context.
    - In the second subgoal, `h : ¬P` is added to the context.
  - `by_contra h` changes a goal `P` to `¬P` and adds `P` to the context.

  - `refine` is like `exact`, but allows for holes (`_`) in the term.
  - `exfalso` changes the goal to `false`.
  - `left` and `right` apply the left or right constructor of a disjunction.
  - `use` provides a witness for an existential quantifier.
-/


/- More tactics
  - `rewrite` replaces occurrences of a term with another term.
    - `←` (left arrow) reverses the direction of the rewrite.
    - `at` specifies where to apply the rewrite (in the goal or in a hypothesis).
    - `only` restricts the rewrite to only the specified occurrences.
    - `*` applies the rewrite to all hypotheses and the goal.
  - `simp` simplifies an expression using known simplification rules.
    - `only` restricts the simplification to only the specified lemmas.
    - `*` applies the simplification to all hypotheses and the goal.
    - `using` adds additional lemmas to the simplification process.
  - `dsimp` simplifies the goal by unfolding definitions.
    - `only` restricts the simplification to only the specified definitions.
    - `*` applies the simplification to all hypotheses and the goal.
  - `split` splits a goal into multiple subgoals.
    - For conjunctions (`P ∧ Q`), it creates two subgoals: one for `P` and one for `Q`.
    - For biconditionals (`P ↔ Q`), it creates two subgoals: one for `P → Q` and one for `Q → P`.
  - `finish` tries to automatically close the current goal using a combination of tactics.
-/

/-
  - `induction` performs induction on a natural number or an inductive type.
    - `with` specifies names for the variables in the inductive step.
    - `generalizing` allows to generalize certain variables during induction.
  - `have` introduces an intermediate assertion.
  - `let` introduces a local definition.
  - `show` changes the goal to a specified expression.
  - `change` changes the goal to a specified expression, if they are definitionally equal.
  - `unfold` expands the definition of a constant in the goal.
  - `assumption` closes the goal if it matches any of the available hypotheses.
  - `trivial` closes the goal if it is trivially true.

  - `try` combinator applies a tactic, but does not fail if the tactic fails.
  - `by` combinator allows for nested tactic proofs.
  - `done` closes the goal if there are no remaining goals.
  - `all_goals` applies a tactic to all current goals.
  - `any_goals` applies a tactic to any one of the current goals.
  - `first` applies the first tactic that succeeds from a list of tactics.
  - `focus` focuses on a specific goal to apply tactics to.
  - `tactic` allows for custom tactics to be written in Lean.
  - `tactic.interactive` provides additional interactive tactics.
  - `tactic.derive` derives instances of certain type classes automatically.
  - `tactic.revert` reverts a hypothesis back to the goal.
  - `tactic.clear` removes a hypothesis from the context.
  - `tactic.rename` renames a hypothesis in the context.
  - `tactic.swap` swaps the order of two goals.
  - `tactic.trace` prints a message to the output.
  - `tactic.trace_state` prints the current state of the proof.
  - `tactic.trace_goal` prints the current goal.
  - `tactic.trace_hyp` prints a specific hypothesis.
  - `tactic.trace_expr` prints a specific expression.
  - `tactic.trace_type` prints the type of a specific expression.
  - `tactic.trace_instance` prints an instance of a specific type class.
  - `tactic.trace_synth` prints the result of synthesizing an instance of a specific type class.
  - `tactic.trace_simp` prints the result of simplifying an expression.
  - `tactic.trace_rewrite` prints the result of rewriting an expression.
  - `tactic.trace_induction` prints the result of performing induction on a hypothesis.
  - `tactic.trace_cases` prints the result of performing case analysis on a hypothesis.
  - `tactic.trace_by_cases` prints the result of performing case analysis on a proposition.
  - `tactic.trace_by_contra` prints the result of performing proof by contradiction.
  - `tactic.trace_exfalso` prints the result of applying `exfalso`.
  - `tactic.trace_constructor` prints the result of applying a constructor.
  - `tactic.trace_left` prints the result of applying the left constructor of a disjunction.
  - `tactic.trace_right` prints the result of applying the right constructor of a disjunction.
  - `tactic.trace_use` prints the result of providing a witness for an existential quantifier.
  - `tactic.trace_have` prints the result of introducing an intermediate assertion.
  - `tactic.trace_let` prints the result of introducing a local definition.
  - `tactic.trace_show` prints the result of changing the goal to a specified expression.
  - `tactic.trace_change` prints the result of changing the goal to a specified expression.
  - `tactic.trace_unfold` prints the result of unfolding a definition in the goal.
  - `tactic.trace_dsimp` prints the result of simplifying the goal by unfolding definitions.
  - `tactic.trace_by_cases` prints the result of performing case analysis on a proposition.
  - `tactic.trace_cases` prints the result of performing case analysis on a hypothesis.
  - `tactic.trace_revert` prints the result of reverting a variable from the context.
  - `tactic.trace_induction` prints the result of performing induction on a natural number or an inductive type.
  - `tactic.trace_rewrite` prints the result of rewriting an expression.
  - `tactic.trace_simp` prints the result of simplifying an expression using known simplification rules.
  - `tactic.trace_split` prints the result of splitting a goal into multiple subgoals.
  - `tactic.trace_finish` prints the result of trying to automatically close the current goal.
  - `refine` is like `exact`, but allows for holes (`_`) in the term.
  - `by_contra` changes a goal `P` to `¬P` and adds `P` to the context.
  - `exfalso` changes the goal to `false`.
  - `constructor` applies a constructor of an inductive type to the goal.
  - `left` and `right` apply the left or right constructor of a disjunction.
  - `use` provides a witness for an existential quantifier.
  - `have` introduces an intermediate assertion.
  - `let` introduces a local definition.
  - `show` changes the goal to a specified expression.
  - `change` changes the goal to a specified expression, if they are definitionally equal.
  - `unfold` expands the definition of a constant in the goal.
  - `dsimp` simplifies the goal by unfolding definitions.
  - `induction` performs induction on a natural number or an inductive type.
  - `rewrite` replaces occurrences of a term with another term.
  - `simp` simplifies an expression using known simplification rules.
  - `split` splits a goal into multiple subgoals.
  - `finish` tries to automatically close the current goal.
-/

end cpt5
end tpil
