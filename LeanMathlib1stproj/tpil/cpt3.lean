namespace tpil
section cpt3 -- # Propositions and Proofs

def Implies (p q : Prop) : Prop := p → q
#check And
#check Or
#check Not
#check Implies

variable (p q r : Prop)
#check And p q
#check Or (And p q) r
#check Implies (And p q) (And q p)

structure Proof (p : Prop) : Type where
  proof : p
#check Proof

axiom and_commut (p q : Prop) : Proof (Implies (And p q) (And q p))
#check and_commut p q

axiom modus_ponens (p q : Prop) :
  Proof (Implies p q) → Proof p →
  Proof q
axiom implies_intro (p q : Prop) :
  (Proof p → Proof q) → Proof (Implies p q)

/- we can avoid writing the term `Proof` repeatedly by
    conflating `Proof p` with `p` itself.  In other words,
    whenever we have `p : Prop`, we can interpret `p` as a type, namely,
    the type of its proofs.
  We can then read `t : p` as the assertion that `t` is a proof of `p`.
  Once we make this identification, the rules for implication show that
    we can pass back and forth between `Implies p q` and `p → q`.
  Implication between propositions `p` and `q` thus corresponds to having
    a function that takes any element of `p` to an element of `q`. Therefore,
    introducing the connective `Implies` is entirely redundant: we can use
    the usual function space constructor `p → q` as our notion of implication.

  This is the approach followed in the Calculus of Constructions,
    and hence in Lean as well.
  The fact that the rules for implication in a proof system for natural deduction
  correspond exactly to the rules governing abstraction and application for functions
  is an instance of the Curry-Howard isomorphism,
  sometimes known as the propositions-as-types paradigm. -/

#check p -> q
#check Nat -> Int

universe u v
#check Sort u -> Sort v

variable (A B : Type u) in
#check A -> B

/- There are at least two ways of thinking about propositions as types.

  - To some who take a constructive view of logic and mathematics,
      this is a faithful rendering of what it means to be a proposition:
      a proposition `p` represents a sort of data type, namely,
      a specification of the type of data that constitutes a proof.
    A proof of `p` is then simply an object `t : p` of the right type.

  - Those not inclined to this ideology can view it, rather, as a simple coding trick.
    To each proposition `p` we associate a type that is empty if `p` is false
      and has a single element, say `*`, if `p` is true.
    In the latter case, we say that (the type associated with) `p` is inhabited.
    It just so happens that the rules for function application and abstraction
      can conveniently help us keep track of which elements of `Prop` are inhabited.
    So constructing an element `t : p` tells us that `p` is indeed true.
    You can think of the inhabitant of `p` as being the “fact that `p` is true.”
    A proof of `p → q` uses “the fact that `p` is true” to obtain “the fact that `q` is true.”

  Indeed, if `p : Prop` is any proposition,
    Lean's kernel treats any two elements `t1 t2 : p` as being definitionally equal,
    much the same way as it treats `(fun x => t) s` and `t[s/x]` as definitionally equal.
  This is known as proof irrelevance, and is consistent with the interpretation in the last paragraph.
  It means that even though we can treat proofs `t : p` as ordinary objects in the language of dependent type theory,
    they carry no information beyond the fact that `p` is true.

  The two ways we have suggested thinking about the propositions-as-types paradigm differ in a fundamental way.
  From the constructive point of view,
    proofs are abstract mathematical objects that are denoted
    by suitable expressions in dependent type theory.
  In contrast, if we think in terms of the coding trick described above,
    then the expressions themselves do not denote anything interesting.
    Rather, it is the fact that we can write them down and check that they are well-typed
    that ensures that the proposition in question is true.
    In other words, the expressions themselves are the proofs.
-/

section sect2 -- ## the `theorem` keyword

set_option linter.unusedVariables false
---
variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

/- Note that the theorem command is really a version of the def command:
    under the propositions and types correspondence,
    proving the theorem `p → q → p` is really the same as
    defining an element of the associated type.
  To the kernel type checker, there is no difference between the two.

  There *are* a few pragmatic differences between definitions and theorems, however.
  In normal circumstances, it is never necessary to unfold the “definition” of a theorem;
    by proof irrelevance, any two proofs of that theorem are definitionally equal.
  Once the proof of a theorem is complete, typically we only need to know that
    the proof exists; it doesn't matter what the proof is.
  In light of that fact, Lean tags proofs as irreducible, which serves
    as a hint to the parser (more precisely, the elaborator) that there is
    generally no need to unfold them when processing a file.
  In fact, Lean is generally able to process and check proofs in parallel,
    since assessing the correctness of one proof does not require
    knowing the details of another.
  Additionally, section variables that are referred to
    in the body of a definition are automatically added as parameters,
    but only the variables referred to in a theorem's type are added.
  This is because the way in which a statement is proved
    should not influence the statement that is being proved. -/

-- We can specify the type of the final term `hp` explicitly, with a `show` statement
theorem t1' : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp /- `show` just annotates the type, and internally,
    all the presentations of `t1` that we have seen produce the same term. -/

-- use the theorem `t1` just as a function application
theorem t1'' (hp : p) (hq : q) : p := hp
axiom hp : p
theorem t2 : q → p := t1'' hp

/- The `axiom` declaration
    postulates the existence of an element of the given type and
    ! may compromise logical consistency.
  For example, we can use it to postulate that
    ! the empty type `False` has an element: -/
  namespace ex_falso_quodlibet
    axiom unsound : False -- * Everything follows from false
    theorem ex : 1 = 0 :=
      False.elim unsound
  end ex_falso_quodlibet
end sect2


-- ## §3.3 propositional logic
#print And
#print and
/- _and-introduction_ and _and-elimination_ are similar to
    the pairing and projection operations for the Cartesian product.
  The difference is that given `hp : p` and `hq : q`,
      `And.intro hp hq` has type `p ∧ q : Prop`,
    while given `a : α` and `b : β`,
      `Prod.mk a b` has type `α × β : Type`.
  `Prod` cannot be used with `Prop`s, and `And` cannot be used with `Type`s.
  `∧` and `×` is another instance of the Curry-Howard isomorphism, but
  in contrast to implication and the function space constructor,
  `∧` and `×` are treated separately in Lean. -/
#check_failure p × q
#check_failure Nat ∧ q
#check_failure Prop ∧ q
#check Prop × Int
#check_failure Nat ∧ Int
#check Nat × Int
#check Nat × (Nat → Prop)
#check Prop → Prop

variable (p q : Prop)
variable (hp : p) (hq : q)
#check_failure (ip : hp)

#check (⟨hp, hq⟩ : p ∧ q)

#print Or
#print or

-- ## Auxiliary subgoals

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
variable (p q : Prop)
-- is equialent to
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

section sect5 -- ## Classical logic
open Classical
  #print em
  variable (p : Prop)
  #check em p
  /- Double-negation elimination allows one to carry out a proof by contradiction,
      something which is not generally possible in constructive logic. -/
  theorem dne {p : Prop} (h : ¬¬p) : p :=
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => absurd hnp h)

  example (h : ¬¬p) : p :=
    byCases
      (fun h1 : p => h1)
      (fun h1 : ¬p => absurd h1 h)
  example (h : ¬¬p) : p :=
    byContradiction
      (fun h1 : ¬p => show False from h h1)

  /- Classical reasoning is needed in the following example because,
    from a constructive standpoint, knowing that `p` and `q` are not both true
    does not necessarily tell you which one is false. -/
  example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
    Or.elim (em p)
      (fun hp : p => Or.inr
        (show ¬q from
          fun hq : q => h ⟨hp, hq⟩))
      (fun hp : ¬p => Or.inl hp)
end sect5  -- todo: axiom of choice

section sect6 -- ## Examples
open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)
end sect6

section sect7 -- ## Exercises
variable (p q r : Prop) -- ! all can be done `by grind`, but don't

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := and_comm -- `And.comm` from `Init.Core`
  example : p ∨ q ↔ q ∨ p := or_comm -- `Or.comm`

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := and_assoc -- from `Init.SimpleLemmas`
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := or_assoc

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := and_or_left -- from `Init.PropLemmas`
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := or_and_left

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := by exact Iff.symm and_imp -- when in doubt, `by exact?`
    -- ⟨fun h ⟨hp, hq⟩ => h hp hq, fun h hp hq => h ⟨hp, hq⟩⟩ -- by
    -- apply Iff.intro
    -- · intro h ⟨hp, hq⟩
    --   exact h hp hq
    -- · intro h hp hq
    --   exact h ⟨hp, hq⟩
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := or_imp
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := not_or
  example : ¬p ∨ ¬q → ¬(p ∧ q) := not_and_of_not_or_not
  example : ¬(p ∧ ¬p) := and_not_self
  example : p ∧ ¬q → ¬(p → q) := not_imp_of_and_not
  example : ¬p → (p → q) := by  -- `False.elim` from `Init.Prelude`
    intro n p; exact absurd p n
  example : (¬p ∨ q) → (p → q) := by
    intro h hp; cases h with
    | inl np => exact absurd hp np
    | inr hq => exact hq
  example : p ∨ False ↔ p := or_iff_left id
  example : p ∧ False ↔ False := by
    apply Iff.intro
    · intro h; exact h.right
    · intro f; exact False.elim f
  example : (p → q) → (¬q → ¬p) := -- fun pq nq ↦ nq ∘ pq  -- `Function.comp` reversed
    mt  -- * modus tollens / contrapositive from `Lean.Core`

  open Classical

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
    intro h; by_cases hp : p -- from `Classical.ByCases`
    · by_cases hq : q
      · exact Or.inl (fun _ => hq)
      · exact Or.inr (fun _ => (h hp).resolve_left hq)
    · exact Or.inl (fun hp' => absurd hp' hp)
    -- intro h
    -- cases em p with -- excluded middle from `Classical`
    -- | inl hp =>
    --   cases em q with
    --   | inl hq => exact Or.inl (fun _ => hq)
    --   | inr hnq =>
    --     cases em r with
    --     | inl hr => exact Or.inr (fun _ => hr)
    --     | inr hnr => exfalso; exact hnr $ (h hp).resolve_left hnq -- `exfalso` from `Init.Tactics`
    -- | inr hnp => exact Or.inl (fun hp => absurd hp hnp)
  example : ¬(p ∧ q) → ¬p ∨ ¬q := by
    intro h; by_cases hp : p
    · right; intro hq; exact h ⟨hp, hq⟩
    · left;  exact hp
  example : ¬(p → q) → p ∧ ¬q := by
    intro h; constructor
    · by_cases hp : p; exact hp
      · exfalso; apply h; intro hp'; exact absurd hp' hp
    · intro hq; apply h; intro _; exact hq
    -- intro h; by_cases hp : p
    -- · by_cases hq : q
    --   · exfalso; exact h (fun _ => hq)
    --   · exact ⟨hp, hq⟩
    -- · by_cases hq : q
    --   · exfalso; exact h (fun _ => hq)
    --   · exfalso; exact h (fun p' => absurd hp (not_not.mpr p'))
  example : (p → q) → (¬p ∨ q) := by
    intro h; by_cases hp : p
    · right; exact h hp
    · left;  exact hp
  example : (¬q → ¬p) → (p → q) := by
    intro h hp; by_cases hq : q; exact hq
    · exfalso; exact h hq hp
  example : p ∨ ¬p := em p
  example : (((p → q) → p) → p) := by
    intro h; by_cases hp : p; exact hp
    · apply h; intro hp'; exfalso; exact hp hp'
    -- intro h; by_cases hp : p; exact hp
    -- · by_cases hq : q;
    --   . exact h (fun _ => hq)
    --   · exact h (fun hp' => absurd hp' hp)

end sect7

end cpt3
end tpil
