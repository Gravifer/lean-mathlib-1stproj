namespace tpil
section cpt4 -- # Quantifiers
set_option autoImplicit true
set_option relaxedAutoImplicit true

-- ## §4.1 Universal
/- Calculus of constructions identifies dependent arrow types with forall-expressions.
  `∀ x : α, p` means `{x : α} → p`, where `x` may appear in `p`;
    its just more readable when `p` is a `Prop`.
  An implication `p -> q` is thus just an arrow type with no `q` dependency in `x`.
* The universal quantifier is given the widest scope possible.
-/
example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

-- irrelevance of bound variable (_alpha-equivalence_)
example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun z : α =>
  show p z from And.left (h z)

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c d : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

-- implicit arguments
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

#check trans_r
#check trans_r hab
#check trans_r hab hbc

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd


-- impredicativity
universe u v
variable (β : Sort v)
#check (x : α) → β
#check Sort (imax 0 v)
#check Sort (imax u 0)
variable (p : α → Prop) in
  #check ∀ a : α , ∀ a₁ : α , p a → p a₁
variable (p : α → Type) in
  #check ∀ a : α , ∀ a₁ : α , p a → p a₁


-- ## §4.2 Equality
#check Eq.refl
#check Eq.symm
#check Eq.trans

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
example : a = d := (hab.trans hcb.symm).trans hcd
-- * `rfl` is just an abbreviation for `Eq.refl`

/- Equality is much more than an equivalence relation, however.
  It has the important property that every assertion respects the equivalence,
  in the sense that we can substitute equal expressions without changing the truth value. -/
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b := Eq.subst h1 h2
example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b := h1 ▸ h2
#check ( (_:a=b) ▸ (_:a=b) )
#check Eq.subst
#check Eq.symm
#check Eq.rec
#check Eq.ndrec
#check Eq.mp
#check Eq.mpr
-- * see https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/#:~:text=The%20motive,-The%20motive%20determines

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

example (x y : Nat) :
    (x + y) * (x + y) =
    x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
/- Notice that the second implicit parameter to `Eq.subst`, which provides
    the context in which the substitution is to occur, has type `α → Prop`.
  Inferring this predicate thus requires an instance of higher-order unification.
  In full generality, the problem of determining whether
    a higher-order unifier exists is undecidable, and Lean can at best
    provide imperfect and approximate solutions to the problem.
  As a result, `Eq.subst` doesn't always do what you want it to.
  The macro ` ▸ ` uses more effective heuristics to get this implicit parameter,
    and often succeeds in situations where applying Eq.subst fails. -/


-- ## §4.3 Calculation
variable (a b c d e : Nat) in
theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d)
  : a = e := calc
      a = b      := by rw [h1]           -- h1
      _ = c + 1  := by rw [h2]           -- h2
      _ = d + 1  := by rw [h3]           -- congrArg Nat.succ h3
      _ = 1 + d  := by rw [Nat.add_comm] -- Nat.add_comm d 1
      _ = e      := by rw [h4]           -- Eq.symm h4
    /- -- shortens to:
      a = d + 1  := by rw [h1, h2, h3]
      _ = 1 + d  := by rw [Nat.add_comm]
      _ = e      := by rw [h4]
    -//- -- or even:
      by rw [h1, h2, h3, Nat.add_comm, h4]
    -//- -- * `simp` rewrites the goal by applying the given identities repeatedly, in any order, anywhere they are applicable in a term.
      by simp [h1, h2, h3, Nat.add_comm, h4]
    -/

/- The `calc` **command** can be configured for any relation
    that supports some form of transitivity.
  It can even combine different relations.
  Add new instances of the `Trans` typeclass to enable `calc`. -/
variable (a b c d : Nat) in
example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b     := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d     := h3
def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

infix:50 " | " => divides -- can be entered as `\dvd` or `\mid`

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x | y   := h₁
    _ = z   := h₂
    _ | 2*z := divides_mul ..


variable (x y : Nat)

example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y  :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y                :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y)            :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y              :=
      by rw [←Nat.add_assoc]
-- When the first expression is taking this much space, using _ in the first relation naturally aligns all relations
example : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y       :=
      by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y     :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) :=
      by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y   :=
      by rw [←Nat.add_assoc]


section sect4 -- ## Existential
#check Exists
#check @Exists.intro
#check Exists.elim

variable (g : Nat → Nat → Nat)

theorem gex1 (hg : g 0 0 = 0) : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4

-- view `Exists.intro` as an information-hiding operation, since it hides the witness to the body of the assertion

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

/- An existential proposition is very similar to a sigma type, as described in dependent types section.
  The difference is that existential propositions are propositions,
    while sigma types are types. Otherwise, they are very similar.
  Given a predicate `p : α → Prop` and a family of types `β : α → Type`,
    for a term `a : α` with `h : p a` and `h' : β a`,
    the term `Exists.intro a h` has type `(∃ x : α, p x) : Prop`,
    while `Sigma.mk a h'` has type `(Σ x : α, β x)`.
  The similarity between `∃` and `Σ` is another instance of the Curry-Howard isomorphism. -/
variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with -- * just the ordinary pattern matching
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩ -- * anonymous constructor pattern

variable (a b : Nat)
def IsEven (a : Nat) := ∃ b, a = 2 * b
theorem even_plus_even (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))
theorem even_plus_even' (h1 : IsEven a) (h2 : IsEven b) :
    IsEven (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ =>
    ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

-- TODO[epic=exercise,id=∃ids] - common identities involving ∃
open Classical

variable (α : Type) (p q : α → Prop)
variable (a : α)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (fun ⟨b, (hb : p b → r)⟩ =>
     fun h2 : ∀ x, p x =>
     show r from hb (h2 b))
    (fun h1 : (∀ x, p x) → r =>
     show ∃ x, p x → r from
       byCases
         (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
         (fun hnap : ¬ ∀ x, p x =>
          byContradiction
            (fun hnex : ¬ ∃ x, p x → r =>
              have hap : ∀ x, p x :=
                fun x =>
                byContradiction
                  (fun hnp : ¬ p x =>
                    have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                    show False from hnex hex)
              show False from hnap hap)))
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end sect4


-- ## §4.5 the proof language
/- Use anonymous `have` to introduce an auxiliary goal without having to label it.
We can refer to the last expression introduced in this way using the keyword `this` -/
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)

-- When the goal can be inferred, ask Lean to fill in the proof with `by assumption`
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))
example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
  show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)

/- Ask Lean to fill in the proof by writing `‹p›`, where `p` is the proposition
    whose proof we want Lean to find in the context.
  Type single guillemets with `\f<` and `\f>` ('f' for "French").

* This approach is more robust than using by assumption, because
    the type of the assumption that needs to be inferred is given explicitly.
  It also makes proofs more readable. -/
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x ≤ f (x + 1))

example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  fun _ : f 0 ≥ f 1 =>
  fun _ : f 1 ≥ f 2 =>
  have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›

/- * Guillemets can be used in this way to refer to
    anything in the context, **not** just things that were introduced anonymously.
  Its use is also not limited to propositions, though using it for data is somewhat odd: -/
example (n : Nat) : Nat := ‹Nat›


-- ## §4.6 Exercises
variable (α : Type) (p q : α → Prop)

/- 1. Prove these equivalences -/
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry  -- * try and understand why the reverse implication is not derivable

/- 2. It is often possible to bring a component of a formula outside a universal quantifier,
        when it does not depend on the quantified variable. Try proving these
        (one direction of the second of these requires classical logic) -/
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry

/- 3. Consider the “barber paradox,” that is, the claim that
      > in a certain town there is a (male) barber that shaves
          all and only the men who do not shave themselves.
      Prove that this is a contradiction -/
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry

/- 4. Note that without parameters, an expr of type `Prop` is just an assertion.
    Fill in the definitions of prime and Fermat_prime below,
        and construct each of the given assertions.
      For example, you can say that there are infinitely many primes
        by asserting that for every natural number `n`,
        there is a prime number greater than `n`.
  - __Goldbach's weak conjecture__ states that
      > every odd number greater than 5 is the sum of three primes.
  - Look up the definition of a Fermat prime or any of the other statements, if necessary. -/
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry

/- 5. Prove as many of the identities listed in the Existential Quantifier section as you can. -/--LINK #∃ids


end cpt4
end tpil
