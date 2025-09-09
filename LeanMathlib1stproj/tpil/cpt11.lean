namespace tpil
section cpt11 -- # The Conversion Tactic Mode
set_option autoImplicit true
set_option relaxedAutoImplicit true

-- ## §11.1 Basic navigation and rewriting
#guard_msgs (drop all) in
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  rw [Nat.mul_comm] -- ! no progress

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    rfl
    rw [Nat.mul_comm]

example :
    ({α : Type} → (x : α) → α)
    =
    ((α : Type) → (x : α) → α)
  := rfl

#print funext -- also a tactic

-- ## §11.2 Pattern matching
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm]
-- is sugar for
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c =>
    rw [Nat.mul_comm]
-- and you can use wildcards
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in _ * c => rw [Nat.mul_comm]

-- ## §11.3 Structuring conversion tactics
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add] -- you can use `.`  and `{ }`
    . rw [Nat.mul_comm]

-- ## §11.4 Other tactics inside conversion mode
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    arg 2  -- and `args` is just `congr`
    rw [Nat.mul_comm]

def f (x : Nat) :=  if x > 0 then x + 1 else x + 2

example (g : Nat → Nat)
    (h₁ : g x = x + 1) (h₂ : x > 0) :
    g x = f x := by
  conv =>
    rhs
    simp [f, h₂]
  exact h₁

/-
  - `enter [1, x, 2, y]` iterate `arg` and `intro` with the given arguments.
  - `done` fail if there are unsolved goals.
  - `trace_state` display the current tactic state.
  - `whnf` put term in weak head normal form.
  - `tactic => <tactic sequence>` go back to regular tactic mode.
      This is useful for discharging goals not supported by conv mode,
        and applying custom congruence and extensionality lemmas.
  - `apply <term>` is syntax sugar for `tactic => apply <term>`.
-/
example (g : Nat → Nat → Nat)
        (h₁ : ∀ x, x ≠ 0 → g x x = 1)
        (h₂ : x ≠ 0)
        : g x x + x = 1 + x := by
  conv =>
    lhs
    arg 1
    rw [h₁]
    . skip
    . tactic =>
       exact h₂

end cpt11
