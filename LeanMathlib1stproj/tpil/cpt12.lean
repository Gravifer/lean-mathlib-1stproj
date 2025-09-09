namespace tpil
section cpt12 -- # Axioms and Computation
/- This is primarily a historical and philosophical account-/

#print propext
#print propext_iff

-- an example of how function extensionality blocks computation inside the Lean kernel
def f (x : Nat) := x
def g (x : Nat) := 0 + x
theorem f_eq_g : f = g :=  funext fun x => (Nat.zero_add x).symm
def val : Nat :=  Eq.recOn (motive := fun _ _ => Nat) f_eq_g 0
#reduce val  -- does not reduce to 0
#eval   val  -- evaluates to 0

-- a similarly contrived example that shows how propext can get in the way
theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))
def val1 : Nat :=  Eq.recOn (motive := fun _ _ => Nat) tteq 0
#reduce val1  -- does not reduce to 0
#eval   val1  -- evaluates to 0


-- ## §12.4 Quotients
#print Lean.Quote -- jk

#print Quot
#print Quot.mk
#print Quot.lift
#print Quot.ind
#print Quot.sound -- the actually strong thing

#print Setoid
/- convenient because there's notation `a ≈ b` (entered with `\approx`) for `Setoid.r a b`,
    where the instance of `Setoid` is implicit in the notation `Setoid.r`. -/
#print Quotient
#print Quotient.mk
#print Quotient.lift
#print Quotient.ind
#print Quotient.sound
#print Quotient.exact

end cpt12
