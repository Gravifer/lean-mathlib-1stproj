-- # [Instance search control](https://leanprover.github.io/functional_programming_in_lean/type-classes/out-params.html)

set_option autoImplicit true

-- ## Out-params
#check HAdd
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

-- ## Default instance
-- variable (α : Type) in
@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

-- ## Exercises
#check HMul

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

@[default_instance]
instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p s := { x := p.x * s, y := p.y * s }

--
