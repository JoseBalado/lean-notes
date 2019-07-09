-- Prove (∀ x : α, p x ∧ q x) → ∀ y : α, p y
variables (α : Type) (p q : α → Prop)

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
assume h : ∀ x : α, p x ∧ q x,
assume y : α,
show p y, from (h y).left

example : (∀ x : α, p x ∧ q x) → ∀ y : α, p y  :=
assume h : ∀ x : α, p x ∧ q x,
assume y : α,
show p y, from and.left (h y)

-- Remember that expressions which differ up to renaming of bound variables are considered to
-- be equivalent. So, for example, we could have used the same variable, x, in both the hypothesis
-- and conclusion, and instantiated it by a different variable, z, in the proof:
example : (∀ x : α, p x ∧ q x) → ∀ x : α, p x  :=
assume h : ∀ x : α, p x ∧ q x,
assume z : α,
show p z, from and.left (h z)
