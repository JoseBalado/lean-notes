-- Prove (∀ x : α, p x ∧ q x) → ∀ y : α, p y
variables (α : Type) (p q : α → Prop) -- This defines α and 'p' and 'q' for the whole file

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

-- Express the fact that a relation, r, is transitive:
variables (r : α → α → Prop)
variable  trans_r : ∀ x y z, r x y → r y z → r x z

variables a b c : α
variables (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc
