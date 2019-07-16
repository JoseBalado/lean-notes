-- Prove (∀ x : α, p x ∧ q x) → ∀ y : α, p y
namespace one
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
end one

-- Express the fact that a relation, r, is transitive:
namespace two
variable (α : Type)
variables (r : α → α → Prop)
variable  trans_r : ∀ x y z, r x y → r y z → r x z

variables a b c : α
variables (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc
end two

namespace three
universe u
variables (α : Type u) (r : α → α → Prop)
variable  trans_r : ∀ {x y z}, r x y → r y z → r x z

variables (a b c : α)
variables (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r hab
#check trans_r hab hbc
end three

namespace four
variables (α : Type) (r : α → α → Prop)

variable refl_r : ∀ x, r x x
variable symm_r : ∀ {x y}, r x y → r y x
variable trans_r : ∀ {x y z}, r x y → r y z → r x z

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) :
  r a d :=
trans_r (trans_r hab (symm_r hcb)) hcd
end four

-- 4.2. Equality

-- 4.4. The Existential Quantifier
example : ∃ x : ℕ, x > 0 :=
have h : 1 > 0, from nat.zero_lt_succ 0,
exists.intro 1 h

example : ∃ x : ℕ, x > 0 :=
have h : 4 > 0, from nat.zero_lt_succ 3,
exists.intro 4 h

example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
exists.intro 0 h

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
  ∃ w, x < w ∧ w < z :=
exists.intro y (and.intro hxy hyz)

#check @exists.intro
