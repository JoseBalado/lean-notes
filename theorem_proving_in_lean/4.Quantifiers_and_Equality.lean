-- 4.1. The Universal Quantifier
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

-- We can use the anonymous constructor notation ⟨t, h⟩ for exists.intro t h, when the
-- type is clear from the context.
example : ∃ x : ℕ, x > 0 :=
⟨1, nat.zero_lt_succ 0⟩

example (x : ℕ) (h : x > 0) : ∃ y, y < x :=
⟨0, h⟩

example (x y z : ℕ) (hxy : x < y) (hyz : y < z) :
  ∃ w, x < w ∧ w < z :=
⟨y, hxy, hyz⟩


-- Note that exists.intro has implicit arguments: Lean has to infer the predicate p : α → Prop
-- in the conclusion ∃ x, p x.
-- For example, if we have have hg : g 0 0 = 0 and write exists.intro 0 hg, there are many
-- possible values for the predicate p, corresponding to the theorems
-- ∃ x, g x x = x, ∃ x, g x x = 0, ∃ x, g x 0 = x, etc.
-- Lean uses the context to infer which one is appropriate.
variable g : ℕ → ℕ → ℕ
variable hg : g 0 0 = 0

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

theorem gex5 : ∃ x, g 0 x = x := ⟨0, hg⟩
theorem gex6 : ∃ x, g x 0 = 0 := ⟨0, hg⟩
theorem gex7 : ∃ x, g 0 x = 0 := ⟨0, hg⟩

set_option pp.implicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4


-- The existential elimination rule, exists.elim, performs the opposite operation.
-- It allows us to prove a proposition q from ∃ x : α, p x, by showing that q follows from p w for an arbitrary value w.
-- Roughly speaking, since we know there is an x satisfying p x, we can give it a name, say, w.
-- If q does not mention w, then showing that q follows from p w is tantamount to showing the q follows from the existence of any such x. Here is an example: 
namespace five
variables (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
exists.elim h
  (assume w,
    assume hw : p w ∧ q w,
    show ∃ x, q x ∧ p x, from ⟨w, ⟨hw.right, hw.left⟩⟩)
end five

-- Lean provides a more convenient way to eliminate from an existential quantifier with the match statement:
namespace six
variables (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨w, hw⟩ :=
  ⟨w, hw.right, hw.left⟩
end

-- We can annotate the types used in the match for greater clarity:
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨(w : α), (hw : p w ∧ q w)⟩ :=
  ⟨w, hw.right, hw.left⟩
end

-- We can even use the match statement to decompose the conjunction at the same time:
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
match h with ⟨w, hpw, hqw⟩ :=
  ⟨w, hqw, hpw⟩
end

-- Lean also provides a pattern-matching let expression:
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
let ⟨w, hpw, hqw⟩ := h in ⟨w, hqw, hpw⟩

-- This is essentially just alternative notation for the match construct above. Lean will even allow
-- us to use an implicit match in the assume statement:
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
assume ⟨w, hpw, hqw⟩, ⟨w, hqw, hpw⟩

end six

-- Prove ¬ ∀ x, ¬ p x → ∃ x, p x
namespace ApEp
variables (α : Type) (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
classical.by_contradiction
  (assume h1 : ¬ ∃ x, p x,
    have h2 : ∀ x, ¬ p x, from
      assume x,
      assume h3 : p x,
      have h4 : ∃ x, p x, from  ⟨x, h3⟩,
      show false, from h1 h4,
    show false, from h h2)

-- Same example using Exists.intro
example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
classical.by_contradiction
  (assume h1 : ¬ ∃ x, p x,
    have h2 : ∀ x, ¬ p x, from
      assume x,
      assume h3 : p x,
      have h4 : ∃ x, p x, from Exists.intro x h3,
      show false, from h1 h4,
    show false, from h h2)
end ApEp
