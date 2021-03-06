-- Prove ¬(p ∨ q) ↔ ¬p ∧ ¬q
example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
⟨λ h, ⟨λ hp, h (or.inl hp), λ hq, h (or.inr hq)⟩, 
λ hn h, or.elim h hn.1 hn.2⟩

-- Page 83
-- Prove (A ∧ B) → (B ∧ A)
example (A B : Prop) : (A ∧ B) → (B ∧ A) :=
λ ⟨A, B⟩, ⟨B, A⟩ 


example (A B : Prop) : (A ∧ B) → (B ∧ A) :=
λ p : A ∧ B, ⟨and.right p, and.left p⟩

example (A B : Prop) : (A ∧ B) → (B ∧ A) :=
λ p, and.intro (and.right p) (and.left p)

-- Prove (((A ∨ B) → C) ∧ A) → C
example (A B C : Prop) : (((A ∨ B) → C) ∧ A) → C :=
λ qr, (and.left qr) (or.inl (and.right qr))

-- Prove (((A ∨ B) → C) ∧ A) → C, second example, closer to Thompson book
example (A B C : Prop) : (((A ∨ B) → C) ∧ A) → C :=
λ ⟨q, r⟩, q (or.inl r)


-- Page 90
-- 4.1. Show that conjunction is associative by deriving a proof of the formula
-- (A ∧ B) ∧ C → A ∧ (B ∧ C)
example (A B C : Prop) : (A ∧ B) ∧ C → A ∧ (B ∧ C) :=
λ p, ⟨and.left (and.left p), ⟨and.right (and.left p), and.right p⟩⟩

example (A B C : Prop) : (A ∧ B) ∧ C → A ∧ (B ∧ C) :=
λ p, ⟨and.left (and.left p), and.right (and.left p), and.right p⟩

example (A B C : Prop) : (A ∧ B) ∧ C → A ∧ (B ∧ C) :=
λ p, and.intro (and.left (and.left p)) (and.intro (and.right (and.left p)) (and.right p))

-- 4.2. A) Show that the formula (¬A ∨ B) → (A → B) is valid by exhibiting a proof object for it.
example (A B : Prop) : (¬A ∨ B) → (A → B) :=
λ p, or.elim p
(λ na, λ a, absurd a na)
(λ b, λ a, b)

example (A B : Prop) : (¬A ∨ B) → (A → B) :=
assume hnab : ¬A ∨ B,
or.elim hnab
(assume hna : ¬A,
assume ha : A,
show B, from absurd ha hna)
(assume hb : B,
assume ha : A,
show B, from hb)

example (A B : Prop) : (¬A ∨ B) → (A → B) :=
assume hnab : ¬A ∨ B,
or.elim hnab
(assume hna : ¬A,
assume ha : A,
show B, from false.elim (hna ha))
(assume hb : B,
assume ha : A,
show B, from hb)


-- 4.2 B) Do you expect the converse, (A → B) → (¬A ∨ B), to be provable?


-- 4.3. A) Show that from the assumption x : (A ∨ ¬A) that you can derive a
-- proof object for the formula (¬¬A → A). 
example (A : Prop) : (A ∨ ¬A) → (¬¬A → A) :=
λ hana, or.elim hana
(λ ha, λ hna, ha)
(λ hna, λ hnna, absurd hna hnna)

example (A : Prop) : (A ∨ ¬A) → (¬¬A → A) :=
assume hana : (A ∨ ¬A),
or.elim hana
(assume ha : A,
assume hna : ¬¬A, show A, from ha)
(assume hna : ¬A,
assume hnna : ¬¬A, show A, from false.elim (hnna hna))

-- 4.3 B) Show that you can find a proof
-- object for the converse, (A → ¬¬A) without this assumption.
example (A : Prop): (A → ¬¬A) :=
assume ha : A,
assume hna : ¬A, show false, from hna ha

example (A : Prop): (A → ¬¬A) :=
assume ha : A,
assume hna : ¬A, absurd ha hna

-- 4.4. Show that from the assumptions x : ((A ∧ B) → C) and y : A you
-- can derive a proof of B → C.
example (A B C : Prop) : ((A ∧ B) → C) ∧ A → (B → C) :=
λ x, λ y, x.left (and.intro x.right y)

example (A B C : Prop) : ((A ∧ B) → C) ∧ A → (B → C) :=
assume habc,
assume hb, show  C, from habc.left (and.intro habc.right hb)

-- 4.5. Given a function of type A → (B → C) how would you define a
-- function of type (A ∧ B) → C from it? How would you do the reverse?
-- A)
example (A B C : Prop) : (A → (B → C)) → ((A ∧ B) → C) :=
assume habc,
assume hab, show C, from  (habc (and.left hab)) (and.right hab)

example (A B C : Prop) : (A → (B → C)) → ((A ∧ B) → C) :=
λ abc, λ ab, show C, from (abc ab.left) ab.right

-- B) How would you do the reverse?
example (A B C : Prop) : ((A ∧ B) → C) → (A → (B → C)) :=
assume habc,
assume ha,
assume hb, show C, from habc (and.intro ha hb)

example (A B C : Prop) : ((A ∧ B) → C) → (A → (B → C)) :=
λ habc, λ ha, λ hb, habc (and.intro ha hb)

-- 4.6. Show that from objects x : A and y : (B ∨ C) you can derive an object
-- of type (A ∧ B) ∨ (A ∧ C).
example (A B C : Prop) : (A ∧ (B ∨ C)) → ((A ∧ B) ∨ (A ∧ C)) :=
assume habc,
show (A ∧ B) ∨ (A ∧ C), from
(or.elim (and.right habc)
(assume hb, or.inl (and.intro (and.left habc) hb))
(assume hc, or.inr (and.intro (and.left habc) hc)))

example (A B C : Prop) : (A ∧ (B ∨ C)) → ((A ∧ B) ∨ (A ∧ C)) :=
λ habc,
(or.elim (and.right habc)
  (λ  hb, or.inl (and.intro (and.left habc) hb))
  (λ  hc, or.inr (and.intro (and.left habc) hc)))

-- 4.7. Show how to define a function of type
-- (A ∧ B) → (C ∧ D)
-- from functions f : A → C and g : B → D.
example (A B C D : Prop): (A ∧ B) → (C ∧ D) :=
λ x: (A ∧ B), and.intro (sorry) (sorry)

example (A B C D : Prop): (A ∧ B) → (A → C) → (B → D) → (C ∧ D) :=
λ x: (A ∧ B), λ f : (A → C), λ g: (B → D), and.intro (f x.left)(g x.right)

-- 4.8. Show that the following formulas are valid, by giving a proof object
-- for each of them.
-- A) A → ¬¬A
example (A : Prop): A → ¬¬A :=
assume ha,
show ¬¬A, from (assume hna, show false, from false.elim (hna ha))

example (A : Prop): A → ¬¬A :=
λ ha, λ hna, false.elim (hna ha)

-- B) (B ∨ C) → ¬(¬B ∧ ¬C)
example (B C : Prop): (B ∨ C) → ¬(¬B ∧ ¬C) :=
assume hbc : B ∨ C,
assume hnbnc : ¬B ∧ ¬C,
or.elim hbc
(assume hb : B, show false, from false.elim ((and.left hnbnc) hb))
(assume hc : C, show false, from false.elim ((and.right hnbnc) hc))

example (B C : Prop): (B ∨ C) → ¬(¬B ∧ ¬C) :=
λ hbc : B ∨ C,
λ hnbnc : ¬B ∧ ¬C,
or.elim hbc
(λ hb : B, false.elim ((and.left hnbnc) hb))
(λ hc : C, false.elim ((and.right hnbnc) hc))

-- C) (A → B) → ((A → C) → (A → (B ∧ C)))
example (A B C : Prop): (A → B) → ((A → C) → (A → (B ∧ C))) :=
assume hab : A → B,
assume hac : A → C,
assume ha : A, show B ∧ C, from and.intro (hab ha) (hac ha)

example (A B C : Prop): (A → B) → ((A → C) → (A → (B ∧ C))) :=
λ hab : A → B,
λ hac : A → C,
λ ha : A, and.intro (hab ha) (hac ha)

-- 4.9. Show that the following formulas are equivalent
-- (A ∧ B) → C    A → (B → C)
example (A B C : Prop): (A ∧ B) → C ↔ A → (B → C) :=
iff.intro
(assume habc, show A → B → C, from
  assume ha,
  assume hb,
show C, from habc (and.intro ha hb))
(assume habc, show A ∧ B → C, from
  assume hab,
  have ha : A, from and.left hab,
  have hb : B, from and.right hab,
  show C, from (habc ha) hb)

example (A B C : Prop): (A ∧ B) → C ↔ A → (B → C) :=
⟨ λ habc, λ ha, λ hb, habc (and.intro ha hb)
  ,
  λ habc, λ hab, habc (and.left hab) (and.right hab)
⟩

-- 4.10. Show that the de Morgan formula
-- (¬A ∨ ¬B) → ¬(A ∧ B)
-- is valid by giving an object of type
-- ((A → C) ∨ (B → C)) → ((A ∧ B) → C)
example (A B C : Prop): ((A → C) ∨ (B → C)) → ((A ∧ B) → C) :=
assume hacbc, show (A ∧ B) → C, from
  assume hab, show C, from
  or.elim hacbc
  (assume hac, show C, from hac (and.left hab))
  (assume hbc, show C, from hbc (and.right hab))

example (A B C : Prop): ((A → C) ∨ (B → C)) → ((A ∧ B) → C) :=
λ hacbc, λ hab, or.elim hacbc
  (λ hac, hac (and.left hab))
  (λ hbc, hbc (and.right hab))


-- 4.12. Give a derivation of a proof object of the formula
-- (∃x : X).¬P → ¬(∀x : X).P
variables (α : Type) (p q : α → Prop)

example (h : ∃ x, ¬p x) : ¬∀ x, p x :=
  (assume h1 : ∀ x, p x,
    have h2 : ∀ x, ¬ p x, from
      assume x,
      assume h3 : p x,
      have h4 : ∃ x, p x, from  ⟨x, h3⟩,
      show false, from h1 h4,
    show false, from h h2)

example (h : ∃ x, ¬p x) : ¬∀ x, p x :=
  (assume h1 : ∀ x, p x,
      assume y : α,
      have  h2 : p y, from  h1 y,
      show false, from sorry)

example (h : ∃ x, ¬p x) : ¬p α :=
      assume y : α,
      show false, from (sorry)
