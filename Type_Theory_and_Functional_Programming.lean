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
  λ  qr, (and.left qr) (or.inl (and.right qr))

-- Prove (((A ∨ B) → C) ∧ A) → C, second example, closer to Thompson book
example (A B C : Prop) : (((A ∨ B) → C) ∧ A) → C :=
  λ  ⟨q, r⟩, q (or.inl r)


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
