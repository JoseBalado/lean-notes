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
λ p, ⟨and.right p, and.left p⟩

-- Prove (((A ∨ B) → C) ∧ A) → C
example (A B C : Prop) : (((A ∨ B) → C) ∧ A) → C :=
  λ  qr, (and.left qr) (or.inl (and.right qr))

-- Prove (((A ∨ B) → C) ∧ A) → C, second example, closer to Thompson book
example (A B C : Prop) : (((A ∨ B) → C) ∧ A) → C :=
  λ  ⟨q, r⟩, q (or.inl r)
