-- Prove ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
⟨λ h, ⟨λ hp, h (or.inl hp), λ hq, h (or.inr hq)⟩, 
  λ hn h, or.elim h hn.1 hn.2⟩

-- Prove (A ∧ B) → (B ∧ A)
example (A B : Prop) : (A ∧ B) → (B ∧ A) :=
λ ⟨A, B⟩, ⟨B, A⟩ 

example (A B : Prop) : (A ∧ B) → (B ∧ A) :=
λ p : A ∧ B, ⟨and.right p, and.left p⟩ 