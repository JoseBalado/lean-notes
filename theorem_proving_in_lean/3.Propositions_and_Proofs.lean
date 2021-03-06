-- p q r s are used in all the examples so they are defined only here
variables p q r s : Prop

-- Conjunction
-- Prove p, q -> p ∧ q
example (hp : p) (hq : q): p ∧ q := and.intro hp hq
-- Prove p ∧ q -> q
example (h : p ∧ q) : p := and.elim_left h
-- Prove p ∧ q -> p
example (h : p ∧ q) : q := and.elim_right h

-- Some examples of type assignment
variables (h : p) (i : q)
#check and.elim_left ⟨h, i⟩  
#reduce and.elim_left ⟨h, i⟩  
#check and.elim_right ⟨h, i⟩  
#reduce and.elim_right ⟨h, i⟩  

#check (⟨h, i⟩ : p ∧ q)  
#reduce (⟨h, i⟩ : p ∧ q)  


-- Prove q ∧ p → p ∧ q
example (h : p ∧ q) : q ∧ p :=
and.intro (and.elim_right h) (and.elim_left h)
-- Lean allows us to use anonymous constructor notation ⟨arg1, arg2, ...⟩
-- In situations like these, when the relevant type is an inductive type and can be inferred from the context.
-- In particular, we can often write ⟨hp, hq⟩ instead of and.intro hp hq:
example (h : p ∧ q) : q ∧ p :=
⟨and.elim_right h, and.elim_left h⟩

-- More examples of using the constructor notation
example (h : p ∧ q) : q ∧ p ∧ q:=
⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q:=
⟨h.right, h.left, h.right⟩

-- Disjunction
-- ∨ introduction left
example (hp : p): p ∨ q := or.intro_left q hp
-- ∨ introduction right
example (hq : q): p ∨ q := or.intro_right p hq

-- Prove p ∨ p → p
example (h: p ∨ p): p :=
or.elim h
(assume hpr : p, show p, from hpr)
(assume hpl : p, show p, from hpl)

-- Prove p ∨ p → p, simplified notation
example (h: p ∨ p): p :=
or.elim h
(assume hpr : p, hpr)
(assume hpl : p, hpl)

-- Prove  p ∨ q, p → r, q -> r, -> r
example (h : p ∨ q) (i : p → r) (j : q -> r) : r :=
or.elim h 
(assume hp : p, show r, from i hp)
(assume hq : q, show r, from j hq)

-- Prove p ∨ q → q ∨ p
example (h : p ∨ q) : q ∨ p :=
or.elim h
(assume hp : p, show q ∨ p, from or.intro_right q hp)
(assume hq : q, show q ∨ p, from or.intro_left p hq)

-- Modus tollens, deriving a contradiction from p to obtain false.
-- Everything follows from false, in this case ¬p
-- order of propositions matters when using absurd
example (hpq : p → q) (hnq : ¬q) : ¬p :=
assume hp : p, show false, from  hnq (hpq hp)

-- Equivalent to the previous one
example (hpq : p → q) (hnq : ¬q) : ¬p :=
assume hp : p, show false, from  false.elim (hnq (hpq hp))
-- Equivalent to the previous one
example (hpq : p → q) (hnq : ¬q) : ¬p :=
assume hp : p, show false, from  (hnq (hpq hp))

-- More examples of false and absurd use
example (hp : p) (hnp : ¬p) : q := false.elim (hnp hp)
-- order of propositions matters when using absurd
example (hp : p) (hnp : ¬p) : q := absurd hp hnp

-- Prove ¬p → q → (q → p) → r, premise ¬p must be added
example (hnp : ¬p) (hq : q) (hqp : q → p): r := 
false.elim (hnp (hqp hq))
-- equivalent proove as the above 
example (hnp : ¬p) (hq : q) (hqp : q → p): r := 
absurd (hqp hq) hnp

-- Other variant from the above
-- Prove ¬p → q → (q → p) → r, premise ¬p must be added
example (hnp : ¬ p) (hnpq : ¬p → q) (hqp : q → p): r := 
absurd (hqp (hnpq hnp)) hnp

example (hnp : ¬ p) (hnpq : ¬p → q) (hqp : q → p): r := 
false.elim (hnp (hqp (hnpq hnp))) 

-- Prove p ∧ q ↔ q ∧ p
example : (p ∧ q) ↔ (q ∧ p) :=
iff.intro
  (assume h : p ∧ q,
    show q ∧ p,
    from and.intro (and.elim_right h) (and.elim_left h))
  (assume h : q ∧ p,
    show p ∧ q,
    from and.intro (and.elim_right h) (and.elim_left h))

 -- Derive q ∧ p from p ∧ q
 example (h : p ∧ q) : (q ∧ p) :=
 and.intro (and.elim_right h) (and.elim_left h)
 
 -- Define a theorem and use the anomimous constructor to prove p ∧ q ↔ q ∧ p 
 theorem and_swap : p ∧ q ↔ q ∧ p :=
⟨ λ h, ⟨h.right, h.left⟩, λ h, ⟨h.right, h.left⟩ ⟩
-- Prove, using and_swap theorem that p ∧ q → q ∧ p
example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

-- Introducing auxiliary subgoals with `have`
example (h : p ∧ q) : q ∧ p :=
have hp : p, from and.left h,
have hq : q, from and.right h,
show q ∧ p, from and.intro hq hp

-- Introducing auxiliary subgoals with `suffices`
example (h : p ∧ q) : q ∧ p :=
have hp : p, from and.left h,
suffices hq : q, from and.intro hq hp,
show q, from and.right h


-- Classical logic
-- Prove double negation
-- To use `em` we can invoke it using classical namespace like so: `classical.em`
-- or import the classical module with 'open classical' and just use 'em' directly,
-- no need to prefix it with namespace name
theorem dne {p : Prop} (h : ¬¬p) : p :=
  or.elim (classical.em p)
    (assume hp : p, show p, from hp)
    (assume hnp : ¬p, show p, from absurd hnp h)

-- Prove double negation, p is defined at the top of the file as p : Prop,
-- so no need to add {p : Prop} to the premises
example (h : ¬¬p) : p :=
or.elim (classical.em p)
  (assume hp : p, show p, from hp)
  (assume hnp : ¬p, show p, from absurd hnp h)

-- Proof by cases
example (h : ¬¬p) : p :=
classical.by_cases
(assume h1 : p, h1)
(assume h1 : ¬p, absurd h1 h)

-- Proof by contradiction
example (h : ¬¬p) : p :=
classical.by_contradiction
(assume h1 : ¬p, absurd h1 h)

example (h : ¬¬p) : p :=
classical.by_contradiction
(assume h1 : ¬p, show false, from h h1)

-- Prove ¬(p ∧ q) → ¬p ∨ ¬q
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
or.elim (classical.em p)
(assume hp : p,
  or.inr (show ¬q, from
          assume hq : q,
          h ⟨hp, hq⟩))
(assume hnp : ¬p, show ¬p ∨ ¬q, from or.inl hnp)

-- Prove p ∧ q → (p → q) :=
example : p ∧ q → (p → q) :=
assume hpq : p ∧ q,
assume hp : p, show q, from and.elim_right hpq

-- Prove p → q → (p ∧ q) :=
example : p → q → (p ∧ q) :=
assume hp : p,
assume hq : q, show  p ∧ q, from and.intro hp hq


-- 3.6. Examples of Propositional Validities

-- commutativity of ∧ and ∨

-- Prove p ∨ q ↔ q ∨ p
example : p ∨ q ↔ q ∨ p :=
iff.intro
(assume h : p ∨ q, show q ∨ p,
  from or.elim h
    (assume hp : p, show q ∨ p, from or.intro_right q hp)
    (assume hq : q, show q ∨ p, from or.intro_left p hq))
(assume h : q ∨ p, show p ∨ q,
  from or.elim h
    (assume hq : q, show p ∨ q, from or.intro_right p hq)
    (assume hp : p, show p ∨ q, from or.intro_left q hp))

-- Associativity of ∧ and ∨ --
-- Prove (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
  (assume hpqr : (p ∧ q) ∧ r, show p ∧ (q ∧ r), from
    ⟨hpqr.left.left, ⟨hpqr.left.right, hpqr.right⟩⟩)
  (assume hpqr : p ∧ (q ∧ r), show (p ∧ q) ∧ r, from
    ⟨⟨hpqr.left, hpqr.right.left⟩, hpqr.right.right⟩)

-- Prove (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro
  (assume hpqr : (p ∨ q) ∨ r, show p ∨ (q ∨ r), from
    or.elim hpqr
      (assume hpq : p ∨ q, show p ∨ (q ∨ r), from
        or.elim hpq
        (assume hp : p, show p ∨ (q ∨ r), from or.inl hp)
        (assume hq : q, show p ∨ (q ∨ r), from or.inr (or.inl hq)))
      (assume hr : r, show p ∨ (q ∨ r), from or.inr (or.inr hr)))
  (assume hpqr : p ∨ (q ∨ r), show (p ∨ q) ∨ r, from
    or.elim hpqr
    (assume hp : p, show (p ∨ q) ∨ r, from or.inl (or.inl hp))
    (assume hqr : q ∨ r, show (p ∨ q) ∨ r, from or.elim hqr
      (assume hq: q, show (p ∨ q) ∨ r, from or.inl (or.inr hq ))
      (assume hr : r, show (p ∨ q) ∨ r, from or.inr hr)))

-- Distributivity --
-- Prove p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (assume h : p ∧ (q ∨ r),
    have hp : p, from h.left,
    or.elim (h.right)
      (assume hq : q,
        show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
      (assume hr : r,
        show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩))
  (assume h : (p ∧ q) ∨ (p ∧ r),
   or.elim h
   (assume hpq : (p ∧ q),
     show p ∧ (q ∨ r), from and.intro hpq.left (or.inl hpq.right))
   (assume hpr : (p ∧ r),
      show p ∧ (q ∨ r), from and.intro hpr.left (or.inr hpr.right)))

-- Prove p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
iff.intro
(assume h: p ∨ (q ∧ r),
  show (p ∨ q) ∧ (p ∨ r), 
  from or.elim h
  (assume hp: p, show (p ∨ q) ∧ (p ∨ r), from ⟨or.inl hp, or.inl hp⟩)
  (assume hqr: (q ∧ r), show (p ∨ q) ∧ (p ∨ r), from ⟨or.inr hqr.left, or.inr hqr.right⟩))
(assume h: (p ∨ q) ∧ (p ∨ r),
  show p ∨ (q ∧ r), 
  from  or.elim (h.left)
  (assume hp : p, show p ∨ (q ∧ r), from or.inl hp)
  (assume hq : q, show p ∨ (q ∧ r), from or.elim h.right
    (assume hp : p, show p ∨ (q ∧ r), from or.inl hp)
    (assume hr : r, show p ∨ (q ∧ r), from or.inr ⟨hq, hr⟩)
   ))

-- Other properties
-- Prove (p → (q → r)) ↔ (p ∧ q → r)
example : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
(assume hpqr : p → (q → r), show p ∧ q → r, from
  (assume hpq : p ∧ q,
    have hp : p, from hpq.left,
    have hq : q, from hpq.right,
    show r, from (hpqr hp) hq))
(assume hpqr : (p ∧ q → r), show (p → (q → r)), from
  (assume hp : p, show q → r, from
    (assume hq, show r, from (hpqr ⟨hp, hq⟩))))

-- Prove ((p ∨ q) → r) ↔ (p → r) ∧ (q → r)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
iff.intro
(assume hpqr : (p ∨ q) → r, show (p → r) ∧ (q → r), from 
  ⟨(assume hp : p, show r, from hpqr(or.inl hp)), 
   (assume hq : q, show r, from hpqr(or.inr hq))⟩) 
(assume hprqr : (p → r) ∧ (q → r), show (p ∨ q) → r, from
  (assume hpq : p ∨ q, show r, from
    or.elim hpq
    (assume hp : p, show r, from hprqr.left hp)
    (assume hq : q, show r, from hprqr.right hq)
  )
)

-- Prove ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
⟨λ h, ⟨λ hp, h (or.inl hp), λ hq, h (or.inr hq)⟩, 
  λ hn h, or.elim h hn.1 hn.2⟩

-- Another proof for ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example (p q : Prop) : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
(assume hnpq : ¬(p ∨ q), show ¬p ∧ ¬q, from
  and.intro
  (assume hp : p, show false, from hnpq (or.inl hp))
  (assume hq : q, show false, from hnpq (or.inr hq))) 
(assume (hnpnq : ¬p ∧ ¬q),
 show ¬(p ∨ q), from
  assume hnpq : p ∨ q, show false, from
   or.elim hnpq (and.left hnpnq) (and.right hnpnq))

-- Prove ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
(assume hnpnq : ¬p ∨ ¬q,
 assume hpq : p ∧ q,
  show false, from
  (or.elim hnpnq
    (assume hnp : ¬p, show false, from hnp (and.left hpq))
    (assume hnq : ¬q, show false, from hnq (and.right hpq))
  )
)

-- Prove ¬(p ∧ ¬p) := sorry
example : ¬(p ∧ ¬p) :=
assume h : p ∧ ¬p,
show false, from h.right h.left

example : ¬(p ∧ ¬p) :=
assume h,
absurd h.left h.right

-- Prove p ∧ ¬q → ¬(p → q)
example : p ∧ ¬q → ¬(p → q) :=
assume hpnq : p ∧ ¬ q,
assume hpq : p → q,
absurd (hpq hpnq.left) hpnq.right

example : p ∧ ¬q → ¬(p → q) :=
assume hpnq : p ∧ ¬ q,
assume hpq : p → q,
show false, from hpnq.right (hpq hpnq.left)

-- Prove ¬p → (p → q) := sorry
example : ¬p → (p → q) :=
assume hnp,
assume hp,
absurd hp hnp

example : ¬p → (p → q) :=
assume hnp,
assume hp,
show q , from absurd hp hnp

example : ¬p → (p → q) :=
assume hp,
assume hnp,
show q , from false.elim(hp hnp)

-- Prove (¬p ∨ q) → (p → q)
example : (¬p ∨ q) → (p → q) := 
(assume hnpq : ¬p ∨ q,
or.elim hnpq
(assume hnp : ¬p, 
 assume hp : p,
 show q, from absurd hp hnp)
(assume hq : q, 
 assume hp : p,
 show q, from hq))

example : (¬p ∨ q) → (p → q) := 
(assume hnpq : ¬p ∨ q,
or.elim hnpq
(assume hnp : ¬p, 
 assume hp : p,
 show q, from false.elim (hnp hp))
(assume hq : q, 
 assume hp : p,
 show q, from hq))

-- Prove p ∨ false ↔ p
example : p ∨ false ↔ p :=
iff.intro
(assume hpf,
or.elim hpf 
  (assume hp, show p, from hp)
  (assume false, show p, from false.elim))
(assume hp, 
 show p ∨ false, from or.inl hp)

 -- Prove p ∧ false ↔ false
example : p ∧ false ↔ false :=
iff.intro
(assume hpf,
show false, from hpf.right)
(assume hf,
show p ∧ false, from and.intro (show p, from hf.elim) hf)

-- Prove ¬(p ↔ ¬p)
example : ¬(p ↔ ¬p) :=
assume hpnp,
have hnp : ¬ p, from
  assume hp : p, show false, from (hpnp.elim_left hp) hp,
show false, from hnp (hpnp.elim_right hnp)

-- Prove (p → q) → (¬q → ¬p)
example : (p → q) → (¬q → ¬p) :=
assume hpq,
assume hnq,
assume hp, show false, from hnq (hpq hp)

example : (p → q) → (¬q → ¬p) :=
assume hpq,
assume hnq,
assume hp, absurd (hpq hp) hnq

-- these require classical reasoning
open classical
-- Prove (p → r ∨ s) → ((p → r) ∨ (p → s))
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
(assume hprs, show (p → r) ∨ (p → s), from sorry)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
(assume hprs, assume hp, show (p → r) ∨ (p → s), from sorry)

example (h : ¬¬p) : p :=
by_cases
  (assume h1 : p, h1)
  (assume h1 : ¬p, absurd h1 h)

example (h : ¬¬p) : p :=
by_contradiction
  (assume h1 : ¬p,
    show false, from h h1)

example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
or.elim (em p)
  (assume hp : p,
    or.inr
      (show ¬q, from
        assume hq : q,
        h ⟨hp, hq⟩))
  (assume hp : ¬p,
    or.inl hp)

-- Prove ¬(p ∧ q) → ¬p ∨ ¬q
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
assume hnpq,
or.elim (em p)
(assume hp, show ¬p ∨ ¬q, from or.inr (assume hq, hnpq (and.intro hp hq)))
(assume hnp, show ¬p ∨ ¬q, from or.inl hnp)

-- Prove: ¬(p ∧ ¬q) → (p → q)
example : ¬(p ∧ ¬q) → (p → q) :=
assume hnpnq :  ¬(p ∧ ¬q), show p → q, from (assume hp: p, show q, from
  by_contradiction (assume hnq: ¬q, show false,
    from hnpnq (and.intro hp hnq)))

-- Prove ¬(p → q) → p ∧ ¬q
example : ¬(p → q) → p ∧ ¬q := 
assume hnpq : ¬(p → q),
show p ∧ ¬q, from by_contradiction (
  assume hnpnq : ¬(p ∧ ¬q), show false, from
    hnpq
    (assume hp: p, show q, from
      by_contradiction (assume hnq: ¬q, show false,
        from hnpnq (and.intro hp hnq))
    )
)

-- Prove (p → q) → (¬p ∨ q)
example : (p → q) → (¬p ∨ q) :=
assume hpq : p → q,
show ¬p ∨ q, from
or.elim (em p)
  (assume hp, show ¬p ∨ q, from or.inr(hpq hp))
  (assume hnp, show ¬p ∨ q, from or.inl hnp)

-- Prove (¬q → ¬p) → (p → q)
example : (¬q → ¬p) → (p → q) :=
assume hnpnq : ¬q → ¬p,
show p → q, from (
  assume hp: p, show q, from by_contradiction (
    assume hnq: ¬q, show false, from (hnpnq hnq) hp
  )
)

-- Prove p ∨ ¬p
example : p ∨ ¬p :=
by_contradiction(assume hnpnp: ¬(p ∨ ¬p), show false, from
  or.elim (em p)
  (assume hp : p, show false, from
    false.elim(hnpnp (or.inl hp)))
  (assume hnp : ¬p, show false, from
    false.elim(hnpnp (or.inr hnp)))
)

-- Prove (((p → q) → p) → p)
example : (((p → q) → p) → p) :=
assume hpqp : (p → q) → p, show p, from
  by_contradiction(
      assume hnp : ¬p, show false, from
      false.elim(
        hnp
        (hpqp (assume hp : p,
          show q, from false.elim(hnp hp)))
      )
  )
