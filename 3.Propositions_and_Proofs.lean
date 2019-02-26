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
-- in situations like these, when the relevant type is an inductive type and can be inferred from the context.
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

-- modus tollens, deriving a contradiction from p to obtain false.
-- Everything follows from false, in this case ¬p
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
-- so no need to add {p : Prop}  to the premises
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