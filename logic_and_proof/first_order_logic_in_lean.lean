namespace one
variable U : Type
variable P : U → Prop

example (y : U) (h : P y) : ∃ x, P x :=
exists.intro y h
end one

namespace two
variable U : Type
variable P : U → Prop
variable Q : Prop

example (h1 : ∃ x, P x) (h2 : ∀ x, P x → Q) : Q :=
exists.elim h1
  (assume (y : U) (h : P y),
    have h3 : P y → Q, from h2 y,
    show Q, from h3 h)
end two

-- More simple example
namespace three
variable U : Type
variable P : U → Prop
variable a : Prop


variables (α : Type) (p q : α → Prop)

example (h : ∃ x, p x) : ∃ x, p x  :=
exists.elim h
  (assume w,
    assume hw : p w ,
    show ∃ x, p x, from ⟨w, hw⟩)
end three