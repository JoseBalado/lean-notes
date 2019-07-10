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
variable y : Prop

example (h1 : ∃ x, P x) :   P U    :=
exists.elim h1
  (assume (y : U),
    show P y, from (h1 y))
end three