import Init

namespace RelationHeadings

variable {α β : Type} (R S : α → β → Prop)

theorem a (h : ∀ x y z, R x y → R x z → y = z)
    (x : α) (y z : β) (hy : R x y) (hz : R x z) : y = z := h x y z hy hz

theorem b (h : ∀ x y z, R x z → R y z → x = y)
    (x y : α) (z : β) (hx : R x z) (hy : R y z) : y = x := (h x y z hx hy).symm

-- The premises refer to different relations.
example (x : α) (y z : β) (_ : R x y) (_ : S x z) (h : y = z) : y = z := h

-- The arguments on the fixed side differ.
example (x w : α) (y z : β) (_ : R x y) (_ : R w z) (h : y = z) : y = z := h

-- The first argument also occurs among the two being compared.
example (T : α → α → Prop) (x y : α) (_ : T x x) (_ : T x y) (h : x = y) : x = y := h

-- The different parameters of the same relation family matter.
example (T : Bool → α → β → Prop) (x : α) (y z : β)
    (_ : T true x y) (_ : T false x z) (h : y = z) : y = z := h

theorem c (h : ∀ x y z, R x y → R x z → y = z)
    (x : α) (y z : β) (hy : R x y) (hz : R x z) : z = y := (a R h x y z hy hz).symm

end RelationHeadings
