import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Ring.Nat

namespace NaturalSubtraction

theorem recover_left (x y z : Nat) (h : x + z = y) : x = y - z :=
  eq_tsub_of_add_eq h

theorem subtract_right (x y z : Nat) (h : x = z + y) : x - y = z :=
  tsub_eq_of_eq_add h

theorem subtract_left (x y z : Nat) (h : x = y + z) : x - y = z :=
  tsub_eq_of_eq_add_rev h

theorem supplied_law (x y z : Nat) (law : OrderedSub Nat) (h : x + z = y) : x = y - z :=
  @eq_tsub_of_add_eq Nat _ _ _ law x y z _ h

theorem chosen_subtraction (s : Sub Nat) (law : @OrderedSub Nat _ _ s)
    (x y z : Nat) (h : x + z = y) : x = @Sub.sub Nat s y z :=
  @eq_tsub_of_add_eq Nat _ _ s law x y z _ h

end NaturalSubtraction
