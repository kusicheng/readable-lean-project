import Lean

namespace EqualityDecisions

structure Packet where
  payload : List Nat
  nonempty : payload ≠ []
  deriving DecidableEq

structure Bundle (α : Type) where
  contents : List α
  nonempty : contents ≠ []
  deriving DecidableEq

structure Coordinates where
  row : Nat
  column : Nat
  deriving DecidableEq

private noncomputable def opaqueDecision (x y : Packet) : Decidable (x = y) :=
  Classical.propDecidable _

noncomputable def alternate : DecidableEq Packet := opaqueDecision

theorem packet_test (x y : Packet) : decide (x = y) = true ↔ x = y :=
  decide_eq_true_iff

theorem bundle_test {α : Type} [DecidableEq α] (x y : Bundle α) :
    decide (x = y) = true ↔ x = y :=
  decide_eq_true_iff

theorem coordinates_test (x y : Coordinates) : decide (x = y) = true ↔ x = y :=
  decide_eq_true_iff

theorem alternate_test (x y : Packet) :
    @decide (x = y) (alternate x y) = true ↔ x = y :=
  @decide_eq_true_iff _ (alternate x y)

end EqualityDecisions
