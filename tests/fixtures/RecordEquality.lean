import Mathlib.Data.Nat.Basic

namespace RecordEquality

@[ext] structure Score where
  value : Nat
  positive : 0 < value
  bounded : value ≤ 10

@[ext] structure OrderedPair where
  left : Nat
  right : Nat
  ordered : left ≤ right

theorem equal_scores (x y : Score) (h : x.value = y.value) : x = y :=
  Score.ext h

theorem equal_ordered_pairs (x y : OrderedPair) (h : x.left = y.left)
    (k : x.right = y.right) : x = y :=
  OrderedPair.ext h k

theorem one_coordinate_does_not_determine_the_pair :
    ∃ x y : OrderedPair, x.left = y.left ∧ x ≠ y := by
  refine ⟨⟨0, 1, by decide⟩, ⟨0, 2, by decide⟩, rfl, ?_⟩
  intro h
  have h' := congrArg OrderedPair.right h
  exact Nat.noConfusion (Nat.succ.inj h')

@[ext] structure CoordinatePair (α : Type) where
  pair ::
  row : α
  column : α

theorem determined_by_coordinates {α : Type} (a b : CoordinatePair α)
    (hr : a.row = b.row) (hc : a.column = b.column) : a = b :=
  CoordinatePair.ext hr hc

@[ext] structure PredicateTag where
  condition : Prop
  witness : condition

theorem determined_by_condition (a b : PredicateTag) (h : a.condition = b.condition) : a = b :=
  PredicateTag.ext h

inductive Fork (α : Type) where
  | idle
  | fork (label : α) (west east : Fork α)

def reflect {α : Type} : Fork α → Fork α
  | .idle => .idle
  | .fork a west east => .fork a (reflect east) (reflect west)

theorem double_reflection {α : Type} : ∀ t : Fork α, reflect (reflect t) = t
  | .idle => rfl
  | .fork _ west east => by simp only [reflect, double_reflection west, double_reflection east]

theorem via_smaller {α : Type} (r : α → α → Prop) (wf : WellFounded r)
    (P : α → Prop) (left right : α → α)
    (hl : ∀ x, r (left x) x) (hr : ∀ x, r (right x) x)
    (step : ∀ x, P (left x) → P (right x) → P x) : ∀ x, P x :=
  wf.fix (C := P) fun x ih => step x (ih (left x) (hl x)) (ih (right x) (hr x))

end RecordEquality
