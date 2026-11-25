import Mathlib.Data.Finset.Powerset

example (s t : Finset Nat) (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  ext x
  exact h x

example (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext1 x
  exact h x
