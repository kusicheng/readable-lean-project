import Mathlib.Combinatorics.Pigeonhole

open Finset

variable {s t : Finset ℕ} {f w : ℕ → ℕ} {b : ℕ}

theorem submissionOne (hf : ∀ x ∈ s, f x ∈ t) (hb : t.card * b < ∑ x ∈ s, w x) :
    ∃ y ∈ t, b < ∑ x ∈ s with f x = y, w x :=
  Finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf hb

theorem submissionTwo (hf : ∀ x ∈ s, f x ∈ t) (hb : t.card * b < ∑ x ∈ s, w x) :
    ∃ y ∈ t, b < ∑ x ∈ s with f x = y, w x := by
  apply Finset.exists_lt_of_sum_lt
  calc
    ∑ _y ∈ t, b = t.card * b := Finset.sum_const b
    _ < ∑ x ∈ s, w x := hb
    _ = ∑ y ∈ t, ∑ x ∈ s with f x = y, w x :=
      (Finset.sum_fiberwise_of_maps_to hf w).symm
