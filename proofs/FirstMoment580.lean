import proofs.Incidence580

namespace FirstMoment580

open Incidence580

/-- Indicator that an outcome experiences no bad events. -/
def zeroIndicator : Nat → Nat
  | 0 => 1
  | _ + 1 => 0

def cleanCount (m r : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => cleanCount m r j + zeroIndicator (column m j r)

theorem charge_outcome (k : Nat) : 1 ≤ k + zeroIndicator k := by
  induction k with
  | zero => exact Nat.le_refl 1
  | succ j _ => exact Nat.succ_le_succ (Nat.zero_le j)

theorem count_columns (m r c : Nat) :
    c ≤ columns m r c + cleanCount m r c := by
  induction c with
  | zero => exact Nat.le_refl 0
  | succ j ih =>
    have ht := Nat.add_le_add ih (charge_outcome (column m j r))
    have regroup := Nat.add_add_add_comm (columns m r j) (cleanCount m r j)
      (column m j r) (zeroIndicator (column m j r))
    have extend : (columns m r j + column m j r) +
        (cleanCount m r j + zeroIndicator (column m j r)) =
        columns m r (j + 1) + cleanCount m r (j + 1) := rfl
    exact Nat.le_trans ht (Nat.le_of_eq (Eq.trans regroup extend))

theorem count_by_events (m r c : Nat) :
    c ≤ rows m r c + cleanCount m r c := by
  have swap := congrArg (fun z => z + cleanCount m r c) (incidence_count m r c).symm
  exact Nat.le_trans (count_columns m r c) (Nat.le_of_eq swap)

theorem first_moment (m r c : Nat) (h : rows m r c < c) :
    0 < cleanCount m r c :=
  Nat.pos_of_lt_add_right (Nat.lt_of_lt_of_le h (count_by_events m r c))

private theorem zeroIndicator_of_positive {k : Nat} (h : k ≠ 0) : zeroIndicator k = 0 := by
  cases k with
  | zero => exact (h rfl).elim
  | succ _ => rfl

theorem clean_witness (m r c : Nat) (h : 0 < cleanCount m r c) :
    ∃ j, j < c ∧ column m j r = 0 := by
  induction c with
  | zero => exact (Nat.lt_irrefl 0 h).elim
  | succ k ih =>
    by_cases last : column m k r = 0
    · exact ⟨k, Nat.lt_succ_self k, last⟩
    · change 0 < cleanCount m r k + zeroIndicator (column m k r) at h
      have prev : 0 < cleanCount m r k := by
        simpa only [zeroIndicator_of_positive last, Nat.add_zero] using h
      obtain ⟨j, before, clean⟩ := ih prev
      exact ⟨j, Nat.lt_trans before (Nat.lt_succ_self k), clean⟩

theorem avoid_all_events (m r c : Nat) (h : rows m r c < c) :
    ∃ j, j < c ∧ column m j r = 0 :=
  clean_witness m r c (first_moment m r c h)

end FirstMoment580
