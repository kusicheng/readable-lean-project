import proofs.PilotParity

namespace Progressions

theorem dvd_translate_iff {q n offset : Nat} (hoffset : q ∣ offset) :
    q ∣ n ↔ q ∣ n + offset := by
  exact Nat.dvd_add_iff_left hoffset

theorem dvd_translate_multiple_iff {q n step count : Nat} (hstep : q ∣ step) :
    q ∣ n ↔ q ∣ n + step * count := by
  have hmultiple : q ∣ step * count := Nat.dvd_mul_right_of_dvd hstep count
  exact dvd_translate_iff hmultiple

theorem even_double_multiple_translate_iff (n d count : Nat) :
    2 ∣ n ↔ 2 ∣ n + (d + d) * count := by
  have hdouble : 2 ∣ d + d := Pilot.two_dvd_double d
  exact dvd_translate_multiple_iff hdouble

theorem even_product {n : Nat} (count : Nat) (hn : 2 ∣ n) :
    2 ∣ n * count := by
  exact Pilot.even_mul_right count hn

theorem even_progression_iff {n step count : Nat} (hstep : 2 ∣ step) :
    2 ∣ n ↔ 2 ∣ n + step * count := by
  have hmultiple : 2 ∣ step * count := even_product count hstep
  exact dvd_translate_iff hmultiple

end Progressions
