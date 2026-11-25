import Mathlib.Tactic.Linarith

namespace Arithmetic

theorem weighted_bound (x y : ℚ) (total : 2 * x + y ≤ 9) (lower : 1 ≤ y) :
    x ≤ 4 := by
  linarith

theorem rounded_bound (x y : ℤ) (lower : 2 * x ≤ y) (upper : y ≤ 9) :
    x ≤ 4 := by
  omega

end Arithmetic
