import Mathlib.Tactic.Ring

namespace RationalPolynomial

theorem distribute (x y : ℚ) : (x + y) * (x - y) = x * x - y * y := by
  ring

theorem cancellation (x y : ℚ) : x * y - y * x = 0 := by
  ring

end RationalPolynomial
