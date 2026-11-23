import Lean

namespace Examples

theorem two_dvd_double_automated (n : Nat) : 2 ∣ n + n := by
  omega

end Examples
