import Lean

namespace Examples

theorem two_dvd_double (n : Nat) : 2 ∣ n + n :=
  let factorization : n + n = 2 * n := Eq.symm (Nat.two_mul n)
  Exists.intro n factorization

theorem even_of_two_dvd (n : Nat) (h : 2 ∣ n) : ∃ k : Nat, n = k + k :=
  Exists.elim h (fun k hk =>
    let doubling : n = k + k := Eq.trans hk (Nat.two_mul k)
    Exists.intro k doubling)

theorem two_dvd_double_mul (a n : Nat) : 2 ∣ (a + a) * n :=
  let doubled : 2 ∣ a + a := two_dvd_double a
  Nat.rec (motive := fun m => 2 ∣ (a + a) * m)
    (Eq.mpr (congrArg (fun total : Nat => 2 ∣ total) (Nat.mul_zero (a + a))) (Nat.dvd_zero 2))
    (fun m ih =>
      let sum : 2 ∣ (a + a) * m + (a + a) := Nat.dvd_add ih doubled
      let expansion : (a + a) * (m + 1) = (a + a) * m + (a + a) := Nat.mul_succ (a + a) m
      Eq.mpr (congrArg (fun total : Nat => 2 ∣ total) expansion) sum)
    n

end Examples
