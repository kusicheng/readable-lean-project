import proofs.Development

namespace Reserved

theorem composed_doubling_sum (a b n : Nat) :
    2 ∣ ((a + a) * n) + (b + b) :=
  Nat.dvd_add (Examples.two_dvd_double_mul a n) (Examples.two_dvd_double b)

theorem divisor_preserved_by_multiplication (n m : Nat) (h : 2 ∣ n) :
    2 ∣ n * m :=
  Exists.elim h (fun k hk =>
    Exists.intro (k * m)
      (Eq.trans (congrArg (fun value => value * m) hk) (Nat.mul_assoc 2 k m)))

end Reserved
