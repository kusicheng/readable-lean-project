import Lean

namespace RecursionFixture

theorem zeroAdd : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (zeroAdd n)

theorem commuteAddition (a b : Nat) : ∀ n : Nat, (a + b) + n = (b + a) + n
  | 0 => Nat.add_comm a b
  | n + 1 => congrArg Nat.succ (commuteAddition a b n)

end RecursionFixture
