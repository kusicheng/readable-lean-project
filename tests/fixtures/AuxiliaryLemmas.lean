import Init

namespace AuxiliaryLemmas

private theorem liftEquality (x y : Nat) (f : Nat → Nat) (h : x = y) :
    f (x + 1 + 2 + 3 + 4 + 5 + 6 + 7) = f (y + 1 + 2 + 3 + 4 + 5 + 6 + 7) := by
  have h₁ := congrArg (fun k : Nat => k + 1) h
  have h₂ := congrArg (fun k : Nat => k + 2) h₁
  have h₃ := congrArg (fun k : Nat => k + 3) h₂
  have h₄ := congrArg (fun k : Nat => k + 4) h₃
  have h₅ := congrArg (fun k : Nat => k + 5) h₄
  have h₆ := congrArg (fun k : Nat => k + 6) h₅
  exact congrArg (fun k : Nat => f (k + 7)) h₆

theorem twoPairs (a b c d : Nat) (h : a = b) (k : c = d) :
    (a + 1 + 2 + 3 + 4 + 5 + 6 + 7 = b + 1 + 2 + 3 + 4 + 5 + 6 + 7) ∧
    (c + 1 + 2 + 3 + 4 + 5 + 6 + 7 = d + 1 + 2 + 3 + 4 + 5 + 6 + 7) :=
  ⟨liftEquality a b (fun n => n) h, liftEquality c d (fun n => n) k⟩

end AuxiliaryLemmas
