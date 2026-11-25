import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Nat.Defs

namespace RepeatedAddition

theorem natural_product (n b : ℕ) : n • b = n * b := rfl

theorem product_in_reverse (n b : ℕ) : n * b = n • b := rfl

theorem constant_sum {M : Type} [AddCommMonoid M] (s : Finset ℕ) (b : M) :
    ∑ _i ∈ s, b = s.card • b := Finset.sum_const b

theorem abstract_action {M : Type} [SMul ℕ M] (n : ℕ) (b : M) : n • b = n • b := rfl

theorem free_index {M : Type} [AddMonoid M] (k : ℕ) (f : ℕ → M) :
    k • f k = k • f k := rfl

theorem local_addition (m : AddMonoid ℕ) (n b : ℕ) :
    @SMul.smul ℕ ℕ (@AddMonoid.toNatSMul ℕ m) n b =
      @SMul.smul ℕ ℕ (@AddMonoid.toNatSMul ℕ m) n b := rfl

def keep_value : SMul ℕ ℕ := ⟨fun _ b => b⟩

theorem custom_action (n b : ℕ) : @SMul.smul ℕ ℕ keep_value n b = b := rfl

theorem custom_action_via_notation (n b : ℕ) :
    @HSMul.hSMul ℕ ℕ ℕ (@instHSMul ℕ ℕ keep_value) n b = b := rfl

theorem two_monoids {M : Type} [first : AddCommMonoid M] [second : AddCommMonoid M]
    (n : ℕ) (b : M) :
    (@SMul.smul ℕ M (@AddMonoid.toNatSMul M first.toAddMonoid) n b =
      @SMul.smul ℕ M (@AddMonoid.toNatSMul M second.toAddMonoid) n b) ↔
    (@SMul.smul ℕ M (@AddMonoid.toNatSMul M second.toAddMonoid) n b =
      @SMul.smul ℕ M (@AddMonoid.toNatSMul M first.toAddMonoid) n b) := eq_comm

end RepeatedAddition
