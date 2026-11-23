-- 1. Define the sum from 0 to n recursively
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

-- 2. Prove the theorem by induction on n
theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero =>
    -- Base case: n = 0
    -- Goal: 2 * sumTo 0 = 0 * (0 + 1)
    rfl
  | succ k ih =>
    -- Inductive step: assume ih : 2 * sumTo k = k * (k + 1)
    -- Goal: 2 * sumTo (k + 1) = (k + 1) * (k + 2)
    calc
      2 * sumTo (k + 1)
        = 2 * (sumTo k + (k + 1)) := by rw [sumTo]
      _ = 2 * sumTo k + 2 * (k + 1) := by rw [Nat.mul_add]
      _ = k * (k + 1) + 2 * (k + 1) := by rw [ih]
      _ = (k + 2) * (k + 1) := by rw [← Nat.add_mul]
      _ = (k + 1) * (k + 2) := by rw [Nat.mul_comm]
