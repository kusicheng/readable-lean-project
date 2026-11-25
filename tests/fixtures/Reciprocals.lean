import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.NNRat.Order

namespace Reciprocals

theorem clear_density (mass scale cap : ℚ≥0) (hs : 0 < scale)
    (h : mass * scale⁻¹ ≤ cap) : mass ≤ scale * cap := by
  simpa only [mul_inv_le_iff₀' hs] using h

theorem clear_sum (s : Finset ℕ) (scale cap : ℚ≥0) (hs : 0 < scale)
    (h : (∑ _k ∈ s, scale⁻¹) ≤ cap) : (s.card : ℚ≥0) ≤ scale * cap := by
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_inv_le_iff₀' hs] using h

theorem introduce_inverse (mass scale cap : ℚ≥0) (hs : 0 < scale)
    (h : mass ≤ scale * cap) : mass * scale⁻¹ ≤ cap := by
  simpa only [mul_inv_le_iff₀' hs] using h

theorem negate_bound (mass scale cap : ℚ≥0) (hs : 0 < scale)
    (h : ¬ mass * scale⁻¹ ≤ cap) : ¬ mass ≤ scale * cap := by
  simpa only [mul_inv_le_iff₀' hs] using h

theorem reciprocal_zero : (0 : ℚ≥0)⁻¹ = 0 := inv_zero

theorem custom_operation (op : Inv ℚ≥0) (q : ℚ≥0) :
    @Inv.inv ℚ≥0 op q = @Inv.inv ℚ≥0 op q := rfl

theorem clear_signed_ratio (a b c : ℚ) (hc : 0 < c)
    (h : a * c⁻¹ ≤ b) : a ≤ c * b := by
  simpa only [mul_inv_le_iff₀' hc] using h

def one_for_two : OfNat ℚ≥0 2 := ⟨1⟩
def reverse_le : LE ℚ≥0 := ⟨fun a b => b ≤ a⟩
def reverse_lt : LT ℚ := ⟨fun a b => b < a⟩

theorem custom_numeral : (@OfNat.ofNat ℚ≥0 2 one_for_two)⁻¹ = 1 := by
  change (1 : ℚ≥0)⁻¹ = 1
  exact inv_one

theorem custom_order (a b : ℚ≥0) : @LE.le ℚ≥0 reverse_le a b ↔ b ≤ a := Iff.rfl

theorem custom_strict_order (a b : ℚ) : @LT.lt ℚ reverse_lt a b ↔ b < a := Iff.rfl

end Reciprocals
