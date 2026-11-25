import Mathlib.Data.List.Basic

namespace IndexedRecordTrial

@[ext] structure DigitRow (width : Nat) where
  digits : List Nat
  decimal : ∀ d ∈ digits, d < 10
  width_eq : digits.length = width

theorem equal_rows {width : Nat} (x y : DigitRow width)
    (h : x.digits = y.digits) : x = y := DigitRow.ext h

end IndexedRecordTrial
