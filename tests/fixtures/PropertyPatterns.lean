namespace PropertyPatterns

structure Bounds (a x b : Nat) : Prop where
  lower : a ≤ x
  upper : x ≤ b

theorem middle (a x b : Nat) (h : Bounds a x b) : a ≤ b :=
  let ⟨hx, hy⟩ := h
  Nat.le_trans hx hy

end PropertyPatterns
