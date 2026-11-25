import Lean

namespace Optimization580

/-- Moving vertices between the two parts leaves their total order unchanged. -/
theorem transfer_size (a b d : Nat) :
    (a + d) + b = a + (b + d) :=
  Eq.trans (Nat.add_right_comm a d b) (Nat.add_assoc a b d)

/-- The gain in edges when the two parts of a complete bipartite graph move closer. -/
theorem transfer_gain (a b c d : Nat) (h : b = a + c) :
    (a + d) * b = a * (b + d) + d * c :=
  calc
    (a + d) * b = a * b + d * b := Nat.add_mul a d b
    _ = a * b + d * (a + c) :=
          congrArg (fun t : Nat => a * b + d * t) h
    _ = a * b + (d * a + d * c) :=
          congrArg (fun t : Nat => a * b + t) (Nat.mul_add d a c)
    _ = a * b + (a * d + d * c) :=
          congrArg (fun t : Nat => a * b + (t + d * c)) (Nat.mul_comm d a)
    _ = (a * b + a * d) + d * c := Eq.symm (Nat.add_assoc (a * b) (a * d) (d * c))
    _ = a * (b + d) + d * c :=
          congrArg (fun t : Nat => t + d * c) (Eq.symm (Nat.mul_add a b d))

theorem transfer_bound (a b c d : Nat) (h : b = a + c) :
    a * (b + d) ≤ (a + d) * b :=
  Eq.mpr (congrArg (fun t : Nat => a * (b + d) ≤ t) (transfer_gain a b c d h))
    (Nat.le_add_right (a * (b + d)) (d * c))

theorem even_split (a d : Nat) :
    a * ((a + d) + d) ≤ (a + d) * (a + d) :=
  transfer_bound a (a + d) d d rfl

theorem odd_split (a d : Nat) :
    a * (((a + d) + 1) + d) ≤ (a + d) * ((a + d) + 1) :=
  transfer_bound a (a + (d + 1)) (d + 1) d rfl

end Optimization580
