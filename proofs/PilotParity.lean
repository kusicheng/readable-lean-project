import Lean

namespace Pilot

theorem two_dvd_double (n : Nat) : 2 ∣ n + n :=
  Exists.intro n (Eq.symm (Nat.two_mul n))

theorem even_has_double (n : Nat) (h : 2 ∣ n) : ∃ k : Nat, n = k + k :=
  Exists.elim h (fun k hk =>
    Exists.intro k (Eq.trans hk (Nat.two_mul k)))

theorem even_of_double (n : Nat) (h : ∃ k : Nat, n = k + k) : 2 ∣ n :=
  Exists.elim h (fun k hk =>
    Eq.mpr (congrArg (fun total : Nat => 2 ∣ total) hk) (two_dvd_double k))

theorem double_characterization (n : Nat) : (2 ∣ n) ↔ ∃ k : Nat, n = k + k :=
  Iff.intro
    (fun h => even_has_double n h)
    (fun h => even_of_double n h)

theorem even_add {m n : Nat} (hm : 2 ∣ m) (hn : 2 ∣ n) : 2 ∣ m + n :=
  Nat.dvd_add hm hn

theorem even_mul_right {n : Nat} (m : Nat) (hn : 2 ∣ n) : 2 ∣ n * m :=
  Nat.dvd_mul_right_of_dvd hn m

theorem even_square_has_double (n : Nat) (hn : 2 ∣ n) : ∃ k : Nat, n * n = k + k :=
  let square : 2 ∣ n * n := even_mul_right n hn
  Iff.mp (double_characterization (n * n)) square

theorem even_progression (start step n : Nat) (startEven : 2 ∣ start) (stepEven : 2 ∣ step) :
    2 ∣ start + step * n :=
  Nat.rec (motive := fun i => 2 ∣ start + step * i)
    (let initial : start + step * 0 = start :=
       Eq.trans (congrArg (fun term : Nat => start + term) (Nat.mul_zero step)) (Nat.add_zero start)
     Eq.mpr (congrArg (fun term : Nat => 2 ∣ term) initial) startEven)
    (fun i ih =>
      let next : 2 ∣ (start + step * i) + step := even_add ih stepEven
      let expansion : start + step * (i + 1) = (start + step * i) + step :=
        Eq.trans
          (congrArg (fun term : Nat => start + term) (Nat.mul_succ step i))
          (Eq.symm (Nat.add_assoc start (step * i) step))
      Eq.mpr (congrArg (fun term : Nat => 2 ∣ term) expansion) next)
    n

end Pilot
