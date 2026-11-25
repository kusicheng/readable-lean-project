import Init

namespace Incidence580

/-- Read the bit assigned to the cell in row i and column j.
    Cells are indexed by diagonals so increasing either dimension preserves all old entries. -/
def entry (m i j : Nat) : Nat :=
  m / 2 ^ ((i + j) * (i + j + 1) / 2 + j) % 2

def row (m i : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => row m i j + entry m i j

def column (m j : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => column m j i + entry m i j

def rows (m : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | i + 1, c => rows m i c + row m i c

def columns (m r : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => columns m r j + column m j r

theorem empty_rows (m c : Nat) : columns m 0 c = 0 := by
  induction c with
  | zero => rfl
  | succ j ih =>
    exact Eq.trans (show columns m 0 (j + 1) = columns m 0 j from rfl) ih

theorem add_one_row (m r c : Nat) :
    columns m (r + 1) c = columns m r c + row m r c := by
  induction c with
  | zero => rfl
  | succ j ih =>
    calc
      columns m (r + 1) (j + 1)
          = columns m (r + 1) j + (column m j r + entry m r j) := rfl
      _ = (columns m r j + row m r j) + (column m j r + entry m r j) :=
          congrArg (fun z => z + (column m j r + entry m r j)) ih
      _ = (columns m r j + column m j r) + (row m r j + entry m r j) :=
          Nat.add_add_add_comm _ _ _ _
      _ = columns m r (j + 1) + row m r (j + 1) := rfl

theorem incidence_count (m r c : Nat) : rows m r c = columns m r c := by
  induction r with
  | zero => exact (empty_rows m c).symm
  | succ i ih =>
    calc
      rows m (i + 1) c = rows m i c + row m i c := rfl
      _ = columns m i c + row m i c := congrArg (fun z => z + row m i c) ih
      _ = columns m (i + 1) c := (add_one_row m i c).symm

theorem parameter_balance (m v b r k : Nat)
    (hp : rows m v b = v * r) (hb : columns m v b = b * k) : v * r = b * k :=
  Eq.trans hp.symm (Eq.trans (incidence_count m v b) hb)

theorem block_size_divides (m v b r k : Nat)
    (hp : rows m v b = v * r) (hb : columns m v b = b * k) : k ∣ v * r :=
  ⟨b, Eq.trans (parameter_balance m v b r k hp hb) (Nat.mul_comm b k)⟩

/-- Constant row degree implies the first total assumed by parameter_balance. -/
theorem sum_regular_rows (m v b r : Nat) (h : ∀ i, i < v → row m i b = r) :
    rows m v b = v * r := by
  induction v with
  | zero => exact (Nat.zero_mul r).symm
  | succ i ih =>
    have hp := ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self i)))
    calc
      rows m (i + 1) b = rows m i b + row m i b := rfl
      _ = i * r + r := by rw [hp, h i (Nat.lt_succ_self i)]
      _ = (i + 1) * r := (Nat.succ_mul i r).symm

/-- Constant block size implies the second total assumed by parameter_balance. -/
theorem sum_uniform_columns (m v b k : Nat) (h : ∀ j, j < b → column m j v = k) :
    columns m v b = b * k := by
  induction b with
  | zero => exact (Nat.zero_mul k).symm
  | succ j ih =>
    have hb := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self j)))
    calc
      columns m v (j + 1) = columns m v j + column m j v := rfl
      _ = j * k + k := by rw [hb, h j (Nat.lt_succ_self j)]
      _ = (j + 1) * k := (Nat.succ_mul j k).symm

theorem regular_uniform_balance (m v b r k : Nat)
    (hp : ∀ i, i < v → row m i b = r)
    (hb : ∀ j, j < b → column m j v = k) : v * r = b * k :=
  parameter_balance m v b r k (sum_regular_rows m v b r hp) (sum_uniform_columns m v b k hb)

example (m b : Nat) (hp : ∀ i, i < 10 → row m i b = 3)
    (hb : ∀ j, j < b → column m j 10 = 4) : False := by
  have hd := block_size_divides m 10 b 3 4
    (sum_regular_rows m 10 b 3 hp) (sum_uniform_columns m 10 b 4 hb)
  exact (by decide : ¬ 4 ∣ 10 * 3) hd

end Incidence580
