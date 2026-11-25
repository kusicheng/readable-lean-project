import Init

namespace Counting580

-- The components count completions following a zero and a one, respectively.
private def counts : Nat → Nat × Nat
  | 0 => (1, 1)
  | n + 1 => let (a, b) := counts n; (a + b, a)

def openCount (n : Nat) : Nat := (counts n).1
def forcedCount (n : Nat) : Nat := (counts n).2

-- Independently enumerate the actual words, with a choice of initial state.
def words : Nat → Bool → List (List Bool)
  | 0, _ => [[]]
  | n + 1, previous =>
    (words n false).map (false :: ·) ++
      (if previous then [] else (words n true).map (true :: ·))

def admissible : Bool → List Bool → Bool
  | _, [] => true
  | previous, b :: rest => !(previous && b) && admissible b rest

theorem words_length (n : Nat) (previous : Bool) :
    (words n previous).length = (if previous then forcedCount n else openCount n) := by
  induction n generalizing previous with
  | zero => cases previous <;> rfl
  | succ n ih =>
    cases previous <;>
      simp [words, ih, openCount, forcedCount, counts]

theorem mem_words (n : Nat) (previous : Bool) (w : List Bool) :
    w ∈ words n previous ↔ w.length = n ∧ admissible previous w = true := by
  induction n generalizing previous w with
  | zero => cases w <;> simp [words, admissible]
  | succ n ih =>
    cases w with
    | nil => cases previous <;> simp [words]
    | cons b tail =>
      cases previous <;> cases b <;>
        simp [words, List.mem_map, ih, admissible]

private theorem prefix_nodup (b : Bool) (xs : List (List Bool)) (h : xs.Nodup) :
    (xs.map (b :: ·)).Nodup :=
  List.Pairwise.map _ (fun _ _ hne heq => hne (List.cons.inj heq).2) h

theorem words_nodup (n : Nat) (previous : Bool) : (words n previous).Nodup := by
  induction n generalizing previous with
  | zero => simp [words]
  | succ n ih =>
    cases previous with
    | false =>
      apply List.pairwise_append.mpr
      refine ⟨prefix_nodup false _ (ih false), prefix_nodup true _ (ih true), ?_⟩
      intro u hu v hv h
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
      cases h
    | true => simpa [words] using prefix_nodup false _ (ih false)

-- With both first-bit branches always available, this is the whole sample space.
def sample : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    let tails := sample n
    tails.map (false :: ·) ++ tails.map (true :: ·)

theorem sample_size (n : Nat) : (sample n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sample, ih, Nat.pow_succ, Nat.mul_two]

theorem mem_sample (n : Nat) (w : List Bool) : w ∈ sample n ↔ w.length = n := by
  induction n generalizing w with
  | zero => cases w <;> simp [sample]
  | succ n ih =>
    cases w with
    | nil => simp [sample]
    | cons b rest => cases b <;> simp [sample, List.mem_map, ih]

theorem sample_nodup (n : Nat) : (sample n).Nodup := by
  induction n with
  | zero => simp [sample]
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨prefix_nodup false _ ih, prefix_nodup true _ ih, ?_⟩
    intro u hu v hv h
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hu
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
    cases h

theorem split_at_first_bit (n : Nat) :
    openCount (n + 1) = openCount n + forcedCount n := rfl

theorem forced_zero (n : Nat) : forcedCount (n + 1) = openCount n := rfl

theorem two_step_recurrence (n : Nat) :
    openCount (n + 2) = openCount (n + 1) + openCount n :=
  Eq.trans (split_at_first_bit (n + 1))
    (congrArg (fun s => openCount (n + 1) + s) (forced_zero n))

theorem forced_le_open (n : Nat) : forcedCount n ≤ openCount n :=
  Nat.rec (motive := fun i => forcedCount i ≤ openCount i)
    (Nat.le_refl 1)
    (fun i _ =>
      have h : openCount i ≤ openCount i + forcedCount i :=
        Nat.le_add_right (openCount i) (forcedCount i)
      have h' : forcedCount (i + 1) ≤ openCount i + forcedCount i :=
        Nat.le_trans (Nat.le_of_eq (forced_zero i)) h
      Nat.le_trans h' (Nat.le_of_eq (split_at_first_bit i).symm)) n

theorem two_bit_bound (n : Nat) : openCount (n + 2) ≤ openCount n * 3 := by
  have expand : openCount (n + 2) = (openCount n + forcedCount n) + openCount n :=
    Eq.trans (two_step_recurrence n)
      (congrArg (fun s => s + openCount n) (split_at_first_bit n))
  have h : openCount n + forcedCount n ≤ openCount n + openCount n :=
    Nat.add_le_add_left (forced_le_open n) (openCount n)
  have triple : (openCount n + openCount n) + openCount n = openCount n * 3 :=
    congrArg (fun s => s + openCount n) (Nat.mul_two (openCount n)).symm
  have bound : (openCount n + forcedCount n) + openCount n ≤ openCount n * 3 :=
    Nat.le_trans (Nat.add_le_add_right h (openCount n)) (Nat.le_of_eq triple)
  exact Nat.le_trans (Nat.le_of_eq expand) bound

theorem exponential_bound (k : Nat) : openCount (2 * k) ≤ 3 ^ k :=
  Nat.rec (motive := fun i => openCount (2 * i) ≤ 3 ^ i)
    (Nat.le_refl 1)
    (fun i ih => Nat.le_trans (two_bit_bound (2 * i)) (Nat.mul_le_mul_right 3 ih)) k

end Counting580
