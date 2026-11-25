import proofs.Counting580

namespace Intersecting580

abbrev Word := List Bool
abbrev Family := Word → Bool

def complement (w : Word) : Word := w.map Bool.not

@[simp] theorem complement_twice (w : Word) : complement (complement w) = w := by
  induction w with
  | nil => rfl
  | cons b t ih => cases b <;> simp_all [complement, List.map_map, Function.comp_def]

-- A pair is indexed by the tail of the member containing the distinguished point.
def left (t : Word) : Word := true :: t
def right (t : Word) : Word := false :: complement t
def member (side : Bool) (tail : Word) := if side then left tail else right tail

theorem member_injective {a b : Bool} {s t : Word} (h : member a s = member b t) :
    a = b ∧ s = t := by
  cases a <;> cases b <;> simp_all [member, left, right]
  simpa only [complement_twice] using congrArg complement h

theorem member_surjective (n : Nat) (w : Word) (h : w.length = n + 1) :
    ∃ side t, t.length = n ∧ member side t = w := by
  cases w with
  | nil => simp at h
  | cons b t =>
    have ht : t.length = n := Nat.succ.inj h
    cases b with
    | false => exact ⟨false, complement t, by simpa [complement] using ht, by simp [member, right]⟩
    | true => exact ⟨true, t, ht, rfl⟩

def share : Word → Word → Bool
  | x :: xs, y :: ys => (x && y) || share xs ys
  | _, _ => false

theorem no_common_coordinate (t : Word) : share t (complement t) = false := by
  induction t with
  | nil => rfl
  | cons b t ih => cases b <;> simp_all [share, complement]

def Intersects (n : Nat) (f : Family) : Prop :=
  ∀ u v, u.length = n + 1 → v.length = n + 1 →
    f u = true → f v = true → share u v = true

def card (n : Nat) (f : Family) : Nat :=
  ((Counting580.sample n).filter (fun t => f (left t))).length +
  ((Counting580.sample n).filter (fun t => f (right t))).length

-- The pair census agrees with filtering all subsets directly.
private def ordinaryCount (n : Nat) (f : Family) := ((Counting580.sample n).filter f).length

private theorem count_prefixed (ts : List Word) (b : Bool) (f : Family) :
    ((ts.map (b :: ·)).filter f).length = (ts.filter (fun t => f (b :: t))).length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases hb : f (b :: t) <;> simp [List.filter_cons, hb, ih]

private theorem ordinary_split (n : Nat) (f : Family) :
    ordinaryCount (n + 1) f =
      ordinaryCount n (fun t => f (false :: t)) + ordinaryCount n (fun t => f (true :: t)) := by
  simp [ordinaryCount, Counting580.sample, count_prefixed]

private theorem complement_invariant (n : Nat) (f : Family) :
    ordinaryCount n (fun t => f (complement t)) = ordinaryCount n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [ordinary_split, ordinary_split]
    change ordinaryCount n (fun t => f (true :: complement t)) +
      ordinaryCount n (fun t => f (false :: complement t)) = _
    rw [ih (fun t => f (true :: t)), ih (fun t => f (false :: t)), Nat.add_comm]

theorem card_counts_selected_subsets (n : Nat) (f : Family) :
    card n f = ((Counting580.sample (n + 1)).filter f).length := by
  change ordinaryCount n (fun t => f (true :: t)) +
    ordinaryCount n (fun t => f (false :: complement t)) = ordinaryCount (n + 1) f
  rw [complement_invariant n (fun t => f (false :: t)), ordinary_split, Nat.add_comm]

private def missed (n : Nat) (f : Family) : Nat :=
  ((Counting580.sample n).filter fun t => !(f (left t) || f (right t))).length

private def doubled (n : Nat) (f : Family) : Nat :=
  ((Counting580.sample n).filter fun t => f (left t) && f (right t)).length

private theorem pair_tally (ts : List Word) (a b : Word → Bool) :
    (ts.filter a).length + (ts.filter b).length +
      (ts.filter (fun t => !(a t || b t))).length =
    ts.length + (ts.filter (fun t => a t && b t)).length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases ha : a t <;> cases hb : b t <;>
      simp only [List.filter_cons, ha, hb, Bool.false_or, Bool.true_or, Bool.not_false,
        Bool.not_true, Bool.false_and, Bool.true_and, ↓reduceIte, Bool.false_eq_true,
        List.length_cons] <;> omega

private theorem doubles_zero (n : Nat) (f : Family) (h : Intersects n f) :
    doubled n f = 0 := by
  apply List.length_eq_zero_iff.mpr
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro t ht
  obtain ⟨ht, hboth⟩ := List.mem_filter.mp ht
  have htlen := (Counting580.mem_sample n t).mp ht
  obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hboth
  have hc := h (left t) (right t) (by simp [left, htlen])
    (by simp [right, complement, htlen]) hl hr
  simp [left, right, share, no_common_coordinate] at hc

def star : Family
  | true :: _ => true
  | _ => false

private theorem star_intersects (n : Nat) : Intersects n star := by
  intro u v _ _ hu hv
  cases u with
  | nil => contradiction
  | cons a us =>
    cases v with
    | nil => contradiction
    | cons b vs => cases a <;> cases b <;> simp_all [star, share]

def starSize (n : Nat) := card n star

private theorem star_counts_tails (n : Nat) : starSize n = (Counting580.sample n).length := by
  change (((Counting580.sample n).filter (fun _ => true)).length +
    ((Counting580.sample n).filter (fun _ => false)).length = _)
  induction Counting580.sample n with
  | nil => rfl
  | cons _ ts ih => simpa [List.filter_cons, Nat.succ_add] using congrArg Nat.succ ih

-- Every attainable cardinality is included in this independent bounded maximum.
private def Attains (n k : Nat) := ∃ f, Intersects n f ∧ card n f = k

private noncomputable def search (p : Nat → Prop) (bound : Nat) : Nat := by
  classical
  exact match bound with
  | 0 => 0
  | k + 1 => if p (k + 1) then k + 1 else search p k

private theorem search_attained (p : Nat → Prop) (hz : p 0) (b : Nat) : p (search p b) := by
  classical
  induction b with
  | zero => exact hz
  | succ b ih => unfold search; split <;> assumption

private theorem le_search (p : Nat → Prop) (k b : Nat) (hp : p k) (hk : k ≤ b) :
    k ≤ search p b := by
  classical
  induction b with
  | zero => exact hk
  | succ b ih =>
    unfold search
    split
    · exact hk
    · rename_i hn
      have hne : k ≠ b + 1 := fun e => hn (e ▸ hp)
      exact ih (by omega)

noncomputable def maximumSize (n : Nat) := search (Attains n) (2 * (Counting580.sample n).length)

private theorem card_bounded (n : Nat) (f : Family) : card n f ≤ 2 * (Counting580.sample n).length := by
  have h := Nat.add_le_add (List.length_filter_le (fun t => f (left t)) (Counting580.sample n))
    (List.length_filter_le (fun t => f (right t)) (Counting580.sample n))
  simpa [card, Nat.two_mul] using h

private theorem maximum_attained (n : Nat) : Attains n (maximumSize n) := by
  apply search_attained
  exact ⟨fun _ => false, by simp [Intersects], by simp [card]⟩

private noncomputable def optimizer (n : Nat) := Classical.choose (maximum_attained n)
noncomputable def emptyPairs (n : Nat) := missed n (optimizer n)
noncomputable def doublePairs (n : Nat) := doubled n (optimizer n)

theorem census (n : Nat) :
    maximumSize n + emptyPairs n = 2 ^ n + doublePairs n := by
  have chosen := (Classical.choose_spec (maximum_attained n)).2
  rw [← chosen]
  exact (pair_tally (Counting580.sample n) (fun t => optimizer n (left t))
    (fun t => optimizer n (right t))).trans
    (congrArg (fun s => s + doublePairs n) (Counting580.sample_size n))

theorem complements_excluded (n : Nat) : doublePairs n = 0 :=
  doubles_zero n (optimizer n) (Classical.choose_spec (maximum_attained n)).1

theorem occupancy_bound (s e p d : Nat) (ht : s + e = p + d) (hd : d = 0) : s ≤ p := by
  have h : s + e = p := Eq.trans ht (Eq.trans (congrArg (fun x => p + x) hd) (Nat.add_zero p))
  exact Nat.le_trans (Nat.le_add_right s e) (Nat.le_of_eq h)

theorem maximum_upper (n : Nat) : maximumSize n ≤ 2 ^ n :=
  occupancy_bound (maximumSize n) (emptyPairs n) (2 ^ n) (doublePairs n)
    (census n) (complements_excluded n)

theorem star_initial : starSize 0 = 1 := rfl

theorem star_doubles (n : Nat) : starSize (n + 1) = starSize n * 2 := by
  simp [star_counts_tails, Counting580.sample_size, Nat.pow_succ]

theorem star_size (n : Nat) : starSize n = 2 ^ n :=
  Nat.rec (motive := fun k => starSize k = 2 ^ k) star_initial
    (fun i ih => Eq.trans (star_doubles i) (congrArg (fun x => x * 2) ih)) n

theorem star_competes (n : Nat) : starSize n ≤ maximumSize n :=
  le_search _ _ _ ⟨star, star_intersects n, rfl⟩ (card_bounded n star)

theorem exact_maximum (n : Nat) : maximumSize n = 2 ^ n :=
  Nat.le_antisymm (maximum_upper n)
    (Nat.le_trans (Nat.le_of_eq (star_size n).symm) (star_competes n))

end Intersecting580
