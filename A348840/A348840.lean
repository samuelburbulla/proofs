import Mathlib

/-!
# OEIS A348840

`T(n,h)` is the number of Motzkin paths of `n ≥ 2` steps that start with an Up step and touch
the horizontal axis `h ≥ 1` times afterwards. To touch means: the path reaches the horizontal
line with a down-step, or it is at the horizontal level and takes another horizontal step.

R. J. Mathar conjectured (2021):
* `T(n, n-2) = n - 2`;
* `T(n, n-3) = A000124(n-3)`, where `A000124(m) = m(m+1)/2 + 1`;
* `T(n, n-4) = -11 + 19n/3 - 3n²/2 + n³/6`.

We prove all three (`A348840.T_sub_two`, `A348840.T_sub_three`, `A348840.T_sub_four`).

Let `C(ℓ, y, t)` count the step sequences of length `ℓ` that start at height `y`, never go
below the axis, end on the axis and touch it `t` times. Splitting off the first step gives a
recursion for `C` (`A348840.C_eq`), and `T(n+1, h) = C(n, 1, h)`. Along the diagonals
`t = ℓ - e` with `e ≤ 3`, the recursion only involves finitely many heights, and it can be
solved in closed form by induction.
-/

namespace A348840

/-- The three kinds of steps: up, horizontal, down. -/
inductive Step
  | U
  | H
  | D
  deriving DecidableEq, Repr

open Step

/-- All step sequences of length `ℓ`. -/
def words : ℕ → List (List Step)
  | 0 => [[]]
  | ℓ + 1 => [U, H, D].flatMap fun s => (words ℓ).map (s :: ·)

lemma mem_words {ℓ : ℕ} {w : List Step} : w ∈ words ℓ ↔ w.length = ℓ := by
  induction ℓ generalizing w with
  | zero => simp [words, List.length_eq_zero_iff]
  | succ ℓ ih =>
    cases w with
    | nil => simp [words]
    | cons s w => cases s <;> simp [words, ih]

lemma nodup_words (ℓ : ℕ) : (words ℓ).Nodup := by
  induction ℓ with
  | zero => simp [words]
  | succ ℓ ih =>
    simp only [words, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine List.Nodup.append (ih.map (fun _ _ h => by simpa using h))
      (List.Nodup.append (ih.map (fun _ _ h => by simpa using h))
        (ih.map (fun _ _ h => by simpa using h)) ?_) ?_
    · intro a ha hb; simp only [List.mem_map] at ha hb
      obtain ⟨_, _, rfl⟩ := ha; obtain ⟨_, _, h⟩ := hb; simp at h
    · intro a ha hb; simp only [List.mem_map, List.mem_append] at ha hb
      obtain ⟨_, _, rfl⟩ := ha
      rcases hb with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> simp at h

/-- `ok y w`: the path `w` started at height `y` never goes below the axis and ends on it. -/
def ok : ℕ → List Step → Bool
  | y, [] => y == 0
  | y, U :: w => ok (y + 1) w
  | y, H :: w => ok y w
  | 0, D :: _ => false
  | y + 1, D :: w => ok y w

/-- `tc y w`: the number of steps of `w` (started at height `y`) that end on the axis, i.e. a
horizontal step on the axis or a down-step onto it. -/
def tc : ℕ → List Step → ℕ
  | _, [] => 0
  | y, U :: w => tc (y + 1) w
  | y, H :: w => (if y = 0 then 1 else 0) + tc y w
  | 0, D :: w => tc 0 w
  | y + 1, D :: w => (if y = 0 then 1 else 0) + tc y w

/-- **The triangle.** Motzkin paths of `n` steps starting with an up-step and touching the axis
`h` times afterwards. -/
def T (n h : ℕ) : ℕ :=
  ((words n).filter fun w => w.head? == some U && ok 0 w && tc 0 w == h).length

-- Sanity check against the OEIS rows `n = 2, …, 8`.
example : (List.range 7).map (fun i => (List.range (i + 1)).map fun j => T (i + 2) (j + 1)) =
    [[1], [1, 1], [2, 2, 1], [4, 4, 3, 1], [9, 9, 7, 4, 1], [21, 21, 17, 11, 5, 1],
      [51, 51, 42, 29, 16, 6, 1]] := by
  decide +kernel

/-- Paths from height `y` of length `ℓ` with `t` touches. -/
def Ccomb (ℓ y t : ℕ) : ℕ := ((words ℓ).filter fun w => ok y w && tc y w == t).length

/-- The same count, as a recursion on the first step. -/
def C : ℕ → ℕ → ℕ → ℕ
  | 0, y, t => if y = 0 ∧ t = 0 then 1 else 0
  | ℓ + 1, 0, t => C ℓ 1 t + (match t with | 0 => 0 | t + 1 => C ℓ 0 t)
  | ℓ + 1, 1, t => C ℓ 2 t + C ℓ 1 t + (match t with | 0 => 0 | t + 1 => C ℓ 0 t)
  | ℓ + 1, y + 2, t => C ℓ (y + 3) t + C ℓ (y + 2) t + C ℓ (y + 1) t

lemma length_filter_words_succ (ℓ : ℕ) (P : List Step → Bool) :
    ((words (ℓ + 1)).filter P).length =
      ((words ℓ).filter fun w => P (U :: w)).length +
      ((words ℓ).filter fun w => P (H :: w)).length +
      ((words ℓ).filter fun w => P (D :: w)).length := by
  simp only [words, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.filter_append,
    List.length_append, List.filter_map, List.length_map, Function.comp_def, add_assoc]

lemma length_filter_false (l : List (List Step)) :
    (l.filter fun _ => false).length = 0 := by simp

lemma sU (ℓ y t : ℕ) :
    ((words ℓ).filter fun w => ok y (U :: w) && tc y (U :: w) == t).length =
      Ccomb ℓ (y + 1) t := rfl

lemma sH (ℓ y t : ℕ) :
    ((words ℓ).filter fun w => ok y (H :: w) && tc y (H :: w) == t).length =
      if y = 0 then (match t with | 0 => 0 | t + 1 => Ccomb ℓ 0 t) else Ccomb ℓ y t := by
  rcases y with _ | y
  · rcases t with _ | t
    · simp [ok, tc]
    · simp only [ok, tc, ite_true, Ccomb]
      congr 1
      apply List.filter_congr
      intro w _
      simp [add_comm]
  · simp only [ok, tc, Ccomb, Nat.add_one_ne_zero, ite_false, zero_add]

lemma sD (ℓ y t : ℕ) :
    ((words ℓ).filter fun w => ok y (D :: w) && tc y (D :: w) == t).length =
      match y with
      | 0 => 0
      | 1 => (match t with | 0 => 0 | t + 1 => Ccomb ℓ 0 t)
      | y + 2 => Ccomb ℓ (y + 1) t := by
  rcases y with _ | _ | y
  · simp [ok]
  · rcases t with _ | t
    · simp [ok, tc]
    · simp only [ok, tc, ite_true, Ccomb]
      congr 1
      apply List.filter_congr
      intro w _
      simp [add_comm]
  · simp only [ok, tc, Ccomb, Nat.add_one_ne_zero, ite_false, zero_add]

/-- The combinatorial count satisfies the recursion. -/
theorem Ccomb_eq_C (ℓ y t : ℕ) : Ccomb ℓ y t = C ℓ y t := by
  induction ℓ generalizing y t with
  | zero =>
    by_cases h : y = 0 ∧ t = 0
    · obtain ⟨rfl, rfl⟩ := h; simp [Ccomb, words, ok, tc, C]
    · simp only [Ccomb, words, C, ite_eq_right_iff.2 (fun h' => absurd h' h)]
      simp only [List.filter_cons, List.filter_nil, ok, tc]
      rcases Nat.eq_zero_or_pos y with rfl | hy
      · have : t ≠ 0 := fun ht => h ⟨rfl, ht⟩
        simp [Ne.symm this]
      · simp [Nat.pos_iff_ne_zero.1 hy]
  | succ ℓ ih =>
    have e : Ccomb (ℓ + 1) y t =
        ((words ℓ).filter fun w => ok y (U :: w) && tc y (U :: w) == t).length +
        ((words ℓ).filter fun w => ok y (H :: w) && tc y (H :: w) == t).length +
        ((words ℓ).filter fun w => ok y (D :: w) && tc y (D :: w) == t).length :=
      length_filter_words_succ ℓ _
    rw [e, sU, sH, sD]
    rcases y with _ | _ | y <;> rcases t with _ | t <;> simp [C, ih]

/-- `T(n+1, h) = C(n, 1, h)`: after the first up-step we are at height `1`. -/
theorem T_eq_C (n h : ℕ) : T (n + 1) h = C n 1 h := by
  rw [← Ccomb_eq_C]
  unfold T Ccomb
  rw [length_filter_words_succ]
  simp [ok, tc]

/-! ### Closed forms along the diagonals -/

lemma C_zero_succ (ℓ t : ℕ) : C (ℓ + 1) 0 (t + 1) = C ℓ 1 (t + 1) + C ℓ 0 t := rfl
lemma C_zero_zero (ℓ : ℕ) : C (ℓ + 1) 0 0 = C ℓ 1 0 := rfl
lemma C_one_succ (ℓ t : ℕ) : C (ℓ + 1) 1 (t + 1) = C ℓ 2 (t + 1) + C ℓ 1 (t + 1) + C ℓ 0 t := rfl
lemma C_two (ℓ t : ℕ) : C (ℓ + 1) 2 t = C ℓ 3 t + C ℓ 2 t + C ℓ 1 t := rfl

/-- `C(ℓ, y, t) = 0` when there are too many touches. -/
lemma C_eq_zero : ∀ ℓ y t, ℓ + 2 ≤ t + y + (if y = 0 then 1 else 0) → C ℓ y t = 0 := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro y t h
    simp only [C]
    split_ifs with h1
    · obtain ⟨rfl, rfl⟩ := h1; simp at h
    · rfl
  | succ ℓ ih =>
    intro y t h
    rcases y with _ | _ | y
    · rcases t with _ | t
      · simp at h
      · rw [C_zero_succ, ih 1 (t + 1) (by simp at h ⊢; omega), ih 0 t (by simp at h ⊢; omega)]
    · rcases t with _ | t
      · simp at h
      · rw [C_one_succ, ih 2 (t + 1) (by simp at h ⊢; omega), ih 1 (t + 1) (by simp at h ⊢; omega),
          ih 0 t (by simp at h ⊢; omega)]
    · show C ℓ (y + 3) t + C ℓ (y + 2) t + C ℓ (y + 1) t = 0
      rw [ih (y + 3) t (by simp at h ⊢; omega), ih (y + 2) t (by simp at h ⊢; omega),
        ih (y + 1) t (by simp at h ⊢; omega)]

lemma C0a (m : ℕ) : C m 0 m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [C_zero_succ, C_eq_zero m 1 (m + 1) (by simp), ih]

lemma C0b (m : ℕ) : C (m + 1) 1 (m + 1) = 1 := by
  rw [C_one_succ, C_eq_zero m 2 (m + 1) (by simp), C_eq_zero m 1 (m + 1) (by simp), C0a]

lemma C0c (m : ℕ) : C (m + 2) 2 (m + 1) = 1 := by
  rw [C_two, C_eq_zero (m + 1) 3 (m + 1) (by simp), C_eq_zero (m + 1) 2 (m + 1) (by simp), C0b]

lemma C1a (m : ℕ) : C (m + 1) 0 m = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [C_zero_succ, C0b, ih]; omega

lemma C1b (m : ℕ) : C (m + 2) 1 (m + 1) = m + 1 := by
  rw [C_one_succ, C_eq_zero (m + 1) 2 (m + 1) (by simp), C0b, C1a]; omega

lemma C1c (m : ℕ) : C (m + 3) 2 (m + 1) = m + 2 := by
  rw [C_two, C_eq_zero (m + 2) 3 (m + 1) (by simp), C0c, C1b]; omega

lemma C2a (m : ℕ) : 2 * C (m + 2) 0 m = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [C_zero_succ, mul_add, C1b, ih]; ring

lemma C2b (m : ℕ) : 2 * C (m + 3) 1 (m + 1) = 2 * (m + 2) + m * (m + 1) := by
  rw [C_one_succ, mul_add, mul_add, C0c, C1b, C2a]; ring

lemma C3a (m : ℕ) : 6 * C (m + 3) 0 m = m ^ 3 + 3 * m ^ 2 + 8 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h := C2b m
    have : 6 * C (m + 3) 1 (m + 1) = 3 * (2 * (m + 2) + m * (m + 1)) := by rw [← h]; ring
    rw [C_zero_succ, mul_add, this, ih]; ring

lemma C3b (m : ℕ) : 6 * C (m + 4) 1 (m + 1) = m ^ 3 + 6 * m ^ 2 + 23 * m + 24 := by
  have h := C2b m
  have : 6 * C (m + 3) 1 (m + 1) = 3 * (2 * (m + 2) + m * (m + 1)) := by rw [← h]; ring
  rw [C_one_succ, mul_add, mul_add, C1c, this, C3a]; ring

/-! ### Mathar's conjectures -/

/-- **Conjecture 1.** `T(n, n-2) = n - 2` for `n ≥ 3`. -/
theorem T_sub_two (n : ℕ) (hn : 3 ≤ n) : T n (n - 2) = n - 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 2 = m + 1 by omega, show m + 3 = (m + 2) + 1 by omega, T_eq_C, C1b]

/-- The lazy caterer's sequence A000124: `m(m+1)/2 + 1`. -/
def A000124 (m : ℕ) : ℕ := m * (m + 1) / 2 + 1

/-- **Conjecture 2.** `T(n, n-3) = A000124(n-3)` for `n ≥ 4`. -/
theorem T_sub_three (n : ℕ) (hn : 4 ≤ n) : T n (n - 3) = A000124 (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 3 = m + 1 by omega, show m + 4 = (m + 3) + 1 by omega, T_eq_C, A000124]
  have h := C2b m
  have e : (m + 1) * (m + 1 + 1) = 2 * (C (m + 3) 1 (m + 1) - 1) := by
    have : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by ring
    omega
  rw [e, Nat.mul_div_cancel_left _ two_pos]
  omega

/-- **Conjecture 3.** `T(n, n-4) = -11 + 19n/3 - 3n²/2 + n³/6` for `n ≥ 5`. -/
theorem T_sub_four (n : ℕ) (hn : 5 ≤ n) :
    (T n (n - 4) : ℚ) = -11 + 19 * n / 3 - 3 * n ^ 2 / 2 + n ^ 3 / 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 4 = m + 1 by omega, show m + 5 = (m + 4) + 1 by omega, T_eq_C]
  have h : ((6 * C (m + 4) 1 (m + 1) : ℕ) : ℚ) = ((m ^ 3 + 6 * m ^ 2 + 23 * m + 24 : ℕ) : ℚ) := by
    rw [C3b]
  push_cast at h ⊢
  linarith

end A348840

#print axioms A348840.T_sub_four
#print axioms A348840.T_sub_three
#print axioms A348840.T_sub_two
