import Mathlib

/-!
# OEIS A397588

`A(x) = Σ_{n ≥ 1} a(n) xⁿ` is the power series with `A(x) = x + (x · A(x)²)'`.

Paul D. Hanna's conjecture in the entry says `a(n)` is odd if and only if `n` is a
power of `2` (for `n ≥ 1`). This is proved below as `A397588.odd_iff_pow_two`.

We also prove that `3 ∣ a(n)` for `n ≥ 2` (`A397588.three_dvd`). The entry states
this fact without a proof.

The sequence is defined by the recurrence `a(n) = (n+1) Σ_{k=1}^{n-1} a(k) a(n-k)`.
We show that its generating function satisfies the defining functional equation
(`gf_eq`). We also show that the equation has no other solution with zero
constant term (`gf_unique`), so this definition really is A397588.
-/

open PowerSeries Finset

namespace A397588

/-- `a 0 = 0`, `a 1 = 1`, and `a n = (n+1) Σ_{k=1}^{n-1} a(k) a(n-k)` for `n ≥ 2`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (n + 3) * ∑ k : Fin (n + 1), a (k + 1) * a (n + 1 - k)
decreasing_by all_goals (have := k.isLt; omega)

/-- The self-convolution `[xⁿ] A(x)²`. -/
def conv (n : ℕ) : ℕ := ∑ p ∈ antidiagonal n, a p.1 * a p.2

-- The first terms agree with the OEIS data.
unseal a in
example : (List.range 10).map a = [0, 1, 3, 24, 285, 4284, 75978, 1530720, 34237485, 837481140] := by
  decide +kernel

lemma conv_eq_fin (n : ℕ) :
    conv (n + 2) = ∑ k : Fin (n + 1), a (k + 1) * a (n + 1 - k) := by
  rw [conv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a i * a j),
    Finset.sum_range_succ, Finset.sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun k => a (k + 1) * a (n + 1 - k))]
  simp only [Nat.sub_self, Nat.sub_zero, a, mul_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  omega

/-- The recurrence in the form `a(n) = [n = 1] + (n+1) [xⁿ] A(x)²`. -/
lemma a_eq (n : ℕ) : a n = (if n = 1 then 1 else 0) + (n + 1) * conv n := by
  match n with
  | 0 => simp [a, conv]
  | 1 => simp [a, conv, Finset.Nat.antidiagonal_succ]
  | n + 2 => rw [conv_eq_fin, a]; simp

/-! ### The generating function -/

/-- The generating function `A(x) = Σ a(n) xⁿ` over `ℤ`. -/
noncomputable def A : ℤ⟦X⟧ := PowerSeries.mk fun n => (a n : ℤ)

lemma coeff_rhs (B : ℤ⟦X⟧) (n : ℕ) :
    coeff n (X + d⁄dX (X * B ^ 2)) =
      (if n = 1 then 1 else 0) + (n + 1) * ∑ p ∈ antidiagonal n, coeff p.1 B * coeff p.2 B := by
  rw [map_add, coeff_X, coeff_derivative, coeff_succ_X_mul, pow_two, coeff_mul]
  ring

/-- `A(x) = x + (x · A(x)²)'`. -/
theorem gf_eq : A = X + d⁄dX (X * A ^ 2) := by
  ext n
  rw [coeff_rhs]
  simp only [A, coeff_mk]
  rw [a_eq n, conv]
  push_cast
  split_ifs <;> simp

/-- The functional equation has exactly one solution with zero constant term. -/
theorem gf_unique (B : ℤ⟦X⟧) (h0 : constantCoeff B = 0)
    (hB : B = X + d⁄dX (X * B ^ 2)) : B = A := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [A, a, h0]
    have hsum : ∑ p ∈ antidiagonal n, coeff p.1 B * coeff p.2 B =
        ∑ p ∈ antidiagonal n, coeff p.1 A * coeff p.2 A := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [HasAntidiagonal.mem_antidiagonal] at hp
      rcases Nat.eq_zero_or_pos p.1 with h1 | h1
      · simp [h1, h0, A, a]
      rcases Nat.eq_zero_or_pos p.2 with h2 | h2
      · simp [h2, h0, A, a]
      rw [ih p.1 (by omega), ih p.2 (by omega)]
    rw [hB, coeff_rhs, hsum, ← coeff_rhs, ← gf_eq]

/-! ### Parity -/

/-- Over `ZMod 2`, `[xⁿ] F(x)² = [xⁿ] F(x²)`. -/
lemma conv_zmod_two (f : ℕ → ZMod 2) (n : ℕ) :
    ∑ p ∈ antidiagonal n, f p.1 * f p.2 = if Even n then f (n / 2) else 0 := by
  have hsplit : ∀ p : ℕ × ℕ, f p.1 * f p.2 =
      (if p.1 = p.2 then f p.1 * f p.2 else 0) + (if p.1 = p.2 then 0 else f p.1 * f p.2) := by
    intro p; split_ifs <;> simp
  rw [Finset.sum_congr rfl fun p _ => hsplit p, Finset.sum_add_distrib]
  have hoff : ∑ p ∈ antidiagonal n, (if p.1 = p.2 then 0 else f p.1 * f p.2) = 0 := by
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap, eq_comm (a := p.2)]
      split_ifs
      · simp
      · rw [mul_comm (f p.2), CharTwo.add_self_eq_zero]
    · intro p _ hp h
      apply hp
      have : p.1 = p.2 := congrArg Prod.snd h
      simp [this]
    · intro p hp; rw [HasAntidiagonal.mem_antidiagonal] at hp ⊢; simp [add_comm, hp]
    · intro p _; simp
  rw [hoff, add_zero]
  split_ifs with he
  · obtain ⟨m, rfl⟩ := he
    rw [Finset.sum_eq_single (m, m)]
    · have : (m + m) / 2 = m := by omega
      simp only [ite_true, this]
      generalize f m = x
      revert x; decide
    · intro p hp hne
      rw [HasAntidiagonal.mem_antidiagonal] at hp
      rw [ite_eq_right]
      intro h; apply hne; ext <;> simp <;> omega
    · intro h; simp at h
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rw [ite_eq_right]
    intro h; exact he ⟨p.1, by omega⟩

lemma a_mod_two (n : ℕ) :
    (a n : ZMod 2) = (if n = 1 then 1 else 0) + (n + 1) * (if Even n then (a (n / 2) : ZMod 2) else 0) := by
  rw [a_eq n, conv]
  push_cast
  rw [conv_zmod_two (fun k => (a k : ZMod 2))]

lemma pow_two_iff_half (m : ℕ) (hm : 1 ≤ m) :
    (∃ k, 2 * m = 2 ^ k) ↔ ∃ k, m = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by ring⟩

/-- **Hanna's conjecture.** For `n ≥ 1`, `a(n)` is odd iff `n` is a power of two. -/
theorem odd_iff_pow_two (n : ℕ) (hn : 1 ≤ n) : Odd (a n) ↔ ∃ k, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [← ZMod.natCast_eq_one_iff_odd, a_mod_two]
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | hodd
    · -- `n = 2m` with `m ≥ 1`: `a(2m) ≡ a(m)`
      have hm : 1 ≤ m := by omega
      have h2 : ((m + m : ℕ) : ZMod 2) = 0 := by
        rw [ZMod.natCast_eq_zero_iff_even]; exact ⟨m, rfl⟩
      rw [ite_eq_right (by omega), ite_eq_left ⟨m, rfl⟩, h2, show (m + m) / 2 = m by omega, zero_add,
        zero_add, one_mul, ZMod.natCast_eq_one_iff_odd, ih m (by omega) hm, ← two_mul,
        pow_two_iff_half m hm]
    · -- `n` odd
      rw [ite_eq_right (Nat.not_even_iff_odd.2 hodd), mul_zero, add_zero]
      by_cases h1 : n = 1
      · subst h1; simp; exact ⟨0, rfl⟩
      · rw [ite_eq_right h1]
        simp only [zero_ne_one, false_iff]
        rintro ⟨k, rfl⟩
        cases k with
        | zero => exact h1 rfl
        | succ k =>
          exact Nat.not_even_iff_odd.2 hodd ⟨2 ^ k, by ring⟩

/-! ### Divisibility by 3 -/

/-- `3 ∣ a(n)` for every `n ≥ 2`. -/
theorem three_dvd (n : ℕ) (hn : 2 ≤ n) : 3 ∣ a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [a_eq, ite_eq_right (by omega), zero_add]
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      exact ⟨conv 2, by ring⟩
    apply Dvd.dvd.mul_left
    refine Finset.dvd_sum fun p hp => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hp
    rcases Nat.eq_zero_or_pos p.1 with h0 | h0
    · simp [h0, a]
    rcases Nat.eq_zero_or_pos p.2 with h0' | h0'
    · simp [h0', a]
    rcases Nat.lt_or_ge p.1 2 with h1 | h1
    · exact Dvd.dvd.mul_left (ih p.2 (by omega) (by omega)) _
    · exact Dvd.dvd.mul_right (ih p.1 (by omega) h1) _

end A397588
