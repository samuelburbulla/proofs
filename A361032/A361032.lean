import Mathlib

/-!
# OEIS A361032 (and its rows A361033, A361034, A361035)

Peter Bala's square array

  `T(n,k) = F(n) · (4k)! / (k! · (k+n+1)!³)`,   `F(n) = (4n+4)! / (8 · (n+1)!)`.

The entry says this choice of `F(n)` "appears to produce integer values". Its first three
rows are A361033 (`3·(4k)!/(k!(k+1)!³)`), A361034 (`2520·(4k)!/(k!(k+2)!³)`) and A361035
(`9979200·(4k)!/(k!(k+3)!³)`). Each row comes with a parity conjecture:

* A361033: `a(k)` is odd iff `k = 2ʲ - 1`;
* A361034: `a(k)` is odd iff `k = 2ʲ - 2` (`j ≥ 1`);
* A361035: `a(k)` is odd iff `k = 2ʲ - 3` (`j ≥ 2`).

We prove:

* `A361032.den_dvd_num`: every `T(n,k)` is an integer;
* `A361032.T_cast`: `T(n,k)` is Bala's expression, computed in `ℚ`;
* `A361032.padicValNat_two_T`: `v₂(T(n,k)) = 3·(M - 1 - v₂(M!))` with `M = n+k+1`.
  Equivalently `v₂(T(n,k)) = 3·(s₂(M) - 1)`, where `s₂` is the binary digit sum;
* `A361032.odd_T_iff`: `T(n,k)` is odd iff `n + k + 1` is a power of 2;
* `A361033_odd_iff`, `A361034_odd_iff`, `A361035_odd_iff`: the three conjectures.
-/

open Nat Finset

namespace A361032

/-! ### 2-adic valuations of factorials -/

/-- `v₂((4m)!) = v₂(m!) + 3m`. -/
lemma v2_four_mul (m : ℕ) :
    padicValNat 2 (4 * m)! = padicValNat 2 m ! + 3 * m := by
  have h1 := padicValNat_factorial_mul (p := 2) (2 * m)
  have h2 := padicValNat_factorial_mul (p := 2) m
  rw [show 4 * m = 2 * (2 * m) by ring, h1, h2]
  ring

/-- `v₂((2m+1)!) = v₂((2m)!)`. -/
lemma v2_odd (m : ℕ) : padicValNat 2 (2 * m + 1)! = padicValNat 2 (2 * m)! := by
  rw [factorial_succ, padicValNat.mul (by omega) (factorial_ne_zero _),
    padicValNat.eq_zero_of_not_dvd (by omega), zero_add]

/-- For `m ≥ 1`: `v₂(m!) ≤ m - 1`, with equality iff `m` is a power of 2. -/
lemma v2_factorial (m : ℕ) (hm : 1 ≤ m) :
    padicValNat 2 m ! + 1 ≤ m ∧ (padicValNat 2 m ! + 1 = m ↔ ∃ j, m = 2 ^ j) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hj : 1 ≤ j := by omega
      obtain ⟨ih1, ih2⟩ := ih j (by omega) hj
      rw [← two_mul, padicValNat_factorial_mul]
      refine ⟨by omega, ?_⟩
      rw [show padicValNat 2 j ! + j + 1 = 2 * j ↔ padicValNat 2 j ! + 1 = j by omega, ih2]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i + 1, by ring⟩
      · rintro ⟨i, hi⟩
        cases i with
        | zero => omega
        | succ i => exact ⟨i, by rw [pow_succ] at hi; omega⟩
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp; exact ⟨0, rfl⟩
      obtain ⟨ih1, -⟩ := ih j (by omega) hj
      rw [v2_odd, padicValNat_factorial_mul]
      refine ⟨by omega, ?_⟩
      constructor
      · intro h; omega
      · rintro ⟨i, hi⟩
        cases i with
        | zero => omega
        | succ i => rw [pow_succ] at hi; omega

/-! ### Legendre's inequality for all primes -/

/-- `⌊N/q⌋ + ⌊k/q⌋ + 3⌊(N+k)/q⌋ ≤ ⌊4N/q⌋ + ⌊4k/q⌋`. -/
lemma floor_ineq (N k q : ℕ) (hq : 0 < q) :
    N / q + k / q + 3 * ((N + k) / q) ≤ 4 * N / q + 4 * k / q := by
  set a := N / q
  set b := k / q
  set c := (N + k) / q
  set x := 4 * N / q
  set y := 4 * k / q
  have ha : a * q ≤ N := Nat.div_mul_le_self N q
  have hb : b * q ≤ k := Nat.div_mul_le_self k q
  have hc : c * q ≤ N + k := Nat.div_mul_le_self (N + k) q
  have hx : 4 * a ≤ x := (Nat.le_div_iff_mul_le hq).2 (by nlinarith)
  have hy : 4 * b ≤ y := (Nat.le_div_iff_mul_le hq).2 (by nlinarith)
  have hN : N < (a + 1) * q := by
    have := Nat.lt_mul_div_succ N hq; rw [Nat.mul_comm q] at this; exact this
  have hk : k < (b + 1) * q := by
    have := Nat.lt_mul_div_succ k hq; rw [Nat.mul_comm q] at this; exact this
  have h4N : 4 * N < (x + 1) * q := by
    have := Nat.lt_mul_div_succ (4 * N) hq; rw [Nat.mul_comm q] at this; exact this
  have h4k : 4 * k < (y + 1) * q := by
    have := Nat.lt_mul_div_succ (4 * k) hq; rw [Nat.mul_comm q] at this; exact this
  have hc' : c ≤ a + b + 1 := by
    by_contra h
    have : (a + b + 2) * q ≤ c * q := Nat.mul_le_mul_right q (by omega)
    nlinarith
  rcases Nat.lt_or_ge c (a + b + 1) with h | h
  · omega
  · -- `c = a + b + 1`
    have hcq : 4 * ((a + b + 1) * q) ≤ 4 * N + 4 * k := by
      have : (a + b + 1) * q ≤ c * q := Nat.mul_le_mul_right q h
      omega
    have : (4 * (a + b + 1)) * q < (x + y + 2) * q := by nlinarith
    have := Nat.lt_of_mul_lt_mul_right this
    omega

/-! ### The array -/

/-- Numerator `(4n+4)! (4k)!`. -/
def num (n k : ℕ) : ℕ := (4 * (n + 1))! * (4 * k)!

/-- Denominator `8 (n+1)! k! (n+k+1)!³`. -/
def den (n k : ℕ) : ℕ := 8 * ((n + 1)! * k ! * (n + k + 1)! ^ 3)

/-- `T(n,k) = F(n) (4k)! / (k! (k+n+1)!³)` with `F(n) = (4n+4)!/(8 (n+1)!)`. -/
def T (n k : ℕ) : ℕ := num n k / den n k

lemma num_ne_zero (n k : ℕ) : num n k ≠ 0 := by
  unfold num; positivity

lemma den_ne_zero (n k : ℕ) : den n k ≠ 0 := by
  unfold den; positivity

lemma v_num (p : ℕ) [Fact p.Prime] (n k : ℕ) :
    padicValNat p (num n k) = padicValNat p (4 * (n + 1))! + padicValNat p (4 * k)! := by
  unfold num
  rw [padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _)]

lemma v_den (p : ℕ) [Fact p.Prime] (n k : ℕ) :
    padicValNat p (den n k) = padicValNat p 8 + (padicValNat p (n + 1)! +
      padicValNat p k ! + 3 * padicValNat p (n + k + 1)!) := by
  unfold den
  rw [padicValNat.mul (by norm_num) (by positivity),
    padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul (factorial_ne_zero _) (factorial_ne_zero _), padicValNat.pow _ _]

lemma v2_eight : padicValNat 2 8 = 3 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]

lemma vp_eight (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : padicValNat p 8 = 0 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.pow, padicValNat_primes hp, mul_zero]

/-- Every entry of the array is an integer. -/
theorem den_dvd_num (n k : ℕ) : den n k ∣ num n k := by
  rw [← Nat.factorization_prime_le_iff_dvd (den_ne_zero n k) (num_ne_zero n k)]
  intro p hp
  have := Fact.mk hp
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, v_num, v_den]
  by_cases h2 : p = 2
  · subst h2
    rw [v2_eight, v2_four_mul, v2_four_mul]
    have := (v2_factorial (n + k + 1) (by omega)).1
    omega
  · rw [vp_eight p h2, zero_add]
    -- Legendre's formula with a common bound `b`
    set N := n + 1
    set b := 4 * (N + k) + 1
    have hlog : ∀ x ≤ 4 * (N + k), Nat.log p x < b := fun x hx =>
      lt_of_le_of_lt (Nat.log_le_self p x) (by omega)
    rw [padicValNat_factorial (hlog (4 * N) (by omega)),
      padicValNat_factorial (hlog (4 * k) (by omega)),
      padicValNat_factorial (hlog N (by omega)), padicValNat_factorial (hlog k (by omega)),
      show n + k + 1 = N + k by omega, padicValNat_factorial (hlog (N + k) (by omega)),
      mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_le_sum fun i _ => floor_ineq N k (p ^ i) (pow_pos hp.pos i)

lemma T_mul_den (n k : ℕ) : T n k * den n k = num n k :=
  Nat.div_mul_cancel (den_dvd_num n k)

lemma T_ne_zero (n k : ℕ) : T n k ≠ 0 := by
  intro h
  have := T_mul_den n k
  rw [h, zero_mul] at this
  exact num_ne_zero n k this.symm

/-- `T(n,k)` equals Bala's expression `F(n) (4k)!/(k! (k+n+1)!³)`, computed in `ℚ`. -/
theorem T_cast (n k : ℕ) :
    (T n k : ℚ) = ((4 * n + 4)! / (8 * (n + 1)!) : ℚ) * (4 * k)! / (k ! * (k + n + 1)! ^ 3) := by
  rw [T, Nat.cast_div (den_dvd_num n k) (by exact_mod_cast den_ne_zero n k), num, den]
  rw [show 4 * n + 4 = 4 * (n + 1) by ring, show k + n + 1 = n + k + 1 by ring]
  push_cast
  field_simp

/-- `v₂(T(n,k)) = 3 (M - 1 - v₂(M!))` with `M = n + k + 1`. -/
theorem padicValNat_two_T (n k : ℕ) :
    padicValNat 2 (T n k) = 3 * (n + k + 1 - 1 - padicValNat 2 (n + k + 1)!) := by
  have h := congrArg (padicValNat 2) (T_mul_den n k)
  rw [padicValNat.mul (T_ne_zero n k) (den_ne_zero n k), v_num, v_den, v2_eight, v2_four_mul,
    v2_four_mul] at h
  have := (v2_factorial (n + k + 1) (by omega)).1
  omega

/-- **Parity of the array.** `T(n,k)` is odd iff `n + k + 1` is a power of 2. -/
theorem odd_T_iff (n k : ℕ) : Odd (T n k) ↔ ∃ j, n + k + 1 = 2 ^ j := by
  rw [← (v2_factorial (n + k + 1) (by omega)).2]
  have hv := padicValNat_two_T n k
  have hle := (v2_factorial (n + k + 1) (by omega)).1
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, ← not_iff_not, not_not]
  constructor
  · intro hdvd h
    have : 1 ≤ padicValNat 2 (T n k) := by
      rw [← padicValNat_dvd_iff_le (T_ne_zero n k), pow_one]; exact hdvd
    omega
  · intro h
    by_contra hnd
    rw [padicValNat.eq_zero_of_not_dvd hnd] at hv
    omega

/-! ### The three rows -/

/-- A361033: `a(k) = 3·(4k)!/(k!·(k+1)!³)`. -/
def A361033 (k : ℕ) : ℕ := 3 * (4 * k)! / (k ! * (k + 1)! ^ 3)

/-- A361034: `a(k) = 2520·(4k)!/(k!·(k+2)!³)`. -/
def A361034 (k : ℕ) : ℕ := 2520 * (4 * k)! / (k ! * (k + 2)! ^ 3)

/-- A361035: `a(k) = 9979200·(4k)!/(k!·(k+3)!³)`. -/
def A361035 (k : ℕ) : ℕ := 9979200 * (4 * k)! / (k ! * (k + 3)! ^ 3)

-- The first terms agree with the OEIS data.
example : (List.range 4).map A361033 = [3, 9, 280, 17325] := by decide +kernel
example : (List.range 3).map A361034 = [315, 280, 3675] := by decide +kernel
example : (List.range 2).map A361035 = [46200, 17325] := by decide +kernel

/-- Row `n` of the array is `c·(4k)!/(k!·(k+n+1)!³)` with `c = (4n+4)!/(8·(n+1)!)`. -/
lemma row_eq (n c : ℕ) (hc : (4 * (n + 1))! = c * (8 * (n + 1)!)) (k : ℕ) :
    T n k = c * (4 * k)! / (k ! * (k + n + 1)! ^ 3) := by
  rw [T, num, den, hc, show k + n + 1 = n + k + 1 by ring,
    show c * (8 * (n + 1)!) * (4 * k)! = (8 * (n + 1)!) * (c * (4 * k)!) by ring,
    show 8 * ((n + 1)! * k ! * (n + k + 1)! ^ 3) = (8 * (n + 1)!) * (k ! * (n + k + 1)! ^ 3)
      by ring]
  exact Nat.mul_div_mul_left _ _ (by positivity)

lemma A361033_eq (k : ℕ) : A361033 k = T 0 k := by
  rw [row_eq 0 3 (by decide) k]; rfl

lemma A361034_eq (k : ℕ) : A361034 k = T 1 k := by
  rw [row_eq 1 2520 (by decide) k]; rfl

lemma A361035_eq (k : ℕ) : A361035 k = T 2 k := by
  rw [row_eq 2 9979200 (by decide) k]; rfl

/-- **Bala's conjecture for A361033.** `a(k)` is odd iff `k = 2ʲ - 1`. -/
theorem A361033_odd_iff (k : ℕ) : Odd (A361033 k) ↔ ∃ j, k = 2 ^ j - 1 := by
  rw [A361033_eq, odd_T_iff]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j, by omega⟩
  · rintro ⟨j, hj⟩; exact ⟨j, by have := Nat.one_le_two_pow (n := j); omega⟩

/-- **Bala's conjecture for A361034.** `a(k)` is odd iff `k = 2ʲ - 2` with `j ≥ 1`. -/
theorem A361034_odd_iff (k : ℕ) : Odd (A361034 k) ↔ ∃ j ≥ 1, k = 2 ^ j - 2 := by
  rw [A361034_eq, odd_T_iff]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_, by omega⟩
    rcases j with _ | j
    · simp at hj
    · omega
  · rintro ⟨j, hj1, hj⟩
    refine ⟨j, ?_⟩
    have : 2 ≤ 2 ^ j := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    omega

/-- **Bala's conjecture for A361035.** `a(k)` is odd iff `k = 2ʲ - 3` with `j ≥ 2`. -/
theorem A361035_odd_iff (k : ℕ) : Odd (A361035 k) ↔ ∃ j ≥ 2, k = 2 ^ j - 3 := by
  rw [A361035_eq, odd_T_iff]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_, by omega⟩
    rcases j with _ | _ | j
    · simp at hj
    · simp at hj; omega
    · omega
  · rintro ⟨j, hj2, hj⟩
    refine ⟨j, ?_⟩
    have : 4 ≤ 2 ^ j := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    omega

end A361032
