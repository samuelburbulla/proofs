import Mathlib

/-!
# OEIS A389540

`A(x) = Σ_{n ≥ 1} a(n) xⁿ` is the power series with `A(x)² = A(2x - 2A(x)) / 2`
and `A(x) = x + O(x²)`.

Paul D. Hanna's conjecture in the entry says `a(n)` is odd if and only if `n` is a
power of `2`. This is proved below for *every* integer power series `A` with
`A(0) = 0`, `A'(0) = 1` and `2 A(x)² = A(2x - 2A(x))` (`A389540.odd_iff_pow_two`).
We also show that such a series exists (`A389540.exists_isSolution`), so the
statement is not vacuous. As a check against the OEIS data, every solution
starts `x - x² + 2x³ + ⋯` (`A389540.coeff_two_three`).
-/

open PowerSeries Finset

namespace A389540

/-- `A` is a solution of `A(x)² = A(2x - 2A(x)) / 2` with `A(x) = x + O(x²)`. -/
def IsSolution (A : ℤ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ 2 * A ^ 2 = A.subst (2 * X - 2 * A)

/-! ### Squaring mod 2 -/

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

/-! ### Parity of the coefficients of a solution -/

lemma coeff_two_pow_mul (d n : ℕ) (g : ℤ⟦X⟧) :
    coeff n ((2 : ℤ⟦X⟧) ^ d * g) = 2 ^ d * coeff n g := by
  rw [show (2 : ℤ⟦X⟧) ^ d = C ((2 : ℤ) ^ d) by simp, coeff_C_mul]

/-- The coefficient of `x^(n+2)` in `2 A(x)² = A(2x - 2A(x))`, written out:
`2 [xⁿ⁺²] A² = Σ_{d ≥ 2} a(d) 2ᵈ [xⁿ⁺²] (x - A)ᵈ - 2 a(n+2)`. -/
lemma coeff_eq {A : ℤ⟦X⟧} (hA : IsSolution A) (n : ℕ) :
    2 * coeff (n + 2) (A ^ 2) =
      ∑ i ∈ range (n + 1), coeff (i + 2) A * (2 ^ (i + 2) * coeff (n + 2) ((X - A) ^ (i + 2)))
        - 2 * coeff (n + 2) A := by
  obtain ⟨h0, h1, heq⟩ := hA
  set B : ℤ⟦X⟧ := 2 * X - 2 * A with hBdef
  have hB0 : constantCoeff B = 0 := by simp [hBdef, h0]
  have hB : HasSubst B := HasSubst.of_constantCoeff_zero' hB0
  have h := congrArg (coeff (n + 2)) heq
  rw [coeff_subst' hB, coeff_ofNat_mul] at h
  -- only the terms `d ≤ n + 2` of the substitution can contribute
  have hsupp : (Function.support fun d : ℕ => coeff d A • coeff (n + 2) (B ^ d)) ⊆
      ↑(range (n + 3)) := by
    intro d hd
    simp only [Function.mem_support] at hd
    simp only [coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    have hX : X ^ d ∣ B ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.2 hB0) d
    rw [X_pow_dvd_iff.1 hX (n + 2) (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, sum_range_succ', sum_range_succ'] at h
  have hc : coeff (n + 2) B = -(2 * coeff (n + 2) A) := by
    rw [hBdef, ← mul_sub, ← pow_one (2 : ℤ⟦X⟧), coeff_two_pow_mul, map_sub, coeff_X,
      ite_eq_right (by omega)]
    ring
  rw [pow_one, h1, hc, coeff_zero_eq_constantCoeff_apply, h0] at h
  simp only [smul_eq_mul, zero_mul, one_mul, add_zero] at h
  rw [h, sub_eq_add_neg]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [hBdef, ← mul_sub, mul_pow, coeff_two_pow_mul]

/-- Reading the equation modulo 4: `a(n) + [xⁿ] A(x)²` is even for `n ≥ 2`. -/
lemma even_coeff_add_coeff_sq {A : ℤ⟦X⟧} (hA : IsSolution A) (n : ℕ) :
    Even (coeff (n + 2) A + coeff (n + 2) (A ^ 2)) := by
  have h := coeff_eq hA n
  have hrest : 4 ∣ ∑ i ∈ range (n + 1),
      coeff (i + 2) A * (2 ^ (i + 2) * coeff (n + 2) ((X - A) ^ (i + 2))) := by
    refine dvd_sum fun i _ => ?_
    exact Dvd.intro (coeff (i + 2) A * (2 ^ i * coeff (n + 2) ((X - A) ^ (i + 2))))
      (by ring)
  obtain ⟨K, hK⟩ := hrest
  rw [hK] at h
  exact ⟨K, by omega⟩

/-- Sanity check against the OEIS data: every solution starts `x - x² + 2x³ + ⋯`. -/
theorem coeff_two_three {A : ℤ⟦X⟧} (hA : IsSolution A) :
    coeff 2 A = -1 ∧ coeff 3 A = 2 := by
  -- `x - A(x) = O(x²)`, so `(x - A)ᵈ = O(x^(2d))`
  have hX2 : X ^ 2 ∣ X - A := by
    rw [X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [coeff_zero_eq_constantCoeff_apply, hA.1]
    · simp [hA.2.1]
  have hvan : ∀ d m, m < 2 * d → coeff m ((X - A) ^ d) = 0 := fun d m hm =>
    X_pow_dvd_iff.1 ((pow_mul (X : ℤ⟦X⟧) 2 d).symm ▸ pow_dvd_pow_of_dvd hX2 d) m hm
  have hsq : ∀ m, coeff m (A ^ 2) = ∑ p ∈ antidiagonal m, coeff p.1 A * coeff p.2 A :=
    fun m => by rw [pow_two, coeff_mul]
  have h2 := coeff_eq hA 0
  have h3 := coeff_eq hA 1
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.reduceAdd] at h2 h3
  rw [hvan 2 2 (by norm_num)] at h2
  rw [hvan 2 3 (by norm_num), hvan 3 3 (by norm_num)] at h3
  rw [hsq] at h2 h3
  simp [Finset.Nat.antidiagonal_succ, coeff_zero_eq_constantCoeff_apply, hA.1, hA.2.1] at h2 h3
  omega

/-- Modulo 2, `a(n) ≡ a(n/2)` for even `n ≥ 2` and `a(n) ≡ 0` for odd `n ≥ 3`. -/
lemma coeff_mod_two {A : ℤ⟦X⟧} (hA : IsSolution A) (n : ℕ) :
    ((coeff (n + 2) A : ℤ) : ZMod 2) =
      if Even (n + 2) then ((coeff ((n + 2) / 2) A : ℤ) : ZMod 2) else 0 := by
  have he := even_coeff_add_coeff_sq hA n
  rw [← ZMod.intCast_eq_zero_iff_even, Int.cast_add] at he
  rw [eq_neg_of_add_eq_zero_left he, ZMod.neg_eq_self_mod_two, pow_two, coeff_mul,
    Int.cast_sum]
  simp only [Int.cast_mul]
  exact conv_zmod_two (fun k => ((coeff k A : ℤ) : ZMod 2)) (n + 2)

lemma pow_two_iff_half (m : ℕ) (hm : 1 ≤ m) :
    (∃ k, 2 * m = 2 ^ k) ↔ ∃ k, m = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => omega
    | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by ring⟩

/-- **Hanna's conjecture.** For every solution `A` and every `n ≥ 1`,
the coefficient `a(n)` is odd iff `n` is a power of two. -/
theorem odd_iff_pow_two {A : ℤ⟦X⟧} (hA : IsSolution A) (n : ℕ) (hn : 1 ≤ n) :
    Odd (coeff n A) ↔ ∃ k, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [← ZMod.intCast_eq_one_iff_odd]
    by_cases h1 : n = 1
    · subst h1; simp [hA.2.1]; exact ⟨0, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [coeff_mod_two hA m]
    rcases Nat.even_or_odd (m + 2) with ⟨j, hj⟩ | hodd
    · -- `m + 2 = 2j`: `a(2j) ≡ a(j)`
      have hj1 : 1 ≤ j := by omega
      rw [ite_eq_left ⟨j, hj⟩, show (m + 2) / 2 = j by omega, ZMod.intCast_eq_one_iff_odd,
        ih j (by omega) hj1, hj, ← two_mul, pow_two_iff_half j hj1]
    · -- `m + 2` odd
      rw [ite_eq_right (Nat.not_even_iff_odd.2 hodd)]
      simp only [zero_ne_one, false_iff]
      rintro ⟨k, hk⟩
      cases k with
      | zero => omega
      | succ k => exact Nat.not_even_iff_odd.2 hodd ⟨2 ^ k, by rw [hk]; ring⟩

/-! ### Existence of a solution

Let `R(y) = Σ_{k ≥ 0} 2^(2ᵏ-k-1) y^(2ᵏ) = y + y² + 2y⁴ + 16y⁸ + ⋯` (formula (1) of the
entry). It satisfies `R(2y²) = 2R(y) - 2y`. Its compositional inverse `A = R⁻¹` then solves
the equation: `R(2A²) = 2x - 2A`, so `A(2x - 2A) = A(R(2A²)) = 2A²`. -/

/-- Coefficients of `R`: `r(2ᵏ) = 2^(2ᵏ-k-1)`, all others `0`, via `r(2m) = 2^(m-1) r(m)`. -/
def r : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => if Even n then 2 ^ ((n + 2) / 2 - 1) * r ((n + 2) / 2) else 0

/-- `R(y) = y + y² + 2y⁴ + 16y⁸ + 2048y¹⁶ + ⋯`. -/
noncomputable def R : ℤ⟦X⟧ := PowerSeries.mk r

lemma r_pow_two (k : ℕ) : r (2 ^ k) = 2 ^ (2 ^ k - k - 1) := by
  induction k with
  | zero => simp [r]
  | succ k ih =>
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ (k + 1) = m + 2 := ⟨2 ^ (k + 1) - 2, by
      have := Nat.one_le_two_pow (n := k); rw [pow_succ]; omega⟩
    have hk1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    rw [hm, r, ite_eq_left ⟨2 ^ k - 1, by rw [pow_succ] at hm; omega⟩,
      show (m + 2) / 2 = 2 ^ k by rw [← hm, pow_succ]; omega, ih, ← pow_add]
    congr 1
    rw [← hm, pow_succ]; omega

lemma r_double (k : ℕ) : r (2 * (k + 1)) = 2 ^ k * r (k + 1) := by
  rw [show 2 * (k + 1) = 2 * k + 2 by ring, r, ite_eq_left ⟨k, by ring⟩,
    show (2 * k + 2) / 2 = k + 1 by omega, Nat.add_sub_cancel]

lemma r_odd (k : ℕ) : r (2 * k + 1 + 2) = 0 := by
  rw [r, ite_eq_right (by simp only [Nat.not_even_iff_odd]; exact ⟨k, rfl⟩)]

lemma R_functional_eq : R.subst (2 * X ^ 2 : ℤ⟦X⟧) = 2 * R - 2 * X := by
  have hS : HasSubst (2 * X ^ 2 : ℤ⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  ext n
  rw [coeff_subst' hS]
  have hpow : ∀ d, coeff n ((2 * X ^ 2 : ℤ⟦X⟧) ^ d) = if n = 2 * d then 2 ^ d else 0 := by
    intro d; rw [mul_pow, ← pow_mul, coeff_two_pow_mul, coeff_X_pow]; simp
  simp only [hpow, smul_eq_mul, map_sub, coeff_ofNat_mul, R, coeff_mk, coeff_X]
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [finsum_eq_single _ m (fun d hd => by simp [show m + m ≠ 2 * d by omega])]
    simp only [show m + m = 2 * m by ring, ite_true]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [r]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [r_double k, ite_eq_right (by omega)]
      ring
  · rw [finsum_eq_zero_of_forall_eq_zero (fun d => by simp [show 2 * m + 1 ≠ 2 * d by omega])]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [r]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, r_odd, ite_eq_right (by omega)]
      simp

lemma R_const : constantCoeff R = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [R, r]

lemma R_unit : IsUnit (coeff 1 R) := by simp [R, r]

/-- The solution, as the compositional inverse of `R`. -/
noncomputable def A : ℤ⟦X⟧ := R.substInvOfIsUnit R_unit

theorem isSolution_A : IsSolution A := by
  have hA : HasSubst A := HasSubst.substInvOfIsUnit R R_unit
  have hR : HasSubst R := HasSubst.of_constantCoeff_zero' R_const
  have hS : HasSubst (2 * X ^ 2 : ℤ⟦X⟧) := HasSubst.of_constantCoeff_zero' (by simp)
  have hRA : R.subst A = X := subst_substInvOfIsUnit_right R R_const R_unit
  have hAR : A.subst R = X := subst_substInvOfIsUnit_left R R_const R_unit
  refine ⟨constantCoeff_substInvOfIsUnit R R_unit, ?_, ?_⟩
  · rw [A, coeff_one_substInvOfIsUnit]
    have : (R_unit.unit : ℤ) = 1 := by simp [R, r]
    rw [show R_unit.unit = 1 from Units.ext this, inv_one, Units.val_one]
  -- `R(2A²) = 2x - 2A`
  have h2A : (2 * X ^ 2 : ℤ⟦X⟧).subst A = 2 * A ^ 2 := by
    rw [two_mul, subst_add hA, subst_pow hA, subst_X hA, two_mul]
  have hB0 : constantCoeff (2 * A ^ 2) = 0 := by
    simp [constantCoeff_substInvOfIsUnit, A]
  have hB : HasSubst (2 * A ^ 2) := HasSubst.of_constantCoeff_zero' hB0
  have hRB : R.subst (2 * A ^ 2) = 2 * X - 2 * A := by
    rw [← h2A, ← subst_comp_subst_apply hS hA, R_functional_eq, two_mul R, two_mul X,
      subst_sub hA, subst_add hA, subst_add hA, hRA, subst_X hA, two_mul]
  rw [← hRB, ← subst_comp_subst_apply hR hB, hAR, subst_X hB]

/-- A solution exists, so `odd_iff_pow_two` is not vacuous. -/
theorem exists_isSolution : ∃ A : ℤ⟦X⟧, IsSolution A := ⟨A, isSolution_A⟩

end A389540
