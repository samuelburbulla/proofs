import Mathlib

/-!
# OEIS A374571

`A(x) = Σ a(n) xⁿ` is the power series with `a(0) = 1` and

  `A(x) = A(x²) - x · A(x²)²`.

Paul D. Hanna's conjecture in the entry says that for `n > 0`, `a(n)` is odd iff `n` is a
Fibbinary number, i.e. its binary representation has no two adjacent `1`s (A003714).

We prove it for every integer power series `A` with constant term `1` satisfying the equation
(`A374571.odd_iff_fibbinary`). We also show that such a series exists (`exists_isSolution`) and
that its first terms agree with the OEIS data.

**Proof.** Modulo 2, squaring is additive, so `A(x²)² ≡ A(x⁴)` and the equation becomes
`A ≡ A(x²) + x·A(x⁴)`. Comparing coefficients gives `a(2n) ≡ a(n)`, `a(4k+1) ≡ a(k)` and
`a(4k+3) ≡ 0`. The Fibbinary predicate satisfies the same recursion: appending `0`, or `01`,
keeps the property, and appending `11` destroys it.
-/

open PowerSeries Finset

namespace A374571

/-- `n` is Fibbinary: no two adjacent `1`s in its binary representation. -/
def Fibbinary (n : ℕ) : Prop := ∀ i, ¬ (n.testBit i ∧ n.testBit (i + 1))

lemma fibbinary_iff (n : ℕ) :
    Fibbinary n ↔ ¬ (n % 2 = 1 ∧ (n / 2) % 2 = 1) ∧ Fibbinary (n / 2) := by
  unfold Fibbinary
  constructor
  · intro h
    refine ⟨fun hc => h 0 ?_, fun i hi => h (i + 1) ?_⟩
    · simp [Nat.testBit_zero, Nat.testBit_succ, hc.1, hc.2]
    · simpa [Nat.testBit_succ] using hi
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => exact h0 (by simpa [Nat.testBit_zero, Nat.testBit_succ] using hi)
    | succ i => exact h i (by simpa [Nat.testBit_succ] using hi)

lemma fibbinary_zero : Fibbinary 0 := by intro i; simp

/-- The functional equation, with constant term `1`. -/
def IsSolution (A : ℤ⟦X⟧) : Prop :=
  constantCoeff A = 1 ∧ A = A.subst (X ^ 2 : ℤ⟦X⟧) - X * (A.subst (X ^ 2 : ℤ⟦X⟧)) ^ 2

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

/-! ### Coefficients of `A(x²)` -/

lemma coeff_subst_sq (A : ℤ⟦X⟧) (n : ℕ) :
    coeff n (A.subst (X ^ 2 : ℤ⟦X⟧)) = if 2 ∣ n then coeff (n / 2) A else 0 := by
  rw [coeff_subst_X_pow (by norm_num)]
  simp

/-- The recursion modulo 2 satisfied by every solution. -/
lemma coeff_mod_two {A : ℤ⟦X⟧} (hA : IsSolution A) (n : ℕ) :
    ((coeff (n + 1) A : ℤ) : ZMod 2) =
      (if 2 ∣ n + 1 then ((coeff ((n + 1) / 2) A : ℤ) : ZMod 2) else 0) +
      (if Even n then (if 2 ∣ n / 2 then ((coeff (n / 2 / 2) A : ℤ) : ZMod 2) else 0) else 0) := by
  set g := A.subst (X ^ 2 : ℤ⟦X⟧) with hg
  have h := congrArg (coeff (n + 1)) hA.2
  rw [map_sub, coeff_succ_X_mul, pow_two g, coeff_mul, coeff_subst_sq] at h
  have hcast := congrArg (Int.cast : ℤ → ZMod 2) h
  push_cast at hcast
  have e2 : (∑ p ∈ antidiagonal n, ((coeff p.1 g : ℤ) : ZMod 2) * ((coeff p.2 g : ℤ) : ZMod 2)) =
      (if Even n then (if 2 ∣ n / 2 then ((coeff (n / 2 / 2) A : ℤ) : ZMod 2) else 0) else 0) := by
    rw [conv_zmod_two (fun i => ((coeff i g : ℤ) : ZMod 2)) n]
    split_ifs <;> simp_all
  rw [hcast, sub_eq_add_neg, ZMod.neg_eq_self_mod_two, e2]

/-! ### The conjecture -/

/-- **Hanna's conjecture.** For every solution and every `n`, `a(n)` is odd iff `n` is Fibbinary.
(For `n = 0` both sides are true, so this includes the OEIS statement for `n > 0`.) -/
theorem odd_iff_fibbinary {A : ℤ⟦X⟧} (hA : IsSolution A) (n : ℕ) :
    Odd (coeff n A) ↔ Fibbinary n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [← ZMod.intCast_eq_one_iff_odd]
    rcases n with _ | n
    · simp only [coeff_zero_eq_constantCoeff_apply, hA.1, Int.cast_one, true_iff]
      exact fibbinary_zero
    rw [coeff_mod_two hA n, fibbinary_iff]
    rcases Nat.even_or_odd n with hn | hn
    · -- `n + 1` odd
      have h2 : ¬ 2 ∣ n + 1 := by rcases hn with ⟨k, rfl⟩; omega
      rw [ite_eq_right h2, zero_add, ite_eq_left hn]
      have hodd : (n + 1) % 2 = 1 := by omega
      have hdiv : (n + 1) / 2 = n / 2 := by rcases hn with ⟨k, rfl⟩; omega
      rw [hdiv]
      by_cases h4 : 2 ∣ n / 2
      · rw [ite_eq_left h4, ZMod.intCast_eq_one_iff_odd, ih (n / 2 / 2) (by omega), fibbinary_iff (n / 2)]
        have : (n / 2) % 2 = 0 := by omega
        simp [this]
      · rw [ite_eq_right h4]
        have : (n / 2) % 2 = 1 := by omega
        simp [hodd, this]
    · -- `n + 1` even
      have h2 : 2 ∣ n + 1 := by rcases hn with ⟨k, rfl⟩; omega
      rw [ite_eq_left h2, ite_eq_right (Nat.not_even_iff_odd.2 hn), add_zero, ZMod.intCast_eq_one_iff_odd,
        ih ((n + 1) / 2) (by omega)]
      have : (n + 1) % 2 = 0 := by omega
      simp [this]

/-! ### Existence and the first terms -/

/-- `g i = [xⁱ] A(x²)` in terms of the coefficients `c`. -/
def sqc (c : ℕ → ℤ) (i : ℕ) : ℤ := if i % 2 = 0 then c (i / 2) else 0

/-- The coefficients, by the recursion read off from the functional equation. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      (if (n + 1) % 2 = 0 then a ((n + 1) / 2) else 0) -
        ∑ i : Fin (n + 1),
          (if i.1 % 2 = 0 then a (i.1 / 2) else 0) *
            (if (n - i.1) % 2 = 0 then a ((n - i.1) / 2) else 0)
decreasing_by all_goals omega

-- The first terms agree with the OEIS data.
unseal a in
example : (List.range 12).map a = [1, -1, -1, 2, -1, 1, 2, -6, -1, 5, 1, 0] := by
  decide +kernel

lemma a_succ (n : ℕ) : a (n + 1) = sqc a (n + 1) -
    ∑ p ∈ antidiagonal n, sqc a p.1 * sqc a p.2 := by
  rw [a, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => sqc a i * sqc a j),
    ← Fin.sum_univ_eq_sum_range (fun i => sqc a i * sqc a (n - i))]
  rfl

/-- The series with coefficients `a` solves the functional equation. -/
theorem isSolution_mk : IsSolution (PowerSeries.mk a) := by
  refine ⟨by rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, a], ?_⟩
  ext n
  rw [map_sub, coeff_subst_sq, coeff_mk]
  rcases n with _ | n
  · simp [a]
  rw [coeff_succ_X_mul, pow_two, coeff_mul, a_succ]
  congr 1
  · simp only [sqc, coeff_mk, Nat.dvd_iff_mod_eq_zero]
  · refine Finset.sum_congr rfl fun p _ => ?_
    simp only [sqc, coeff_subst_sq, coeff_mk, Nat.dvd_iff_mod_eq_zero]

theorem exists_isSolution : ∃ A : ℤ⟦X⟧, IsSolution A := ⟨_, isSolution_mk⟩

end A374571
