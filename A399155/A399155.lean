import Mathlib

/-!
# OEIS A399155

`a(n) = f(n) - g(n)`, where `f(n)` is the number of steps to reach `0` from `n` by repeatedly
subtracting the smallest prime factor of the current value, and `g(n)` is the number of steps
when the largest prime factor is subtracted instead.

J. Dilkhush conjectured (2026): `a(n) ≥ 0` for all `n ≥ 2`, i.e. `g(n) ≤ f(n)`.

We prove it (`A399155.g_le_f`). The key facts:
* If a prime `q` divides `m > 0`, then `g(m) ≤ m / q` (`A399155.g_le_div`). Each step subtracts
  the largest prime factor `P ≥ q`, and the new value `m - P` is again a multiple of `P`.
* `f(n) ≥ n / p` for `p` the smallest prime factor of `n` (`A399155.div_le_f`). For even `n`,
  `f(n) = n/2`. For odd `n`, the first step leads to the even number `n - p`, so
  `f(n) = 1 + (n - p)/2 ≥ 1 + (n - p)/p = n/p`.
-/

namespace A399155

/-- The largest prime factor of `n`, with the value `1` for `n ≤ 1` (where no prime factor
exists; this matches Mathematica's `FactorInteger[1] = {{1,1}}`). -/
def lpf (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 1

lemma lpf_pos (n : ℕ) : 0 < lpf n := by
  unfold lpf
  split_ifs with h
  · exact (Nat.prime_of_mem_primeFactors (Finset.max'_mem _ h)).pos
  · exact one_pos

lemma lpf_spec {n q : ℕ} (hn : n ≠ 0) (hq : q.Prime) (hqn : q ∣ n) :
    (lpf n).Prime ∧ lpf n ∣ n ∧ q ≤ lpf n := by
  have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hq, hqn, hn⟩
  have h : n.primeFactors.Nonempty := ⟨q, hmem⟩
  have hl : lpf n = n.primeFactors.max' h := by simp only [lpf, h, dite_true]
  have hmax := Finset.max'_mem _ h
  rw [hl]
  exact ⟨Nat.prime_of_mem_primeFactors hmax, Nat.dvd_of_mem_primeFactors hmax,
    Finset.le_max' _ _ hmem⟩

/-- Steps to reach `0` subtracting the smallest prime factor. -/
def f : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + f (n + 1 - (n + 1).minFac)
decreasing_by have := Nat.minFac_pos (n + 1); omega

/-- Steps to reach `0` subtracting the largest prime factor. -/
def g : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + g (n + 1 - lpf (n + 1))
decreasing_by have := lpf_pos (n + 1); omega

lemma f_succ (n : ℕ) (hn : n ≠ 0) : f n = 1 + f (n - n.minFac) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [f]

lemma g_succ (n : ℕ) (hn : n ≠ 0) : g n = 1 + g (n - lpf n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [g]

/-- If `q` is a prime factor of `m`, then `g(m) ≤ m / q`. -/
lemma g_le_div (m : ℕ) : ∀ q, q.Prime → q ∣ m → g m ≤ m / q := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro q hq hqm
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [g]
    obtain ⟨hP, hPm, hqP⟩ := lpf_spec hm.ne' hq hqm
    rw [g_succ m hm.ne']
    set P := lpf m
    obtain ⟨k, hk⟩ := hPm
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    have hsub : m - P = P * (k - 1) := by rw [hk, Nat.mul_sub_one]
    have hmP : m / P = k := by rw [hk, Nat.mul_div_cancel_left _ hP.pos]
    have hstep : g (m - P) ≤ (m - P) / P := by
      rcases Nat.eq_zero_or_pos (m - P) with h0 | hpos
      · rw [h0]; simp [g]
      · exact ih (m - P) (by have := hP.pos; omega) P hP (hsub ▸ dvd_mul_right _ _)
    have hdiv : (m - P) / P = k - 1 := by rw [hsub, Nat.mul_div_cancel_left _ hP.pos]
    rw [hdiv] at hstep
    have : m / P ≤ m / q := Nat.div_le_div_left hqP hq.pos
    omega

/-- `f(n) ≥ n / p` where `p` is the smallest prime factor of `n ≥ 2`. -/
lemma div_le_f (n : ℕ) (hn : 2 ≤ n) : n / n.minFac ≤ f n := by
  -- even numbers: `f(2k) = k`
  have heven : ∀ k, f (2 * k) = k := by
    intro k
    induction k with
    | zero => simp [f]
    | succ k ih =>
      rw [f_succ _ (by omega), (Nat.minFac_eq_two_iff _).2 (dvd_mul_right _ _),
        show 2 * (k + 1) - 2 = 2 * k by omega, ih]
      omega
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | hodd
  · rw [← two_mul, heven, (Nat.minFac_eq_two_iff _).2 (dvd_mul_right _ _)]
    omega
  · set p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hp2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpn
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpn)
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2)
    have hnodd : n % 2 = 1 := Nat.odd_iff.1 hodd
    have hple : p ≤ n := Nat.le_of_dvd (by omega) hpn
    obtain ⟨j, hj⟩ : ∃ j, n - p = 2 * j := ⟨(n - p) / 2, by omega⟩
    rw [f_succ n (by omega), hj, heven]
    obtain ⟨c, hc⟩ := hpn
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · omega
      · exact h
    have hnp : n / p = c := by rw [hc, Nat.mul_div_cancel_left _ hp.pos]
    rw [hnp]
    -- `n - p = p * (c - 1) = 2 * j` and `p ≥ 2`, so `c - 1 ≤ j`
    have h1 : p * (c - 1) = 2 * j := by rw [Nat.mul_sub_one, ← hc]; exact hj
    have h2 : 2 ≤ p := hp.two_le
    have : 2 * (c - 1) ≤ 2 * j := h1 ▸ Nat.mul_le_mul_right _ h2
    omega

/-- **Dilkhush's conjecture.** `g(n) ≤ f(n)` for all `n ≥ 2`, i.e. `A399155(n) ≥ 0`. -/
theorem g_le_f (n : ℕ) (hn : 2 ≤ n) : g n ≤ f n :=
  (g_le_div n _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd n)).trans (div_le_f n hn)

/-- The sequence itself, as an integer. -/
def a (n : ℕ) : ℤ := (f n : ℤ) - g n

-- Sanity check against the OEIS data `a(2), …, a(33)`.
unseal f g Nat.minFacAux Nat.primeFactorsList in
example : (List.range 32).map (fun i => a (i + 2)) =
    [0, 0, 0, 0, 1, 0, 1, 1, 3, 0, 2, 0, 5, 4, 5, 0, 5, 0, 6, 7, 9, 0, 8, 6, 11, 8, 10, 0, 9,
      0, 9, 13] := by decide +kernel

theorem a_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ a n := by
  unfold a; exact sub_nonneg.2 (by exact_mod_cast g_le_f n hn)

end A399155

#print axioms A399155.a_nonneg
