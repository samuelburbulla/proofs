import Mathlib

/-!
# OEIS A337945

A337945 lists the numbers `m` for which there is a solution `(s, t, k)` of
`s² + t² = k·m`, `s + t = m`, `1 ≤ s ≤ t` and `1 ≤ k ≤ m − 1`.

P. Luschny conjectured (2023):
`m` is a term iff `m·Clausen(m, 1) ≠ 2·Clausen(m, 0)` (`Clausen` = A160014); in other words,
`m` is a term iff it is not an odd squarefree number.

We prove both forms (`A337945.isTerm_iff`, `A337945.isTerm_iff_clausen`). With `t = m − s`,
`s² + t² ≡ 2s² (mod m)`, and the bounds on `k` hold automatically. So `m` is a term iff
`m ∣ 2s²` for some `1 ≤ s ≤ m/2`.
* Even `m`: take `s = t = m/2`.
* Odd `m`: the condition becomes `m ∣ s²` with `0 < s < m`, which is possible iff `m` is not
  squarefree.
-/

namespace A337945

/-- `m` is a term of A337945. -/
def IsTerm (m : ℕ) : Prop :=
  ∃ s t k : ℕ, s ^ 2 + t ^ 2 = k * m ∧ s + t = m ∧ 1 ≤ s ∧ s ≤ t ∧ 1 ≤ k ∧ k ≤ m - 1

/-- A bounded reformulation, used for decidability. -/
lemma isTerm_iff_bounded (m : ℕ) :
    IsTerm m ↔ ∃ s < m + 1, ∃ t < m + 1, ∃ k < m + 1,
      s ^ 2 + t ^ 2 = k * m ∧ s + t = m ∧ 1 ≤ s ∧ s ≤ t ∧ 1 ≤ k ∧ k ≤ m - 1 := by
  constructor
  · rintro ⟨s, t, k, h⟩
    exact ⟨s, by omega, t, by omega, k, by omega, h⟩
  · rintro ⟨s, -, t, -, k, -, h⟩
    exact ⟨s, t, k, h⟩

instance : DecidablePred IsTerm := fun m => decidable_of_iff _ (isTerm_iff_bounded m).symm

-- Sanity check against the OEIS data.
example : (List.range 43).filter (fun m => decide (IsTerm m)) =
    [2, 4, 6, 8, 9, 10, 12, 14, 16, 18, 20, 22, 24, 25, 26, 27, 28, 30, 32, 34, 36, 38, 40,
      42] := by decide +kernel

/-- **Luschny's conjecture**, second form: for `m ≥ 1`, `m` is a term iff `m` is not an odd
squarefree number. -/
theorem isTerm_iff {m : ℕ} (hm : 1 ≤ m) : IsTerm m ↔ ¬ (Odd m ∧ Squarefree m) := by
  constructor
  · rintro ⟨s, t, k, hk, hst, hs, hst', -, -⟩ ⟨hodd, hsq⟩
    -- `m ∣ 2 s²`
    have h2 : m ∣ 2 * s ^ 2 := by
      have : 2 * s ^ 2 + m * (m - 2 * s) = k * m := by
        rw [← hk, ← hst]
        have : t = (s + t) - s := by omega
        zify [show 2 * s ≤ s + t by omega] at *
        ring
      have h' : m ∣ 2 * s ^ 2 + m * (m - 2 * s) := this ▸ dvd_mul_left m k
      exact (Nat.dvd_add_left (dvd_mul_right m _)).1 h'
    have hcop : Nat.Coprime m 2 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_)
      have := Nat.odd_iff.1 hodd
      omega
    have h3 : m ∣ s ^ 2 := hcop.dvd_of_dvd_mul_left h2
    have h4 : m ∣ s := (hsq.dvd_pow_iff_dvd two_ne_zero).1 h3
    have := Nat.le_of_dvd (by omega) h4
    omega
  · intro h
    rcases Nat.even_or_odd m with ⟨j, rfl⟩ | hodd
    · -- `s = t = k = m/2`
      refine ⟨j, j, j, by ring, rfl, by omega, le_rfl, by omega, by omega⟩
    · have hnsq : ¬ Squarefree m := fun hsq => h ⟨hodd, hsq⟩
      rw [Nat.squarefree_iff_prime_squarefree] at hnsq
      push Not at hnsq
      obtain ⟨p, hp, q, hq⟩ := hnsq
      have hp2 := hp.two_le
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with rfl | h
        · omega
        · exact h
      -- `s₀ = p q` satisfies `m ∣ s₀²`; take `s = min s₀ (m - s₀)`
      have hs0 : p * q < m := by
        rw [hq]; nlinarith
      have key : ∀ s, 1 ≤ s → 2 * s ≤ m → m ∣ s ^ 2 → 9 ≤ m → IsTerm m := by
        intro s hs1 hs2 hdiv h9
        obtain ⟨c, hc⟩ := hdiv
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with h0 | h0
          · rw [h0, mul_zero] at hc
            have : 0 < s ^ 2 := by positivity
            omega
          · exact h0
        -- `s² + (m - s)² = m (m - 2 s + 2 c)`
        refine ⟨s, m - s, m - 2 * s + 2 * c, ?_, by omega, hs1, by omega, ?_, ?_⟩
        · zify [show s ≤ m by omega, show 2 * s ≤ m by omega] at *
          rw [sq, sq] at *
          nlinarith [hc]
        · omega
        · -- `2 c ≤ 2 s - 1`, since `2 s² ≤ m (2 s - 1)`
          have h1 : 2 * (s * s) + m ≤ 2 * s * m := by nlinarith
          have h2 : s ^ 2 = m * c := hc
          rw [sq] at h2
          have : m * (2 * c) + m ≤ m * (2 * s) := by nlinarith
          have : 2 * c + 1 ≤ 2 * s :=
            Nat.le_of_mul_le_mul_left (by rw [mul_add, mul_one]; exact this) (by omega)
          omega
      have h9 : 9 ≤ m := by
        -- `m` is odd, so `p ≥ 3`, `q` is odd and `m ≥ p² ≥ 9`
        have hp3 : 3 ≤ p := by
          have hpm : p ∣ m := ⟨p * q, by rw [hq]; ring⟩
          have hne : p ≠ 2 := by
            rintro rfl
            have := Nat.odd_iff.1 hodd
            omega
          omega
        nlinarith
      have hdiv0 : m ∣ (p * q) ^ 2 := ⟨q, by rw [hq]; ring⟩
      rcases le_or_gt (2 * (p * q)) m with hle | hgt
      · exact key (p * q) (Nat.mul_pos (by omega) hq0) hle hdiv0 h9
      · have hA : 1 ≤ m - p * q := by omega
        have hB : 2 * (m - p * q) ≤ m := by omega
        refine key (m - p * q) hA hB ?_ h9
        -- `(m - s₀)² = m (m + c - 2 s₀)` where `s₀² = m c`
        obtain ⟨c, hc⟩ := hdiv0
        have hZ : ((m : ℤ) - p * q) ^ 2 = m * (m + c - 2 * (p * q)) := by
          have : ((p * q : ℕ) : ℤ) ^ 2 = m * c := by exact_mod_cast hc
          push_cast at this
          nlinarith [this]
        have hnn : (0 : ℤ) ≤ m + c - 2 * (p * q) := by
          have h1 : (0 : ℤ) ≤ m * (m + c - 2 * (p * q)) := hZ ▸ sq_nonneg _
          have hm0 : (0 : ℤ) < m := by exact_mod_cast (show 0 < m by omega)
          exact (mul_nonneg_iff_of_pos_left hm0).1 h1
        refine ⟨m + c - 2 * (p * q), ?_⟩
        have hle : 2 * (p * q) ≤ m + c := by
          have : (2 * (p * q) : ℤ) ≤ m + c := by linarith
          exact_mod_cast this
        zify [hs0.le, hle]
        rw [hZ]

/-- Generalized Clausen numbers (A160014): the product of the primes `p` with `p - k ∣ n`,
i.e. of the primes of the form `d + k` with `d ∣ n`. -/
def clausen (n k : ℕ) : ℕ := ∏ p ∈ (n.divisors.image (· + k)).filter Nat.Prime, p

lemma clausen_zero (n : ℕ) : clausen n 0 = ∏ p ∈ n.primeFactors, p := by
  unfold clausen
  congr 1
  ext p
  simp [Nat.mem_primeFactors, and_comm]

lemma prime_of_mem {n k p : ℕ} (hp : p ∈ (n.divisors.image (· + k)).filter Nat.Prime) :
    p.Prime := (Finset.mem_filter.1 hp).2

lemma clausen_pos (n k : ℕ) : 0 < clausen n k :=
  Finset.prod_pos fun _ hp => (prime_of_mem hp).pos

lemma dvd_clausen {n k p : ℕ} (hn : n ≠ 0) (d : ℕ) (hd : d ∣ n) (hp : (d + k).Prime)
    (hpd : p = d + k) : p ∣ clausen n k :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.2
    ⟨Finset.mem_image.2 ⟨d, Nat.mem_divisors.2 ⟨hd, hn⟩, hpd.symm⟩, hpd ▸ hp⟩)

/-- The radical is `< m` when `m` is not squarefree. -/
lemma rad_lt {m : ℕ} (hm : m ≠ 0) (h : ¬ Squarefree m) : ∏ p ∈ m.primeFactors, p < m := by
  rw [Nat.squarefree_iff_prime_squarefree] at h
  push Not at h
  obtain ⟨p, hp, q, hq⟩ := h
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact hm hq
  have hdvd : ∏ p ∈ m.primeFactors, p ∣ p * q := by
    rw [Nat.prod_primeFactors_dvd_iff (Nat.mul_ne_zero hp.ne_zero hq0)]
    intro r hr
    have hr' := Nat.mem_primeFactors.1 hr
    refine Nat.mem_primeFactors.2 ⟨hr'.1, ?_, Nat.mul_ne_zero hp.ne_zero hq0⟩
    rcases eq_or_ne r p with rfl | hne
    · exact dvd_mul_right _ _
    · have : r ∣ p * p * q := hq ▸ hr'.2.1
      rw [mul_assoc] at this
      exact (Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_primes hr'.1 hp).2 hne) this)
  have := Nat.le_of_dvd (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hq0)) hdvd
  have : p * q < m := by
    rw [hq]
    have := hp.two_le
    have : 0 < p * q := Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hq0)
    nlinarith
  omega

/-- **Luschny's conjecture**, first form: for `m ≥ 1`, `m` is a term iff
`m · Clausen(m, 1) ≠ 2 · Clausen(m, 0)`. -/
theorem isTerm_iff_clausen {m : ℕ} (hm : 1 ≤ m) :
    IsTerm m ↔ m * clausen m 1 ≠ 2 * clausen m 0 := by
  rw [isTerm_iff hm, clausen_zero]
  have hm0 : m ≠ 0 := by omega
  have hrad : ∏ p ∈ m.primeFactors, p ≤ m := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)
  have h2 : 2 ∣ clausen m 1 := dvd_clausen hm0 1 (one_dvd m) Nat.prime_two rfl
  have hC : 2 ≤ clausen m 1 := Nat.le_of_dvd (clausen_pos m 1) h2
  constructor
  · intro h heq
    rcases Nat.even_or_odd m with heven | hodd
    · -- `2` and `3` both divide `Clausen(m, 1)`
      have h3 : 3 ∣ clausen m 1 :=
        dvd_clausen hm0 2 (even_iff_two_dvd.1 heven) Nat.prime_three rfl
      have h6 : 6 ∣ clausen m 1 :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
      have := Nat.le_of_dvd (clausen_pos m 1) h6
      nlinarith
    · have hnsq : ¬ Squarefree m := fun hs => h ⟨hodd, hs⟩
      have := rad_lt hm0 hnsq
      nlinarith
  · rintro h ⟨hodd, hsq⟩
    apply h
    rw [Nat.prod_primeFactors_of_squarefree hsq]
    -- for odd `m`, the only prime of the form `d + 1` with `d ∣ m` is `2`
    have hC2 : clausen m 1 = 2 := by
      unfold clausen
      rw [show (m.divisors.image (· + 1)).filter Nat.Prime = {2} from ?_]
      · simp
      ext p
      simp only [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨d, ⟨hd, -⟩, rfl⟩, hp⟩
        have hdodd : Odd d := hodd.of_dvd_nat hd
        rcases hp.eq_two_or_odd' with h2 | ho
        · exact h2
        · exfalso
          obtain ⟨r, hr⟩ := hdodd
          obtain ⟨u, hu⟩ := ho
          omega
      · rintro rfl
        exact ⟨⟨1, ⟨one_dvd m, hm0⟩, rfl⟩, Nat.prime_two⟩
    rw [hC2, mul_comm]

end A337945

#print axioms A337945.isTerm_iff_clausen
