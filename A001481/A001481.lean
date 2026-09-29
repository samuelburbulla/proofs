import Mathlib

/-!
# OEIS A001481

A001481 lists the numbers that are sums of two squares, `n = x² + y²` with `x, y ≥ 0`.

J. Lowell conjectured (2022): apart from `0 + 2ᵏ`, the sum of two *distinct* terms of the
sequence is never a power of `2`.

We prove this (`A001481.lowell`). The key facts are elementary:
* if `x² + y²` is even, then `(x² + y²)/2 = ((x+y)/2)² + ((x-y)/2)²` is again a sum of two
  squares (`IsSumTwoSq.half`);
* an odd sum of two squares is `≡ 1 (mod 4)` (`IsSumTwoSq.mod_four`).

If `a + b = 2ᵏ` with `a ≠ b` both nonzero, halve both while they are even. If both are odd,
then `a + b ≡ 2 (mod 4)`, so `a + b = 2` and `a = b = 1`, which is a contradiction. If exactly
one is odd, the sum is odd, hence `1`, so one of them is `0`.
-/

namespace A001481

/-- `n` is a sum of two squares of natural numbers, i.e. `n` is a term of A001481. -/
def IsSumTwoSq (n : ℕ) : Prop := ∃ x y : ℕ, n = x ^ 2 + y ^ 2

/-- A bounded version of `IsSumTwoSq`, used only to make the predicate decidable. -/
lemma isSumTwoSq_iff (n : ℕ) :
    IsSumTwoSq n ↔ ∃ x < n + 1, ∃ y < n + 1, n = x ^ 2 + y ^ 2 := by
  constructor
  · rintro ⟨x, y, rfl⟩
    refine ⟨x, ?_, y, ?_, rfl⟩ <;> nlinarith
  · rintro ⟨x, -, y, -, h⟩; exact ⟨x, y, h⟩

instance : DecidablePred IsSumTwoSq := fun n =>
  decidable_of_iff _ (isSumTwoSq_iff n).symm

-- Sanity check against the OEIS data.
example : (List.range 51).filter (fun n => decide (IsSumTwoSq n)) =
    [0, 1, 2, 4, 5, 8, 9, 10, 13, 16, 17, 18, 20, 25, 26, 29, 32, 34, 36, 37, 40, 41, 45,
      49, 50] := by decide +kernel

/-- Every power of two is a sum of two squares, so the excluded pairs `0 + 2ᵏ` are genuine. -/
lemma isSumTwoSq_two_pow (k : ℕ) : IsSumTwoSq (2 ^ k) := by
  induction k with
  | zero => exact ⟨1, 0, by norm_num⟩
  | succ k ih =>
    obtain ⟨x, y, h⟩ := ih
    exact ⟨x + y, max x y - min x y, by
      rw [pow_succ, h]
      rcases le_total x y with hxy | hxy
      · rw [max_eq_right hxy, min_eq_left hxy]
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
        rw [Nat.add_sub_cancel_left]; ring
      · rw [max_eq_left hxy, min_eq_right hxy]
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
        rw [Nat.add_sub_cancel_left]; ring⟩

lemma isSumTwoSq_zero : IsSumTwoSq 0 := ⟨0, 0, rfl⟩

/-- Halving an even sum of two squares gives a sum of two squares. -/
lemma IsSumTwoSq.half {n : ℕ} (h : IsSumTwoSq n) (he : n % 2 = 0) : IsSumTwoSq (n / 2) := by
  obtain ⟨x, y, rfl⟩ := h
  have key : ∀ a b : ℕ, b ≤ a → (a ^ 2 + b ^ 2) % 2 = 0 →
      IsSumTwoSq ((a ^ 2 + b ^ 2) / 2) := by
    intro a b hba hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hba
    have hc : c % 2 = 0 := by
      have : (b + c) ^ 2 + b ^ 2 = 2 * (b ^ 2 + b * c) + c ^ 2 := by ring
      rw [this, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.pow_mod] at hab
      rcases Nat.mod_two_eq_zero_or_one c with h | h
      · exact h
      · rw [h] at hab; norm_num at hab
    obtain ⟨d, rfl⟩ : ∃ d, c = 2 * d := ⟨c / 2, by omega⟩
    exact ⟨b + d, d, by
      have : (b + 2 * d) ^ 2 + b ^ 2 = 2 * ((b + d) ^ 2 + d ^ 2) := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]⟩
  rcases le_total y x with hxy | hxy
  · exact key x y hxy he
  · rw [add_comm] at he ⊢; exact key y x hxy he

/-- An odd sum of two squares is `≡ 1 (mod 4)`. -/
lemma IsSumTwoSq.mod_four {n : ℕ} (h : IsSumTwoSq n) (ho : n % 2 = 1) : n % 4 = 1 := by
  obtain ⟨x, y, rfl⟩ := h
  have h4 : (x ^ 2 + y ^ 2) % 4 = ((x % 4) ^ 2 + (y % 4) ^ 2) % 4 := by
    rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod y, ← Nat.add_mod]
  have h2 : (x ^ 2 + y ^ 2) % 2 = (x ^ 2 + y ^ 2) % 4 % 2 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num)]
  rw [h2, h4] at ho
  rw [h4]
  have hx := Nat.mod_lt x (show 4 > 0 by norm_num)
  have hy := Nat.mod_lt y (show 4 > 0 by norm_num)
  interval_cases (x % 4) <;> interval_cases (y % 4) <;> simp_all

/-- **Lowell's conjecture.** If two distinct sums of two squares add up to a power of `2`,
then one of them is `0`. -/
theorem lowell (k : ℕ) : ∀ a b : ℕ, IsSumTwoSq a → IsSumTwoSq b → a ≠ b →
    a + b = 2 ^ k → a = 0 ∨ b = 0 := by
  induction k with
  | zero => intro a b _ _ _ h; rw [pow_zero] at h; omega
  | succ k ih =>
    intro a b ha hb hab h
    rcases Nat.mod_two_eq_zero_or_one a with hA | hA <;>
      rcases Nat.mod_two_eq_zero_or_one b with hB | hB
    · -- both even: halve
      have := ih (a / 2) (b / 2) (ha.half hA) (hb.half hB) (by omega)
        (by rw [pow_succ] at h; omega)
      omega
    · -- sum odd, but `2^(k+1)` is even
      have : 2 ^ (k + 1) % 2 = 0 := by rw [pow_succ]; simp
      omega
    · have : 2 ^ (k + 1) % 2 = 0 := by rw [pow_succ]; simp
      omega
    · -- both odd: `a + b ≡ 2 (mod 4)`
      have h4a := ha.mod_four hA
      have h4b := hb.mod_four hB
      rcases k with _ | k
      · omega
      · have : 2 ^ (k + 1 + 1) % 4 = 0 := by
          rw [pow_succ, pow_succ, mul_assoc]; simp
        omega

/-- The conjecture as stated: apart from `0 + 2ᵏ`, no two distinct terms sum to a power of 2,
and the exceptions `0 + 2ᵏ` do occur. -/
theorem lowell_conjecture :
    (∀ a b k : ℕ, IsSumTwoSq a → IsSumTwoSq b → a ≠ b → a + b = 2 ^ k →
      (a = 0 ∧ b = 2 ^ k) ∨ (b = 0 ∧ a = 2 ^ k)) ∧
    (∀ k : ℕ, IsSumTwoSq 0 ∧ IsSumTwoSq (2 ^ k)) := by
  refine ⟨fun a b k ha hb hab h => ?_, fun k => ⟨isSumTwoSq_zero, isSumTwoSq_two_pow k⟩⟩
  rcases lowell k a b ha hb hab h with rfl | rfl
  · left; omega
  · right; omega

end A001481

#print axioms A001481.lowell_conjecture
