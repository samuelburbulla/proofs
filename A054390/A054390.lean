import Mathlib

/-!
# OEIS A054390

`a(n)` is the number of ways of writing `n` as a sum of powers of 3, each power being used at
most three times.

R. J. Mathar conjectured (2023) that `a(n)` is also the number of partitions of `n` into
distinct parts from A038754, the numbers of the form `3ᵏ` or `2·3ᵏ`.

We prove this (`A054390.card_reps_eq_card_parts`) with an explicit bijection. A representation
uses `3ᵏ` with multiplicity `cₖ ∈ {0,1,2,3}`. It corresponds to the partition that contains
`3ᵏ` iff `cₖ` is odd and `2·3ᵏ` iff `cₖ ≥ 2`, since `cₖ·3ᵏ` equals the sum of those parts.

Only powers `3ᵏ ≤ n` can occur, so a representation of `n` is recorded as a function
`Fin (n+1) → Fin 4` of multiplicities.
-/

open Finset

namespace A054390

/-- `m` belongs to A038754: `m = 3ᵏ` or `m = 2·3ᵏ` for some `k` (necessarily `k ≤ m`). -/
def IsPart (m : ℕ) : Prop := ∃ k < m + 1, m = 3 ^ k ∨ m = 2 * 3 ^ k

lemma lt_three_pow (k : ℕ) : k < 3 ^ k := Nat.lt_pow_self (by norm_num)

/-- The bound on `k` in `IsPart` is harmless. -/
lemma isPart_iff (m : ℕ) : IsPart m ↔ ∃ k, m = 3 ^ k ∨ m = 2 * 3 ^ k := by
  constructor
  · rintro ⟨k, -, h⟩; exact ⟨k, h⟩
  · rintro ⟨k, h⟩
    refine ⟨k, ?_, h⟩
    have := lt_three_pow k
    rcases h with rfl | rfl <;> omega

instance : DecidablePred IsPart := fun m => by unfold IsPart; infer_instance

/-- Representations of `n` as `Σ cₖ 3ᵏ` with `0 ≤ cₖ ≤ 3`. -/
def reps (n : ℕ) : Finset (Fin (n + 1) → Fin 4) :=
  univ.filter fun c => ∑ k, (c k : ℕ) * 3 ^ (k : ℕ) = n

/-- Partitions of `n` into distinct parts of A038754. -/
def parts (n : ℕ) : Finset (Finset ℕ) :=
  ((range (n + 1)).filter IsPart).powerset.filter fun S => S.sum id = n

-- The first terms agree with the OEIS data `1, 1, 1, 2, 1, 1`.
example : (List.range 4).map (fun n => (reps n).card) = [1, 1, 1, 2] := by decide +kernel
example : (List.range 16).map (fun n => (parts n).card) =
    [1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2] := by decide +kernel

/-! ### Injectivity facts -/

lemma pow_inj {a b : ℕ} (h : 3 ^ a = 3 ^ b) : a = b :=
  Nat.pow_right_injective (by norm_num) h

lemma two_pow_inj {a b : ℕ} (h : 2 * 3 ^ a = 2 * 3 ^ b) : a = b :=
  pow_inj (by omega)

lemma pow_ne_two_pow (a b : ℕ) : 3 ^ a ≠ 2 * 3 ^ b := by
  intro h
  have h1 : Odd (3 ^ a) := Odd.pow (by decide)
  rw [h] at h1
  exact (Nat.not_odd_iff_even.2 (even_two_mul _)) h1

/-! ### The bijection -/

variable {n : ℕ}

/-- The partition of a representation. -/
def toParts (c : Fin (n + 1) → Fin 4) : Finset ℕ :=
  (univ.filter fun k => (c k : ℕ) % 2 = 1).image (fun k : Fin (n + 1) => 3 ^ (k : ℕ)) ∪
    (univ.filter fun k => 2 ≤ (c k : ℕ)).image (fun k : Fin (n + 1) => 2 * 3 ^ (k : ℕ))

/-- The representation of a partition. -/
def ofParts (S : Finset ℕ) : Fin (n + 1) → Fin 4 := fun k =>
  ⟨(if 3 ^ (k : ℕ) ∈ S then 1 else 0) + (if 2 * 3 ^ (k : ℕ) ∈ S then 2 else 0), by
    split_ifs <;> omega⟩

lemma val_ofParts (S : Finset ℕ) (k : Fin (n + 1)) :
    (ofParts (n := n) S k : ℕ) =
      (if 3 ^ (k : ℕ) ∈ S then 1 else 0) + (if 2 * 3 ^ (k : ℕ) ∈ S then 2 else 0) := rfl

lemma mem_toParts (c : Fin (n + 1) → Fin 4) (m : ℕ) :
    m ∈ toParts c ↔ ∃ k : Fin (n + 1),
      ((c k : ℕ) % 2 = 1 ∧ 3 ^ (k : ℕ) = m) ∨ (2 ≤ (c k : ℕ) ∧ 2 * 3 ^ (k : ℕ) = m) := by
  simp only [toParts, mem_union, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨k, h1, h2⟩ | ⟨k, h1, h2⟩)
    · exact ⟨k, Or.inl ⟨h1, h2⟩⟩
    · exact ⟨k, Or.inr ⟨h1, h2⟩⟩
  · rintro ⟨k, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact Or.inl ⟨k, h1, h2⟩
    · exact Or.inr ⟨k, h1, h2⟩

lemma mem_toParts_pow (c : Fin (n + 1) → Fin 4) (k : Fin (n + 1)) :
    3 ^ (k : ℕ) ∈ toParts c ↔ (c k : ℕ) % 2 = 1 := by
  simp only [toParts, mem_union, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨j, hj, hjk⟩ | ⟨j, -, hjk⟩)
    · rwa [Fin.ext (pow_inj hjk)] at hj
    · exact absurd hjk.symm (pow_ne_two_pow _ _)
  · intro h; exact Or.inl ⟨k, h, rfl⟩

lemma mem_toParts_two_pow (c : Fin (n + 1) → Fin 4) (k : Fin (n + 1)) :
    2 * 3 ^ (k : ℕ) ∈ toParts c ↔ 2 ≤ (c k : ℕ) := by
  simp only [toParts, mem_union, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨j, -, hjk⟩ | ⟨j, hj, hjk⟩)
    · exact absurd hjk (pow_ne_two_pow _ _)
    · rwa [Fin.ext (two_pow_inj hjk)] at hj
  · intro h; exact Or.inr ⟨k, h, rfl⟩

lemma sum_toParts (c : Fin (n + 1) → Fin 4) :
    (toParts c).sum id = ∑ k, (c k : ℕ) * 3 ^ (k : ℕ) := by
  rw [toParts, sum_union, sum_image, sum_image, sum_filter, sum_filter, ← sum_add_distrib]
  · refine sum_congr rfl fun k _ => ?_
    have := (c k).isLt
    simp only [id]
    interval_cases h : (c k : ℕ) <;> (simp; try ring)
  · intro a _ b _ h; exact Fin.ext (two_pow_inj h)
  · intro a _ b _ h; exact Fin.ext (pow_inj h)
  · rw [disjoint_left]
    intro m h1 h2
    simp only [mem_image, mem_filter, mem_univ, true_and] at h1 h2
    obtain ⟨a, -, rfl⟩ := h1
    obtain ⟨b, -, hb⟩ := h2
    exact pow_ne_two_pow _ _ hb.symm

lemma ofParts_toParts (c : Fin (n + 1) → Fin 4) : ofParts (toParts c) = c := by
  funext k
  apply Fin.ext
  simp only [ofParts, mem_toParts_pow, mem_toParts_two_pow]
  have := (c k).isLt
  interval_cases h : (c k : ℕ) <;> simp

lemma toParts_ofParts {S : Finset ℕ} (hS : S ∈ parts n) : toParts (ofParts (n := n) S) = S := by
  simp only [parts, mem_filter, mem_powerset] at hS
  obtain ⟨hsub, hsum⟩ := hS
  ext m
  rw [mem_toParts]
  constructor
  · rintro ⟨k, ⟨hk, rfl⟩ | ⟨hk, rfl⟩⟩
    · rw [val_ofParts] at hk
      by_contra h; rw [ite_eq_right h] at hk; split_ifs at hk
    · rw [val_ofParts] at hk
      by_contra h; rw [ite_eq_right h] at hk; split_ifs at hk <;> omega
  · intro hm
    have hmS := hsub hm
    simp only [mem_filter, mem_range] at hmS
    obtain ⟨hmn, k, -, hk⟩ := hmS
    have hkn : k < n + 1 := by
      have := lt_three_pow k
      rcases hk with rfl | rfl <;> omega
    refine ⟨⟨k, hkn⟩, ?_⟩
    rw [val_ofParts]
    rcases hk with rfl | rfl
    · refine Or.inl ⟨?_, rfl⟩
      rw [ite_eq_left hm]
      split_ifs <;> omega
    · refine Or.inr ⟨?_, rfl⟩
      rw [ite_eq_left hm]
      split_ifs <;> omega

/-- **Mathar's conjecture.** The two counts agree for every `n`. -/
theorem card_reps_eq_card_parts (n : ℕ) : (reps n).card = (parts n).card := by
  refine card_nbij' toParts ofParts ?_ ?_ ?_ ?_
  · intro c hc
    simp only [reps, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc
    simp only [parts, coe_filter, mem_powerset, Set.mem_ofPred_eq]
    refine ⟨?_, by rw [sum_toParts, hc]⟩
    intro m hm
    simp only [mem_filter, mem_range]
    simp only [toParts, mem_union, mem_image, mem_filter, mem_univ, true_and] at hm
    rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · refine ⟨?_, (isPart_iff _).2 ⟨k, Or.inl rfl⟩⟩
      have : 3 ^ (k : ℕ) ≤ (c k : ℕ) * 3 ^ (k : ℕ) :=
        Nat.le_mul_of_pos_left _ (by omega)
      have := single_le_sum (f := fun j : Fin (n + 1) => (c j : ℕ) * 3 ^ (j : ℕ))
        (fun _ _ => Nat.zero_le _) (mem_univ k)
      omega
    · refine ⟨?_, (isPart_iff _).2 ⟨k, Or.inr rfl⟩⟩
      have : 2 * 3 ^ (k : ℕ) ≤ (c k : ℕ) * 3 ^ (k : ℕ) := Nat.mul_le_mul_right _ hk
      have := single_le_sum (f := fun j : Fin (n + 1) => (c j : ℕ) * 3 ^ (j : ℕ))
        (fun _ _ => Nat.zero_le _) (mem_univ k)
      omega
  · intro S hS
    simp only [reps, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    rw [← sum_toParts, toParts_ofParts hS]
    simp only [parts, coe_filter, Set.mem_ofPred_eq] at hS
    exact hS.2
  · intro c _
    exact ofParts_toParts c
  · intro S hS
    exact toParts_ofParts hS

end A054390
