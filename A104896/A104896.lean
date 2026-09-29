import Mathlib

/-!
# OEIS A104896

`a(0) = 0`, `a(n) = 7·a(n-1) + 7`.

A. Wajnberg conjectured (2005): `a(n)` is also the number of integers from `0` to `10ⁿ − 1`
that lack `0`, `1` and `2` as a digit.

We prove it (`A104896.card_lacks`). Write `m = 10q + r` with `r` the last digit. Then `m`
lacks `0, 1, 2` iff `r ∈ {3,…,9}` and `q` is either `0` or lacks `0, 1, 2` itself. So the count
`c(n)` of such `m < 10ⁿ` satisfies `c(n+1) = 7·(c(n) + 1)`, which is the defining recursion.
-/

open Finset

namespace A104896

/-- The sequence: `a(0) = 0`, `a(n+1) = 7 a(n) + 7`. -/
def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => 7 * a n + 7

example : (List.range 6).map a = [0, 7, 56, 399, 2800, 19607] := by decide

/-- `m` has no digit `0`, `1` or `2` in its decimal expansion. The number `0` is written `0`, so
it does not qualify; for `m > 0`, `Nat.digits 10 m` is the list of its decimal digits. -/
def Lacks (m : ℕ) : Prop := m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, 3 ≤ d

instance : DecidablePred Lacks := fun m => by unfold Lacks; infer_instance

/-- The count of such integers in `[0, 10ⁿ)`. -/
def c (n : ℕ) : ℕ := #{m ∈ range (10 ^ n) | Lacks m}

example : (List.range 4).map c = [0, 7, 56, 399] := by decide +kernel

lemma lacks_iff {m : ℕ} (hm : m ≠ 0) :
    Lacks m ↔ 3 ≤ m % 10 ∧ (m / 10 = 0 ∨ Lacks (m / 10)) := by
  rw [Lacks, Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hm)]
  simp only [List.mem_cons, forall_eq_or_imp, ne_eq, hm, not_false_eq_true, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases hq : m / 10 = 0
    · exact Or.inl hq
    · exact Or.inr ⟨hq, h2⟩
  · rintro ⟨h1, h2 | ⟨-, h2⟩⟩
    · refine ⟨h1, ?_⟩
      rw [h2]; simp
    · exact ⟨h1, h2⟩

lemma c_succ (n : ℕ) : c (n + 1) = 7 * (c n + 1) := by
  have hprod : c (n + 1) = #(({q ∈ range (10 ^ n) | q = 0 ∨ Lacks q}) ×ˢ Icc 3 9) := by
    unfold c
    refine card_nbij' (fun m => (m / 10, m % 10)) (fun p => 10 * p.1 + p.2) ?_ ?_ ?_ ?_
    · intro m hm
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hm
      obtain ⟨hlt, hl⟩ := hm
      have := (lacks_iff hl.1).1 hl
      simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_ofPred_eq, coe_Icc,
        Set.mem_Icc]
      refine ⟨⟨?_, this.2⟩, this.1, by omega⟩
      rw [pow_succ] at hlt
      omega
    · intro p hp
      simp only [coe_product, coe_filter, mem_range, Set.mem_prod, Set.mem_ofPred_eq, coe_Icc,
        Set.mem_Icc] at hp
      obtain ⟨⟨hq, hql⟩, hr1, hr2⟩ := hp
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
      have hne : 10 * p.1 + p.2 ≠ 0 := by omega
      refine ⟨by rw [pow_succ]; omega, (lacks_iff hne).2 ⟨by omega, ?_⟩⟩
      have : (10 * p.1 + p.2) / 10 = p.1 := by omega
      rw [this]; exact hql
    · intro m _; simp only; omega
    · intro p hp
      simp only [coe_product, coe_Icc, Set.mem_prod, Set.mem_Icc] at hp
      ext <;> simp only <;> omega
  rw [hprod, card_product, Nat.card_Icc, filter_or]
  rw [card_union_of_disjoint]
  · have : ({q ∈ range (10 ^ n) | q = 0} : Finset ℕ) = {0} := by
      ext q; simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨by positivity, rfl⟩
    rw [this, card_singleton, c]
    ring
  · rw [disjoint_left]
    intro q h1 h2
    simp only [mem_filter] at h1 h2
    exact h2.2.1 h1.2

/-- **Wajnberg's conjecture.** The number of integers in `[0, 10ⁿ)` without a digit `0`, `1`,
`2` is `a(n)`. -/
theorem card_lacks (n : ℕ) : c n = a n := by
  induction n with
  | zero => decide
  | succ n ih => rw [c_succ, ih, a]; ring

end A104896

#print axioms A104896.card_lacks
