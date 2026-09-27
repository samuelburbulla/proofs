# OEIS A397588: `a(n)` is odd iff `n` is a power of 2

**Source:** [OEIS A397588](https://oeis.org/A397588) (Paul D. Hanna, Jul 03 2026).

## Problem

Let `A(x) = Σ_{n≥1} a(n) xⁿ` be the power series satisfying

```
A(x) = x + (x · A(x)²)'
```

The sequence starts `1, 3, 24, 285, 4284, 75978, 1530720, 34237485, 837481140, …`

The OEIS entry states:

> **Conjecture:** `a(n)` is odd iff `n` is a power of 2 for `n ≥ 1`.

It also says, without proof, that `a(n)` is divisible by 3 for `n > 1`.

## Result

**Theorem.** For `n ≥ 1`, `a(n)` is odd if and only if `n = 2ᵏ` for some `k ≥ 0`.

**Theorem.** For `n ≥ 2`, `3 ∣ a(n)`.

## Proof

**Recurrence.** Put `a(0) = 0`. The coefficient of `xⁿ` in `(x·A²)'` is `(n+1)·[xⁿ]A²`.
Comparing the coefficients of `xⁿ` on both sides of the equation gives

```
a(n) = [n = 1] + (n+1) · Σ_{i+j=n} a(i) a(j),            (1)
```

so `a(1) = 1` and `a(n) = (n+1) Σ_{k=1}^{n-1} a(k) a(n-k)` for `n ≥ 2` (Manyama's formula in the
entry). Terms with `i = 0` or `j = 0` vanish, so the right-hand side of (1) only involves
`a(k)` with `k < n`. This means (1) determines the sequence uniquely.

**Lemma (squaring mod 2).** For any `f : ℕ → 𝔽₂`,
`Σ_{i+j=n} f(i) f(j) = f(n/2)` if `n` is even, and `0` if `n` is odd.

*Proof.* The swap `(i, j) ↦ (j, i)` pairs up the terms with `i ≠ j`. Each pair adds up
to `2 f(i) f(j) = 0`. The only possible fixed point is `i = j = n/2`, which exists only
when `n` is even. It contributes `f(n/2)² = f(n/2)`, because `x² = x` in `𝔽₂`.
(Equivalently, `A(x)² ≡ A(x²) (mod 2)`.) ∎

Reducing (1) mod 2 with the lemma gives, for `n ≥ 2`:

* `n` odd: `Σ_{i+j=n} a(i)a(j) ≡ 0`, so `a(n) ≡ 0`;
* `n` even: `n+1 ≡ 1`, so `a(n) ≡ a(n/2)`.

Now use strong induction on `n ≥ 1`. `a(1) = 1` is odd and `1 = 2⁰`. For odd `n ≥ 3`,
`a(n)` is even and `n` is not a power of 2. For even `n = 2m`, `a(n)` has the same
parity as `a(m)`, and `2m` is a power of 2 iff `m` is one. ∎

**Divisibility by 3.** `a(2) = 3·a(1)² = 3`. For `n ≥ 3`, every nonzero term
`a(i)a(j)` of (1) has `i, j ≥ 1` and `i + j = n ≥ 3`, so one of `i, j` lies in `[2, n)`.
By induction that factor is divisible by 3, so `3 ∣ a(n)`. ∎

## Lean formalization

[`A397588.lean`](A397588.lean) builds with Lean 4 and Mathlib (`lake build`). It uses
no `sorry`, no `native_decide` and no extra axioms. `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

| Statement | Lean |
|---|---|
| definition by the recurrence | `A397588.a` |
| first ten terms match OEIS | `example` (by `decide +kernel`) |
| `A(x) = x + (x·A(x)²)'` over `ℤ⟦X⟧` | `A397588.gf_eq` |
| this is the only solution with `A(0) = 0` | `A397588.gf_unique` |
| mod 2 squaring lemma | `A397588.conv_zmod_two` |
| **Hanna's conjecture** | `A397588.odd_iff_pow_two : 1 ≤ n → (Odd (a n) ↔ ∃ k, n = 2 ^ k)` |
| `3 ∣ a(n)` for `n ≥ 2` | `A397588.three_dvd` |

## Novelty

Checked on 2026-09-27:

* The OEIS entry (revision #18, Jul 04 2026) still lists the parity statement as a
  *Conjecture*. It gives no proof and has no link to one.
* A web search found no proof of this statement for A397588.
* S. Fried's papers proving OEIS conjectures ([arXiv:2410.07237](https://arxiv.org/abs/2410.07237),
  [arXiv:2607.24832](https://arxiv.org/abs/2607.24832)) do not cover A397588.
