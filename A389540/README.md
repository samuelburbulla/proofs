# OEIS A389540: `a(n)` is odd iff `n` is a power of 2

**Source:** [OEIS A389540](https://oeis.org/A389540) (Paul D. Hanna, Nov 16 2025).

## Problem

Let `A(x) = Σ_{n≥1} a(n) xⁿ` be the power series with `A(x) = x + O(x²)` and

```
A(x)² = A(2x − 2A(x)) / 2.
```

The sequence starts `1, −1, 2, −7, 26, −98, 388, −1615, 6914, −30118, …`

The OEIS entry states:

> **Conjecture:** `a(n)` is odd iff `n = 2ᵏ` for `k ≥ 0`.

## Result

**Theorem.** Let `A ∈ ℤ[[x]]` with `A(0) = 0`, `a(1) = 1` and `2A(x)² = A(2x − 2A(x))`.
Then for every `n ≥ 1`, `a(n)` is odd if and only if `n` is a power of 2.

**Theorem.** Such an `A` exists.

## Proof

**Parity.** Let `B = 2x − 2A = 2(x − A)`. Since `B(0) = 0`,

```
A(B) = Σ_{d≥1} a(d) Bᵈ = Σ_{d≥1} a(d) 2ᵈ (x − A)ᵈ .
```

Take the coefficient of `xⁿ` with `n ≥ 2`. The `d = 1` term gives `2·[xⁿ](x − A) = −2a(n)`.
Every term with `d ≥ 2` is divisible by `2ᵈ`, hence by `4`. So the equation gives

```
2·[xⁿ]A² = −2a(n) + 4K    for some integer K,
```

which means `a(n) + [xⁿ]A²` is even. Modulo 2, `[xⁿ]A² = Σ_{i+j=n} a(i)a(j)`. The swap
`(i, j) ↦ (j, i)` pairs up the terms with `i ≠ j`, and each pair adds up to an even number.
So, modulo 2, the sum equals `a(n/2)² ≡ a(n/2)` if `n` is even and `0` if `n` is odd.
In other words, `A(x)² ≡ A(x²) (mod 2)`. Hence, for `n ≥ 2`,

* `n` odd: `a(n) ≡ 0 (mod 2)`;
* `n` even: `a(n) ≡ a(n/2) (mod 2)`.

Strong induction on `n` finishes the proof. `a(1) = 1` is odd. For odd `n ≥ 3`, `a(n)` is even
and `n` is not a power of 2. For `n = 2m`, `a(n)` has the same parity as `a(m)`, and `2m` is
a power of 2 iff `m` is one. ∎

Note that `A(x)² ≡ A(x²)` holds for *every* integer power series. The content of the
equation is the congruence `A(x) ≡ −A(x)² ≡ A(x)² (mod 2)` on the coefficients from `x²` on. This gives
`A ≡ x + A(x²)`, i.e. `A ≡ x + x² + x⁴ + x⁸ + ⋯ (mod 2)`.

**Existence.** Let `R(y) = Σ_{k≥0} 2^(2ᵏ−k−1) y^(2ᵏ) = y + y² + 2y⁴ + 16y⁸ + 2048y¹⁶ + ⋯`
(formula (1) of the entry). Comparing coefficients shows `R(2y²) = 2R(y) − 2y`.
Since `R(0) = 0` and `R'(0) = 1`, `R` has an integer compositional inverse `A`, with
`R(A(x)) = x` and `A(R(y)) = y`. Substituting `y = A(x)` gives
`R(2A²) = 2R(A) − 2A = 2x − 2A`. Therefore

```
A(2x − 2A) = A(R(2A²)) = 2A².
```
∎

## Lean formalization

[`A389540.lean`](A389540.lean) builds with Lean 4 and Mathlib (`lake build`). It uses
no `sorry`, no `native_decide` and no extra axioms. `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

The functional equation is stated literally, using Mathlib's power series substitution
`PowerSeries.subst`:

```lean
def IsSolution (A : ℤ⟦X⟧) : Prop :=
  constantCoeff A = 0 ∧ coeff 1 A = 1 ∧ 2 * A ^ 2 = A.subst (2 * X - 2 * A)
```

| Statement | Lean |
|---|---|
| coefficient `n+2` of the equation | `A389540.coeff_eq` |
| `a(n) + [xⁿ]A²` is even for `n ≥ 2` | `A389540.even_coeff_add_coeff_sq` |
| mod 2 squaring lemma | `A389540.conv_zmod_two` |
| **Hanna's conjecture** | `A389540.odd_iff_pow_two : IsSolution A → 1 ≤ n → (Odd (coeff n A) ↔ ∃ k, n = 2 ^ k)` |
| every solution starts `x − x² + 2x³` (matches OEIS) | `A389540.coeff_two_three` |
| `R(2y²) = 2R(y) − 2y` | `A389540.R_functional_eq` |
| coefficients of `R` are `2^(2ᵏ−k−1)` at `2ᵏ` | `A389540.r_pow_two` |
| a solution exists (`A = R⁻¹`) | `A389540.isSolution_A`, `A389540.exists_isSolution` |

## Novelty

Checked on 2026-09-27:

* The OEIS entry (revision #20, Nov 18 2025) still lists the statement as a *Conjecture*.
  It gives no proof and has no link to one.
* A web search found no proof. S. Fried's papers proving OEIS conjectures
  ([arXiv:2410.07237](https://arxiv.org/abs/2410.07237),
  [arXiv:2607.24832](https://arxiv.org/abs/2607.24832)) do not cover A389540.
