# OEIS A374571: `a(n)` is odd iff `n` is Fibbinary

**Source:** [OEIS A374571](https://oeis.org/A374571) (Paul D. Hanna, 2024).

## Problem

Let `A(x) = Σ_{n≥0} a(n) xⁿ` with `a(0) = 1` satisfy

```
A(x) = A(x²) − x·A(x²)².
```

The sequence starts `1, −1, −1, 2, −1, 1, 2, −6, −1, 5, 1, 0, …`

> **Conjecture (OEIS):** for `n > 0`, `a(n)` is odd iff `n` is a Fibbinary number (A003714), i.e.
> the binary representation of `n` has no two adjacent `1`s.

## Result

**Theorem.** For every integer power series `A` with `A(0) = 1` satisfying the equation, and
every `n ≥ 0`, `a(n)` is odd if and only if `n` is Fibbinary. Such a series exists.

## Proof

Modulo 2, squaring a power series with coefficients in `𝔽₂` gives `F(x)² = F(x²)`: the swap
`(i, j) ↦ (j, i)` pairs up the off-diagonal terms of `Σ_{i+j=n} f_i f_j`. So the equation
reduces to

```
A(x) ≡ A(x²) + x·A(x⁴)   (mod 2).
```

Comparing coefficients:

* `a(2n) ≡ a(n)`;
* `a(4k+1) ≡ a(k)`;
* `a(4k+3) ≡ 0`.

Moreover `a(0) = 1`. The Fibbinary numbers obey the same recursion:
* `0` is Fibbinary;
* `2n` is Fibbinary iff `n` is;
* `4k+1` (binary `…01`) is Fibbinary iff `k` is;
* `4k+3` (binary `…11`) never is.

Strong induction on `n` finishes the proof. ∎

## Lean formalization

[`A374571.lean`](A374571.lean) builds with no warnings. It uses no `sorry` and no
`native_decide`, and `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`.
The functional equation is stated literally, using Mathlib's `PowerSeries.subst`.

| Statement | Lean |
|---|---|
| Fibbinary (`∀ i, ¬(bit i ∧ bit (i+1))`) | `A374571.Fibbinary` |
| the equation, `A(0) = 1` | `A374571.IsSolution` |
| mod 2 squaring lemma | `A374571.conv_zmod_two` |
| recursion mod 2 | `A374571.coeff_mod_two` |
| **Hanna's conjecture** | `A374571.odd_iff_fibbinary : IsSolution A → (Odd (coeff n A) ↔ Fibbinary n)` |
| a solution exists | `A374571.isSolution_mk`, `A374571.exists_isSolution` |
| first 12 terms match OEIS | `example` (by `decide +kernel`) |

## Novelty

Checked on 2026-09-29:

* The OEIS entry (revision #43, Feb 2026) lists the statement as a *Conjecture*, without a
  proof.
* A web search found no proof.
* The sequence is absent from:
  - formal-conjectures;
  - the AlphaProof Nexus results;
  - the OEIS OPEN benchmark;
  - S. Fried's OEIS-conjecture papers.
