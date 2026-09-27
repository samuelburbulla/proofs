# OEIS A361032–A361035: integrality and parity of Bala's quartic array

**Sources:** [OEIS A361032](https://oeis.org/A361032), [A361033](https://oeis.org/A361033),
[A361034](https://oeis.org/A361034), [A361035](https://oeis.org/A361035)
(Peter Bala, Mar 01 2023).

## Problem

Bala defines the square array

```
T(n,k) = F(n) · (4k)! / (k! · (k+n+1)!³),     F(n) = (4n+4)! / (8 · (n+1)!),     n, k ≥ 0,
```

by analogy with Gessel's generalized Catalan numbers. He remarks that this choice of `F(n)`
"**appears to produce integer values**". Rows 0, 1, 2 of the array are

| row | sequence | formula | conjecture in the entry |
|---|---|---|---|
| 0 | A361033 | `3·(4k)!/(k!(k+1)!³)` | `a(k)` is odd iff `k = 2ʲ − 1` |
| 1 | A361034 | `2520·(4k)!/(k!(k+2)!³)` | `a(k)` is odd iff `k = 2ʲ − 2`, `j ≥ 1` |
| 2 | A361035 | `9979200·(4k)!/(k!(k+3)!³)` | `a(k)` is odd iff `k = 2ʲ − 3`, `j ≥ 2` |

## Result

**Theorem 1 (integrality).** `T(n,k)` is an integer for all `n, k ≥ 0`.

**Theorem 2 (2-adic valuation).** With `M = n + k + 1` and `s₂(M)` the binary digit sum of `M`,

```
v₂(T(n,k)) = 3·(s₂(M) − 1).
```

**Corollary.** `T(n,k)` is odd iff `n + k + 1` is a power of 2. Taking `n = 0, 1, 2`
proves all three conjectures.

## Proof

Write `N = n + 1`, so `T(n,k) = (4N)!·(4k)! / (8·N!·k!·(N+k)!³)`.

**Odd primes `p`.** By Legendre's formula `v_p(m!) = Σ_{i≥1} ⌊m/pⁱ⌋`, and `v_p(8) = 0`. So it is
enough to show, for every integer `q ≥ 1`,

```
⌊N/q⌋ + ⌊k/q⌋ + 3⌊(N+k)/q⌋ ≤ ⌊4N/q⌋ + ⌊4k/q⌋ .
```

Let `a = ⌊N/q⌋`, `b = ⌊k/q⌋`. Then `⌊4N/q⌋ ≥ 4a` and `⌊4k/q⌋ ≥ 4b`, and `⌊(N+k)/q⌋` is `a+b`
or `a+b+1`. In the first case the inequality is immediate. In the second case,
`4(a+b+1)q ≤ 4N + 4k < (⌊4N/q⌋ + ⌊4k/q⌋ + 2)q`, so `⌊4N/q⌋ + ⌊4k/q⌋ ≥ 4a + 4b + 3`. ∎

**The prime 2.** Legendre's formula for `p = 2` reads `v₂(m!) = m − s₂(m)`. In particular
`v₂((4m)!) − v₂(m!) = 3m`. Hence

```
v₂(T) = [v₂(N!) + 3N] + [v₂(k!) + 3k] − 3 − v₂(N!) − v₂(k!) − 3·v₂((N+k)!)
      = 3(N + k) − 3 − 3(N + k − s₂(N+k)) = 3·(s₂(M) − 1) ≥ 0 .
```

So `v₂(T) ≥ 0`, which completes the proof of integrality. Also, `v₂(T) = 0` iff `s₂(M) = 1`,
i.e. iff `M` is a power of 2. ∎

For the rows, `F(0) = 4!/8 = 3`, `F(1) = 8!/16 = 2520` and `F(2) = 12!/48 = 9979200`. Row `n`
is therefore odd exactly when `k + n + 1 = 2ʲ`.

## Lean formalization

[`A361032.lean`](A361032.lean) builds with Lean 4 and Mathlib (`lake build`). It uses
no `sorry`, no `native_decide` and no extra axioms. `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

The Lean proof avoids binary digit sums. It uses `v₂((2m)!) = v₂(m!) + m` and
`v₂((2m+1)!) = v₂((2m)!)` to show `v₂(m!) ≤ m − 1`, with equality iff `m` is a power of 2.

| Statement | Lean |
|---|---|
| definition `T n k = (4(n+1))!(4k)! / (8 (n+1)! k! (n+k+1)!³)` | `A361032.T` |
| `T` equals Bala's expression in `ℚ` | `A361032.T_cast` |
| Legendre floor inequality | `A361032.floor_ineq` |
| **integrality** | `A361032.den_dvd_num` |
| `v₂(T(n,k)) = 3(M − 1 − v₂(M!))` | `A361032.padicValNat_two_T` |
| **parity of the array** | `A361032.odd_T_iff : Odd (T n k) ↔ ∃ j, n + k + 1 = 2 ^ j` |
| rows defined by the OEIS formulas, equal to rows 0–2 | `A361033_eq`, `A361034_eq`, `A361035_eq` |
| first terms match OEIS | `example`s (by `decide +kernel`) |
| **A361033 conjecture** | `A361032.A361033_odd_iff : Odd (A361033 k) ↔ ∃ j, k = 2 ^ j - 1` |
| **A361034 conjecture** | `A361032.A361034_odd_iff : Odd (A361034 k) ↔ ∃ j ≥ 1, k = 2 ^ j - 2` |
| **A361035 conjecture** | `A361032.A361035_odd_iff : Odd (A361035 k) ↔ ∃ j ≥ 2, k = 2 ^ j - 3` |

## Novelty

Checked on 2026-09-27:

* The entries A361033 (rev. #14, Jul 2024), A361034 and A361035 (Mar 2023) still list the
  parity statements as *Conjectures*. A361032 (rev. #16, Jan 2024) still says only that `F(n)`
  "appears to produce integer values". None of them gives or links a proof.
* A web search found no proof.
* The sequences do not appear in:
  - S. Fried's papers proving OEIS conjectures
    ([arXiv:2410.07237](https://arxiv.org/abs/2410.07237),
    [arXiv:2607.24832](https://arxiv.org/abs/2607.24832));
  - the AlphaProof Nexus OEIS results (Tsoukalas et al.,
    [arXiv:2605.22763](https://arxiv.org/abs/2605.22763),
    [results repo](https://github.com/google-deepmind/alphaproof-nexus-results));
  - the OEIS OPEN benchmark ([arXiv:2608.11941](https://arxiv.org/abs/2608.11941));
  - DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
    library.
