# OEIS A399155: subtracting the largest prime factor is never slower

## Source

[OEIS A399155](https://oeis.org/A399155) (J. Dilkhush, Aug 2026):
`a(n) = f(n) − g(n)`, where
* `f(n)` is the number of steps to reach `0` from `n` by repeatedly subtracting the
  **smallest** prime factor of the current value;
* `g(n)` is the same count when the **largest** prime factor is subtracted.

> Conjecture: a(n) >= 0 for all n >= 2; equivalently, subtracting the largest prime factor
> never takes more steps than subtracting the smallest.

## Statement

For every `n ≥ 2`: `g(n) ≤ f(n)`.

## Proof

**Lemma 1.** If `q` is a prime dividing `m > 0`, then `g(m) ≤ m/q`.

*Proof.* Strong induction on `m`. Let `P` be the largest prime factor of `m`, so `P ≥ q`, and
write `m = kP`. The first step goes to `m − P = (k−1)P`. If `k = 1`, then `g(m) = 1 ≤ m/q`.
Otherwise, apply the induction hypothesis to `(k−1)P` with the prime `P`. This gives
`g(m) = 1 + g((k−1)P) ≤ 1 + (k−1) = m/P ≤ m/q`. ∎

**Lemma 2.** Let `p` be the smallest prime factor of `n ≥ 2`. Then `f(n) ≥ n/p`.

*Proof.* For even numbers every step subtracts `2`, so `f(2k) = k`, which is the claim with
`p = 2`. For odd `n`, `p` is odd, so `n − p` is even and `f(n) = 1 + (n−p)/2`. Writing
`n = cp`, we get `(n−p)/2 = p(c−1)/2 ≥ c−1`, so `f(n) ≥ c = n/p`. ∎

**Theorem.** Apply Lemma 1 with `q = p`, the smallest prime factor of `n`, and then Lemma 2:
`g(n) ≤ n/p ≤ f(n)`. ∎

## Lean formalization

File: [`A399155.lean`](A399155.lean). The largest prime factor is
`A399155.lpf n = max n.primeFactors`, and the step counts are `A399155.f` and `A399155.g`,
defined by well-founded recursion exactly as in the OEIS programs. `A399155.a n = f n − g n`
is checked against the OEIS data `a(2..33)` by `decide +kernel`.

| Statement | Lean name |
|---|---|
| Lemma 1 | `A399155.g_le_div` |
| Lemma 2 | `A399155.div_le_f` |
| the conjecture `g(n) ≤ f(n)` | `A399155.g_le_f` |
| `a(n) ≥ 0` for `n ≥ 2` | `A399155.a_nonneg` |

`#print axioms A399155.a_nonneg` lists only `propext`, `Classical.choice` and `Quot.sound`.

## Novelty check (2026-09-29)

* The OEIS entry (revision #15, Aug 27 2026) still states the inequality as a conjecture.
* A web search found no proof.
* [formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
  [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results),
  [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)
  (file names) and
  [Horace-Maxwell/ai4math-results](https://github.com/Horace-Maxwell/ai4math-results)
  (`ATTEMPTS.md`): none of them mentions A399155.
* OEIS OPEN benchmark (arXiv:2608.11941): the sequence dates from Aug 2026, and no proof was
  found.
