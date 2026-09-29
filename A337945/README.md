# OEIS A337945: numbers with a solution of s² + t² = k·m, s + t = m

## Source

[OEIS A337945](https://oeis.org/A337945) (W. I. Hurt, 2020): numbers `m` with a solution
`(s, t, k)` of `s² + t² = k·m`, `s + t = m`, `1 ≤ s ≤ t` and `1 ≤ k ≤ m − 1`.
The terms are `2, 4, 6, 8, 9, 10, 12, 14, 16, 18, 20, 22, 24, 25, …`

> Conjecture: k is a term <=> k * Clausen(k, 1) <> 2 * Clausen(k, 0), (Clausen = A160014).
> In other words: k is in this sequence iff it is not an odd squarefree number.
> — _Peter Luschny_, Jun 08 2023

Here `Clausen(n, k)` is the product of the primes `p` with `p − k ∣ n` ([A160014](https://oeis.org/A160014)).
So `Clausen(n, 0) = rad(n)`, and `Clausen(n, 1)` is the classical Clausen number.

## Statement

For every `m ≥ 1`:
1. `m` is a term ⟺ `m` is not an odd squarefree number;
2. `m` is a term ⟺ `m · Clausen(m, 1) ≠ 2 · Clausen(m, 0)`.

## Proof

**1.** Put `t = m − s`. Then `s² + t² = m² − 2m·s + 2s² ≡ 2s² (mod m)`. The bounds on `k` hold
automatically: `k ≤ m − 1` ⟺ `2st ≥ m`, which holds because `s ≥ 1` and `t ≥ m/2`. Hence `m` is
a term iff `m ∣ 2s²` for some `1 ≤ s ≤ m/2`, apart from checking `k ≥ 1`, which is clear.
* If `m` is even, `s = t = k = m/2` is a solution.
* If `m` is odd, then `m ∣ 2s²` ⟺ `m ∣ s²`.
  - If `m` is squarefree, this forces `m ∣ s`, which is impossible for `0 < s < m`.
  - If `p² ∣ m`, then `s₀ = m/p` satisfies `m ∣ s₀²`, and so does `m − s₀`. The smaller of the
    two gives a solution, with `k ≥ 1` since `m ≥ 9`.

**2.** `Clausen(m, 1)` is divisible by `2` (from the divisor `1`), and by `6` if `m` is even (from
the divisor `2`). Also `Clausen(m, 0) = rad(m) ≤ m`, with equality iff `m` is squarefree.
* If `m` is odd and squarefree, every divisor `d` is odd, so the only prime of the form `d + 1`
  is `2`. Then `Clausen(m, 1) = 2` and `m · 2 = 2 · rad(m)`.
* If `m` is even, `m · Clausen(m, 1) ≥ 6m > 2m ≥ 2 rad(m)`.
* If `m` is odd and not squarefree, `m · Clausen(m, 1) ≥ 2m > 2 rad(m)`.

Combining with part 1 gives part 2. ∎

## Lean formalization

File: [`A337945.lean`](A337945.lean). `A337945.IsTerm` is the definition from the entry, and the
terms `≤ 42` are checked against the OEIS data by `decide +kernel`. `A337945.clausen n k` is the
product of the primes of the form `d + k` with `d ∣ n`, as in the Maple program of A160014.

| Statement | Lean name |
|---|---|
| form 1 (not odd squarefree) | `A337945.isTerm_iff` |
| form 2 (Clausen numbers) | `A337945.isTerm_iff_clausen` |
| `Clausen(n, 0) = rad(n)` | `A337945.clausen_zero` |
| `rad(m) < m` for non-squarefree `m` | `A337945.rad_lt` |

`#print axioms A337945.isTerm_iff_clausen` lists only `propext`, `Classical.choice` and
`Quot.sound`.

## Novelty check (2026-09-29)

* The OEIS entry (revision #20, Jun 08 2023) still states the equivalence as a conjecture.
* A web search found no proof.
* None of the following mentions A337945:
  - [formal-conjectures](https://github.com/google-deepmind/formal-conjectures);
  - [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results);
  - [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)
    (file names);
  - [Horace-Maxwell/ai4math-results](https://github.com/Horace-Maxwell/ai4math-results);
  - [farev/Matematica](https://github.com/farev/Matematica).
* [astrafala/Conjectures](https://github.com/astrafala/Conjectures) lists it only in
  `engine/deep-check/unread-unsettled.txt`, i.e. as not settled.
* OEIS OPEN benchmark (arXiv:2608.11941): no proof was found.
