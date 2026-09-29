# OEIS A001481: sums of two distinct sums of two squares

## Source

[OEIS A001481](https://oeis.org/A001481): numbers that are the sum of 2 squares,
`0, 1, 2, 4, 5, 8, 9, 10, 13, 16, 17, 18, 20, 25, …`. The entry has this comment:

> Conjecture: barring the 0+2, 0+4, 0+8, 0+16, ... sequence, the sum of 2 distinct terms in
> this sequence is never a power of 2. — _J. Lowell_, Jan 14 2022

## Statement

Let `a ≠ b` be sums of two squares of nonnegative integers with `a + b = 2ᵏ`. Then
`{a, b} = {0, 2ᵏ}`. These exceptions do occur, because every `2ᵏ` is a sum of two squares.

## Proof

**Lemma 1 (halving).** If `n = x² + y²` is even, then `n/2` is a sum of two squares.
Since `n` is even, `x` and `y` have the same parity. Say `x = y + 2d`. Then
`n/2 = (y+d)² + d²`.

**Lemma 2.** An odd sum of two squares is `≡ 1 (mod 4)`, since squares are `≡ 0, 1 (mod 4)`.

**Theorem.** Induction on `k`. For `k = 0`, `a + b = 1` forces `{a, b} = {0, 1}`. Let
`a + b = 2ᵏ⁺¹`.
* If `a` and `b` are both even, then by Lemma 1, `a/2` and `b/2` are distinct sums of two
  squares with sum `2ᵏ`. By induction, one of them is `0`.
* If exactly one of them is odd, then `a + b` is odd, which is impossible for `2ᵏ⁺¹`.
* If both are odd, then by Lemma 2 `a + b ≡ 2 (mod 4)`. So `2ᵏ⁺¹ = 2`, and `a = b = 1`,
  contradicting `a ≠ b`.

Finally, `2⁰ = 1² + 0²` and `2ᵏ = x² + y²` gives `2ᵏ⁺¹ = (x+y)² + (x−y)²`. So each `0 + 2ᵏ` is
a genuine exception. ∎

## Lean formalization

File: [`A001481.lean`](A001481.lean).

| Statement | Lean name |
|---|---|
| membership in A001481 (`n = x² + y²`, `x, y ∈ ℕ`) | `A001481.IsSumTwoSq` |
| first terms match the OEIS data (`n ≤ 50`) | `example` (by `decide +kernel`) |
| Lemma 1 | `A001481.IsSumTwoSq.half` |
| Lemma 2 | `A001481.IsSumTwoSq.mod_four` |
| `2ᵏ` is a sum of two squares | `A001481.isSumTwoSq_two_pow` |
| main theorem (one of `a`, `b` is `0`) | `A001481.lowell` |
| the conjecture as stated, with its exceptions | `A001481.lowell_conjecture` |

`#print axioms A001481.lowell_conjecture` lists only `propext`, `Classical.choice` and
`Quot.sound`.

## Novelty check (2026-09-29)

* The OEIS entry (revision current on 2026-09-29) still states the comment as a conjecture,
  with no note of a proof.
* A web search for a proof of the statement found only the OEIS conjecture itself.
* [formal-conjectures](https://github.com/google-deepmind/formal-conjectures): no file
  mentions A001481.
* [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results):
  no file mentions A001481.
* OEIS OPEN benchmark (arXiv:2608.11941): no proof of this statement was found.
* [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing): no
  file for A001481.
* [Horace-Maxwell/ai4math-results](https://github.com/Horace-Maxwell/ai4math-results)
  (`ATTEMPTS.md`): A001481 is not mentioned.

The proof is elementary, so the statement may well be folklore. We found no published or
recorded proof of this conjecture.
