# OEIS A104896: integers without the digits 0, 1, 2

## Source

[OEIS A104896](https://oeis.org/A104896): `a(0) = 0`, `a(n) = 7·a(n−1) + 7`, i.e.
`0, 7, 56, 399, 2800, …`

> Conjecture: this is also the number of integers from 0 to 10^n - 1 that lack 0, 1 and 2 as a
> digit. — _Alexandre Wajnberg_, Apr 24 2005

## Statement

For every `n ≥ 0`, the number `c(n)` of integers `m` with `0 ≤ m < 10ⁿ` whose decimal expansion
contains none of the digits `0`, `1`, `2` equals `a(n)`. (The number `0` is written `0` and does
not count.)

## Proof

Let `m > 0` and write `m = 10q + r` with `0 ≤ r ≤ 9`. The decimal digits of `m` are those of `q`
(none if `q = 0`) followed by `r`. So `m` qualifies iff `r ∈ {3,…,9}` and either `q = 0` or `q`
qualifies. For `m < 10ⁿ⁺¹`, the quotient `q` ranges over `[0, 10ⁿ)`. Hence
`c(n+1) = 7·(c(n) + 1) = 7·c(n) + 7`. Since `c(0) = 0`, it follows that `c(n) = a(n)`. ∎

## Lean formalization

File: [`A104896.lean`](A104896.lean). `A104896.Lacks m` means `m ≠ 0` and every decimal digit of
`m` (Mathlib's `Nat.digits 10 m`) is at least `3`. `A104896.c n` counts such `m < 10ⁿ`. Both
`a` and `c` are checked against the OEIS data by `decide`.

| Statement | Lean name |
|---|---|
| `m` qualifies iff its last digit is `≥ 3` and `m / 10` is `0` or qualifies | `A104896.lacks_iff` |
| `c(n+1) = 7(c(n) + 1)` | `A104896.c_succ` |
| **Wajnberg's conjecture** `c(n) = a(n)` | `A104896.card_lacks` |

`#print axioms A104896.card_lacks` lists only `propext`, `Classical.choice` and `Quot.sound`.

## Novelty check (2026-09-29)

* The OEIS entry still states the statement as a conjecture.
* A web search found no proof.
* None of the following mentions A104896:
  - [formal-conjectures](https://github.com/google-deepmind/formal-conjectures);
  - [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results);
  - [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)
    (file names and contents);
  - [Horace-Maxwell/ai4math-results](https://github.com/Horace-Maxwell/ai4math-results);
  - [farev/Matematica](https://github.com/farev/Matematica).
* [astrafala/Conjectures](https://github.com/astrafala/Conjectures) lists it only in
  `engine/deep-check/unread-unsettled.txt`, i.e. as not settled.
* OEIS OPEN benchmark (arXiv:2608.11941): no proof was found.

The proof is elementary, so the statement may well be folklore. We found no recorded proof of
this conjecture.
