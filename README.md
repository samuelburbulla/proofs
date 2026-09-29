# Proofs of open problems

Proofs of previously open problems. Each proof is written out by hand and also
checked in [Lean 4](https://lean-lang.org/) with [Mathlib](https://github.com/leanprover-community/mathlib4).
See [AGENTS.md](AGENTS.md) for the rules.

| Problem | Statement | Status |
|---|---|---|
| [A361032](A361032/) | OEIS A361032–A361035, Bala's array `F(n)(4k)!/(k!(k+n+1)!³)`: integrality, and odd iff `n+k+1` is a power of 2 (settles the conjectures in A361033, A361034, A361035) | proved, checked in Lean |
| [WOWII19](WOWII19/) | Graffiti.pc / Written on the Wall II Conjecture 19: `⌊avg ecc + max_v α(N(v))⌋ ≤ b(G)` for connected graphs | proved, checked in Lean (also inside formal-conjectures) |
| [A054390](A054390/) | OEIS A054390 (Mathar): hyperternary representations of `n` ↔ partitions of `n` into distinct parts `3ᵏ`, `2·3ᵏ` | proved, checked in Lean |
| [A001481](A001481/) | OEIS A001481 (Lowell): two distinct sums of two squares never sum to a power of 2, except `0 + 2ᵏ` | proved, checked in Lean |
| [A216971](A216971/) | OEIS A216971 (Perry): every entry of row `n` of the recurrent-element triangle is divisible by `n` | proved, checked in Lean |
| [A337945](A337945/) | OEIS A337945 (Luschny): `m` has a solution of `s²+t² = km`, `s+t = m` iff `m` is not odd squarefree (both forms, incl. Clausen numbers) | proved, checked in Lean |
| [A348840](A348840/) | OEIS A348840 (Mathar): the diagonals `T(n,n−2)`, `T(n,n−3)`, `T(n,n−4)` of the Motzkin touch triangle | proved, checked in Lean |
| [A326250](A326250/) | OEIS A326250 (Wiseman): graphs on `{1..n}` without weakly nesting edges are counted by Catalan numbers, `2^C(n,2) = a(n) + Cₙ` | proved, checked in Lean |

## Withdrawn

These proofs were removed because an earlier proof exists.

The first two are Lean proofs in
[the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing),
added on 2026-09-09:

* **OEIS A389540** (Hanna, `A(x)² = A(2x − 2A(x))/2`: `a(n)` odd iff `n` is a power of 2).
  It was added here on 2026-09-27 and removed on 2026-09-29.
* **OEIS A374571** (Hanna, `A(x) = A(x²) − x·A(x²)²`: `a(n)` odd iff `n` is Fibbinary).
  It was added and removed on 2026-09-29.

The third has a written proof in the session log
[`log/2026-09-03-bit-deletion.md`](https://github.com/farev/Matematica/blob/main/log/2026-09-03-bit-deletion.md)
of [farev/Matematica](https://github.com/farev/Matematica), dated 2026-09-03:

* **OEIS A399155** (Dilkhush: subtracting the largest prime factor reaches `0` no slower than
  subtracting the smallest). It was added and removed on 2026-09-29.

The fourth is a Lean proof in trureturing (`D5/S1/Recurrence/ConvolutionRecurrenceOddPowersOfTwo.lean`).
A trureturing triage note of 2026-09-11 already lists it as present:

* **OEIS A397588** (Hanna, `A(x) = x + (x·A(x)²)'`: `a(n)` odd iff `n` is a power of 2).
  It was added here on 2026-09-27 and removed on 2026-09-29.

## Building

```sh
lake exe cache get
lake build
```
