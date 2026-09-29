# OEIS A054390: hyperternary representations = partitions into distinct parts `3ᵏ`, `2·3ᵏ`

**Source:** [OEIS A054390](https://oeis.org/A054390). The conjecture is by R. J. Mathar (Mar 01 2023).

## Problem

`a(n)` is the number of ways of writing `n` as a sum of powers of 3, each power used at most
three times. These are the hyperternary representations of `n`, with
`1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 2, …`

> **Conjecture (Mathar):** `a(n)` equals the number of partitions of `n` into distinct parts of
> A038754, i.e. distinct numbers of the form `3ᵏ` or `2·3ᵏ`.

## Result

**Theorem.** The conjecture holds for every `n ≥ 0`.

## Proof

Let a representation use `3ᵏ` exactly `cₖ ∈ {0,1,2,3}` times. Map it to the set of parts

```
S(c) = {3ᵏ : cₖ odd} ∪ {2·3ᵏ : cₖ ≥ 2}.
```

For each `k`, the parts of `S(c)` of the form `3ᵏ` or `2·3ᵏ` add up to `cₖ·3ᵏ`:
`0 ↦ ∅`, `1 ↦ {3ᵏ}`, `2 ↦ {2·3ᵏ}`, `3 ↦ {3ᵏ, 2·3ᵏ}`. So `S(c)` is a partition of `n` into
distinct parts of A038754. The numbers `3ᵏ` (odd) and `2·3ʲ` (even) never coincide.

Conversely, a partition `S` gives `cₖ = [3ᵏ ∈ S] + 2·[2·3ᵏ ∈ S]`. The two maps are inverse to
each other. ∎

Equivalently, `∏ₖ (1 + x^{3ᵏ} + x^{2·3ᵏ} + x^{3·3ᵏ}) = ∏ₖ (1 + x^{3ᵏ})(1 + x^{2·3ᵏ})`.

## Lean formalization

[`A054390.lean`](A054390.lean) builds with no warnings. It uses no `sorry` and no
`native_decide`, and `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`.

Only powers `3ᵏ ≤ n` can occur, so a representation of `n` is a multiplicity function
`Fin (n+1) → Fin 4`.

| Statement | Lean |
|---|---|
| A038754 membership (`isPart_iff`: `∃ k, m = 3ᵏ ∨ m = 2·3ᵏ`) | `A054390.IsPart` |
| representations / partitions | `A054390.reps`, `A054390.parts` |
| the bijection and its inverse | `A054390.toParts`, `A054390.ofParts` |
| **Mathar's conjecture** | `A054390.card_reps_eq_card_parts : (reps n).card = (parts n).card` |
| first terms match OEIS | `example`s (by `decide +kernel`) |

## Novelty

Checked on 2026-09-29:

* The OEIS entry (revision #49, Sep 27 2026) still lists the statement as a conjecture, with no
  proof.
* A web search found no proof. The hyper-b-ary literature cited in the entry does not state this
  equivalence:
  - Dilcher–Ericksen 2018;
  - Flowers 2017.
* The sequence does not appear in:
  - the-omega-institute/trureturing;
  - Horace-Maxwell/ai4math-results;
  - formal-conjectures;
  - alphaproof-nexus-results.
* Also checked on 2026-09-29:
  - [farev/Matematica](https://github.com/farev/Matematica): no mention in `conjectures/` or in
    `log/`;
  - [astrafala/Conjectures](https://github.com/astrafala/Conjectures): the sequence is listed only
    in `engine/deep-check/unread-unsettled.txt`, i.e. as not yet settled, and has no ledger
    entry.
