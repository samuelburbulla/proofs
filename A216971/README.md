# OEIS A216971: divisibility of the recurrent-element triangle

## Source

[OEIS A216971](https://oeis.org/A216971) (G. Critzer, 2012): `T(n,k)` is the number of functions
`f : {1,…,n} → {1,…,n}` that have exactly `k` nonrecurrent elements mapped to some recurrent
element. An element `x` is *recurrent* if `f^j(x) = x` for some `j ≥ 1`, i.e. `x` lies on a
cycle of the functional digraph.

```
   1
   2    2
   6   18    3
  24  156   72    4
 120 1520 1260  220    5
```

> Conjecture: every entry in row n is divisible by n. — _Jon Perry_, Sep 21 2012

## Statement

For every `n ≥ 1` and every `k`, `n ∣ T(n,k)`.

## Proof

Write `R(f)` for the set of recurrent elements of `f` and `s(f)` for the statistic, the number
of `x ∉ R(f)` with `f(x) ∈ R(f)`. For a set `S`, let `N(S)` be the set of functions with
`R(f) = S` and `s(f) = k`. Then `T(n,k) = Σ_S |N(S)|`.

1. **`|S|! ∣ |N(S)|`.** The map `f` sends `R(f)` bijectively onto itself. Given a permutation
   `π` of `S` and `f ∈ N(S)`, let `f'` agree with `π` on `S` and with `f` off `S`. Then `f'` has
   the same recurrent set:
   * `S` is permuted, so its points are recurrent;
   * an orbit starting outside `S` that ever enters `S` stays there, so it cannot return;
   * an orbit that never enters `S` is an `f`-orbit, and it is not periodic.

   The statistic only involves values off `S`, so `s(f') = s(f)`. Hence `N(S)` splits into
   blocks of `|S|!` functions each: those that coincide off `S` and are arbitrary permutations
   on `S`.
2. **`|N(S)|` depends only on `|S|`.** Conjugating by a permutation `σ` of `{1,…,n}`,
   `f ↦ σ∘f∘σ⁻¹`, maps `N(S)` bijectively onto `N(σ(S))`. Any two sets of equal size are
   related by some `σ`.
3. **Conclusion.** Let `N_m` denote the common value of `|N(S)|` for `|S| = m`. Then
   `T(n,k) = Σ_m C(n,m) N_m`.
   * For `m = 0` the term vanishes, because every function on a nonempty finite set has a
     cycle (pigeonhole).
   * For `m ≥ 1`, write `N_m = m!·q`. Then `C(n,m) N_m = n(n−1)⋯(n−m+1)·q`, which is divisible
     by `n`. ∎

## Lean formalization

File: [`A216971.lean`](A216971.lean).
* The definitions follow the OEIS entry: `IsRec f x` means `∃ j > 0, f^[j] x = x`, the
  statistic is `A216971.stat`, and `A216971.T n k` counts `f : Fin n → Fin n` with `stat f = k`.
* Recurrence is decided with the bound `j ≤ n`, justified by `A216971.isRec_iff_bounded`.
* The rows `n = 1, …, 4` are checked against the OEIS data by `decide +kernel`.

| Statement | Lean name |
|---|---|
| gluing lemma (step 1) | `A216971.isRec_glue`, `A216971.stat_eq_of` |
| `|S|! ∣ |N(S)|` | `A216971.factorial_dvd_card_N` |
| conjugation invariance (step 2) | `A216971.card_N_map`, `A216971.card_N_eq` |
| every function has a cycle | `A216971.exists_isRec` |
| **Perry's conjecture** `n ∣ T(n,k)` | `A216971.dvd_T` |

`#print axioms A216971.dvd_T` lists only `propext`, `Classical.choice` and `Quot.sound`.

## Novelty check (2026-09-29)

* The OEIS entry (revision #43, Aug 09 2022) still states the divisibility as a conjecture.
  It gives the e.g.f. but no proof.
* A web search for the statement found no proof.
* None of the following mentions A216971:
  - [formal-conjectures](https://github.com/google-deepmind/formal-conjectures);
  - [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results);
  - [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)
    (file names);
  - [Horace-Maxwell/ai4math-results](https://github.com/Horace-Maxwell/ai4math-results);
  - [farev/Matematica](https://github.com/farev/Matematica).
* [astrafala/Conjectures](https://github.com/astrafala/Conjectures) lists it only in
  `engine/deep-check/unread-unsettled.txt`, i.e. as not settled.
* OEIS OPEN benchmark (arXiv:2608.11941): no proof was found.
