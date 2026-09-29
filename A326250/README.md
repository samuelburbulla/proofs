# OEIS A326250: graphs without weakly nesting edges are counted by Catalan numbers

## Source

[OEIS A326250](https://oeis.org/A326250) (G. Wiseman, 2019): the number of weakly nesting simple
graphs with vertices `{1,…,n}`. Two edges `{a,b}`, `{c,d}` are weakly nesting if
`a ≤ c < d ≤ b` or `c ≤ a < b ≤ d`. Data: `0, 0, 0, 3, 50, 982, 32636, 2096723`.

> Conjecture: A006125(n) = a(n) + A000108(n).

Here `A006125(n) = 2^C(n,2)` counts all simple graphs on `{1,…,n}` and `A000108(n) = Cₙ` are the
Catalan numbers.

## Statement

For every `n`, the number of simple graphs on `{1,…,n}` with no two weakly nesting edges is
the Catalan number `Cₙ`. Equivalently, `2^C(n,2) = a(n) + Cₙ`.

## Proof

Write each edge as `(a, b)` with `a < b`. If a graph has no two weakly nesting edges, its left
endpoints are distinct, its right endpoints are distinct, and ordering its edges by left
endpoint also orders them by right endpoint.

**Deleting the last vertex.** For `m, h ≥ 0`, let `S(m, h)` count the pairs `(G, P)` where:
* `G` is a non-nesting graph on `{1,…,m}`;
* `P ⊆ {1,…,m}` has `h` elements (the "pending" left endpoints);
* every element of `P` is larger than every left endpoint of `G`.

Then `S(n, 0)` is the number we want. Consider vertex `v = m+1` in a pair counted by `S(m+1, h)`:
* **`v` unused.** The pair lives on `{1,…,m}`, which gives `S(m, h)`.
* **`v` is the right endpoint of an edge `(a, v)`, and `v ∉ P`.** This edge is unique, and `a`
  is the largest left endpoint. Deleting the edge and adding `a` to `P` gives a pair counted
  by `S(m, h+1)`. Conversely, from such a pair we recover `a = min P`.
* **`v ∈ P`.** Removing `v` from `P` is a bijection with the pairs counted by `S(m+1, h−1)` in
  which `v ∉ P`. By the first two cases there are `S(m, h−1) + S(m, h)` of them.

Hence
```
S(m+1, 0)   = S(m, 0) + S(m, 1),
S(m+1, h+1) = S(m, h) + 2·S(m, h+1) + S(m, h+2).
```
This is the recursion for Dyck paths read two steps at a time (`UU`, `UD`, `DU`, `DD`). Using
`C(N+2, k+2) = C(N,k) + 2C(N,k+1) + C(N,k+2)`, the ballot numbers
`B(m, h) = C(2m, m+h) − C(2m, m+h+1)` satisfy the same recursion and the same initial values
`S(0, h) = [h = 0]`. So `S(m, h) = B(m, h)`, and
`S(n, 0) = C(2n, n) − C(2n, n+1) = C(2n,n)/(n+1) = Cₙ`. ∎

## Lean formalization

File: [`A326250.lean`](A326250.lean).
* A graph is a subset of `A326250.edgeSet n`, the pairs `(a, b)` with `1 ≤ a < b ≤ n`.
  `A326250.WeaklyNesting G` is the definition from the entry.
* `A326250.a n` counts the weakly nesting graphs. It is checked against the OEIS data
  `a(0..4) = 0, 0, 0, 3, 50` by `decide +kernel`.
* The Catalan numbers are Mathlib's `catalan`.

| Statement | Lean name |
|---|---|
| `S(n,0)` counts the non-nesting graphs | `A326250.S_zero_eq` |
| the three cases for vertex `m+1` | `A326250.filter_notR_notP`, `A326250.card_filter_R_notP`, `A326250.card_filter_P` |
| the recursion | `A326250.S_succ_zero`, `A326250.S_succ_succ` |
| `S(m,h) = C(2m,m+h) − C(2m,m+h+1)` | `A326250.S_eq_B` |
| `C(2n,n) − C(2n,n+1) = Cₙ` | `A326250.B_zero_eq_catalan` |
| non-nesting graphs are counted by `Cₙ` | `A326250.card_not_weaklyNesting` |
| **Wiseman's conjecture** `2^C(n,2) = a(n) + Cₙ` | `A326250.wiseman` |

`#print axioms A326250.wiseman` lists only `propext`, `Classical.choice` and `Quot.sound`.

## Novelty check (2026-09-29)

* The OEIS entry (revision #4, Jun 21 2019) still states the identity as a conjecture.
* A web search found no proof.
* None of the following mentions A326250:
  - [formal-conjectures](https://github.com/google-deepmind/formal-conjectures);
  - [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results);
  - [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)
    (file names and contents);
  - [Horace-Maxwell/ai4math-results](https://github.com/Horace-Maxwell/ai4math-results);
  - [farev/Matematica](https://github.com/farev/Matematica).
* [astrafala/Conjectures](https://github.com/astrafala/Conjectures) lists it only in
  `engine/deep-check/unread-unsettled.txt`, i.e. as not settled.
* OEIS OPEN benchmark (arXiv:2608.11941): no proof was found.
