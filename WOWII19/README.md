# Written on the Wall II, Conjecture 19

**Source:** E. DeLaViña, *Written on the Wall II* (conjectures of Graffiti.pc),
[conjecture 19](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/). Formal statement:
Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
`FormalConjectures/WrittenOnTheWallII/GraphConjecture19.lean`, marked `research open`.

## Problem

For a connected graph `G` on `n` vertices, let
- `ecc(v)` be the eccentricity of `v`;
- `ℓ(v) = α(G[N(v)])` be the independence number of the neighbourhood of `v`;
- `b(G)` be the number of vertices of a largest induced bipartite subgraph.

**Conjecture 19.** For every connected graph `G`,

```
⌊ (1/n)·Σ_v ecc(v) + max_v ℓ(v) ⌋ ≤ b(G).
```

## Result

**Theorem.** Conjecture 19 is true.

## Proof

Let `w` be a vertex with the largest `L = ℓ(w)`, and let `D` be the diameter.

**Layer lemma.** Let `S` be a vertex set whose vertices at equal distance from `w` are
pairwise non-adjacent. Then `S` induces a bipartite graph. Indeed, every edge joins two
vertices whose distances from `w` differ by at most 1. They are never equal inside `S`, so
they differ by exactly 1, and `dist(w, ·) mod 2` is a proper 2-colouring. Hence
`|S| ≤ b(G)`.

**One path.** Let `a` be any vertex and `p = dist(w, a)`. Take `w`, a maximum independent
set `I ⊆ N(w)` (layer 1, `|I| = L`), and the vertices of a shortest `w`–`a` path in layers
`2, …, p`. By the layer lemma, `p + L ≤ b(G)`.

**Two paths.** Let `a, c` be any vertices, `p = dist(w, a)`, `q = dist(w, c)`,
`d = dist(a, c)` and `t = ⌊(p + q + 1 − d)/2⌋`. Also add the vertices `c_j` of a shortest
`w`–`c` path in layers `j ≥ max(2, t+1)`.

Suppose that in some layer `j > t` the two path vertices `a_j, c_j` are equal or adjacent.
Then `d ≤ (p − j) + 1 + (q − j) < d`, a contradiction. So the layer lemma still applies.
Counting the vertices, and using `d ≤ p + q`, gives `d + L ≤ b(G) + 1`.

**Conclusion.** The average eccentricity `ē` is at most `D`.
* If `ecc(w) = D`, the one-path bound towards a vertex at distance `D` from `w` gives
  `D + L ≤ b(G)`. So `⌊ē + L⌋ ≤ D + L ≤ b(G)`.
* If `ecc(w) < D`, then `ē < D`, so `⌊ē + L⌋ ≤ D + L − 1`. The two-path bound for a pair
  `a, c` at distance `D` gives `D + L − 1 ≤ b(G)`. ∎

Both cases are sharp. For the star `K_{1,L}`, `⌊ē + L⌋ = L + 1 = b(G)`.

## Lean formalization

[`WOWII19.lean`](WOWII19.lean) builds with Lean 4 and Mathlib (`lake build`) with no
warnings. It uses no `sorry`, no `native_decide` and no extra axioms. `#print axioms` shows
only `propext`, `Classical.choice`, `Quot.sound`.

The theorem `WOWII19.conjecture19` is stated verbatim as in formal-conjectures. The
definitions it uses (`largestInducedBipartiteSubgraphSize`, `b`, `indepNeighborsCard`,
`indepNeighbors`) are copied verbatim from `FormalConjecturesForMathlib`.

As an independent check, the same proof was compiled inside formal-conjectures itself
(Mathlib v4.33.1), with the `sorry` of their `conjecture19` replaced. There it uses their
own definitions and depends only on `propext`, `Classical.choice`, `Quot.sound`.

| Statement | Lean |
|---|---|
| layer lemma | `WOWII19.card_le_of_layers` |
| splitting a shortest path | `WOWII19.exists_split` |
| maximum independent set of `N(v)` | `WOWII19.exists_indep_nbhd` |
| the combined construction | `WOWII19.core` |
| `dist(w,a) + ℓ(w) ≤ b(G)` | `WOWII19.one_path` |
| `dist(a,c) + ℓ(w) ≤ b(G) + 1` | `WOWII19.two_path` |
| **Conjecture 19** | `WOWII19.conjecture19` |

Numerical sanity checks (outside the repository):
* the conjecture holds on every connected graph with at most 10 vertices;
* the two intermediate bounds hold on every connected graph with at most 9 vertices
  (all enumerated with nauty's `geng`).

## Novelty

Checked on 2026-09-28:

* formal-conjectures (`main`) marks `conjecture19` as `research open`.
* Web searches found no proof of WOWII Conjecture 19. Other WOWII conjectures were resolved
  recently by other authors:
  - 100 ([Zenodo](https://zenodo.org/records/21914031));
  - 141–143 ([arXiv:2608.01396](https://arxiv.org/abs/2608.01396));
  - 194, disproved ([arXiv:2609.19195](https://arxiv.org/abs/2609.19195));
  - 198a ([formal-conjectures #6520](https://github.com/google-deepmind/formal-conjectures/issues/6520)).

  None of these covers 19.
* DeLaViña's WOWII page was unreachable (HTTP 503), so its status marker could not be
  checked there.
