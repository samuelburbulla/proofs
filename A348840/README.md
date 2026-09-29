# OEIS A348840: Motzkin paths touching the axis many times

## Source

[OEIS A348840](https://oeis.org/A348840) (R. J. Mathar, 2021): `T(n,h)` is the number of
Motzkin paths of `n ≥ 2` steps that start with an Up step and touch the horizontal axis `h ≥ 1`
times afterwards. To touch means: the path reaches the horizontal line with a down-step, or it
is at the horizontal level and takes another horizontal step.

```
  1
  1   1
  2   2   1
  4   4   3   1
  9   9   7   4   1
 21  21  17  11   5   1
```

The entry lists three conjectures (R. J. Mathar):

> Conjecture: T(n,n-2) = n-2.
> Conjecture: T(n,n-3) = A000124(n-3).
> Conjecture: T(n,n-4) = -11 + 19*n/3 - 3*n^2/2 + n^3/6.

Here `A000124(m) = m(m+1)/2 + 1` is the lazy caterer's sequence. (P. Bala's separate Riordan-array
conjecture in the same entry is not treated here.)

## Statement

* `T(n, n−2) = n − 2` for `n ≥ 3`;
* `T(n, n−3) = (n−3)(n−2)/2 + 1` for `n ≥ 4`;
* `T(n, n−4) = −11 + 19n/3 − 3n²/2 + n³/6` for `n ≥ 5`.

These are all the entries on those diagonals, since `h ≥ 1`.

## Proof

Let `C(ℓ, y, t)` be the number of step sequences of length `ℓ` from height `y` that stay weakly
above the axis, end on it, and touch it `t` times. After the obligatory first up-step,
`T(n+1, h) = C(n, 1, h)`. Splitting off the first step gives

```
C(ℓ+1, 0, t)   = C(ℓ, 1, t) + C(ℓ, 0, t−1)
C(ℓ+1, 1, t)   = C(ℓ, 2, t) + C(ℓ, 1, t) + C(ℓ, 0, t−1)
C(ℓ+1, y+2, t) = C(ℓ, y+3, t) + C(ℓ, y+2, t) + C(ℓ, y+1, t),
```

where `C(ℓ, 0, −1) = 0` and `C(0, y, t) = [y = t = 0]`.

A path from height `y ≥ 1` touches at most `ℓ − y + 1` times, and one from height `0` at most
`ℓ` times. Otherwise `C = 0`.

Call `e`, the gap to this maximum, the *excess*. Each step keeps or lowers `e`: an up-step
costs `2`, a horizontal step off the axis costs `1`. So the values with `e ≤ 3` satisfy a closed
triangular system, which can be solved by induction on `ℓ`:

| value | closed form |
|---|---|
| `C(m, 0, m)`, `C(m+1, 1, m+1)`, `C(m+2, 2, m+1)` | `1` |
| `C(m+1, 0, m)` | `m` |
| `C(m+2, 1, m+1)` | `m + 1` |
| `C(m+3, 2, m+1)` | `m + 2` |
| `2·C(m+2, 0, m)` | `m(m+1)` |
| `2·C(m+3, 1, m+1)` | `2(m+2) + m(m+1)` |
| `6·C(m+3, 0, m)` | `m³ + 3m² + 8m` |
| `6·C(m+4, 1, m+1)` | `m³ + 6m² + 23m + 24` |

Substituting `n = m+3`, `m+4` and `m+5` gives the three formulas. For example,
`6·T(m+5, m+1) = m³ + 6m² + 23m + 24 = n³ − 9n² + 38n − 66`. ∎

## Lean formalization

File: [`A348840.lean`](A348840.lean).
* Paths are lists of steps `U`, `H`, `D`.
* `A348840.words ℓ` lists every word of length `ℓ` exactly once (`mem_words`, `nodup_words`).
* `A348840.ok y w` says that `w`, started at height `y`, never goes below the axis and ends on
  it.
* `A348840.tc y w` counts the steps that end on the axis.
* `A348840.T n h` counts the words of length `n` that start with `U`, are Motzkin paths and have
  `h` touches.
* The rows `n = 2, …, 8` are checked against the OEIS data by `decide +kernel`.

| Statement | Lean name |
|---|---|
| the combinatorial count satisfies the recursion | `A348840.Ccomb_eq_C` |
| `T(n+1, h) = C(n, 1, h)` | `A348840.T_eq_C` |
| vanishing beyond the maximal number of touches | `A348840.C_eq_zero` |
| closed forms of the table above | `A348840.C0a` … `A348840.C3b` |
| `T(n, n−2) = n − 2` | `A348840.T_sub_two` |
| `T(n, n−3) = A000124(n−3)` | `A348840.T_sub_three` |
| `T(n, n−4) = −11 + 19n/3 − 3n²/2 + n³/6` | `A348840.T_sub_four` |

`#print axioms` for the three theorems lists only `propext`, `Classical.choice` and
`Quot.sound`.

## Novelty check (2026-09-29)

* The OEIS entry (revision #30, Feb 04 2024) still states all three formulas as conjectures.
* A web search found no proof.
* None of the following mentions A348840:
  - [formal-conjectures](https://github.com/google-deepmind/formal-conjectures);
  - [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results);
  - [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)
    (file names and contents);
  - [Horace-Maxwell/ai4math-results](https://github.com/Horace-Maxwell/ai4math-results);
  - [farev/Matematica](https://github.com/farev/Matematica).
* [astrafala/Conjectures](https://github.com/astrafala/Conjectures) lists it only in
  `engine/deep-check/unread-unsettled.txt`, i.e. as not settled.
* OEIS OPEN benchmark (arXiv:2608.11941): no proof was found.
