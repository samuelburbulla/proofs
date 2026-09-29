# Proofs of open problems

Proofs of previously open problems. Each proof is written out by hand and also
checked in [Lean 4](https://lean-lang.org/) with [Mathlib](https://github.com/leanprover-community/mathlib4).
See [AGENTS.md](AGENTS.md) for the rules.

| Problem | Statement | Status |
|---|---|---|
| [A397588](A397588/) | OEIS A397588, `A(x) = x + (x·A(x)²)'`: `a(n)` is odd iff `n` is a power of 2 | proved, checked in Lean |
| [A389540](A389540/) | OEIS A389540, `A(x)² = A(2x − 2A(x))/2`: `a(n)` is odd iff `n` is a power of 2 | proved, checked in Lean |
| [A361032](A361032/) | OEIS A361032–A361035, Bala's array `F(n)(4k)!/(k!(k+n+1)!³)`: integrality, and odd iff `n+k+1` is a power of 2 (settles the conjectures in A361033, A361034, A361035) | proved, checked in Lean |
| [WOWII19](WOWII19/) | Graffiti.pc / Written on the Wall II Conjecture 19: `⌊avg ecc + max_v α(N(v))⌋ ≤ b(G)` for connected graphs | proved, checked in Lean (also inside formal-conjectures) |
| [A374571](A374571/) | OEIS A374571, `A(x) = A(x²) − x·A(x²)²`: `a(n)` is odd iff `n` is Fibbinary | proved, checked in Lean |

## Building

```sh
lake exe cache get
lake build
```
