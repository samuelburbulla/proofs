# Proofs of open problems

Proofs of previously open problems. Each proof is written out by hand and also
checked in [Lean 4](https://lean-lang.org/) with [Mathlib](https://github.com/leanprover-community/mathlib4).
See [AGENTS.md](AGENTS.md) for the rules.

| Problem | Statement | Status |
|---|---|---|
| [A397588](A397588/) | OEIS A397588, `A(x) = x + (x·A(x)²)'`: `a(n)` is odd iff `n` is a power of 2 | proved, checked in Lean |

## Building

```sh
lake exe cache get
lake build
```
