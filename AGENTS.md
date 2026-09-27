# Instructions for agents

This repository collects **new proofs of open problems**, each one checked by Lean 4 and Mathlib.

## Rules

1. **Only open problems.** Before starting, make sure nobody has already solved the problem:
   - Read the source, e.g. the current OEIS entry (`https://oeis.org/search?q=id:AXXXXXX&fmt=text`)
     and its history. The statement must still be marked as a conjecture or open question.
   - Search the web and arXiv for an existing proof.
   - Check the AI-driven collections of formalized or resolved OEIS conjectures:
     [formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
     [alphaproof-nexus-results](https://github.com/google-deepmind/alphaproof-nexus-results)
     (arXiv:2605.22763) and the OEIS OPEN benchmark (arXiv:2608.11941).
   - Record what you checked, with the date, in the problem's README ("Novelty" section).
     If a proof already exists, stop and don't add the problem.
2. **One subfolder per problem**, named after the problem (e.g. `A397588/` for an OEIS
   sequence). It contains:
   - `README.md` with the source, the problem statement, the solution (a readable proof
     written out by hand), the novelty check, and a map from the statements to the Lean theorem names.
   - A Lean file (e.g. `A397588/A397588.lean`) that formalizes the statement and verifies the proof.
3. **The Lean proof must be complete and honest:**
   - no `sorry`, no `admit`, no new `axiom`, no `native_decide`
     (`#print axioms` should list only `propext`, `Classical.choice`, `Quot.sound`);
   - the formal statement must match the original problem. If the object is defined in
     a different way than in the source (e.g. by a recurrence instead of a generating function),
     also prove that the two definitions agree;
   - sanity-check definitions against known data (e.g. the first OEIS terms, using `decide`).
4. **Register the library** in `lakefile.toml` (a `[[lean_lib]]` with `srcDir` set to the
   subfolder, and add it to `defaultTargets`), and add a row to the table in the root `README.md`.
5. `lake build` must succeed with no errors or warnings before you commit.
6. **Merge into `main`** once the Lean proof builds and the GitHub Actions `Lean` workflow
   is green on the work branch.

## Building

```sh
# install elan (Lean toolchain manager) once, then:
lake exe cache get   # download prebuilt Mathlib
lake build
```
