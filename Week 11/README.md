# Week 11: SOS and proofs by reflection

November 18, 2026. One two-hour live-coding session, including a five-minute break.

## Files

- `Lecture11.lean`: student worksheet, with selected holes and slide markers.
- `Lecture11_Solution.lean`: complete worked version.
- `Lecture11_Instructor.lean`: the same sequence with teaching goals and notes below each heading.
- `Lecture11.tex` and `Lecture11_Content.tex`: editable style and content for `Lecture11.pdf`.
- `triangle-sos.txt`: a saved certificate for the external-search demonstration.
- `find_sos.py` and `sum_of_squares.ipynb`: the Python adapter and solver walkthrough.
- `setup_sos.sh`, `requirements-sos.txt`, and `triangle-problem.json`: Python setup and its smoke test.

The former Reflection worksheet is incorporated into sections 5–8. There is one
teaching route and one slide deck. The final four slides share the section
“Proofs by computation.” The Python files are local to Week 11 and reuse the
repository's `.venv-sos` environment.

## Starting point

The instructor reports that SOS was not reached last week. The edited Week 10
student file stops inside `myIntervalCases_2`; later exercises still have holes.
Begin with SOS and give a short completed walkthrough of `exactTerm`. Use
`constructor` without depending on last week's unfinished `split_and`.
Week 6 used `decide +kernel` for finite Hamming-code computations; this class
explains how that command constructs a proof.

## Learning sequence

| Minutes | Section | What students should learn | Work in Lean | Slide |
|---|---|---|---|---|
| 0–10 | 1 | What makes a proposed square a certificate of nonnegativity | Write a proof; separate sign and identity | 1–2 |
| 10–25 | 2 | How a tactic abstracts a proof already written | `sos_step`, `square_using`; read `exactTerm` | — |
| 25–43 | 3 | How a theorem generalizes the proof to any certificate | Handwritten sums, then the weighted-list induction | — |
| 43–65 | 4 | How to build an external tactic incrementally | String, file, printed request, printed response, full tactic | 3 |
| 65–70 | — | Break | — | — |
| 70–80 | 5 | How an algebraic equality becomes a computation on finite data | Ordinary monoid proof; inspect the completed normalizer | 4 |
| 80–97 | 6 | Why the computation implies the original mathematical statement | Prove the append lemma and soundness, then apply soundness and inspect the list equality | 5 |
| 97–112 | 7 | How to prove a statement by computation and what native evaluation assumes | Compare three methods on that same list equality; inspect axioms | 6–7 |
| 112–120 | 8 | How the reflection tactic abstracts the manual theorem application | Use the completed reifier and assemble `reflectMonoid` | — |

At 6.3, pause after applying `reflect_sound`: the goal becomes an equality of two
computed lists. Expose `[0, 1, 2] = [0, 1, 2]` with `change`, then use `rfl`.
Students should be able to identify the soundness theorem and the computation
separately in the finished proof. Section 7 retains that same proposition for
`of_decide_eq_true`, `decide`, `decide +kernel`, and `native_decide`.

The expression representation and normalizer are pre-filled. Students already
know expression trees; the new work is the correctness argument and its use.
The separate quadratic checker and unrelated arithmetic/finite-enumeration
examples have been removed from the route. This avoids another polynomial data
model after the general SOS tactic and another context change before reflection.

If time slips, give the induction step and show the final tactic completed.
Preserve the manual application of the soundness theorem and the comparison of
its computational evidence. Use the saved SOS certificate if Python setup fails.

## What belongs in each part of Lean

The evaluators, normalizer, and correctness theorems are ordinary Lean code.
The list-based SOS wrappers are macros expanding fixed proof templates.
`askSOS` uses `IO` for the external process. `MetaM` is used where expression
operations need definitional equality, type information, or local declarations.
`TacticM` is used to access the current goal and submit its proof.

The syntax helpers, external protocol, and monoid reifier are pre-filled.
In section 4, `parseSOS` is a complete, pure function from an environment and
certificate string to ``Except String (TSyntax `term)``. Students fill
`closeWithSOS`, which receives that syntax and constructs the proof used by
`sos_text`. They then fill `sos_from` to read a saved certificate, `sos_problem`
to print the request, `sos_search` to print Python's response, and `external_sos`
to use that response with the working string tactic.
Instructor-only `squaresProofsTactic` and `sosProofsTactic` preserve the optional
comparison with constructing a separate proof term for each certificate.

## External-search protocol

`getSOSProblem` sends variable names and an arithmetic tree to Python. The adapter
calls SumOfSquares.py and CVXOPT, reconstructs rational coefficients, and prints a
weighted list in Lean syntax. Lean elaborates this list in the goal's context,
checks its weights, and proves the polynomial identity with `ring`.
`quartic_external` demonstrates that the squares can contain higher-degree
polynomials. Numerical search and rational reconstruction can fail; a returned
candidate must still pass the sign and identity proofs.

The adapter also accepts Week 10's older variable-count format. The current
saved certificate uses the same weighted-list syntax as `sos_using`.

## References and adaptation

- [CPDT: Proof by Reflection](https://adam.chlipala.net/cpdt/html/Reflection),
  “A Monoid Expression Simplifier”: interpretation, normalization, correctness,
  the reflection theorem, then a tactic applying that theorem. Sections 5–8 follow this mathematical pattern.
- [Timothy Mou: Proof by Reflection](https://timothymou.com/posts/proof-by-reflection-and-why-not-to-use-it/)
  develops the monoid example in Lean. Our version uses indexed atoms and a
  shared environment so the comparison computes without knowing their values.
- [MPiL 7](https://leanprover-community.github.io/lean4-metaprogramming-book/main/07_elaboration.html)
  and [MPiL 9](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html):
  elaboration in the goal's context and incremental tactic construction.
- [LoVe 8](https://github.com/lean-forward/logical_verification_2026/blob/main/lean/LoVe/LoVe08_Metaprogramming_Demo.lean):
  ordinary proofs before their tactic abstractions, informing sections 1–4.
- [TPiL: decidable propositions](https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/#decidable-propositions)
  and [FPiL: standard classes](https://lean-lang.org/functional_programming_in_lean/Overloading-and-Type-Classes/Standard-Classes/):
  the evidence in `Decidable` and its relationship to Boolean computation.
- [TPiL: axioms and computation](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/),
  together with the pinned Lean
  [Decide.lean](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Lean/Elab/Tactic/Decide.lean)
  and [Native.lean](https://github.com/leanprover/lean4/blob/v4.34.0-rc2/src/Lean/Meta/Native.lean),
  supports the evaluation and trust discussion.
- [SumOfSquares.py](https://github.com/yuanchenyang/SumOfSquares.py) is the Python
  search library. [leanprover/sos](https://github.com/leanprover/sos) inspired the
  search/certificate architecture. Attribution is in `Week 10/attribution`.

## Validation and setup

Use the pinned `leanprover/lean4:v4.34.0-rc2` environment. From the Week 11 directory:

```sh
bash setup_sos.sh
../.venv-sos/bin/python find_sos.py < triangle-problem.json
lake -d .. env lean Lecture11.lean
lake -d .. env lean -DwarningAsError=true Lecture11_Solution.lean
lake -d .. env lean -DwarningAsError=true Lecture11_Instructor.lean
```

Select `../.venv-sos/bin/python` for the notebook kernel. The Lean examples support running from either
Week 11 or the repository root. From the root, use `lake env lean` followed by
the file path, for example `'Week 11/Lecture11_Solution.lean'`.

Student `sorry` warnings are intentional. Computations in sections 5 and 7 run
immediately because `flatten` is complete. Tactic examples dependent on blanks
are commented out. Print the reflection theorems' axioms after completing their
proofs, so the result describes the finished proof rather than `sorryAx`.

Expected observations on this toolchain:

- `lists_decide` and `lists_kernel` have no axioms.
- `lists_native` depends on a generated native-computation axiom.
- `reflected` and `automated` use `propext` through their supporting proofs.
- `reflected_native` additionally depends on the axiom from `lists_native`.
- `triangle_external` uses `propext`, `Classical.choice`, and `Quot.sound`, with
  no native-computation axiom from the Python search.

The kernel checks every finished proof relative to its axioms. It does not replay
native execution to verify the added native-computation axiom.

Build the slides from `Week 11` with `latexmk -lualatex Lecture11.tex`.
LuaLaTeX uses the available Latin Modern fonts; the previous pdfLaTeX build
failed because its `mathkerncmssi8` font was missing.
