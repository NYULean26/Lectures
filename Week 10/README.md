# Week 10: Metaprogramming II: Asking another computer

Draft for November 11, 2026. A two-hour live-coding continuation of Week 09.

- [Student file (empty)](Lecture10.lean)
- [Solutions (full)](Lecture10_Solution.lean)
- [Instructor copy](Lecture10_Instructor.lean)
- [Eight lecture slides](Lecture10.pdf) ([editable Beamer source](Lecture10.tex))

The class follows one question: how does a program turn an unfinished proof into
a complete proof, including when another program supplies the proposed answer?
Students begin with ordinary proofs in Lean, then inspect their expression trees
and fill metavariables to complete unfinished proofs. They implement those
proof steps and reuse the implementations to check an external result.

## What students should learn

1. Describe a metavariable's type, local context, and assignment, and distinguish
   an available hypothesis from a hole that still needs filling. Identify their
   `Lean.Expr` representations and distinguish the hole from its target type.
2. Construct a proof by inspecting a goal, assigning it an expression, and exposing
   new subgoals while preserving other pending work.
3. Explain how elaboration turns syntax into an expression using the local context
   and an expected type.
4. Read an external answer through IO and construct a Lean proof from checked
   evidence. Recognize why search failure and successful parsing prove nothing.

## Slides and the Lean file

Stay in Lean for 1 and 2.1: the interval warmup, then a conjunction proof with
`constructor`. Print its term with `pp.structureInstances false` to expose `And.intro hp hq`.

The first switch to slides is at **2.2, How Lean represents these terms**.
Show `Expr` first, then move to the separate section **3, Metavariables**.
The same conjunction connects the complete proof, its expression tree, and
the proof under construction. Section 2.3 inspects its target and local proof, then constructs `And.intro`
applied to `P`, `Q`, `hp`, and `hq` using `.const` and `.app`. It passes the
complete proof to `closeMainGoal`. Section 3 introduces unfinished expressions.
The two-context example first appears in 3.3, alongside `withContext`.
The student file marks each slide transition with `(Slide …)` comments.

| Slide | Lean section | Example and checkpoint |
| --- | --- | --- |
| 1. What is an expression? | 2.2–2.3 | Show the Expr inductive; identify its constructors except mvar, then inspect the complete target and local proof |
| 2. Metavariables: unfinished expressions | 3 | Explain mvar using the familiar goal, its required type, and its local context |
| 3. MetaM: context and state | 3.2 | Look up a constant, find a local proof, create and assign a hole |
| 4. MetaM: create, assign, instantiate | 3.2, then 5 | Create a hole, record its assignment, and instantiate it in an expression |
| 5. Normal forms and definitional equality | 4.2, then 4.3 and 5.1 | Compare reductions, infer a hole, and extract an interval bound from a hypothesis |
| 6. Elaborating a term in context | 6 | Add a proof term with have and reuse interval_cases; implement exact_term |
| 7. Sums of squares (SOS) | 7 | Explain the weighted-square certificate and why discovery can be harder than verification |
| 8. External search and checked evidence | 8–12 | Check the certificate, read it from a file, call Python, reject wrong answers |

The Expr slide shows the constructors used in this introduction. Identify
binders, sorts, literals, and metadata without teaching their
implementation details. Defer de Bruijn calculations and universe arithmetic.
Explain `mvar` on slide 2. This follows MPiL's order:
Expressions (chapter 3), then Metavariables (chapter 4).

Introduce MetaM in 3.2 through concrete operations on constants, local proofs,
and holes, then follow the create/build/assign/instantiate recipe. Assume the
monad background from previous weeks. Introduce withContext in 3.3, when
inspecting h in two different goal contexts gives it a purpose.
The former partial-proof table has been replaced: follow that construction in
Lean with refine and show_term, then with splitAndCore and its goal-list adapter.
Then introduce TacticM in 4 for the current goal list, and TermElabM in 6 for
term elaboration. Section 5 reuses MetaM to construct a conjunction proof.

Revisit the interval warmup twice. In 4.2.1, inspect a named hypothesis of type
`n ≤ a`, extract the local variable `a`, and call the original macro. In 6.1.1,
accept a proof term by adding it with `have`, then call the first wrapper.
The second revisit reuses the bound reader unchanged.

## Two-hour route

| Minutes | Section | Live work |
| --- | --- | --- |
| 0–10 | 1: Macbeth warmup | Use interval_cases; reproduce its case splits by hand |
| 10–16 | 2.1: A proof and its term | Complete the conjunction proof and print And.intro hp hq |
| 16–23 | 2.2–2.3: Expressions | First slide transition; identify Expr constructors and inspect the same conjunction |
| 23–37 | 3: Metavariables | Slides 2–4; named goals, inferred witness, context/state, assignment recipe |
| 37–49 | 4: Inspect and solve | Compare reduction; infer a hole; extract interval bounds; complete hypothesis |
| 49–62 | 5: Construct subgoals | Observe implicit arguments; create holes, assign parent, preserve pending goals |
| 62–67 | Break | |
| 67–78 | 6: Term elaboration | Run inspector; wrap interval_cases with have; implement exact_term |
| 78–90 | 7: Certificate | Distinguish ring from reduction; prove one square, then combine weighted squares |
| 90–97 | 8: One-square checker | Expose conditions with sos_step; write square_using |
| 97–105 | 9: Weighted sums | Read the certificate builder; write closeWithSOS |
| 105–109 | 10: File IO | Read and check a certificate; explain IO lifting and when it runs |
| 109–115 | 11: Python | Follow input/output types and connect external_sos |
| 115–120 | 12: Failure experiments | Reject negative weights and incorrect identities |

The macro in 1.3 is prefilled for reuse in 4.2.1; its warmup walkthrough and
1.4’s endpoint tests are optional.
Move to 2 at minute 10 and to 12 at minute 115.
Reuse the supplied inspector and hypothesis loop rather than retyping Week 09.
Allow three minutes for 4.2.1 and two for 6.1.1 by keeping the intermediate
transparency modes optional. The parser,
polynomial reader and Python internals are black boxes; explain their interfaces.
If behind, omit the intermediate transparency modes;
give the quotation in 9.1.
Preserve expressions, metavariables, the Python call, and a wrong-answer experiment.

The student gaps are 1.1–1.2, 2.1, 2.3, 4.2.1, 4.3, 5.1–5.2, 6.1.1, 6.2, 7.1, 8.2,
9.1, and 11.2. The interval wrappers have short gaps; lookup and matching are prefilled.
In 4.3, fill only the goal update and return; the previous search loop is retained.
Students predict and run the other examples. Fill each gap, then uncomment its
checks. Do not execute a computational `sorry`. Open each file independently.

The capstone proves polynomial inequalities by finding weighted sums of squares:

`sos_step ((x-y)^2)` → `square_using (x-y)` → `closeWithSOS` → `sos_from` → `external_sos`.

Section 8 reuses `split_and` on the two certificate obligations. The checkers reuse
`exactTerm`. Use the returned rational weights and affine coefficients to construct
Lean proofs with `sq_nonneg`, `mul_nonneg`, and `add_nonneg`, then check
the polynomial identity with `linear_combination`. Parsing alone proves nothing.

The Python adapter calls [SumOfSquares.py](https://github.com/yuanchenyang/SumOfSquares.py)
with the CVXOPT semidefinite solver. SymPy converts its numerical Gram matrix into
exact rational weighted squares. Lean independently checks the resulting certificate.
Show the three library calls in `find_sos.py`: `SOSProblem`, `add_sos_constraint`,
and `solve`. The remaining conversion code can stay a black box.

The classroom adapter supports quadratic polynomials, including affine and constant
terms, in at most eight real variables. The Lean reader accepts real variables,
numerals, addition, subtraction, multiplication, negation, numerical powers 0–2,
and division by nonzero constants. It sends `rhs - lhs` to Python and uses no
hypotheses. Unsupported expressions fail explicitly. Numerical search or rational
reconstruction can fail even for a nonnegative polynomial.

## Before class

Use the pinned Lean version, `v4.34.0-rc2`, and Python 3.10 or newer.
Install the Python packages once before class; the solver then runs locally.
Open **the repository root** in the editor: file and process paths are relative
to that directory. The process wrapper uses `.venv-sos/bin/python`.

```sh
bash 'Week 10/setup_sos.sh'
.venv-sos/bin/python 'Week 10/test_find_sos.py'
lake env lean 'Week 10/Lecture10.lean'
lake env lean 'Week 10/Lecture10_Solution.lean'
lake env lean 'Week 10/Lecture10_Instructor.lean'
```

On Debian/Ubuntu, if creating the environment fails because `ensurepip` is
missing, install the venv package matching your Python version. For Python 3.10:

```sh
sudo apt update
sudo apt install python3.10-venv
bash 'Week 10/setup_sos.sh'
```

The setup script can be rerun after a failed attempt; it creates or repairs the
environment, installs the pinned dependencies, and checks the triangle example.

The search prints a JSON array of weighted affine squares, using
`[numerator, denominator]` pairs. In each affine form, the constant precedes
the variable coefficients in the order sent by Lean. The worksheet has intentional `sorry`
warnings. The full and instructor copies should have no errors or warnings.

IO happens during elaboration. After changing Python, re-elaborate the example;
the editor may otherwise reuse the previous result. Use a local Lean setup for
subprocess work. The final theorem contains a proof term, with no Python call.

## Checkpoints and fallback

| Checkpoint | Complete first | Expected result |
| --- | --- | --- |
| `test_constructor` | 2.1 | Inspect the complete conjunction proof |
| `test_refine` | 3.1 | Follow the proof with two named metavariables |
| Witness inference | 3.1 | Proving the equality determines the existential witness |
| `metavarDemo` | 3.2 | Instantiate the recorded assignment in a new expression tree |
| Local context | 3.3 | h has type P in one goal and Q in another |
| Reduction | 4.2 | Same expression at four transparencies; weak-head versus full reduction; defeq |
| `inferMetavar` | 4.2 | Observe unification assigning the unknown |
| `my_interval_cases_2 h` | 4.2.1 | Extract the bound and variable from h, then reuse the warmup macro |
| `hypothesis` | 4.3 | Assign a local proof, update the goal list, or report failure |
| Implicit arguments | 5 | mkAppM given hp/hq constructs an application with P/Q/hp/hq |
| `split_and` | 5.1–5.2 | Expose Both using whnf; split twice with the handwritten adapter and retain R |
| `my_interval_cases_term t` | 4.2.1, 6.1.1 | Name an elaborated proof with have and call the first wrapper |
| `exact_term` | 6.2 | Elaborate against the target; reject wrong types and holes |
| Manual square proof | 7.1 | Check a nonnegative square and its identity |
| Weighted squares | 7.2 | Use mul_nonneg, then add_nonneg: the builder’s loop invariant |
| `sos_step` | 5.1–5.2 for split_and | Expose nonnegativity and equality obligations |
| `square_using` | 6.2, 8.2 | Check the proposed square |
| `closeWithSOS` | 6.2, 9.1 | Check rational weights and a polynomial identity |
| `sos_from` | 6.2, 9.1 | Check triangle-sos.json against the current goal |
| `external_sos` | 6.2, 9.1, 11.2 | Search externally, check internally |

If Python is unavailable, use section 10's file route. The failures involving
weights and identities in 12 still work; leave the subprocess examples commented.
The student file reads the saved JSON but does not run the unfinished checkers.

`find_sos.py` returns a certificate (exit 0), no certificate (exit 2), or invalid or
unsupported input (exit 1). A search failure proves nothing. In particular, the
classroom search rejects `x^4` even though it is nonnegative. Section 12 demonstrates
this limitation and rejects a negative weight, an incorrect square, bad JSON,
and a zero denominator. `wrong-sos.json` has a plausible but incorrect weight.

## Exposition choices from the references

These are adaptations to this class, not claims about the references' timing.

| Reference and passage | Presentation idea used here |
| --- | --- |
| [Macbeth, Phase 0](https://github.com/hrmacbeth/Simons2025/blob/44d1d930a3b532e6f77abe2a96931eed63884c81/Simons2025/Metaprogramming/Phase0_Model.lean) | Write a proof manually before automating it. Use this both for intervals and the SOS certificate. Phase 1's explicit goal-to-subgoals interface motivates 5. |
| [MPiL 3, Expressions](https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html) | 2.2 shows the Expr inductive before introducing metavariables in 3. Section 2.3 follows Constructing Expressions using the familiar conjunction and direct const/app nodes. |
| [MPiL 4, Metavariables](https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html) | Relate a goal to a hole with a type and local context. 3.1 uses a conjunction; 3.2 adapts Basic Operations; 3.3 follows Local Contexts with withContext and hypothesis lookup. |
| [Olšák–Gerbscheid, proof state](https://github.com/mirefek/lean-tactic-programming-guide/blob/a6c1b880df9fb938619832f5a043966bcb8c636c/TacticProgrammingGuide.lean) | Annotate an ordinary tactic proof with successive partial proof terms. 3.1 follows this explanatory pattern; 6.1 follows my_check. |
| [LoVe 8, traceGoals and hypothesis](https://github.com/lean-forward/logical_verification_2026/blob/460f6be0846eefc3d9441e4e48d75753fcfe1709/lean/LoVe/LoVe08_Metaprogramming_Demo.lean) | Observe the proof state before changing it. 4 revisits Week 09's hypothesis with explicit failure and goal management. |
| [MPiL 9, exercises 1–2](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html) | Turn partial proof terms into tactic steps. 5's conjunction construction follows forker and tests preservation of pending goals. |
| [MPiL 7, Term elaboration](https://leanprover-community.github.io/lean4-metaprogramming-book/main/07_elaboration.html) | Use syntax, expected type, and resulting expression as the boundary to explain. 6 uses familiar proofs rather than adding a new custom term language. |
| [FPiL 4.5, The IO Monad](https://lean-lang.org/functional_programming_in_lean/Monads/The-IO-Monad/) | Recall how IO returns values or errors. 10–11 reuse Week 08's read/validate pattern without deriving IO's internal state representation. |

Use MPiL and LoVe for the tactic-writing sequence, with FPiL's monad-transformer
chapters as background for combined effects. FPiL's tactics interlude focuses on
using tactics.

## How much elaboration?

Eleven minutes in 6. Reuse the interval wrapper through `have`, then implement
a small `exact_term`, inspect expected-type inference, and reject an unfinished
term. Section 9 immediately reuses `exactTerm`.
Connect the slide to the examples in the Lean file.

Use the precise name **TermElabM** when it becomes relevant. Reuse `elabTerm`
with the goal's target as the expected type, then use `inferType` and `isDefEq`
to check the resulting proof's type. `closeMainGoal` rejects remaining holes
and closes the goal. These steps are explained in the instructor notes.

Defer command elaborators, registration attributes, postponement, and the full
transformer stack. Mention CommandElabM only if asked about commands such as
`def` or `#check`; it is not another rung above TacticM.

## References and adaptations

The opening follows Macbeth's interval-cases tutorial, adapted to the tactic
quotations used last week. The other references supply the metaprogramming and
IO building blocks; the external-SOS lesson is a new course adaptation.

- [Heather Macbeth, Simons 2025, Metaprogramming, phases 0–2](https://github.com/hrmacbeth/Simons2025/tree/44d1d930a3b532e6f77abe2a96931eed63884c81/Simons2025/Metaprogramming):
  the `1 ≤ k ≤ 4 ⊢ k ∣ 12` example and the recursive split/increment algorithm.
  Our macro adapts the original construction with Qq and fresh metavariables
  to tactic quotations, trying `omega` before splitting cases. The warmup
  expects natural numbers, small numerical bounds, and an explicit lower-bound
  hypothesis. It does not implement Mathlib's complete `interval_cases` interface.
- [LoVe 8, Metaprogramming](https://github.com/lean-forward/logical_verification_2026/blob/460f6be0846eefc3d9441e4e48d75753fcfe1709/lean/LoVe/LoVe08_Metaprogramming_Demo.lean):
  the continuation of Week 09's goal manipulation and conjunction tactics.
- *Metaprogramming in Lean 4*: [3, Expressions](https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html),
  [4, MetaM](https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html),
  [7, Elaboration](https://leanprover-community.github.io/lean4-metaprogramming-book/main/07_elaboration.html),
  and [9, Tactics](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html).
  Chapter 9 exercise 2 (`forker`) is the closest reference for 5's explicit
  conjunction proof and goal-management adapters.
- [FPiL 4.5, The IO Monad](https://lean-lang.org/functional_programming_in_lean/Monads/The-IO-Monad/):
  conceptual IO background. Parsing continues Week 08's `checkInteger`;
  the proof-carrying comparison is its optional `readEven`.
- [Lean reference, Processes](https://lean-lang.org/doc/reference/latest/IO/Processes/):
  `IO.Process.output`, arguments, standard output, and exit codes.
- [Mathlib, linear_combination](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html):
  combines explicit (in)equality proofs and checks the resulting polynomial identity.
- [leanprover/sos](https://github.com/leanprover/sos):
  inspiration for separating external SOS search from certificate verification.
  The classroom wrappers are new code; we do not import this Lean package.
- [Chenyang Yuan, SumOfSquares.py](https://github.com/yuanchenyang/SumOfSquares.py):
  the Python SOS library used by our adapter, with CVXOPT as its solver and
  SymPy for exact rational certificate conversion.

Source acknowledgments and license notices are in [attribution](attribution/README.txt).
