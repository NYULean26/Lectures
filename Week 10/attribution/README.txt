Sources and adaptations for Metaprogramming II: Asking another computer

Heather Macbeth, Simons 2025 metaprogramming tutorial (Apache-2.0):
https://github.com/hrmacbeth/Simons2025
Source revision: 44d1d930a3b532e6f77abe2a96931eed63884c81
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth.
The opening example, eq_or_le_succ_of_le, and recursive proof idea come from
Simons2025/Metaprogramming/Phase0_Model.lean and Phase2_Cleanup.lean.
Section 1 adapts these to tactic quotations and omega, rather than the source's
Qq expressions and explicit metavariable assignment. The original is linked
for further study; our small macro is not the complete Mathlib implementation.
The source file headers specify Apache-2.0. Its license text is included as
LICENSE-Metaprogramming-Book.txt in this directory.

The Hitchhiker's Guide to Logical Verification, 2026, chapter 8 (BSD-3-Clause):
https://github.com/lean-forward/logical_verification_2026
Source revision: 460f6be0846eefc3d9441e4e48d75753fcfe1709
Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg.
Section 4 adapts goal tracing and hypothesis from Week 09 and LoVe's chapter 8
demo. Sections 5–6 extend the sequence with proof construction and elaboration.
The instructor notes recall Week 09's conjunction example as a comparison.
The BSD-3-Clause license accompanies this notice.

Metaprogramming in Lean 4, chapters 3, 4, 7, and 9 (Apache-2.0):
https://leanprover-community.github.io/lean4-metaprogramming-book/
Consulted November 10–11, 2026. Goal inspection, expressions, quotations, and
tactic elaboration follow these chapters. Chapter 9 exercise 2 (forker) is
the closest source for 5's explicit conjunction proof and adapters.
The SOS classroom exercise is new.
The Apache-2.0 license accompanies this notice.

Functional Programming in Lean, section 4.5:
https://lean-lang.org/functional_programming_in_lean/Monads/The-IO-Monad/
Conceptual reference for IO; the file-reading/parser example continues Week 08.
No FPiL prose or code has been reproduced here.

Lean Language Reference, IO / Processes:
https://lean-lang.org/doc/reference/latest/IO/Processes/
API reference, checked against the installed v4.34.0-rc2 source and compiler.

Mathlib (Apache-2.0):
https://github.com/leanprover-community/mathlib4
Pinned source revision: 69fae596b29969db7afb6ac4a40653e882274410
Tactic/LinearCombination.lean: combines explicit nonnegativity proofs and
checks the polynomial identity. Copyright (c) 2022 Abby J. Goldberg.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth.
No Mathlib implementation is copied; the classroom tactic uses its public API.

Mirek Olšák and Jovan Gerbscheid, Introduction to Tactic Writing in Lean:
https://github.com/mirefek/lean-tactic-programming-guide
Source revision: a6c1b880df9fb938619832f5a043966bcb8c636c
Reference for sections 2–6: proof state, basic tactics, then syntax.
The guide's my_check and runConstructor examples inform sections 6.1 and 5. 6.2's exact-like elaborator is a course extension.
Our examples use the course's notation and Lean's public APIs; no prose is copied.
The repository is Apache-2.0; its license text is the same Apache-2.0 text already
included in this directory.

Section 3 uses MPiL 4's goal/hole viewpoints and the
Olšák–Gerbscheid guide's partial-proof annotations. The conjunction example,
inference-hole checkpoint, and teaching sequence are course adaptations.

2.2–2.3 use MPiL 3 as background for Expr's constructors, before introducing
metavariables in 3. Its inspector identifies the conjunction's head,
arguments, and an available local proof; it then constructs And P Q using const
and app, following MPiL 3, Constructing Expressions. Section 3 then distinguishes a hole
expression from its target type and follows its assignment.

Section 3.2 adapts MPiL 4, Basic Operations, to one Nat metavariable:
create it, use it in an application, assign it, and instantiate the expression.
Section 3.3 follows MPiL 4, Local Contexts, using the two implication goals
to illustrate withContext and lookup by a hypothesis name.
Section 4.2 follows MPiL 4's normalisation and definitional-equality exposition,
using a conjunction abbreviation to motivate whnf before matching And. It also
adapts the transparency example and demonstrates isDefEq assigning an unknown.
The two MetaM slides distinguish contextual information from assignment state,
then follow the create/build/assign/instantiate operations of section 3.2.
Section 5 shows the implicit arguments inferred by mkAppM.
FPiL 6.1–6.2 supplies the explanation of automatic IO lifting at the file boundary:
https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/Combining-IO-and-Reader/
https://lean-lang.org/functional_programming_in_lean/Monad-Transformers/A-Monad-Construction-Kit/

leanprover/sos:
https://github.com/leanprover/sos
Consulted November 11, 2026. Architectural inspiration for external SOS search
followed by rational certificate verification.
No source code or prose from this project is copied. The Python adapter, JSON
protocol, certificate builder, and classroom wrapper are new course code.

Chenyang Yuan, SumOfSquares.py (MIT):
https://github.com/yuanchenyang/SumOfSquares.py
Runtime dependency: SumOfSquares 1.3.1, installed from PyPI.
find_sos.py calls SOSProblem, add_sos_constraint, and solve, following the
upstream README example. CVXOPT performs the numerical solve; SymPy supplies
exact matrix decomposition for rational certificate conversion.
The classroom adapter restricts the input and output to quadratics and affine squares.

Sections 4.2.1 and 6.1.1 revisit the Macbeth warmup using the course's existing
lookup, expression-inspection, and tactic-quotation techniques. The first wrapper
extracts a natural-number lower bound from a local proof; the second adds a proof
term with have and delegates to that wrapper. These wrappers are course adaptations.
